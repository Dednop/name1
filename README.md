import os
import json
import threading
import queue
import shutil
import requests
import gpxpy
import pandas as pd
import warnings
from bs4 import BeautifulSoup
from geopy.distance import geodesic
import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk
import tempfile
import matplotlib
import psycopg2
from psycopg2.extras import execute_values, Json

matplotlib.use("Agg")
import matplotlib.pyplot as plt

import geopandas as gpd
import contextily as ctx
from geopy.geocoders import Nominatim
from PIL import Image, ImageTk
import numpy as np

from sklearn.cluster import MiniBatchKMeans

warnings.filterwarnings("ignore")


REFERENCE_COLORS = {
    "forest_nearby": (172, 206, 157),
    "water_nearby": (170, 211, 223),
    "road_nearby": (254, 254, 254),
    "building_nearby": (215, 208, 202),
}

ENV_COLS = list(REFERENCE_COLORS.keys())

MAPS_DIR = "maps"
AUG_MAPS_DIR = "augmented_maps"



def disable_widgets(widgets):
    for w in widgets:
        try:
            w.config(state="disabled")
        except Exception:
            pass


def enable_widgets(widgets):
    for w in widgets:
        try:
            w.config(state="normal")
        except Exception:
            pass


class ProgressWindow:

    def __init__(self, master, title="Выполнение...", text="Пожалуйста, подождите...",
                 determinate=False, maximum=100):
        self.master = master
        self.win = tk.Toplevel(master)
        self.win.title(title)
        self.win.geometry("460x140")
        self.win.resizable(False, False)
        self.win.transient(master)
        self.win.grab_set()

        self.label = tk.Label(self.win, text=text, wraplength=430, justify="left")
        self.label.pack(padx=14, pady=(14, 8), anchor="w")

        mode = "determinate" if determinate else "indeterminate"
        self.progress = ttk.Progressbar(self.win, orient="horizontal", length=430, mode=mode, maximum=maximum)
        self.progress.pack(padx=14, pady=(0, 12))


        self.win.protocol("WM_DELETE_WINDOW", lambda: None)

        if not determinate:
            self.progress.start(10)

    def set_text(self, text: str):
        try:
            self.label.config(text=text)
            self.label.update_idletasks()
        except Exception:
            pass

    def set_maximum(self, maximum: int):
        try:
            self.progress.config(maximum=maximum)
            self.progress.update_idletasks()
        except Exception:
            pass

    def set_value(self, value: float):
        try:
            self.progress.stop()
        except Exception:
            pass
        try:
            self.progress.config(mode="determinate")
            self.progress["value"] = value
            self.progress.update_idletasks()
        except Exception:
            pass

    def step(self, step: float = 1.0):
        try:
            self.progress.step(step)
            self.progress.update_idletasks()
        except Exception:
            pass

    def close(self):
        try:
            self.progress.stop()
        except Exception:
            pass
        try:
            self.win.grab_release()
        except Exception:
            pass
        try:
            self.win.destroy()
        except Exception:
            pass


class AsyncRunner:
    """
    Выполняет тяжёлую функцию в отдельном потоке, чтобы не фризить Tkinter.
    Worker получает progress_cb, через который можно слать:
      {"type":"text","text": "..." }
      {"type":"max","max": N}
      {"type":"value","value": x}
      {"type":"step","step": s}
    """

    def __init__(self, master):
        self.master = master
        self.q = queue.Queue()
        self._polling = False

    def run(self, worker_fn, on_done=None, on_error=None, on_progress=None):
        def progress_cb(payload: dict):
            self.q.put(("progress", payload))

        def target():
            try:
                res = worker_fn(progress_cb)
                self.q.put(("done", res))
            except Exception as e:
                self.q.put(("error", e))

        threading.Thread(target=target, daemon=True).start()

        if not self._polling:
            self._polling = True
            self._poll(on_done, on_error, on_progress)

    def _poll(self, on_done, on_error, on_progress):
        try:
            while True:
                kind, payload = self.q.get_nowait()
                if kind == "progress" and on_progress:
                    on_progress(payload)
                elif kind == "done":
                    self._polling = False
                    if on_done:
                        on_done(payload)
                    return
                elif kind == "error":
                    self._polling = False
                    if on_error:
                        on_error(payload)
                    return
        except queue.Empty:
            pass

        self.master.after(100, lambda: self._poll(on_done, on_error, on_progress))



def _calc_bounds_and_figsize(gdf_3857, pad_ratio=0.10, fallback_pad=50, base_w=8.0):
    minx, miny, maxx, maxy = gdf_3857.total_bounds
    pad_x = (maxx - minx) * pad_ratio if (maxx - minx) != 0 else fallback_pad
    pad_y = (maxy - miny) * pad_ratio if (maxy - miny) != 0 else fallback_pad

    tminx, tminy, tmaxx, tmaxy = (minx - pad_x, miny - pad_y, maxx + pad_x, maxy + pad_y)

    bw = max(tmaxx - tminx, 1e-9)
    bh = max(tmaxy - tminy, 1e-9)
    aspect = bh / bw

    fig_w = base_w
    fig_h = base_w * aspect

    return (tminx, tminy, tmaxx, tmaxy), (fig_w, fig_h)


def _meta_path(dir_path: str, track_id: int) -> str:
    return os.path.join(dir_path, f"track_{track_id}_meta.json")


def save_track_assets(df_track: pd.DataFrame, track_id: int, out_dir: str = MAPS_DIR):
    """
    Сохраняет 3 файла:
      - track_{id}_basemap.png  (только фон)
      - track_{id}_route.png    (только маршрут, прозрачный)
      - track_{id}_combined.png (фон + маршрут)
    + сохраняет META:
      - track_{id}_meta.json (bbox_3857 + W/H)
    """
    os.makedirs(out_dir, exist_ok=True)

    gdf = gpd.GeoDataFrame(
        df_track,
        geometry=gpd.points_from_xy(df_track.longitude, df_track.latitude),
        crs="EPSG:4326"
    )
    gdf_3857 = gdf.to_crs(epsg=3857)

    bounds, (fig_w, fig_h) = _calc_bounds_and_figsize(gdf_3857)
    tminx, tminy, tmaxx, tmaxy = bounds

    basemap_path = os.path.join(out_dir, f"track_{track_id}_basemap.png")
    route_path = os.path.join(out_dir, f"track_{track_id}_route.png")
    combined_path = os.path.join(out_dir, f"track_{track_id}_combined.png")

    fig, ax = plt.subplots(figsize=(fig_w, fig_h))
    fig.subplots_adjust(left=0, right=1, bottom=0, top=1)
    ax.set_xlim(tminx, tmaxx)
    ax.set_ylim(tminy, tmaxy)
    ax.set_axis_off()
    ax.margins(0)

    ctx.add_basemap(ax, source=ctx.providers.OpenStreetMap.Mapnik)

    plt.savefig(basemap_path, dpi=300, pad_inches=0, bbox_inches=None)
    plt.close(fig)

    base_img = Image.open(basemap_path)
    W, H = base_img.size
    meta = {
        "bbox_3857": [float(tminx), float(tminy), float(tmaxx), float(tmaxy)],
        "width": int(W),
        "height": int(H),
    }
    with open(_meta_path(out_dir, track_id), "w", encoding="utf-8") as f:
        json.dump(meta, f, ensure_ascii=False, indent=2)

    fig, ax = plt.subplots(figsize=(fig_w, fig_h))
    fig.subplots_adjust(left=0, right=1, bottom=0, top=1)
    ax.set_xlim(tminx, tmaxx)
    ax.set_ylim(tminy, tmaxy)
    ax.set_axis_off()
    ax.margins(0)

    ax.plot(
        gdf_3857.geometry.x,
        gdf_3857.geometry.y,
        color="red",
        linewidth=2,
        marker="o",
        markersize=2
    )

    plt.savefig(route_path, dpi=300, pad_inches=0, bbox_inches=None, transparent=True)
    plt.close(fig)

    base_img_rgba = base_img.convert("RGBA")
    route_img = Image.open(route_path).convert("RGBA")
    if route_img.size != base_img_rgba.size:
        route_img = route_img.resize(base_img_rgba.size, Image.Resampling.LANCZOS)
    combined = Image.alpha_composite(base_img_rgba, route_img)
    combined.save(combined_path)

    return basemap_path, route_path, combined_path


def classify_environment(colors, ref_colors, threshold=30):
    attrs = {k: False for k in ref_colors.keys()}
    for c in colors:
        for name, ref in ref_colors.items():
            dist = np.linalg.norm(np.array(c) - np.array(ref))
            if dist <= threshold:
                attrs[name] = True
    return attrs


def _load_meta(meta_path: str):
    with open(meta_path, "r", encoding="utf-8") as f:
        return json.load(f)


def _ensure_rgb_np(img: Image.Image) -> np.ndarray:
    arr = np.asarray(img)
    if arr.ndim == 2:
        arr = np.stack([arr, arr, arr], axis=-1)
    elif arr.ndim == 3 and arr.shape[2] == 4:
        arr = arr[:, :, :3]
    elif arr.ndim == 3 and arr.shape[2] >= 3:
        arr = arr[:, :, :3]
    return arr


def add_environment_for_track_from_image(
        df_track: pd.DataFrame,
        basemap_png_path: str,
        meta_json_path: str,
        radius_m=500,
        n_clusters=6,
        threshold=35,
        sample_max_pixels=20000
) -> pd.DataFrame:
    """
    Считает окружение для точек df_track по картинке basemap_png_path.
    Маппинг координат -> пиксель по bbox из meta_json_path.
    """
    if df_track.empty:
        return df_track

    meta = _load_meta(meta_json_path)
    tminx, tminy, tmaxx, tmaxy = meta["bbox_3857"]
    W = int(meta["width"])
    H = int(meta["height"])

    base_img = Image.open(basemap_png_path).convert("RGB")
    img = _ensure_rgb_np(base_img)

    mpp_x = (tmaxx - tminx) / max(W, 1)
    mpp_y = (tmaxy - tminy) / max(H, 1)
    mpp = float((mpp_x + mpp_y) / 2.0) if (mpp_x > 0 and mpp_y > 0) else max(mpp_x, mpp_y, 1.0)
    radius_px = int(max(3, radius_m / max(mpp, 1e-9)))

    gdf = gpd.GeoDataFrame(
        df_track,
        geometry=gpd.points_from_xy(df_track.longitude, df_track.latitude),
        crs="EPSG:4326"
    ).to_crs(epsg=3857)

    xs = gdf.geometry.x.to_numpy()
    ys = gdf.geometry.y.to_numpy()

    env_rows = []
    for x, y in zip(xs, ys):
        px = int((x - tminx) / max(tmaxx - tminx, 1e-9) * (W - 1))
        py = int((tmaxy - y) / max(tmaxy - tminy, 1e-9) * (H - 1))

        if px < 0 or px >= W or py < 0 or py >= H:
            env_rows.append({k: False for k in REFERENCE_COLORS.keys()})
            continue

        x0 = max(0, px - radius_px)
        x1 = min(W, px + radius_px)
        y0 = max(0, py - radius_px)
        y1 = min(H, py + radius_px)

        patch = img[y0:y1, x0:x1]
        if patch.size == 0:
            env_rows.append({k: False for k in REFERENCE_COLORS.keys()})
            continue

        pixels = patch.reshape(-1, 3)

        if pixels.shape[0] > sample_max_pixels:
            idx = np.random.choice(pixels.shape[0], size=sample_max_pixels, replace=False)
            pixels = pixels[idx]

        kmeans = MiniBatchKMeans(n_clusters=n_clusters, batch_size=2048, n_init=1)
        kmeans.fit(pixels)
        colors = kmeans.cluster_centers_.astype(int)

        attrs = classify_environment(colors, REFERENCE_COLORS, threshold)
        env_rows.append(attrs)

    env_df = pd.DataFrame(env_rows)
    out = df_track.copy()
    for c in ENV_COLS:
        out[c] = env_df[c].values
    return out


def visualize_environment_from_image_for_point(
        df_track: pd.DataFrame,
        point_idx: int,
        basemap_png_path: str,
        meta_json_path: str,
        radius_m=500,
        n_clusters=6,
        threshold=35,
        sample_max_pixels=20000
):
    """
    Наглядная проверка:
    - basemap (именно та, по которой считаем окружение)
    - маршрут трека (в пикселях basemap)
    - выбранная точка МАРШРУТА + круг 500м
    - patch (вырезанный участок)
    - палитра доминирующих цветов (kmeans центры)
    """
    if df_track.empty:
        return None
    if point_idx not in df_track.index:
        return None

    meta = _load_meta(meta_json_path)
    tminx, tminy, tmaxx, tmaxy = meta["bbox_3857"]
    W = int(meta["width"])
    H = int(meta["height"])

    base_img = Image.open(basemap_png_path).convert("RGB")
    img_np = _ensure_rgb_np(base_img)

    mpp_x = (tmaxx - tminx) / max(W, 1)
    mpp_y = (tmaxy - tminy) / max(H, 1)
    mpp = float((mpp_x + mpp_y) / 2.0) if (mpp_x > 0 and mpp_y > 0) else max(mpp_x, mpp_y, 1.0)
    radius_px = int(max(3, radius_m / max(mpp, 1e-9)))

    gdf_all = gpd.GeoDataFrame(
        df_track,
        geometry=gpd.points_from_xy(df_track.longitude, df_track.latitude),
        crs="EPSG:4326"
    ).to_crs(epsg=3857)

    xs = gdf_all.geometry.x.to_numpy()
    ys = gdf_all.geometry.y.to_numpy()


    denom_x = max(tmaxx - tminx, 1e-9)
    denom_y = max(tmaxy - tminy, 1e-9)

    px_all = ((xs - tminx) / denom_x * (W - 1)).astype(int)
    py_all = ((tmaxy - ys) / denom_y * (H - 1)).astype(int)

    px_all = np.clip(px_all, 0, W - 1)
    py_all = np.clip(py_all, 0, H - 1)

    pos = np.where(df_track.index.to_numpy() == point_idx)[0]
    if len(pos) == 0:
        return None
    ppos = int(pos[0])

    px = int(px_all[ppos])
    py = int(py_all[ppos])

    x0 = max(0, px - radius_px)
    x1 = min(W, px + radius_px)
    y0 = max(0, py - radius_px)
    y1 = min(H, py + radius_px)

    patch_np = img_np[y0:y1, x0:x1]
    if patch_np.size == 0:
        return None

    pixels = patch_np.reshape(-1, 3)
    if pixels.shape[0] > sample_max_pixels:
        idx = np.random.choice(pixels.shape[0], size=sample_max_pixels, replace=False)
        pixels = pixels[idx]

    kmeans = MiniBatchKMeans(n_clusters=n_clusters, batch_size=2048, n_init=1)
    kmeans.fit(pixels)
    colors = kmeans.cluster_centers_.astype(int)

    attrs = classify_environment(colors, REFERENCE_COLORS, threshold)

    out_dir = tempfile.gettempdir()
    map_path = os.path.join(out_dir, "env_debug_map.png")
    patch_path = os.path.join(out_dir, "env_debug_patch.png")
    palette_path = os.path.join(out_dir, "env_debug_palette.png")

    fig, ax = plt.subplots(figsize=(9, 7))
    ax.imshow(img_np)

    ax.plot(px_all, py_all, linewidth=2)

    ax.scatter([px], [py], s=110, marker="o")
    ax.scatter([px], [py], s=90, marker="x")

    circ = plt.Circle((px, py), radius_px, fill=False, linewidth=2)
    ax.add_patch(circ)

    ax.set_title("Окружение считается вокруг точки МАРШРУТА:\nлиния=маршрут, точка=выбранная точка маршрута, круг=500м")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(map_path, dpi=200)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(patch_np)
    ax.set_title("Patch вокруг точки маршрута (радиус 500м)")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(patch_path, dpi=200)
    plt.close(fig)

    palette = np.zeros((60, 60 * len(colors), 3), dtype=np.uint8)
    for i, c in enumerate(colors):
        palette[:, i * 60:(i + 1) * 60, :] = c

    fig, ax = plt.subplots(figsize=(max(6, len(colors) * 1.2), 2.2))
    ax.imshow(palette)
    ax.set_title("Доминирующие цвета patch (KMeans cluster centers)")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(palette_path, dpi=200)
    plt.close(fig)

    return {
        "map_path": map_path,
        "patch_path": patch_path,
        "palette_path": palette_path,
        "attrs": attrs,
        "point_pixel": (px, py),
        "radius_px": radius_px,
        "bbox_3857": (tminx, tminy, tmaxx, tmaxy),
        "point_idx": int(point_idx),
    }


def add_environment_attributes_by_track_images(df: pd.DataFrame, progress_cb=None):
    """
    Окружение по картинке для всех треков (в основной df).
    """
    if df is None or df.empty:
        return df

    track_ids = sorted(df["track_id"].unique())
    if progress_cb:
        progress_cb({"type": "max", "max": len(track_ids)})

    parts = []
    for i, tid in enumerate(track_ids, start=1):
        if progress_cb:
            progress_cb({"type": "text", "text": f"Окружение по картинке: трек {tid} ({i}/{len(track_ids)})..."})
            progress_cb({"type": "value", "value": i - 1})

        df_track = df[df["track_id"] == tid].copy()

        aug_base = os.path.join(AUG_MAPS_DIR, f"track_{tid}_basemap.png")
        aug_meta = _meta_path(AUG_MAPS_DIR, tid)

        orig_base = os.path.join(MAPS_DIR, f"track_{tid}_basemap.png")
        orig_meta = _meta_path(MAPS_DIR, tid)

        if os.path.exists(aug_base) and os.path.exists(aug_meta):
            base_path, meta_path = aug_base, aug_meta
        elif os.path.exists(orig_base) and os.path.exists(orig_meta):
            base_path, meta_path = orig_base, orig_meta
        else:
            for c in ENV_COLS:
                df_track[c] = False
            parts.append(df_track)
            if progress_cb:
                progress_cb({"type": "value", "value": i})
            continue

        df_track_env = add_environment_for_track_from_image(
            df_track,
            basemap_png_path=base_path,
            meta_json_path=meta_path,
            radius_m=500,
            n_clusters=6,
            threshold=35
        )
        parts.append(df_track_env)

        if progress_cb:
            progress_cb({"type": "value", "value": i})

    return pd.concat(parts, ignore_index=True)

def build_window_features(df: pd.DataFrame, window_size: int = 5) -> pd.DataFrame:
    """
    Делает новый DataFrame с признаками по "участкам" (окнам).
    Ничего в исходный df не записывает.
    """
    if df is None or df.empty:
        return pd.DataFrame()

    if "track_id" not in df.columns:
        return pd.DataFrame()

    d = df.copy()
    if "time" in d.columns:
        d = d.sort_values(["track_id", "time"]).reset_index(drop=True)
    else:
        d = d.sort_values(["track_id"]).reset_index(drop=True)

    rows = []
    for tid, g in d.groupby("track_id"):
        g = g.reset_index(drop=True)
        if len(g) < window_size:
            continue

        for start in range(0, len(g) - window_size + 1):
            w = g.iloc[start:start + window_size]

            dist_sum = float(w["distance_to_previous"].fillna(0).sum()) if "distance_to_previous" in w.columns else 0.0

            elev_gain = elev_loss = slope_mean = slope_std = 0.0
            if "elevation" in w.columns and "distance_to_previous" in w.columns:
                elev = pd.to_numeric(w["elevation"], errors="coerce").to_numpy()
                dist = pd.to_numeric(w["distance_to_previous"], errors="coerce").fillna(0).to_numpy()
                de = np.diff(elev)
                dd = np.clip(dist[1:], 1e-6, None)

                if len(de) > 0:
                    elev_gain = float(np.nansum(de[de > 0]))
                    elev_loss = float(np.nansum(-de[de < 0]))
                    slopes = de / dd
                    slope_mean = float(np.nanmean(slopes))
                    slope_std = float(np.nanstd(slopes))

            temp_mean = temp_std = np.nan
            if "temperature" in w.columns:
                temps = pd.to_numeric(w["temperature"], errors="coerce")
                temp_mean = float(temps.mean())
                temp_std = float(temps.std())

            env_feats = {}
            for c in ENV_COLS:
                out_name = c.replace("_nearby", "_share")
                if c in w.columns:
                    env_feats[out_name] = float(w[c].astype(bool).mean())
                else:
                    env_feats[out_name] = np.nan

            season = None
            if "season" in w.columns and pd.notna(w["season"].iloc[0]):
                season = str(w["season"].iloc[0])

            rows.append({
                "track_id": int(tid),
                "window_start": int(start),
                "dist_sum": dist_sum,
                "elev_gain": elev_gain,
                "elev_loss": elev_loss,
                "slope_mean": slope_mean,
                "slope_std": slope_std,
                "temp_mean": temp_mean,
                "temp_std": temp_std,
                "season": season,
                **env_feats,
            })

    return pd.DataFrame(rows)


class GPXLoaderAgent:
    def __init__(self):
        self.dataframes = []
        self.geolocator = Nominatim(user_agent="track_region_identifier")

    def _load_single_gpx(self, track_url: str, track_id: int) -> pd.DataFrame:
        response = requests.get(track_url, timeout=30)
        response.raise_for_status()

        soup = BeautifulSoup(response.text, "html.parser")
        gpx_link = None
        for a in soup.find_all("a"):
            href = a.get("href", "")
            if href.endswith(".gpx"):
                gpx_link = href if href.startswith("http") else f"https://caucasia.ru{href}"
                break

        if not gpx_link:
            raise ValueError("Не удалось найти GPX-файл")

        gpx_response = requests.get(gpx_link, timeout=30)
        gpx_response.raise_for_status()
        gpx = gpxpy.parse(gpx_response.text)

        data = {
            "latitude": [],
            "longitude": [],
            "elevation": [],
            "time": [],
            "temperature": [],
            "heart_rate": [],
            "cadence": [],
            "track_id": []
        }

        for track in gpx.tracks:
            for segment in track.segments:
                for point in segment.points:
                    data["latitude"].append(point.latitude)
                    data["longitude"].append(point.longitude)
                    data["elevation"].append(point.elevation)
                    data["time"].append(point.time)

                    temperature = heart_rate = cadence = None
                    if point.extensions:
                        for ext in point.extensions:
                            if ext.tag.endswith("TrackPointExtension"):
                                for child in ext:
                                    if child.tag.endswith("atemp"):
                                        temperature = float(child.text)
                                    elif child.tag.endswith("hr"):
                                        heart_rate = int(child.text)
                                    elif child.tag.endswith("cad"):
                                        cadence = int(child.text)

                    data["temperature"].append(temperature)
                    data["heart_rate"].append(heart_rate)
                    data["cadence"].append(cadence)
                    data["track_id"].append(track_id)

        df = pd.DataFrame(data)
        df = self._calculate_distances(df)
        return df

    def _calculate_distances(self, df: pd.DataFrame) -> pd.DataFrame:
        distances = [0]
        for i in range(1, len(df)):
            if df.iloc[i]["track_id"] != df.iloc[i - 1]["track_id"]:
                distances.append(0)
            else:
                p1 = (df.iloc[i - 1]["latitude"], df.iloc[i - 1]["longitude"])
                p2 = (df.iloc[i]["latitude"], df.iloc[i]["longitude"])
                distances.append(geodesic(p1, p2).meters)
        df["distance_to_previous"] = distances
        return df

    def _filter_track_points(self, df: pd.DataFrame, target_distance=500) -> pd.DataFrame:
        if len(df) == 0:
            return df

        filtered = [df.iloc[0]]
        current_sum = 0
        for i in range(1, len(df)):
            current_sum += df.loc[i, "distance_to_previous"]
            if current_sum >= target_distance:
                filtered.append(df.iloc[i])
                current_sum = 0

        if filtered[-1].name != df.iloc[-1].name:
            filtered.append(df.iloc[-1])

        out = pd.DataFrame(filtered).reset_index(drop=True)

        distances = [0]
        for i in range(1, len(out)):
            p1 = (out.iloc[i - 1]["latitude"], out.iloc[i - 1]["longitude"])
            p2 = (out.iloc[i]["latitude"], out.iloc[i]["longitude"])
            distances.append(geodesic(p1, p2).meters)
        out["distance_to_previous"] = distances
        return out

    def fetch_temperature_day(self, lat, lon, date_str):
        """
        Запрос на один день по одной (округленной) координате.
        Возвращает dict: {"YYYY-MM-DDTHH:00": temp, ...}
        """
        url = "https://archive-api.open-meteo.com/v1/archive"
        params = {
            "latitude": lat,
            "longitude": lon,
            "start_date": date_str,
            "end_date": date_str,
            "hourly": "temperature_2m",
            "timezone": "UTC",
        }
        resp = requests.get(url, params=params, timeout=20)
        if resp.status_code != 200:
            return None
        data = resp.json()
        times = data.get("hourly", {}).get("time", [])
        temps = data.get("hourly", {}).get("temperature_2m", [])
        return dict(zip(times, temps))

    def fill_temperatures(self, df: pd.DataFrame, progress_cb=None, coord_round=3):
        """
        Быстрое заполнение температур:
        - округляем координаты (для кэша)
        - группируем по (lat_r, lon_r, date)
        - на каждую группу 1 запрос в Open-Meteo
        - берём температуру по часу
        """
        df = df.copy()

        if "time" not in df.columns:
            return df

        mask = df["temperature"].isna()
        if mask.sum() == 0:
            return df

        lat_r = df.loc[mask, "latitude"].round(coord_round)
        lon_r = df.loc[mask, "longitude"].round(coord_round)

        t = df.loc[mask, "time"]
        try:
            t_utc = t.dt.tz_convert("UTC")
        except Exception:
            t_utc = pd.to_datetime(t, utc=True)

        date_str = t_utc.dt.strftime("%Y-%m-%d")

        hour_key = t_utc.dt.floor("h").dt.strftime("%Y-%m-%dT%H:00")

        tmp = pd.DataFrame({
            "idx": df.loc[mask].index,
            "lat": lat_r.values,
            "lon": lon_r.values,
            "date": date_str.values,
            "hour_key": hour_key.values,
        })

        groups = tmp.groupby(["lat", "lon", "date"], sort=False)

        cache = {}

        total_groups = len(groups)
        if progress_cb:
            progress_cb({"type": "max", "max": total_groups})

        done = 0
        for (lat, lon, dstr), g in groups:
            if progress_cb:
                progress_cb(
                    {"type": "text", "text": f"Температуры: {done + 1}/{total_groups} (lat={lat}, lon={lon}, {dstr})"})
                progress_cb({"type": "value", "value": done})

            key = (float(lat), float(lon), str(dstr))
            if key not in cache:
                try:
                    cache[key] = self.fetch_temperature_day(key[0], key[1], key[2])
                except Exception:
                    cache[key] = None

            day_map = cache[key] or {}

            for _, row in g.iterrows():
                hk = row["hour_key"]
                temp = day_map.get(hk, None)
                df.at[row["idx"], "temperature"] = temp

            done += 1
            if progress_cb:
                progress_cb({"type": "value", "value": done})

        return df

    def add_seasons(self, df: pd.DataFrame) -> pd.DataFrame:
        def get_season(m):
            return ("winter" if m in [12, 1, 2] else
                    "spring" if m in [3, 4, 5] else
                    "summer" if m in [6, 7, 8] else
                    "autumn")

        season_month = {"winter": 1, "spring": 4, "summer": 7, "autumn": 10}

        df = df.copy()
        df["season"] = df["time"].dt.month.apply(get_season)

        rows_to_add = []
        for _, row in df.iterrows():
            old_time = row["time"]
            curr_season = row["season"]
            for s in ["winter", "spring", "summer", "autumn"]:
                if s == curr_season:
                    continue

                new_row = row.copy()
                new_row["time"] = pd.Timestamp(
                    year=old_time.year,
                    month=season_month[s],
                    day=old_time.day,
                    hour=old_time.hour,
                    minute=old_time.minute,
                    second=old_time.second,
                    tz=old_time.tz
                )
                new_row["temperature"] = None
                new_row["season"] = s
                rows_to_add.append(new_row)

        df = pd.concat([df, pd.DataFrame(rows_to_add)], ignore_index=True)
        return df

    def _get_region(self, lat, lon):
        try:
            location = self.geolocator.reverse((lat, lon), language="ru", timeout=10)
            if location and "address" in location.raw:
                addr = location.raw["address"]
                return addr.get("state") or addr.get("region") or addr.get("country")
        except Exception:
            return None


class GPXMapAgent:
    def __init__(self, df: pd.DataFrame):
        self.df = df
        self.gdf = gpd.GeoDataFrame(
            df,
            geometry=gpd.points_from_xy(df.longitude, df.latitude),
            crs="EPSG:4326"
        )

    def plot_track_to_png(self, track_id: int, save_folder: str = MAPS_DIR):
        combined_path = os.path.join(save_folder, f"track_{track_id}_combined.png")
        if os.path.exists(combined_path):
            return combined_path

        group = self.gdf[self.gdf.track_id == track_id]
        if group.empty:
            raise ValueError("Трек не найден")

        bounds = group.to_crs(epsg=3857).total_bounds
        minx, miny, maxx, maxy = bounds
        width = maxx - minx
        height = maxy - miny
        aspect = height / width if width != 0 else 1.0

        base_size = 10
        fig_width = base_size
        fig_height = base_size * aspect

        fig, ax = plt.subplots(figsize=(fig_width, fig_height))
        fig.subplots_adjust(left=0, right=1, bottom=0, top=1)

        gdf_3857 = group.to_crs(epsg=3857)
        ax.plot(gdf_3857.geometry.x, gdf_3857.geometry.y, color="red", linewidth=2, marker="o", markersize=2)

        ctx.add_basemap(ax, source=ctx.providers.OpenStreetMap.Mapnik)
        ax.set_aspect("equal", adjustable="box")
        ax.set_axis_off()
        ax.margins(0)

        os.makedirs(save_folder, exist_ok=True)
        png_path = os.path.join(save_folder, f"track_{track_id}.png")

        plt.savefig(png_path, dpi=300, pad_inches=0, bbox_inches=None)
        plt.close(fig)

        return png_path


def compute_corr_heatmap_and_explanations(
        df_windows: pd.DataFrame,
        top_k: int = 10,
        corr_threshold: float = 0.45,
):
    """
    Делает:
    - корреляционную матрицу по числовым признакам окон
    - heatmap (PNG)
    - выбирает top_k "значимых" признаков по их 'связности'
      (средняя |corr| с остальными признаками)
    - формирует объяснения с конкретными r
    """
    if df_windows is None or df_windows.empty:
        return None

    dfw = df_windows.copy()

    num = dfw.select_dtypes(include=[np.number]).copy()

    for col in ["track_id", "window_start"]:
        if col in num.columns:
            num.drop(columns=[col], inplace=True)

    if num.shape[1] < 3:
        return None

    num = num.replace([np.inf, -np.inf], np.nan)
    num = num.dropna(axis=1, how="all")
    num = num.fillna(num.median(numeric_only=True))

    if num.shape[1] < 3:
        return None

    corr = num.corr(method="spearman")

    abs_corr = corr.abs()
    np.fill_diagonal(abs_corr.values, np.nan)
    connectivity = abs_corr.mean(axis=1).sort_values(ascending=False)

    top_features = connectivity.head(min(top_k, len(connectivity))).index.tolist()

    explanations = []
    for feat in top_features:
        s = corr[feat].drop(index=feat).sort_values(key=lambda x: x.abs(), ascending=False)

        strong = s[s.abs() >= corr_threshold].head(4)

        if len(strong) == 0:
            explanations.append(
                f"• **{feat}** важен: у него высокая средняя |корреляция| с другими признаками "
                f"(связность ≈ {connectivity.loc[feat]:.3f}), то есть он хорошо описывает общий характер участка."
            )
            continue

        pairs_txt = ", ".join([f"{idx} (r={val:+.2f})" for idx, val in strong.items()])

        explanations.append(
            f"• **{feat}** важен: он сильно коррелирует с {pairs_txt}. "
            f"Это значит, что **{feat}** отражает общий фактор участка маршрута (например рельеф/урбанизацию/ландшафт), "
            f"и помогает отличать разные типы участков."
        )

    heatmap_path = os.path.join(tempfile.gettempdir(), "corr_heatmap.png")

    fig, ax = plt.subplots(figsize=(10, 8))
    im = ax.imshow(corr.values, aspect="auto")
    ax.set_xticks(range(len(corr.columns)))
    ax.set_yticks(range(len(corr.index)))
    ax.set_xticklabels(corr.columns, rotation=90, fontsize=8)
    ax.set_yticklabels(corr.index, fontsize=8)
    fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    ax.set_title("Корреляционная матрица признаков (Spearman)")
    fig.tight_layout()
    fig.savefig(heatmap_path, dpi=200)
    plt.close(fig)

    return {
        "corr": corr,
        "connectivity": connectivity,
        "top_features": top_features,
        "explanations": explanations,
        "heatmap_path": heatmap_path,
    }


def _select_existing_feature_columns(df: pd.DataFrame):
    """
    Берём только существующие признаки из df, которые логично использовать в модели.
    Ничего не создаём нового.
    """
    if df is None or df.empty:
        return []

    exclude = {
        "track_id",
        "time",
        "latitude",
        "longitude",
        "geometry",
        "window_start",
    }

    cand = []
    for c in df.columns:
        if c in exclude:
            continue
        s = df[c]
        if pd.api.types.is_bool_dtype(s):
            cand.append(c)
        elif pd.api.types.is_numeric_dtype(s):
            cand.append(c)
    return cand


def compute_heatmap_and_pick_features_from_existing_df(
        df: pd.DataFrame,
        top_k: int = 12,
        strong_corr_threshold: float = 0.45,
        drop_corr_threshold: float = 0.85,
):
    """
    1) Берём только существующие признаки result_df (числовые + булевые).
    2) Строим Spearman corr heatmap.
    3) Выбираем значимые признаки по связности (mean |corr|).
    4) Убираем сильно коррелирующие дубли.
    5) Возвращаем heatmap png + список выбранных фич + объяснения с конкретными r.
    """
    cols = _select_existing_feature_columns(df)
    if len(cols) < 3:
        return None

    X = df[cols].copy()

    for c in X.columns:
        if pd.api.types.is_bool_dtype(X[c]):
            X[c] = X[c].astype(int)

    X = X.replace([np.inf, -np.inf], np.nan)

    X = X.dropna(axis=1, how="all")
    if X.shape[1] < 3:
        return None

    X = X.fillna(X.median(numeric_only=True))

    corr = X.corr(method="spearman")

    abs_corr = corr.abs().copy()
    np.fill_diagonal(abs_corr.values, np.nan)
    connectivity = abs_corr.mean(axis=1).sort_values(ascending=False)

    candidates = connectivity.head(min(top_k, len(connectivity))).index.tolist()

    selected = []
    for f in candidates:
        keep = True
        for s in selected:
            if abs(corr.loc[f, s]) >= drop_corr_threshold:
                keep = False
                break
        if keep:
            selected.append(f)

    explanations = []
    for f in selected:
        s = corr[f].drop(index=f).sort_values(key=lambda x: x.abs(), ascending=False)
        strong = s[s.abs() >= strong_corr_threshold].head(5)

        if len(strong) == 0:
            explanations.append(
                f"- {f}: выбран, потому что имеет высокую среднюю связь с другими признаками "
                f"(связность={connectivity.loc[f]:.3f}), даже если нет отдельных очень сильных пар."
            )
            continue

        pairs = ", ".join([f"{idx} (r={val:+.2f})" for idx, val in strong.items()])
        explanations.append(
            f"- {f}: важен, потому что сильно коррелирует с {pairs}. "
            f"Это означает, что {f} отражает общий фактор структуры данных и помогает различать типы участков."
        )

    import tempfile

    heatmap_path = os.path.join(tempfile.gettempdir(), "corr_heatmap.png")
    fig, ax = plt.subplots(figsize=(10, 8))
    im = ax.imshow(corr.values, aspect="auto", cmap="coolwarm", vmin=-1, vmax=1)
    ax.set_xticks(range(len(corr.columns)))
    ax.set_yticks(range(len(corr.index)))
    ax.set_xticklabels(corr.columns, rotation=90, fontsize=8)
    ax.set_yticklabels(corr.index, fontsize=8)
    fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    ax.set_title("Correlation heatmap (Spearman), cmap=coolwarm")
    fig.tight_layout()
    fig.savefig(heatmap_path, dpi=200)
    plt.close(fig)

    return {
        "corr": corr,
        "connectivity": connectivity,
        "selected_features": selected,
        "explanations": explanations,
        "heatmap_path": heatmap_path,
    }


def cleanup_image_folders():
    """Чистим папки с картинками треков при выходе из программы."""
    for folder in [MAPS_DIR, AUG_MAPS_DIR]:
        try:
            if os.path.exists(folder) and os.path.isdir(folder):
                shutil.rmtree(folder, ignore_errors=True)
        except Exception:
            pass


class GPXAppGUI:
    def __init__(self, master):
        self.master = master
        master.title("GPX Tracks Manager")
        master.geometry("1000x600")

        self.agent = GPXLoaderAgent()
        self.result_df = None
        self.runner = AsyncRunner(master)

        self.all_buttons = []

        self.notebook = ttk.Notebook(master)
        self.notebook.pack(fill="both", expand=True)

        self.tab_load = ttk.Frame(self.notebook)
        self.tab_process = ttk.Frame(self.notebook)
        self.tab_view = ttk.Frame(self.notebook)
        self.tab_augment = ttk.Frame(self.notebook)

        self.notebook.add(self.tab_load, text="Загрузка треков")
        self.notebook.add(self.tab_process, text="Обработка треков")
        self.notebook.add(self.tab_view, text="Просмотр треков")
        self.notebook.add(self.tab_augment, text="Аугментация треков")

        self.create_tab_load()
        self.create_tab_process()
        self.create_tab_view()
        self.create_tab_augment()

    def _open_image_window(self, path, title):
        if not os.path.exists(path):
            messagebox.showerror("Ошибка", "Файл изображения не найден")
            return

        win = tk.Toplevel(self.master)
        win.title(title)

        img = Image.open(path)
        max_w, max_h = 1000, 800
        w, h = img.size
        scale_k = min(max_w / w, max_h / h, 1.0)
        if scale_k < 1.0:
            img = img.resize((int(w * scale_k), int(h * scale_k)))

        img_tk = ImageTk.PhotoImage(img)
        lbl = tk.Label(win, image=img_tk)
        lbl.image = img_tk
        lbl.pack(padx=10, pady=10)

    def _reg_btn(self, btn):
        self.all_buttons.append(btn)
        return btn

    def save_all_tracks_to_one_excel(self):
        """
        Сохраняет все треки в ОДИН Excel-файл:
        каждый track_id -> отдельный лист.
        """
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning(
                "Ошибка",
                "Для выполнения операции необходимо сначала загрузить данные."
            )
            return

        out_dir = os.path.join(os.getcwd(), "exports")
        os.makedirs(out_dir, exist_ok=True)

        out_path = os.path.join(out_dir, "all_tracks_by_sheets.xlsx")

        try:
            with pd.ExcelWriter(out_path) as writer:
                for tid in sorted(self.result_df["track_id"].unique()):
                    df_t = self.result_df[self.result_df["track_id"] == tid].copy()

                    for col in df_t.columns:
                        if pd.api.types.is_datetime64tz_dtype(df_t[col]):
                            df_t[col] = df_t[col].dt.tz_localize(None)

                    sheet_name = f"track_{int(tid)}"
                    df_t.to_excel(writer, sheet_name=sheet_name[:31], index=False)

            messagebox.showinfo("Готово", f"Сохранено в один файл:\n{out_path}")

        except Exception as e:
            messagebox.showerror("Ошибка сохранения", str(e))

    def set_busy(self, busy: bool):
        if busy:
            disable_widgets(self.all_buttons)
        else:
            enable_widgets(self.all_buttons)


    def create_tab_load(self):
        tk.Label(self.tab_load, text="Загрузка треков", font=("Arial", 14, "bold")).pack(pady=(10, 4))

        hint = (
            "Формат ввода ссылок на GPX-треки:\n"
            "• Каждая ссылка может быть указана на отдельной строке\n"
            "• Допускается вставка списка ссылок за один раз\n"
            "• Ссылки могут быть разделены переносами строк, пробелами, запятыми или точкой с запятой\n\n"
            "Пример корректного ввода:\n"
            "https://caucasia.ru/track/295\n"
            "https://caucasia.ru/track/638\n"
        )
        tk.Label(self.tab_load, text=hint, justify="left", wraplength=900).pack(pady=(0, 8), anchor="w", padx=12)

        btn_frame = tk.Frame(self.tab_load)
        btn_frame.pack(fill="x", padx=12, pady=(0, 6))

        self.btn_paste = self._reg_btn(
            tk.Button(btn_frame, text="Вставить из буфера", command=self.paste_links_from_clipboard)
        )
        self.btn_paste.pack(side="left", padx=(0, 6))

        self.btn_validate = self._reg_btn(
            tk.Button(btn_frame, text="Проверка корректности ссылок", command=self.validate_links_ui)
        )
        self.btn_validate.pack(side="left", padx=(0, 6))

        self.btn_dedup = self._reg_btn(
            tk.Button(btn_frame, text="Удалить повторяющиеся ссылки", command=self.dedup_links_ui)
        )
        self.btn_dedup.pack(side="left", padx=(0, 6))

        self.btn_clear = self._reg_btn(
            tk.Button(btn_frame, text="Очистить", command=self.clear_links_ui)
        )
        self.btn_clear.pack(side="left")

        self.links_counter_var = tk.StringVar(value="Ссылок: 0 (уникальных: 0)")
        tk.Label(self.tab_load, textvariable=self.links_counter_var).pack(anchor="w", padx=12, pady=(0, 4))

        self.text_area = scrolledtext.ScrolledText(self.tab_load, width=110, height=14)
        self.text_area.pack(padx=12, pady=(0, 10), fill="both", expand=False)

        placeholder = "Вставьте ссылки сюда...\n(Одна ссылка на строку)"
        self.text_area.insert("1.0", placeholder)
        self.text_area.bind("<FocusIn>", self._clear_placeholder_if_needed)
        self.text_area.bind("<KeyRelease>", lambda _e: self.update_links_counter())

        self.btn_load = self._reg_btn(
            tk.Button(self.tab_load, text="Загрузить треки", width=30, command=self.load_tracks)
        )
        self.btn_load.pack(pady=10)

        self.update_links_counter()

    def load_tracks(self):
        urls = self.get_links_from_ui()
        urls = [u.strip() for u in urls if u.strip()]
        urls = list(dict.fromkeys(urls))

        if len(urls) == 0:
            messagebox.showwarning("Ошибка", "Вставьте хотя бы одну ссылку")
            return
        if not urls:
            messagebox.showwarning("Ошибка", "Вставьте хотя бы одну ссылку")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Загрузка", text="Загрузка треков...", determinate=True, maximum=len(urls))

        def worker(progress_cb):
            dfs = []
            os.makedirs(MAPS_DIR, exist_ok=True)

            for i, url in enumerate(urls, start=1):
                if progress_cb:
                    progress_cb({"type": "text", "text": f"Загрузка трека {i}/{len(urls)}..."})
                    progress_cb({"type": "value", "value": i - 1})

                df = self.agent._load_single_gpx(url, i)
                df_filtered = self.agent._filter_track_points(df)

                try:
                    save_track_assets(df_filtered, track_id=i, out_dir=MAPS_DIR)
                except Exception:
                    pass

                dfs.append(df_filtered)

                if progress_cb:
                    progress_cb({"type": "value", "value": i})

            return pd.concat(dfs, ignore_index=True)

        def on_progress(payload):
            t = payload.get("type")
            if t == "text":
                pwin.set_text(payload.get("text", ""))
            elif t == "value":
                pwin.set_value(float(payload.get("value", 0)))

        def on_done(df):
            self.result_df = df
            pwin.close()
            self.set_busy(False)
            self.update_track_list()
            self.update_augment_list()
            messagebox.showinfo("Готово", "Загрузка треков успешно завершена. (карты+meta сохранены в maps/)")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)


    def create_tab_process(self):
        tk.Label(
            self.tab_process,
            text="Обработка треков",
            font=("Arial", 14, "bold"),
            bg="#f2f2f2"
        ).pack(pady=(15, 0))

        tk.Label(
            self.tab_process,
            text="Выполните действия поочередно",
            font=("Arial", 10),
            bg="#f2f2f2",
            fg="#555555"
        ).pack(pady=(0, 10))

        def create_button_with_info(parent, text, command, info_text):
            frame = tk.Frame(parent)
            frame.pack(pady=10)

            btn = self._reg_btn(tk.Button(frame, text=text, width=40, command=command))
            btn.pack(side="left")

            info_btn = self._reg_btn(
                tk.Button(frame, text="ⓘ", width=3, command=lambda: messagebox.showinfo("Информация", info_text))
            )
            info_btn.pack(side="left", padx=5)

            frame.pack(anchor="center")

        create_button_with_info(
            self.tab_process,
            "1. Определение региона маршрута",
            self.assign_regions,
            "Определяет регион прохождения маршрута на основе координат начальной точки.",
        )
        create_button_with_info(
            self.tab_process,
            "2. Добавить сезонность",
            self.add_seasons,
            "Автоматическое определение сезона на основе даты прохождения трека.",
        )
        create_button_with_info(
            self.tab_process,
            "3. Заполнить температуры",
            self.fill_temperatures,
            "Заполняет пропущенные значения температуры с использованием метеорологических данных.",
        )
        create_button_with_info(
            self.tab_process,
            "4. Определение окружения",
            self.add_environment,
            "Считает окружение по картинке basemap для каждой точки.",
        )

        create_button_with_info(
            self.tab_process,
            "5. Значимые атрибуты (heatmap)",
            self.show_significant_attributes,
            "Выбор значимых атрибутов по корреляционной матрице (Spearman) "
            "из уже существующих колонок DataFrame.",
        )

    def assign_regions(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        track_ids = sorted(self.result_df["track_id"].unique())
        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Регионы", text="Определение регионов...", determinate=True,
                              maximum=len(track_ids))

        def worker(progress_cb):
            regions = {}
            for i, track_id in enumerate(track_ids, start=1):
                if progress_cb:
                    progress_cb({"type": "text", "text": f"Трек {track_id}: регион ({i}/{len(track_ids)})..."})
                    progress_cb({"type": "value", "value": i - 1})

                group = self.result_df[self.result_df["track_id"] == track_id]
                lat = group.iloc[0]["latitude"]
                lon = group.iloc[0]["longitude"]
                regions[track_id] = self.agent._get_region(lat, lon)

                if progress_cb:
                    progress_cb({"type": "value", "value": i})
            return regions

        def on_progress(payload):
            t = payload.get("type")
            if t == "text":
                pwin.set_text(payload.get("text", ""))
            elif t == "value":
                pwin.set_value(float(payload.get("value", 0)))

        def on_done(regions):
            self.result_df["region"] = self.result_df["track_id"].map(regions)
            pwin.close()
            self.set_busy(False)
            messagebox.showinfo("Готово", "Регионы определены!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def add_seasons(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Сезонность", text="Добавление сезонности...", determinate=False)

        def worker(_progress_cb):
            return self.agent.add_seasons(self.result_df)

        def on_done(df):
            self.result_df = df
            pwin.close()
            self.set_busy(False)
            self.update_track_list()
            self.update_augment_list()
            messagebox.showinfo("Готово", "Сезонность добавлена.")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error)

    def fill_temperatures(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Температуры", text="Заполнение температур...", determinate=True,
                              maximum=len(self.result_df))

        def worker(progress_cb):
            return self.agent.fill_temperatures(self.result_df, progress_cb=progress_cb)

        def on_progress(payload):
            t = payload.get("type")
            if t == "text":
                pwin.set_text(payload.get("text", ""))
            elif t == "max":
                pwin.set_maximum(int(payload.get("max", 100)))
            elif t == "value":
                pwin.set_value(float(payload.get("value", 0)))
            elif t == "step":
                pwin.step(float(payload.get("step", 1)))

        def on_done(df):
            self.result_df = df
            pwin.close()
            self.set_busy(False)
            messagebox.showinfo("Готово", "Температуры заполнены!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def add_environment(self):
        """Окружение считается ПО КАРТИНКЕ трека (maps/ или augmented_maps/)."""
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        self.set_busy(True)
        pwin = ProgressWindow(
            self.master,
            title="Окружение",
            text="Окружение по картинкам...",
            determinate=True,
            maximum=len(self.result_df["track_id"].unique()),
        )

        def worker(progress_cb):
            return add_environment_attributes_by_track_images(self.result_df, progress_cb=progress_cb)

        def on_progress(payload):
            t = payload.get("type")
            if t == "text":
                pwin.set_text(payload.get("text", ""))
            elif t == "max":
                pwin.set_maximum(int(payload.get("max", 100)))
            elif t == "value":
                pwin.set_value(float(payload.get("value", 0)))

        def on_done(df):
            self.result_df = df

            pwin.close()
            self.set_busy(False)
            messagebox.showinfo("Готово", "Окружение добавлено (по картинкам)!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)


    def create_tab_view(self):
        tk.Label(
            self.tab_view,
            text="Просмотр треков",
            font=("Arial", 14, "bold")
        ).pack(pady=10)

        tk.Label(self.tab_view, text="Выберите трек:").pack()

        self.track_combo = ttk.Combobox(self.tab_view, state="readonly")
        self.track_combo.pack()

        self.btn_update_tracks = self._reg_btn(
            tk.Button(self.tab_view, text="Обновить список треков", command=self.update_track_list)
        )
        self.btn_update_tracks.pack(pady=5)

        self.btn_show_map = self._reg_btn(
            tk.Button(self.tab_view, text="Показать карту трека", command=self.show_track_map)
        )
        self.btn_show_map.pack(pady=5)

        self.btn_show_df = self._reg_btn(
            tk.Button(self.tab_view, text="Показать DataFrame трека", command=self.show_dataframe)
        )
        self.btn_show_df.pack(pady=5)
        self.btn_save_all_one = self._reg_btn(
            tk.Button(self.tab_view, text="Сохранить все треки в один Excel", command=self.save_all_tracks_to_one_excel)
        )
        self.btn_save_all_one.pack(pady=5)


    def update_track_list(self):
        if self.result_df is None or self.result_df.empty:
            self.track_combo["values"] = []
            return

        tracks = sorted(self.result_df["track_id"].unique())
        self.track_combo["values"] = tracks
        if tracks:
            self.track_combo.current(0)

    def show_track_map(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        track_id = self.track_combo.get()
        if not track_id:
            messagebox.showwarning("Ошибка", "Выберите трек")
            return

        track_id = int(track_id)

        combined_path = os.path.join(MAPS_DIR, f"track_{track_id}_combined.png")
        if os.path.exists(combined_path):
            self._open_image_window(combined_path, f"Карта трека {track_id}")
            return

        map_agent = GPXMapAgent(self.result_df)
        png_path = map_agent.plot_track_to_png(track_id, save_folder=MAPS_DIR)
        self._open_image_window(png_path, f"Карта трека {track_id}")

    def show_dataframe(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        track_id = self.track_combo.get()
        if not track_id:
            messagebox.showwarning("Ошибка", "Выберите трек")
            return

        track_id = int(track_id)
        df = self.result_df[self.result_df.track_id == track_id]

        win = tk.Toplevel(self.master)
        win.title(f"DataFrame трека {track_id}")

        text = scrolledtext.ScrolledText(win, width=120, height=30)
        text.pack(fill="both", expand=True)
        text.insert(tk.END, df.to_string())
        text.config(state="disabled")


    def create_tab_augment(self):
        tk.Label(
            self.tab_augment,
            text="Аугментация треков",
            font=("Arial", 14, "bold")
        ).pack(pady=10)

        frame = tk.Frame(self.tab_augment)
        frame.pack(pady=8)

        self.btn_augment_all = self._reg_btn(
            tk.Button(
                frame,
                text="Аугментировать все треки",
                command=self.augment_all_tracks,
                width=40,
            )
        )
        self.btn_augment_all.pack(side="left")

        info_btn = self._reg_btn(
            tk.Button(
                frame,
                text="ⓘ",
                width=3,
                command=lambda: messagebox.showinfo(
                    "Аугментация треков",
                    "Выполняется аугментация всех загруженных треков:\n\n"
                    "• Поворот фоновой карты на 180°\n"
                    "• Формирование нового трека\n"
                    "• Пересчёт окружения по изображению\n\n"
                    "Каждый аугментированный трек добавляется как отдельный track_id."
                ),
            )
        )
        info_btn.pack(side="left", padx=6)

        tk.Label(self.tab_augment, text="Просмотр треков (оригинал + аугментированные):").pack(pady=10)

        self.augment_combo = ttk.Combobox(self.tab_augment, state="readonly")
        self.augment_combo.pack()

        self.btn_update_aug = self._reg_btn(
            tk.Button(self.tab_augment, text="Обновить список треков", command=self.update_augment_list)
        )
        self.btn_update_aug.pack(pady=5)

        self.btn_show_aug_map = self._reg_btn(
            tk.Button(self.tab_augment, text="Показать карту выбранного трека", command=self.show_selected_track_map)
        )
        self.btn_show_aug_map.pack(pady=5)

        self.btn_show_aug_df = self._reg_btn(
            tk.Button(self.tab_augment, text="Показать DataFrame выбранного трека",
                      command=self.show_selected_track_dataframe)
        )
        self.btn_show_aug_df.pack(pady=5)

    def update_augment_list(self):
        if self.result_df is None or self.result_df.empty:
            self.augment_combo["values"] = []
            return

        tracks = sorted(self.result_df["track_id"].unique())
        self.augment_combo["values"] = tracks
        if tracks:
            self.augment_combo.current(0)

    def show_selected_track_map(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        track_id = self.augment_combo.get()
        if not track_id:
            messagebox.showwarning("Ошибка", "Выберите трек")
            return

        track_id = int(track_id)

        aug_path = os.path.join(AUG_MAPS_DIR, f"track_{track_id}_augmented.png")
        if os.path.exists(aug_path):
            self._open_image_window(aug_path, f"Аугментированный трек {track_id}")
            return

        combined_path = os.path.join(MAPS_DIR, f"track_{track_id}_combined.png")
        if os.path.exists(combined_path):
            self._open_image_window(combined_path, f"Карта трека {track_id}")
            return

        messagebox.showwarning("Нет карты", "Для этого трека нет сохранённой картинки (combined/augmented).")

    def show_selected_track_dataframe(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        track_id = self.augment_combo.get()
        if not track_id:
            messagebox.showwarning("Ошибка", "Выберите трек")
            return

        track_id = int(track_id)
        df = self.result_df[self.result_df.track_id == track_id]
        if df.empty:
            messagebox.showerror("Ошибка", "DataFrame трека не найден")
            return

        win = tk.Toplevel(self.master)
        win.title(f"DataFrame трека {track_id}")

        text = scrolledtext.ScrolledText(win, width=120, height=30)
        text.pack(fill="both", expand=True)
        text.insert(tk.END, df.to_string())
        text.config(state="disabled")

    def augment_all_tracks(self):
        """Твоя текущая логика аугментации (без изменений здесь)."""
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        original_ids = sorted(self.result_df["track_id"].unique())
        max_id = int(max(original_ids)) if original_ids else 0

        self.set_busy(True)
        pwin = ProgressWindow(
            self.master,
            title="Аугментация",
            text="Аугментация + окружение по картинке...",
            determinate=True,
            maximum=len(original_ids),
        )
        os.makedirs(AUG_MAPS_DIR, exist_ok=True)

        def worker(progress_cb):
            df_base = self.result_df.copy()
            augmented_list = []
            new_id = max_id + 1

            for i, tid in enumerate(original_ids, start=1):
                if progress_cb:
                    progress_cb({"type": "text", "text": f"Трек {tid} -> новый {new_id} ({i}/{len(original_ids)})"})
                    progress_cb({"type": "value", "value": i - 1})

                df_track = df_base[df_base["track_id"] == tid].copy()
                if df_track.empty:
                    continue

                basemap_path = os.path.join(MAPS_DIR, f"track_{tid}_basemap.png")
                route_path = os.path.join(MAPS_DIR, f"track_{tid}_route.png")
                meta_path = _meta_path(MAPS_DIR, tid)

                df_aug = df_track.copy()
                df_aug["track_id"] = new_id

                if not (os.path.exists(basemap_path) and os.path.exists(route_path) and os.path.exists(meta_path)):
                    augmented_list.append(df_aug)
                    new_id += 1
                    if progress_cb:
                        progress_cb({"type": "value", "value": i})
                    continue

                base_img = Image.open(basemap_path).convert("RGBA")
                route_img = Image.open(route_path).convert("RGBA")
                base_rot = base_img.rotate(180, expand=False)

                aug_basemap_path = os.path.join(AUG_MAPS_DIR, f"track_{new_id}_basemap.png")
                base_rot.save(aug_basemap_path)

                aug_meta_path = _meta_path(AUG_MAPS_DIR, new_id)
                shutil.copyfile(meta_path, aug_meta_path)

                if route_img.size != base_rot.size:
                    route_img = route_img.resize(base_rot.size, Image.Resampling.LANCZOS)

                augmented_img = Image.alpha_composite(base_rot, route_img)
                out_path = os.path.join(AUG_MAPS_DIR, f"track_{new_id}_augmented.png")
                augmented_img.save(out_path)

                try:
                    df_aug = add_environment_for_track_from_image(
                        df_aug,
                        basemap_png_path=aug_basemap_path,
                        meta_json_path=aug_meta_path,
                        radius_m=500,
                        n_clusters=6,
                        threshold=35,
                    )
                except Exception:
                    pass

                augmented_list.append(df_aug)
                new_id += 1

                if progress_cb:
                    progress_cb({"type": "value", "value": i})

            if not augmented_list:
                return df_base

            df_aug_all = pd.concat(augmented_list, ignore_index=True)
            final_df = pd.concat([df_base, df_aug_all], ignore_index=True)
            return final_df

        def on_progress(payload):
            t = payload.get("type")
            if t == "text":
                pwin.set_text(payload.get("text", ""))
            elif t == "value":
                pwin.set_value(float(payload.get("value", 0)))

        def on_done(df):
            self.result_df = df
            pwin.close()
            self.set_busy(False)
            self.update_track_list()
            self.update_augment_list()
            messagebox.showinfo("Готово", "Процесс аугментации маршрутов успешно завершён.")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def show_significant_attributes(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Для выполнения операции необходимо сначала загрузить данные.")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Анализ", text="Строим heatmap и выбираем признаки...",
                              determinate=False)

        def worker(_progress_cb):
            import matplotlib
            matplotlib.use("Agg")
            import matplotlib.pyplot as plt
            import seaborn as sns
            import tempfile
            import numpy as np

            try:
                df = self.result_df.copy()
                numeric_cols = df.select_dtypes(include=[np.number, bool]).columns.tolist()
                if not numeric_cols:
                    return None

                df_num = df[numeric_cols].fillna(0)
                corr = df_num.corr(method='spearman')

                tmp_file = os.path.join(tempfile.gettempdir(), "gpx_heatmap.png")

                plt.figure(figsize=(10, 8))
                sns.heatmap(corr, annot=True, fmt=".2f", cmap="coolwarm", cbar=True)
                plt.title("Корреляция признаков (Spearman)")
                plt.tight_layout()
                plt.savefig(tmp_file)
                plt.close()

                avg_corr = corr.abs().mean().sort_values(ascending=False)
                selected_features = avg_corr.head(12).index.tolist()
                explanations = [f"{f}: средняя |corr| = {avg_corr[f]:.2f}" for f in selected_features]

                return {"heatmap_path": tmp_file, "selected_features": selected_features, "explanations": explanations}

            except Exception as e:
                import traceback
                print("Ошибка при построении heatmap:", e)
                print(traceback.format_exc())
                raise e

        def on_done(res):
            pwin.close()
            self.set_busy(False)

            if res is None:
                messagebox.showerror(
                    "Ошибка",
                    "Недостаточно числовых/булевых признаков для анализа.\n"
                    "Добавьте атрибуты окружения и температуры."
                )
                return

            win = tk.Toplevel(self.master)
            win.title("Значимые атрибуты (heatmap Spearman)")

            main_frame = tk.Frame(win)
            main_frame.pack(fill="both", expand=True, padx=10, pady=10)

            left_frame = tk.Frame(main_frame)
            left_frame.pack(side="left", fill="both", expand=False)

            if os.path.exists(res["heatmap_path"]):
                from PIL import Image, ImageTk
                img = Image.open(res["heatmap_path"])

                max_w, max_h = 700, 600
                w, h = img.size
                k = min(max_w / w, max_h / h, 1.0)
                if k < 1.0:
                    img = img.resize((int(w * k), int(h * k)))

                img_tk = ImageTk.PhotoImage(img)
                lbl = tk.Label(left_frame, image=img_tk)
                lbl.image = img_tk
                lbl.pack()

            right_frame = tk.Frame(main_frame)
            right_frame.pack(side="left", fill="both", expand=True, padx=(10, 0))

            box = scrolledtext.ScrolledText(right_frame, width=60, height=30)
            box.pack(fill="both", expand=True)

            lines = []
            lines.append("Выбор значимых атрибутов по корреляции (Spearman)")
            lines.append("")
            lines.append("Как выбирались признаки:")
            lines.append("1) Взяты числовые и булевые признаки.")
            lines.append("2) Построена корреляция Spearman (устойчива к выбросам).")
            lines.append("3) Для каждого признака посчитана средняя |corr|.")
            lines.append("")
            lines.append("Рекомендуемые признаки:")
            for f in res["selected_features"]:
                lines.append(f"- {f}")
            lines.append("")
            lines.append("Обоснование:")
            lines.extend(res["explanations"])

            box.insert(tk.END, "\n".join(lines))
            box.config(state="disabled")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error)

    def _clear_placeholder_if_needed(self, _event=None):
        txt = self.text_area.get("1.0", tk.END).strip()
        if txt.startswith("Вставьте ссылки сюда"):
            self.text_area.delete("1.0", tk.END)

    def parse_links_from_text(self, raw_text: str):
        """
        Разбирает ссылки из текста:
        - строки
        - пробелы
        - запятые / точка с запятой
        Удаляет пустые и обрезает пробелы.
        """
        if not raw_text:
            return []

        s = raw_text.replace(";", "\n").replace(",", "\n").replace("\t", "\n")

        parts = []
        for line in s.splitlines():
            line = line.strip()
            if not line:
                continue
            for token in line.split():
                token = token.strip()
                if token:
                    parts.append(token)

        parts = [p.strip() for p in parts if p.strip()]
        return parts

    def get_links_from_ui(self):
        raw = self.text_area.get("1.0", tk.END)
        links = self.parse_links_from_text(raw)
        links = [u for u in links if not u.startswith("Вставьте ссылки сюда")]
        return links

    def update_links_counter(self):
        links = self.get_links_from_ui()
        uniq = list(dict.fromkeys(links))
        self.links_counter_var.set(f"Ссылок: {len(links)} (уникальных: {len(uniq)})")

    def paste_links_from_clipboard(self):
        try:
            clip = self.master.clipboard_get()
        except Exception:
            messagebox.showwarning("Буфер", "Буфер обмена пуст или недоступен")
            return

        self._clear_placeholder_if_needed()
        links = self.parse_links_from_text(clip)
        if not links:
            messagebox.showwarning("Буфер", "Не удалось найти ссылки в буфере обмена")
            return

        current = self.get_links_from_ui()
        merged = current + links

        self.text_area.delete("1.0", tk.END)
        self.text_area.insert("1.0", "\n".join(merged))
        self.update_links_counter()

    def clear_links_ui(self):
        self.text_area.delete("1.0", tk.END)
        self.update_links_counter()

    def dedup_links_ui(self):
        links = self.get_links_from_ui()
        uniq = list(dict.fromkeys(links))
        self.text_area.delete("1.0", tk.END)
        self.text_area.insert("1.0", "\n".join(uniq))
        self.update_links_counter()
        messagebox.showinfo("Готово", f"Удалено дубликатов: {len(links) - len(uniq)}")

    def validate_links_ui(self):
        links = self.get_links_from_ui()
        if not links:
            messagebox.showwarning("Проверка", "Ссылок нет")
            return

        bad = []
        for i, u in enumerate(links, start=1):
            if not (u.startswith("http://") or u.startswith("https://")):
                bad.append(f"{i}) {u} (не начинается с http/https)")

        seen = set()
        dups = []
        for u in links:
            if u in seen and u not in dups:
                dups.append(u)
            seen.add(u)

        msg_lines = []
        msg_lines.append(f"Всего ссылок: {len(links)}")
        msg_lines.append(f"Уникальных: {len(set(links))}")
        msg_lines.append("")

        if bad:
            msg_lines.append("Проблемные ссылки:")
            msg_lines.extend(bad[:20])
            if len(bad) > 20:
                msg_lines.append(f"... и ещё {len(bad) - 20}")
            msg_lines.append("")
        else:
            msg_lines.append("Проблемных ссылок не найдено.")
            msg_lines.append("")

        if dups:
            msg_lines.append("Есть дубликаты (пример):")
            msg_lines.extend([f"- {x}" for x in dups[:10]])
            if len(dups) > 10:
                msg_lines.append(f"... и ещё {len(dups) - 10}")
        else:
            msg_lines.append("Дубликатов нет.")

        messagebox.showinfo("Проверка ссылок", "\n".join(msg_lines))


if __name__ == "__main__":
    root = tk.Tk()
    app = GPXAppGUI(root)


    def on_close():
        cleanup_image_folders()
        root.destroy()


    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()
