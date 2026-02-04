import os
import io
import json
import threading
import queue
import shutil
import requests
import gpxpy
import pandas as pd
import warnings
from bs4 import BeautifulSoup
import time as _time
from urllib.parse import urlparse, urljoin
import re
import tempfile
from datetime import datetime  # Импортируем datetime
from geopy.distance import geodesic
import tkinter as tk
import tempfile
import psycopg2
from psycopg2.extras import execute_values, Json
from tkinter import simpledialog
import matplotlib
from tkinter import messagebox, scrolledtext, ttk, filedialog

import re

matplotlib.use("Agg")
import matplotlib.pyplot as plt

import geopandas as gpd
import contextily as ctx
from geopy.geocoders import Nominatim
from PIL import Image, ImageTk
import numpy as np

from sklearn.cluster import MiniBatchKMeans, KMeans
from sklearn.ensemble import RandomForestClassifier
from sklearn.inspection import permutation_importance
from sklearn.feature_selection import f_classif
from sklearn.preprocessing import OneHotEncoder

from shapely.geometry import Point

warnings.filterwarnings("ignore")

# ==========================================================
# Константы / пути
# ==========================================================
REFERENCE_COLORS = {
    "forest_nearby": (172, 206, 157),
    "water_nearby": (170, 211, 223),
    "road_nearby": (254, 254, 254),
    "building_nearby": (215, 208, 202),
}

ENV_COLS = list(REFERENCE_COLORS.keys())

MAPS_DIR = "maps"
AUG_MAPS_DIR = "augmented_maps"


# ==========================================================
# UI helpers: disable/enable + progress window + async runner
# ==========================================================
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
    """
    Toplevel окно с прогресс-баром.
    determinate=True: value/max.
    determinate=False: крутилка.
    """

    def __init__(self, master, title="Выполнение...", text="Пожалуйста, подождите...",
                 determinate=False, maximum=100):
        self.master = master
        self.win = tk.Toplevel(master)
        self.win.title(title)
        self.win.geometry("460x140")
        self.win.resizable(False, False)
        self.win.transient(master)
        self.win.grab_set()  # блокируем основное окно

        self.label = tk.Label(self.win, text=text, wraplength=430, justify="left")
        self.label.pack(padx=14, pady=(14, 8), anchor="w")

        mode = "determinate" if determinate else "indeterminate"
        self.progress = ttk.Progressbar(self.win, orient="horizontal", length=430, mode=mode, maximum=maximum)
        self.progress.pack(padx=14, pady=(0, 12))

        # запретить закрытие во время работы
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


# ==========================================================
# Track image assets: basemap / route / combined + META
# ==========================================================
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

    # 1) basemap (фон без маршрута)
    fig, ax = plt.subplots(figsize=(fig_w, fig_h))
    fig.subplots_adjust(left=0, right=1, bottom=0, top=1)
    ax.set_xlim(tminx, tmaxx)
    ax.set_ylim(tminy, tmaxy)
    ax.set_axis_off()
    ax.margins(0)
    ctx.set_cache_dir(os.path.join(tempfile.gettempdir(), "contextily_cache"))

    ctx.add_basemap(ax, source=ctx.providers.OpenStreetMap.Mapnik)
    ctx.add_basemap(
        ax,
        source=ctx.providers.OpenStreetMap.Mapnik,
        zoom="auto",
        attribution=False
    )

    plt.savefig(basemap_path, dpi=300, pad_inches=0, bbox_inches=None)
    plt.close(fig)

    # meta: bbox + размер basemap
    base_img = Image.open(basemap_path)
    W, H = base_img.size
    meta = {
        "bbox_3857": [float(tminx), float(tminy), float(tmaxx), float(tmaxy)],
        "width": int(W),
        "height": int(H),
    }
    with open(_meta_path(out_dir, track_id), "w", encoding="utf-8") as f:
        json.dump(meta, f, ensure_ascii=False, indent=2)

    # 2) route (маршрут на прозрачном фоне)
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

    # 3) combined (фон + маршрут)
    base_img_rgba = base_img.convert("RGBA")
    route_img = Image.open(route_path).convert("RGBA")
    if route_img.size != base_img_rgba.size:
        route_img = route_img.resize(base_img_rgba.size, Image.Resampling.LANCZOS)
    combined = Image.alpha_composite(base_img_rgba, route_img)
    combined.save(combined_path)

    return basemap_path, route_path, combined_path


# ==========================================================
# Environment by IMAGE (по картинке трека)
# ==========================================================
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

    # метры на пиксель (по bbox)
    mpp_x = (tmaxx - tminx) / max(W, 1)
    mpp_y = (tmaxy - tminy) / max(H, 1)
    mpp = float((mpp_x + mpp_y) / 2.0) if (mpp_x > 0 and mpp_y > 0) else max(mpp_x, mpp_y, 1.0)
    radius_px = int(max(3, radius_m / max(mpp, 1e-9)))

    # точки -> 3857
    gdf = gpd.GeoDataFrame(
        df_track,
        geometry=gpd.points_from_xy(df_track.longitude, df_track.latitude),
        crs="EPSG:4326"
    ).to_crs(epsg=3857)

    xs = gdf.geometry.x.to_numpy()
    ys = gdf.geometry.y.to_numpy()

    env_rows = []
    for x, y in zip(xs, ys):
        # px (0..W-1), py (0..H-1)
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

        # сэмпл чтобы быстрее
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

    # метры на пиксель
    mpp_x = (tmaxx - tminx) / max(W, 1)
    mpp_y = (tmaxy - tminy) / max(H, 1)
    mpp = float((mpp_x + mpp_y) / 2.0) if (mpp_x > 0 and mpp_y > 0) else max(mpp_x, mpp_y, 1.0)
    radius_px = int(max(3, radius_m / max(mpp, 1e-9)))

    # --- ВСЕ точки трека -> 3857 ---
    gdf_all = gpd.GeoDataFrame(
        df_track,
        geometry=gpd.points_from_xy(df_track.longitude, df_track.latitude),
        crs="EPSG:4326"
    ).to_crs(epsg=3857)

    xs = gdf_all.geometry.x.to_numpy()
    ys = gdf_all.geometry.y.to_numpy()

    # --- 3857 -> пиксели basemap ---
    # px = (x - tminx) / (tmaxx - tminx) * (W-1)
    # py = (tmaxy - y) / (tmaxy - tminy) * (H-1)
    denom_x = max(tmaxx - tminx, 1e-9)
    denom_y = max(tmaxy - tminy, 1e-9)

    px_all = ((xs - tminx) / denom_x * (W - 1)).astype(int)
    py_all = ((tmaxy - ys) / denom_y * (H - 1)).astype(int)

    # ограничим чтобы не улетали
    px_all = np.clip(px_all, 0, W - 1)
    py_all = np.clip(py_all, 0, H - 1)

    # --- выбранная точка ---
    pos = np.where(df_track.index.to_numpy() == point_idx)[0]
    if len(pos) == 0:
        return None
    ppos = int(pos[0])

    px = int(px_all[ppos])
    py = int(py_all[ppos])

    # --- patch вокруг выбранной точки ---
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

    # 1) basemap + маршрут + выбранная точка + круг
    fig, ax = plt.subplots(figsize=(9, 7))
    ax.imshow(img_np)

    # маршрут (именно точки маршрута!)
    ax.plot(px_all, py_all, linewidth=2)  # цвет не задаю по твоему правилу

    # выбранная точка маршрута
    ax.scatter([px], [py], s=110, marker="o")  # точка заметнее
    ax.scatter([px], [py], s=90, marker="x")  # крестик сверху

    # круг радиуса 500м в пикселях
    circ = plt.Circle((px, py), radius_px, fill=False, linewidth=2)
    ax.add_patch(circ)

    ax.set_title("Окружение считается вокруг точки МАРШРУТА:\nлиния=маршрут, точка=выбранная точка маршрута, круг=500м")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(map_path, dpi=200)
    plt.close(fig)

    # 2) patch
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.imshow(patch_np)
    ax.set_title("Patch вокруг точки маршрута (радиус 500м)")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(patch_path, dpi=200)
    plt.close(fig)

    # 3) палитра кластеров
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


# ==========================================================
# Анализ значимых атрибутов (ОТДЕЛЬНЫЙ DF, НЕ трогаем основной)
# ==========================================================
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


# ==========================================================
# GPX Loader Agent
# ==========================================================
class GPXLoaderAgent:
    def __init__(self):
        self.dataframes = []
        self.geolocator = Nominatim(user_agent="track_region_identifier")

    # ----------------------------
    # HIKEPLAN: build GPX URL
    # ----------------------------
    def _hikeplan_build_gpx_url(self, any_url: str) -> str:
        # 1) hikes
        m = re.search(r"https?://hikeplan\.ru/hikes/([0-9a-fA-F-]{36})", any_url)
        if m:
            uuid = m.group(1)
            return f"https://hikeplan.ru/hikes/{uuid}/download/gpx?nomarkers=1"

        # 2) trail -> trail_templates
        m = re.search(r"https?://hikeplan\.ru/trail/([0-9a-fA-F-]{36})", any_url)
        if m:
            uuid = m.group(1)
            return f"https://hikeplan.ru/trail_templates/{uuid}/download/gpx?nomarkers=1"

        # 3) если уже дали trail_templates
        m = re.search(r"https?://hikeplan\.ru/trail_templates/([0-9a-fA-F-]{36})", any_url)
        if m:
            uuid = m.group(1)
            return f"https://hikeplan.ru/trail_templates/{uuid}/download/gpx?nomarkers=1"

        raise ValueError(f"Неподдерживаемая ссылка hikeplan: {any_url}")

    def _hikeplan_fetch_gpx_text(self, gpx_url: str) -> str:
        headers = {
            "User-Agent": "Mozilla/5.0 (compatible; GPXTracksManager/1.0)"
        }
        r = requests.get(gpx_url, timeout=(15, 120), allow_redirects=True, headers=headers)
        r.raise_for_status()

        # проверяем, что это реально GPX
        head = (r.content[:500] or b"").lower()
        if b"<gpx" not in head:
            # пробуем без nomarkers=1
            if "nomarkers=1" in gpx_url:
                alt = gpx_url.replace("?nomarkers=1", "")
                r2 = requests.get(alt, timeout=(15, 120), allow_redirects=True, headers=headers)
                r2.raise_for_status()
                if b"<gpx" in (r2.content[:500] or b"").lower():
                    return r2.text

            raise RuntimeError(
                f"Ответ не похож на GPX: {gpx_url} "
                f"(Content-Type={r.headers.get('Content-Type')})"
            )

        return r.text

    def _load_hikeplan_gpx(self, track_url: str, track_id: int) -> pd.DataFrame:
        gpx_url = self._hikeplan_build_gpx_url(track_url)
        gpx_text = self._hikeplan_fetch_gpx_text(gpx_url)
        gpx = gpxpy.parse(io.StringIO(gpx_text))

        data = {
            "latitude": [],
            "longitude": [],
            "elevation": [],
            "time": [],
            "temperature": [],
            "cadence": [],
            "track_id": [],
        }

        for track in gpx.tracks:
            for segment in track.segments:
                for point in segment.points:
                    data["latitude"].append(point.latitude)
                    data["longitude"].append(point.longitude)
                    data["elevation"].append(point.elevation)
                    data["time"].append(point.time)

                    temperature = None
                    cadence = None

                    # В hikeplan чаще всего extensions пустые, но оставим обработку на всякий случай
                    if point.extensions:
                        for ext in point.extensions:
                            if ext.tag.endswith("TrackPointExtension"):
                                for child in ext:
                                    if child.tag.endswith("atemp"):
                                        try:
                                            temperature = float(child.text)
                                        except Exception:
                                            temperature = None
                                    elif child.tag.endswith("cad"):
                                        try:
                                            cadence = int(child.text)
                                        except Exception:
                                            cadence = None

                    data["temperature"].append(temperature)
                    data["cadence"].append(cadence)
                    data["track_id"].append(track_id)

        df = pd.DataFrame(data)

        # time -> datetime UTC
        df["time"] = pd.to_datetime(df["time"], errors="coerce", utc=True)

        df = self._calculate_distances(df)
        df = self._fill_cadence_from_distance_and_time(df, stride_m=0.75)

        return df

    def _pick_temp_nearest(self, day_map: dict, target_hour_key: str, max_diff_hours: int = 2):
        """
        day_map: dict {"YYYY-MM-DDTHH:00": temp, ...} (UTC)
        target_hour_key: "YYYY-MM-DDTHH:00" (UTC)
        """
        if not day_map:
            return None

        # точное совпадение
        if target_hour_key in day_map:
            return day_map.get(target_hour_key, None)

        # --- кэшируем распарсенные ключи (ускоряет) ---
        # ключ кэша — id(day_map), потому что day_map создаётся заново на каждый день
        cache_attr = "_day_map_dt_cache"
        if not hasattr(self, cache_attr):
            setattr(self, cache_attr, {})

        dt_cache = getattr(self, cache_attr)
        cache_key = id(day_map)

        if cache_key not in dt_cache:
            keys = list(day_map.keys())
            dts = pd.to_datetime(keys, utc=True, errors="coerce")
            ok = dts.notna()
            dts_ok = dts[ok]
            keys_ok = [k for k, m in zip(keys, ok) if m]
            dt_cache[cache_key] = (dts_ok, keys_ok)

        dts_ok, keys_ok = dt_cache.get(cache_key, (None, None))
        if dts_ok is None or len(dts_ok) == 0:
            return None

        target_dt = pd.to_datetime(target_hour_key, utc=True, errors="coerce")
        if pd.isna(target_dt):
            return None

        diffs = (dts_ok - target_dt).abs()
        j = int(diffs.argmin())
        best_key = keys_ok[j]
        best_diff_hours = float(diffs.iloc[j].total_seconds() / 3600.0)

        if best_diff_hours <= float(max_diff_hours):
            return day_map.get(best_key, None)

        return None

    def _fill_cadence_from_distance_and_time(self, df: pd.DataFrame, stride_m: float = 0.75) -> pd.DataFrame:
        """
        Если cadence отсутствует, оцениваем cadence (шагов/мин) через:
          steps ~= distance_to_previous / stride_m
          cadence_spm = steps / (dt_minutes)
        + дополнительно:
          - делаем cadence типом Int64 (чтобы не превращался в float с NaN)
          - внутри трека заполняем пропуски ближайшим известным значением (ffill/bfill),
            а если трек полностью пустой по cadence — ставим 0.
        """
        if df is None or df.empty:
            return df

        d = df.copy()

        if "cadence" not in d.columns:
            d["cadence"] = pd.Series([pd.NA] * len(d), dtype="Int64")
        else:
            d["cadence"] = pd.to_numeric(d["cadence"], errors="coerce").astype("Int64")

        if "time" not in d.columns or "distance_to_previous" not in d.columns:
            return d

        t = pd.to_datetime(d["time"], errors="coerce", utc=True)
        dt_sec = t.diff().dt.total_seconds()

        dist = pd.to_numeric(d["distance_to_previous"], errors="coerce")

        can = (
                d["cadence"].isna() &
                dt_sec.notna() & (dt_sec > 0) &
                dist.notna() & (dist > 0)
        )

        dt_min = dt_sec / 60.0
        steps = dist / float(max(stride_m, 1e-6))
        cad = (steps / dt_min).round()

        filled = cad.loc[can].clip(lower=0, upper=300)
        d.loc[can, "cadence"] = filled.astype("Int64")

        # ✅ добиваем пропуски внутри каждого track_id
        d["cadence"] = (
            d.groupby("track_id", sort=False)["cadence"]
            .apply(lambda s: s.ffill().bfill())
            .reset_index(level=0, drop=True)
            .astype("Int64")
        )

        # если по треку вообще нечего было заполнить — пусть будет 0 (или можешь median)
        d["cadence"] = d["cadence"].fillna(0).astype("Int64")

        return d

    def _load_single_gpx(self, track_url: str, track_id: int) -> pd.DataFrame:
        """
        Универсальная загрузка:
        - hikeplan.ru/hikes/<uuid>/report  (и любые /hikes/<uuid>...)
        - hikeplan.ru/trail/<uuid>         (и trail_templates)
        - caucasia.ru/track/<id>
        """
        u = track_url.strip()
        parsed = urlparse(u)
        host = (parsed.netloc or "").lower()
        path = (parsed.path or "").lower()

        if "caucasia.ru" in host and path.startswith("/track/"):
            df = self._load_gpx_from_caucasia(u, track_id)

        elif "hikeplan.ru" in host:
            # ✅ СНАЧАЛА пробуем прямой download endpoint (самый стабильный)
            try:
                df = self._load_hikeplan_gpx(u, track_id)  # <-- это твой метод через /download/gpx
            except Exception:
                # 🔁 fallback: старый способ (скрейп HTML report-страницы), вдруг где-то ещё работает
                df = self._load_gpx_from_hikeplan(u, track_id)  # <-- твой HTML-скрейпер

        else:
            raise ValueError(f"Неизвестный формат ссылки: {track_url}")

        df = self._calculate_distances(df)
        return df

    # ---------- caucasia.ru ----------
    def _load_gpx_from_caucasia(self, track_url: str, track_id: int) -> pd.DataFrame:
        response = requests.get(track_url, timeout=30)
        response.raise_for_status()

        soup = BeautifulSoup(response.text, "html.parser")

        # Ищем первую ссылку на .gpx
        gpx_link = None
        for a in soup.find_all("a"):
            href = (a.get("href") or "").strip()
            if href.lower().endswith(".gpx"):
                gpx_link = href
                break

        if not gpx_link:
            raise ValueError("caucasia.ru: Не удалось найти ссылку на GPX на странице")

        gpx_url = urljoin(track_url, gpx_link)

        gpx_response = requests.get(gpx_url, timeout=30)
        gpx_response.raise_for_status()

        # Важно: парсим bytes безопаснее, чем text (кодировки)
        gpx = gpxpy.parse(gpx_response.content.decode("utf-8", errors="ignore"))
        return self._gpx_to_df(gpx, track_id)

    # ---------- hikeplan.ru ----------
    def _load_gpx_from_hikeplan(self, report_url: str, track_id: int) -> pd.DataFrame:
        """
        Для hikeplan на report-странице обычно есть:
        - прямая ссылка на .gpx
        - или кнопка/endpoint export/download
        Мы делаем:
        1) ищем href с .gpx
        2) если нет — ищем любые ссылки где есть gpx (download/export)
        """
        response = requests.get(report_url, timeout=30)
        response.raise_for_status()

        soup = BeautifulSoup(response.text, "html.parser")

        # 1) прямой .gpx
        gpx_link = None
        for a in soup.find_all("a"):
            href = (a.get("href") or "").strip()
            if href.lower().endswith(".gpx"):
                gpx_link = href
                break

        # 2) fallback: ссылки содержащие "gpx" (download/export)
        if not gpx_link:
            for a in soup.find_all("a"):
                href = (a.get("href") or "").strip()
                if "gpx" in href.lower():
                    gpx_link = href
                    break

        if not gpx_link:
            raise ValueError("hikeplan.ru: Не удалось найти ссылку на GPX на странице report")

        gpx_url = urljoin(report_url, gpx_link)

        gpx_response = requests.get(gpx_url, timeout=30)
        gpx_response.raise_for_status()

        # иногда может быть gzip/zip — но чаще обычный XML
        content = gpx_response.content

        # если вдруг скачался HTML (редирект/защита) — будет видно по началу
        if content[:50].lstrip().startswith(b"<!DOCTYPE") or content[:20].lstrip().startswith(b"<html"):
            raise ValueError("hikeplan.ru: вместо GPX пришёл HTML (возможно нужна авторизация или другой endpoint)")

        gpx = gpxpy.parse(content.decode("utf-8", errors="ignore"))
        return self._gpx_to_df(gpx, track_id)

    # ---------- общая сборка DF ----------
    def _gpx_to_df(self, gpx: gpxpy.gpx.GPX, track_id: int) -> pd.DataFrame:
        data = {
            "latitude": [],
            "longitude": [],
            "elevation": [],
            "time": [],
            "temperature": [],
            "cadence": [],
            "track_id": []
        }

        for trk in gpx.tracks:
            for seg in trk.segments:
                for point in seg.points:
                    data["latitude"].append(point.latitude)
                    data["longitude"].append(point.longitude)
                    data["elevation"].append(point.elevation)
                    data["time"].append(point.time)

                    if point.extensions:
                        for ext in point.extensions:
                            if ext.tag.endswith("TrackPointExtension"):
                                for child in ext:
                                    if child.tag.endswith("atemp"):
                                        try:
                                            temperature = float(child.text)
                                        except Exception:
                                            temperature = None
                                    elif child.tag.endswith("cad"):
                                        try:
                                            cadence = int(child.text)
                                        except Exception:
                                            cadence = None

                    data["temperature"].append(temperature)
                    data["cadence"].append(cadence)
                    data["track_id"].append(track_id)

        df = pd.DataFrame(data)
        df["time"] = pd.to_datetime(df["time"], errors="coerce", utc=True)

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
        current_sum = 0.0

        # ✅ безопаснее через iloc (индекс может быть не 0..n-1)
        for i in range(1, len(df)):
            current_sum += float(df.iloc[i]["distance_to_previous"] or 0)
            if current_sum >= target_distance:
                filtered.append(df.iloc[i])
                current_sum = 0.0

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

    def fetch_temperature_day(self, lat, lon, date_str, retries=4):
        url = "https://archive-api.open-meteo.com/v1/archive"
        params = {
            "latitude": float(lat),
            "longitude": float(lon),
            "start_date": date_str,
            "end_date": date_str,
            "hourly": "temperature_2m",
            "timezone": "UTC",
        }

        for attempt in range(int(max(retries, 1))):
            try:
                resp = requests.get(url, params=params, timeout=30)

                # ✅ временные ошибки / лимиты
                if resp.status_code in (429, 500, 502, 503, 504):
                    _time.sleep(0.7 * (attempt + 1))
                    continue

                resp.raise_for_status()
                data = resp.json()

                times = data.get("hourly", {}).get("time", []) or []
                temps = data.get("hourly", {}).get("temperature_2m", []) or []

                return dict(zip(times, temps))
            except Exception:
                _time.sleep(0.7 * (attempt + 1))

        return None

    def fill_temperatures(self, df: pd.DataFrame, progress_cb=None):
        """
        Вариант №1: ОДИН запрос на трек/день.
        Берём опорные координаты трека (медиана широты/долготы по треку)
        и подтягиваем температуру по времени (UTC) для всех точек трека.
        """
        df = df.copy()
        if df is None or df.empty:
            return df
        if "time" not in df.columns or "track_id" not in df.columns:
            return df
        if "temperature" not in df.columns:
            df["temperature"] = None

        # где надо заполнять
        mask = df["temperature"].isna()
        if mask.sum() == 0:
            return df

        # гарантируем datetime UTC
        t_all = pd.to_datetime(df["time"], errors="coerce", utc=True)
        df["time"] = t_all

        # подготовим таблицу "что заполняем"
        tmp = df.loc[mask, ["track_id", "time"]].copy()
        tmp["date"] = tmp["time"].dt.strftime("%Y-%m-%d")
        tmp["hour_key"] = tmp["time"].dt.floor("h").dt.strftime("%Y-%m-%dT%H:00")

        # ✅ опорные координаты на трек (медиана устойчивее, чем first)
        # если хочешь ещё быстрее — можно заменить median() на first()
        coords = (
            df.dropna(subset=["latitude", "longitude"])
            .groupby("track_id", sort=False)[["latitude", "longitude"]]
            .median()
        )

        # группируем по трек/день => один запрос на группу
        groups = tmp.groupby(["track_id", "date"], sort=False)

        total_groups = len(groups)
        if progress_cb:
            progress_cb({"type": "max", "max": total_groups})

        cache = {}  # (track_id, date) -> day_map
        done = 0

        for (tid, dstr), g in groups:
            if progress_cb:
                progress_cb({"type": "text", "text": f"Температуры: {done + 1}/{total_groups} (track={tid}, {dstr})"})
                progress_cb({"type": "value", "value": done})

            # координаты трека
            if tid not in coords.index:
                # если нет координат — пропускаем
                done += 1
                continue

            lat = float(coords.loc[tid, "latitude"])
            lon = float(coords.loc[tid, "longitude"])

            key = (int(tid), str(dstr))
            if key not in cache:
                try:
                    cache[key] = self.fetch_temperature_day(lat, lon, str(dstr))
                except Exception:
                    cache[key] = None

            day_map = cache[key] or {}

            # проставляем значения
            for idx, hk in zip(g.index, g["hour_key"].values):
                df.at[idx, "temperature"] = self._pick_temp_nearest(day_map, hk, max_diff_hours=2)

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


# ==========================================================
# GPX Map Agent (показываем combined если есть)
# ==========================================================
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
        corr_threshold: float = 0.45,  # порог для "сильной" корреляции в объяснениях
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

    # берем числовые колонки
    num = dfw.select_dtypes(include=[np.number]).copy()

    # выкидываем служебные
    for col in ["track_id", "window_start"]:
        if col in num.columns:
            num.drop(columns=[col], inplace=True)

    # если мало признаков
    if num.shape[1] < 3:
        return None

    # чистим nan/inf
    num = num.replace([np.inf, -np.inf], np.nan)
    num = num.dropna(axis=1, how="all")
    num = num.fillna(num.median(numeric_only=True))

    if num.shape[1] < 3:
        return None

    corr = num.corr(method="spearman")  # spearman устойчивее к выбросам

    abs_arr = corr.abs().to_numpy(copy=True)
    np.fill_diagonal(abs_arr, np.nan)

    connectivity = pd.Series(
        np.nanmean(abs_arr, axis=1),
        index=corr.index
    ).sort_values(ascending=False)

    top_features = connectivity.head(min(top_k, len(connectivity))).index.tolist()

    # ---- формируем объяснения для top_features ----
    explanations = []
    for feat in top_features:
        # топ корреляции для этого признака
        s = corr[feat].drop(index=feat).sort_values(key=lambda x: x.abs(), ascending=False)

        # берем те, что выше порога
        strong = s[s.abs() >= corr_threshold].head(4)

        if len(strong) == 0:
            # если нет сильных корреляций, всё равно даём число "связности"
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

    # ---- рисуем heatmap ----
    # (без seaborn, только matplotlib)
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

    # исключаем очевидные не-фичи
    exclude = {
        "track_id",
        "time",
        "latitude",
        "longitude",
        "geometry",
        # если есть такие:
        "window_start",
    }

    # берём числовые + булевые
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
    strong_corr_threshold: float = 0.45,  # для объяснений
    drop_corr_threshold: float = 0.85,  # для удаления дублей
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

    # bool -> int (0/1)
    for c in X.columns:
        if pd.api.types.is_bool_dtype(X[c]):
            X[c] = X[c].astype(int)

    # чистим nan/inf
    X = X.replace([np.inf, -np.inf], np.nan)

    # если колонка вся nan — выкинуть
    X = X.dropna(axis=1, how="all")
    if X.shape[1] < 3:
        return None

    # заполняем nan медианой
    X = X.fillna(X.median(numeric_only=True))

    # корреляции
    corr = X.corr(method="spearman")

    abs_arr = corr.abs().to_numpy(copy=True)  # <-- гарантированно writable
    np.fill_diagonal(abs_arr, np.nan)

    connectivity = pd.Series(
        np.nanmean(abs_arr, axis=1),
        index=corr.index
    ).sort_values(ascending=False)

    # кандидаты top_k по связности
    candidates = connectivity.head(min(top_k, len(connectivity))).index.tolist()

    # убираем мультиколлинеарность: если два признака сильно коррелируют, оставляем один
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

    # heatmap
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


# ==========================================================
# GUI
# ==========================================================

def cleanup_image_folders():
    """Чистим папки с картинками треков при выходе из программы."""
    for folder in [MAPS_DIR, AUG_MAPS_DIR]:
        try:
            if os.path.exists(folder) and os.path.isdir(folder):
                shutil.rmtree(folder, ignore_errors=True)
        except Exception:
            pass


class DatabaseAgent:
    def __init__(self, cfg: dict, table_name: str = "gpx_dataset"):
        self.cfg = cfg
        self.conn = None
        self.table_name = table_name

    def connect(self):
        if self.conn is not None:
            return self.conn
        self.conn = psycopg2.connect(
            host=self.cfg["host"],
            port=int(self.cfg["port"]),
            dbname=self.cfg["dbname"],
            user=self.cfg["user"],
            password=self.cfg["password"],
        )
        self.conn.autocommit = False
        return self.conn

    def close(self):
        try:
            if self.conn is not None:
                self.conn.close()
        except Exception:
            pass
        self.conn = None

    def init_schema(self):
        conn = self.connect()
        t = self.table_name
        try:
            with conn.cursor() as cur:
                cur.execute(f"""
                    CREATE TABLE IF NOT EXISTS {t} (
                        id BIGSERIAL PRIMARY KEY,
                        track_id INT NOT NULL,
                        time TIMESTAMPTZ NULL,
                        latitude DOUBLE PRECISION NULL,
                        longitude DOUBLE PRECISION NULL,
                        elevation DOUBLE PRECISION NULL,
                        temperature DOUBLE PRECISION NULL,
                        cadence INT NULL,
                        distance_to_previous DOUBLE PRECISION NULL,
                        region TEXT NULL,
                        season TEXT NULL,
                        forest_nearby BOOLEAN NULL,
                        water_nearby BOOLEAN NULL,
                        road_nearby BOOLEAN NULL,
                        building_nearby BOOLEAN NULL
                    );
                """)
                cur.execute(f"CREATE INDEX IF NOT EXISTS idx_{t}_track_id ON {t}(track_id);")
            conn.commit()
        except Exception:
            conn.rollback()
            raise

    def overwrite_dataset(self, df: pd.DataFrame):
        """
        Полностью перезаписывает таблицу одним DataFrame.
        Делает: DELETE FROM table; затем bulk insert.
        """
        if df is None or df.empty:
            return

        conn = self.connect()
        t = self.table_name

        d = df.copy()

        # гарантируем колонки
        cols = [
            "track_id","time","latitude","longitude","elevation","temperature","cadence",
            "distance_to_previous","region","season",
            "forest_nearby","water_nearby","road_nearby","building_nearby",
        ]
        for c in cols:
            if c not in d.columns:
                d[c] = None

        # типы
        d["track_id"] = pd.to_numeric(d["track_id"], errors="coerce").fillna(0).astype(int)
        d["latitude"] = pd.to_numeric(d["latitude"], errors="coerce")
        d["longitude"] = pd.to_numeric(d["longitude"], errors="coerce")
        d["elevation"] = pd.to_numeric(d["elevation"], errors="coerce")
        d["temperature"] = pd.to_numeric(d["temperature"], errors="coerce")
        d["cadence"] = pd.to_numeric(d["cadence"], errors="coerce")
        d["distance_to_previous"] = pd.to_numeric(d["distance_to_previous"], errors="coerce")

        # time -> python datetime или None
        d["time"] = pd.to_datetime(d["time"], errors="coerce", utc=True)
        times_py = [
            x.to_pydatetime() if pd.notna(x) else None
            for x in d["time"].tolist()
        ]

        # bool -> python bool/None
        for c in ["forest_nearby","water_nearby","road_nearby","building_nearby"]:
            if c in d.columns:
                d[c] = d[c].astype("boolean")

        rows = []
        for i, r in d.iterrows():
            rows.append((
                int(r["track_id"]),
                times_py[i],
                float(r["latitude"]) if pd.notna(r["latitude"]) else None,
                float(r["longitude"]) if pd.notna(r["longitude"]) else None,
                float(r["elevation"]) if pd.notna(r["elevation"]) else None,
                float(r["temperature"]) if pd.notna(r["temperature"]) else None,
                int(r["cadence"]) if pd.notna(r["cadence"]) else None,
                float(r["distance_to_previous"]) if pd.notna(r["distance_to_previous"]) else None,
                str(r["region"]) if pd.notna(r["region"]) else None,
                str(r["season"]) if pd.notna(r["season"]) else None,
                bool(r["forest_nearby"]) if pd.notna(r["forest_nearby"]) else None,
                bool(r["water_nearby"]) if pd.notna(r["water_nearby"]) else None,
                bool(r["road_nearby"]) if pd.notna(r["road_nearby"]) else None,
                bool(r["building_nearby"]) if pd.notna(r["building_nearby"]) else None,
            ))

        try:
            with conn.cursor() as cur:
                cur.execute(f"DELETE FROM {t};")
                execute_values(
                    cur,
                    f"""
                    INSERT INTO {t} (
                        track_id, time, latitude, longitude,
                        elevation, temperature, cadence,
                        distance_to_previous, region, season,
                        forest_nearby, water_nearby, road_nearby, building_nearby
                    ) VALUES %s
                    """,
                    rows,
                    page_size=5000,
                )
            conn.commit()
        except Exception:
            conn.rollback()
            raise


def _read_file_bytes(path: str) -> bytes:
    with open(path, "rb") as f:
        return f.read()


# ===========================
# ДОБАВЬ ЭТО ОКНО ДЛЯ ВВОДА ПОДКЛЮЧЕНИЯ (где-нибудь выше GPXAppGUI)
# ===========================

class DBConnectDialog(tk.Toplevel):
    """Окно подключения к Postgres. Возвращает cfg dict или None (если закрыли/отменили)."""

    def __init__(self, master, default_cfg=None):
        super().__init__(master)
        self.title("Подключение к PostgreSQL")
        self.resizable(False, False)
        self.transient(master)
        self.grab_set()

        self.result_cfg = None

        cfg = default_cfg or {}
        defaults = {
            "host": cfg.get("host", "127.0.0.1"),
            "port": str(cfg.get("port", "5432")),
            "dbname": cfg.get("dbname", ""),
            "user": cfg.get("user", "postgres"),
            "password": cfg.get("password", ""),
        }
        self.vars = {k: tk.StringVar(value=v) for k, v in defaults.items()}

        frm = tk.Frame(self)
        frm.pack(padx=12, pady=12)

        def row(label, key, show=None):
            r = tk.Frame(frm)
            r.pack(fill="x", pady=4)
            tk.Label(r, text=label, width=12, anchor="w").pack(side="left")
            e = tk.Entry(r, textvariable=self.vars[key], width=32, show=show)
            e.pack(side="left")
            return e

        self.e_host = row("Host", "host")
        self.e_port = row("Port", "port")
        self.e_db = row("DB name", "dbname")
        self.e_user = row("User", "user")
        self.e_pass = row("Password", "password", show="*")

        hint = (
            "Подключение нужно для сохранения треков/картинок/точек в Postgres.\n"
            "DB name — это УЖЕ созданная база (в pgAdmin).\n"
            "Если база не создана — создай её в pgAdmin заранее."
        )
        tk.Label(frm, text=hint, justify="left", wraplength=360).pack(pady=(10, 8), anchor="w")

        btns = tk.Frame(frm)
        btns.pack(fill="x")

        self.btn_test = tk.Button(btns, text="Проверить", command=self._test_connection)
        self.btn_test.pack(side="left")

        self.btn_ok = tk.Button(btns, text="Подключиться", command=self._ok)
        self.btn_ok.pack(side="right")

        self.btn_cancel = tk.Button(btns, text="Без БД", command=self._cancel)
        self.btn_cancel.pack(side="right", padx=6)

        self.protocol("WM_DELETE_WINDOW", self._cancel)
        self.e_host.focus_set()

    def _cfg(self):
        return {
            "host": self.vars["host"].get().strip(),
            "port": self.vars["port"].get().strip(),
            "dbname": self.vars["dbname"].get().strip(),
            "user": self.vars["user"].get().strip(),
            "password": self.vars["password"].get(),
        }

    def _test_connection(self):
        cfg = self._cfg()
        try:
            conn = psycopg2.connect(
                host=cfg["host"],
                port=int(cfg["port"]),
                dbname=cfg["dbname"],
                user=cfg["user"],
                password=cfg["password"],
                connect_timeout=5,
            )
            conn.close()
            messagebox.showinfo("PostgreSQL", "Подключение успешно!")
        except Exception as e:
            messagebox.showerror("PostgreSQL", f"Ошибка подключения:\n{e}")

    def _ok(self):
        cfg = self._cfg()
        if not cfg["dbname"]:
            messagebox.showwarning("PostgreSQL", "Введите DB name (имя базы)")
            return

        self.result_cfg = cfg
        self.grab_release()
        self.destroy()

    def _cancel(self):
        self.result_cfg = None
        self.grab_release()
        self.destroy()

    def _safe_close(self):
        """Закрыть диалог без падений Tk."""
        # аккуратно снять grab, если он наш
        try:
            if self.grab_current() == self:
                self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass

    def _ok(self):
        cfg = self._cfg()
        if not cfg["dbname"]:
            messagebox.showwarning("PostgreSQL", "Введите DB name (имя базы)")
            return

        self.result_cfg = cfg
        self._safe_close()

    def _cancel(self):
        self.result_cfg = None
        self._safe_close()


# ==========================================================
# Cleanup при закрытии
# ==========================================================

class GPXAppGUI:
    def __init__(self, master):
        self.master = master
        master.title("GPX Tracks Manager")
        master.geometry("1000x600")

        self.agent = GPXLoaderAgent()
        self.result_df = None
        self.runner = AsyncRunner(master)

        self.db = None
        self.db_cfg = None

        # ✅ 1) СНАЧАЛА создаём статус-бар
        self.db_status_var = tk.StringVar(value="DB: нет подключения")
        status_bar = tk.Label(master, textvariable=self.db_status_var, anchor="w")
        status_bar.pack(side="bottom", fill="x")

        # ✅ (по желанию) флаг для синхронизации
        self._db_sync_in_progress = False

        # ✅ 2) теперь уже можно спрашивать подключение (статус будет обновляться)
        self._ask_db_connection_on_start()

        self.all_buttons = []
        self.notebook = ttk.Notebook(master)
        self.notebook.pack(fill="both", expand=True)

        self.tab_load = ttk.Frame(self.notebook)
        self.tab_process = ttk.Frame(self.notebook)
        self.tab_view = ttk.Frame(self.notebook)
        self.tab_augment = ttk.Frame(self.notebook)
        self.tab_exit = ttk.Frame(self.notebook)

        self.notebook.add(self.tab_load, text="Загрузка треков")
        self.notebook.add(self.tab_process, text="Обработка треков")
        self.notebook.add(self.tab_view, text="Просмотр треков")
        self.notebook.add(self.tab_augment, text="Аугментация треков")
        self.notebook.add(self.tab_exit, text="Выход")

        self.create_tab_load()
        self.create_tab_process()
        self.create_tab_view()
        self.create_tab_augment()
        self.create_tab_exit()

        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_change)

        self.last_selected_tab = self.notebook.select()

    def create_tab_exit(self):
        # Вкладка "Выход" не имеет кнопки, окно с вопросом появится при выборе вкладки
        pass

    def on_tab_change(self, event):
        # Проверяем, что пользователь выбрал вкладку "Выход"
        selected_tab = self.notebook.tab(self.notebook.select(), "text")

        if selected_tab == "Выход":
            self.confirm_exit()

    def confirm_exit(self):
        # Открываем окно с вопросом, чтобы подтвердить выход
        exit_confirmation = messagebox.askyesno(
            "Подтвердите выход",
            "Вы уверены, что хотите выйти?"
        )

        if exit_confirmation:  # Если нажали "Да"
            self.master.quit()  # Завершаем приложение
        else:
            # Если нажали "Нет", возвращаем на последнюю вкладку
            self.notebook.select(self.last_selected_tab)  # Переключаемся на последнюю вкладку
            pass  # Если "Нет", просто ничего не делаем

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


    def save_dataset_to_single_table(self):
        if self.db is None:
            messagebox.showwarning("База данных", "Нет подключения к БД.")
            return
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("База данных", "Нет данных: сначала загрузите треки.")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="БД", text="Сохраняем dataset в БД...", determinate=False)

        def worker(_progress_cb):
            self.db.overwrite_dataset(self.result_df)
            return len(self.result_df)

        def on_done(nrows):
            pwin.close()
            self.set_busy(False)
            messagebox.showinfo("База данных", f"Готово ✅\nСохранено строк: {nrows}\nТаблица: {self.db.table_name}")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("База данных", f"Ошибка сохранения:\n{err}")

        self.runner.run(worker, on_done=on_done, on_error=on_error)

    def _reg_btn(self, btn):
        self.all_buttons.append(btn)
        return btn

    def show_environment_debug(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
            return

        # Попробуем взять выбранный трек из combo на вкладке "Просмотр"
        track_id = None
        try:
            if hasattr(self, "track_combo"):
                v = self.track_combo.get()
                if v:
                    track_id = int(v)
        except Exception:
            track_id = None

        # Если не получилось — возьмём первый трек
        if track_id is None:
            try:
                track_id = int(sorted(self.result_df["track_id"].unique())[0])
            except Exception:
                messagebox.showerror("Ошибка", "Не удалось определить track_id")
                return

        df_track = self.result_df[self.result_df["track_id"] == track_id].copy()
        if df_track.empty:
            messagebox.showerror("Ошибка", f"Трек {track_id} не найден")
            return

        # Спросим индекс точки (по умолчанию середина трека)
        default_idx = int(df_track.index[len(df_track) // 2])
        point_idx = simpledialog.askinteger(
            "Debug окружения",
            f"Введите index точки (DataFrame index) для трека {track_id}.\n"
            f"Например: {default_idx}",
            initialvalue=default_idx,
            parent=self.master
        )
        if point_idx is None:
            return

        # Выбираем basemap/meta: augmented -> original
        aug_base = os.path.join(AUG_MAPS_DIR, f"track_{track_id}_basemap.png")
        aug_meta = _meta_path(AUG_MAPS_DIR, track_id)

        orig_base = os.path.join(MAPS_DIR, f"track_{track_id}_basemap.png")
        orig_meta = _meta_path(MAPS_DIR, track_id)

        if os.path.exists(aug_base) and os.path.exists(aug_meta):
            base_path, meta_path = aug_base, aug_meta
        elif os.path.exists(orig_base) and os.path.exists(orig_meta):
            base_path, meta_path = orig_base, orig_meta
        else:
            messagebox.showerror(
                "Ошибка",
                "Не найден basemap/meta для трека.\n"
                "Сначала загрузи треки (чтобы создались maps/*_basemap.png и *_meta.json)\n"
                "или сделай аугментацию (augmented_maps/*)."
            )
            return

        try:
            res = visualize_environment_from_image_for_point(
                df_track=df_track,
                point_idx=point_idx,
                basemap_png_path=base_path,
                meta_json_path=meta_path,
                radius_m=500,
                n_clusters=6,
                threshold=35
            )
            if res is None:
                messagebox.showerror("Ошибка", "Не удалось построить debug-визуализацию (res=None)")
                return

            # Открываем картинки
            self._open_image_window(res["map_path"], f"Debug map: track {track_id}, idx {point_idx}")
            self._open_image_window(res["patch_path"], f"Debug patch: track {track_id}, idx {point_idx}")
            self._open_image_window(res["palette_path"], f"Debug palette: track {track_id}, idx {point_idx}")

            attrs = res.get("attrs", {})
            attrs_txt = "\n".join([f"{k}: {v}" for k, v in attrs.items()])
            messagebox.showinfo(
                "Результат окружения",
                f"Трек: {track_id}\n"
                f"point_idx: {point_idx}\n"
                f"pixel: {res.get('point_pixel')}, radius_px: {res.get('radius_px')}\n\n"
                f"Атрибуты:\n{attrs_txt}"
            )
        except Exception as e:
            messagebox.showerror("Ошибка", f"show_environment_debug:\n{e}")

    def _ask_db_connection_on_start(self):
        dlg = DBConnectDialog(
            self.master,
            default_cfg={
                "host": "127.0.0.1",
                "port": "5432",
                "dbname": "",
                "user": "postgres",
                "password": "",
            },
        )
        self.master.wait_window(dlg)

        cfg = dlg.result_cfg
        if cfg is None:
            self.db = None
            self.db_cfg = None
            self._set_db_status("DB: нет подключения (работаем без БД)")

            # ✅ важно: показать сообщение НЕ сразу, а после инициализации UI
            self.master.after(
                0,
                lambda: messagebox.showinfo(
                    "PostgreSQL",
                    "Работаем без базы данных. Сохранение в БД отключено."
                )
            )
            return

        try:
            db = DatabaseAgent(cfg)
            db.init_schema()
            self.db = db
            self.db_cfg = cfg
            self._set_db_status("DB: подключено ✅ | таблицы готовы")

            self.master.after(
                0,
                lambda: messagebox.showinfo(
                    "PostgreSQL",
                    "Подключение к БД установлено. Таблицы готовы."
                )
            )
        except Exception as e:
            self.db = None
            self.db_cfg = None
            self._set_db_status("DB: ошибка подключения ❌ | работаем без БД")

            self.master.after(
                0,
                lambda: messagebox.showerror(
                    "PostgreSQL",
                    f"Не удалось подключиться/инициализировать БД:\n{e}\n\nРаботаем без БД."
                )
            )

    def set_busy(self, busy: bool):
        if busy:
            disable_widgets(self.all_buttons)
        else:
            enable_widgets(self.all_buttons)

    def _db_sync_all_points(self):
        if self.db is None:
            return
        if self.result_df is None or self.result_df.empty:
            return

        try:
            self._set_db_status("DB: синхронизация... ⏳")
        except Exception:
            pass

        track_ids = sorted(self.result_df["track_id"].unique())
        for tid in track_ids:
            df_track = self.result_df[self.result_df["track_id"] == tid].copy()
            if not df_track.empty:
                self.db.replace_points(int(tid), df_track)

        # время можно без import datetime, через time:
        import time

        ts = time.strftime("%H:%M:%S")
        self._set_db_status(f"DB: актуально ✅ | последняя синхронизация {ts} | треков: {len(track_ids)}")

    # ----------------- Загрузка -----------------

    def create_tab_load(self):
        # Заголовок вкладки - жирный и по центру
        tk.Label(self.tab_load, text="Загрузка треков", font=("Arial", 14, "bold")).grid(row=0, column=0, columnspan=2,
                                                                                         pady=(10, 10), sticky="n",
                                                                                         padx=12)

        # Под заголовком выводим количество уникальных ссылок по центру
        self.links_counter_var = tk.StringVar(value="Ссылок: 0, Уникальных ссылок: 0")
        tk.Label(self.tab_load, textvariable=self.links_counter_var, font=("Arial", 12)).grid(row=1, column=0,
                                                                                              columnspan=2,
                                                                                              pady=(0, 10), sticky="n",
                                                                                              padx=12)

        # Текстовое поле для ввода ссылок теперь сверху, растягиваем его на два столбца
        self.text_area = scrolledtext.ScrolledText(self.tab_load, width=110, height=14)
        self.text_area.grid(row=2, column=0, columnspan=2, padx=12, pady=(0, 10), sticky="nsew")

        placeholder = "Вставьте ссылки сюда...\n(Одна ссылка на строку)"
        self.text_area.insert("1.0", placeholder)
        self.text_area.bind("<FocusIn>", self._clear_placeholder_if_needed)
        self.text_area.bind("<KeyRelease>", lambda _e: self.update_links_counter())

        # Фрейм для кнопок, кнопки теперь расположены под полем ввода, с отступом слева как у текста и поля ввода
        btn_frame = tk.Frame(self.tab_load)
        btn_frame.grid(row=3, column=0, columnspan=2, pady=(10, 10), sticky="w",
                       padx=12)  # Добавили отступ слева как у текста и поля ввода

        # Кнопки для работы с ссылками, выровнены по горизонтали слева
        self.btn_paste = self._reg_btn(
            tk.Button(btn_frame, text="Вставить из буфера", command=self.paste_links_from_clipboard))
        self.btn_paste.grid(row=0, column=0, padx=(0, 6))

        self.btn_dedup = self._reg_btn(
            tk.Button(btn_frame, text="Удалить повторяющиеся ссылки", command=self.dedup_links_ui))
        self.btn_dedup.grid(row=0, column=1, padx=(0, 6))

        self.btn_clear = self._reg_btn(
            tk.Button(btn_frame, text="Очистить", command=self.clear_links_ui, bg="#F44336", fg="white",
                      font=("Arial", 10)))
        self.btn_clear.grid(row=0, column=2, padx=(0, 6), pady=10)

        # Добавляем эффект наведения на кнопку "Очистить" (красный цвет при наведении)
        self.btn_clear.bind("<Enter>", lambda e: e.widget.config(bg="#D32F2F"))  # Красный при наведении
        self.btn_clear.bind("<Leave>", lambda e: e.widget.config(bg="#F44336"))  # Оригинальный красный цвет

        # Под кнопками добавляем текст с правилами
        hint = (
            "Формат ввода ссылок на GPX-треки:\n"
            "- Каждая ссылка может быть указана на отдельной строке\n"
            "- Допускается вставка списка ссылок за один раз\n"
            "- Ссылки могут быть разделены переносами строк, пробелами, запятыми или точкой с запятой\n\n"
        )

        # Добавляем текст с правилами - выравнивание по левому краю
        tk.Label(self.tab_load, text=hint, justify="left", wraplength=900).grid(row=4, column=0, columnspan=2,
                                                                                pady=(0, 10), padx=12, sticky="w")

        # Кнопка для загрузки треков - расположена в правом углу
        self.btn_load = self._reg_btn(
            tk.Button(self.tab_load, text="Загрузить треки", width=30, command=self.load_tracks))
        self.btn_load.grid(row=3, column=1, pady=10, padx=(10, 20), sticky="e")  # В правом углу

    def load_tracks(self):
        urls = self.get_links_from_ui()
        urls = [u.strip() for u in urls if u.strip()]
        urls = list(dict.fromkeys(urls))  # убираем дубликаты, сохраняя порядок

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

                # Сохраняем в Postgres (если подключены), получаем db id
                # ✅ БД не трогаем при загрузке — только локальные картинки
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
            messagebox.showinfo("Успех", "Треки загружены! (карты+meta сохранены в maps/)")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def _db_save_track_bundle(self, source_url: str, local_track_id: int, df_track: pd.DataFrame):
        """
        Сохраняет трек + точки в БД всегда.
        Картинки пытается сохранить, но если OSM таймаут — это НЕ ошибка БД.
        Возвращает ID трека в БД или None (если реально БД недоступна).
        """
        if self.db is None:
            return None

        # 1) Сохраняем трек + точки (это главное)
        try:
            db_id = self.db.upsert_track(source_url)
            self.db.replace_points(db_id, df_track)
        except Exception as e:
            # вот это — РЕАЛЬНАЯ ошибка БД
            try:
                messagebox.showwarning("PostgreSQL", f"Ошибка БД (точки не сохранены):\n\n{e}")
            except Exception:
                pass
            return None

        # 2) Пытаемся сделать и сохранить картинки, но НЕ валим БД при ошибках сети
        try:
            os.makedirs(MAPS_DIR, exist_ok=True)
            basemap_path, route_path, combined_path = save_track_assets(df_track, track_id=db_id, out_dir=MAPS_DIR)
            meta_path = _meta_path(MAPS_DIR, db_id)

            # basemap
            if os.path.exists(basemap_path):
                self.db.upsert_image(
                    db_id, "basemap",
                    _read_file_bytes(basemap_path),
                    _load_meta(meta_path) if os.path.exists(meta_path) else None
                )

            # route
            if os.path.exists(route_path):
                self.db.upsert_image(
                    db_id, "route",
                    _read_file_bytes(route_path),
                    _load_meta(meta_path) if os.path.exists(meta_path) else None
                )

            # combined
            if os.path.exists(combined_path):
                self.db.upsert_image(
                    db_id, "combined",
                    _read_file_bytes(combined_path),
                    _load_meta(meta_path) if os.path.exists(meta_path) else None
                )

        except Exception as e:
            # это НЕ ошибка БД — просто интернет/OSM/тайлы
            try:
                messagebox.showwarning(
                    "Карты (OSM)",
                    "Точки сохранены в БД ✅\n"
                    "Но не удалось скачать карту OpenStreetMap (таймаут/нет сети).\n\n"
                    f"Ошибка:\n{e}\n\n"
                    "Можно продолжать — картинки просто не обновились."
                )
            except Exception:
                pass

        return int(db_id)
        """
        Сохраняет трек + картинки в БД, если подключена.
        Возвращает ID трека в БД (int) или None если работаем без БД/ошибка.
        """
        if self.db is None:
            return None

        try:
            # 1) upsert трека, получаем db id
            db_id = self.db.upsert_track(source_url)

            # 2) сохраняем точки
            self.db.replace_points(db_id, df_track)

            # 3) генерим и сохраняем картинки+meta (берём на диске из maps/, затем в БД)
            os.makedirs(MAPS_DIR, exist_ok=True)
            basemap_path, route_path, combined_path = save_track_assets(df_track, track_id=db_id, out_dir=MAPS_DIR)
            meta_path = _meta_path(MAPS_DIR, db_id)

            # basemap
            if os.path.exists(basemap_path):
                self.db.upsert_image(db_id, "basemap", _read_file_bytes(basemap_path),
                                     _load_meta(meta_path) if os.path.exists(meta_path) else None)

            # route
            if os.path.exists(route_path):
                self.db.upsert_image(db_id, "route", _read_file_bytes(route_path),
                                     _load_meta(meta_path) if os.path.exists(meta_path) else None)

            # combined
            if os.path.exists(combined_path):
                self.db.upsert_image(db_id, "combined", _read_file_bytes(combined_path),
                                     _load_meta(meta_path) if os.path.exists(meta_path) else None)

            return int(db_id)

        except Exception as e:
            # если что-то пошло не так — не валим приложение
            try:
                messagebox.showwarning("PostgreSQL", f"Не удалось сохранить трек в БД, продолжим без БД.\n\n{e}")
            except Exception:
                pass
            return None

    def _db_sync_all_points_async(self):
        if self.db is None:
            return
        if self.result_df is None or self.result_df.empty:
            return
        if getattr(self, "_db_sync_in_progress", False):
            return  # ✅ уже идёт синк, не дублим

        self._db_sync_in_progress = True
        self._set_db_status("DB: синхронизация... ⏳")

        def target():
            try:
                self._db_sync_all_points()
            except Exception as e:
                self._set_db_status(f"DB: ошибка синхронизации ❌ ({e})")
            finally:
                self._db_sync_in_progress = False

        threading.Thread(target=target, daemon=True).start()


    def save_selected_track_to_db(self):
        """Сохраняет в БД точки выбранного трека (в таблицу track_points)."""
        if self.db is None:
            messagebox.showwarning("База данных", "Нет подключения к БД.")
            return
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("База данных", "Нет данных: сначала загрузите треки.")
            return

        track_id = None
        try:
            v = self.track_combo.get() if hasattr(self, "track_combo") else None
            if v:
                track_id = int(v)
        except Exception:
            track_id = None

        if track_id is None:
            messagebox.showwarning("База данных", "Выберите трек в списке.")
            return

        df_track = self.result_df[self.result_df["track_id"] == track_id].copy()
        if df_track.empty:
            messagebox.showerror("База данных", f"Трек {track_id} не найден в DataFrame.")
            return

        self.set_busy(True)
        pwin = ProgressWindow(
            self.master,
            title="Сохранение в БД",
            text=f"Сохраняем трек {track_id} в БД...",
            determinate=False
        )

        def worker(_progress_cb):
            # replace_points сам удалит старые точки и вставит новые
            self.db.replace_points(int(track_id), df_track)
            return track_id

        def on_done(tid):
            pwin.close()
            self.set_busy(False)
            self._set_db_status("DB: сохранено ✅ (выбранный трек)")
            messagebox.showinfo("База данных", f"Трек {tid} сохранён в таблицу track_points.")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("База данных", f"Ошибка сохранения:\n{err}")

        self.runner.run(worker, on_done=on_done, on_error=on_error)

    def save_all_tracks_to_db(self):
        """Сохраняет в БД точки всех треков из result_df."""
        if self.db is None:
            messagebox.showwarning("База данных", "Нет подключения к БД.")
            return
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("База данных", "Нет данных: сначала загрузите треки.")
            return

        track_ids = sorted(self.result_df["track_id"].unique())
        self.set_busy(True)
        pwin = ProgressWindow(
            self.master,
            title="Сохранение в БД",
            text="Сохраняем все треки в БД...",
            determinate=True,
            maximum=len(track_ids)
        )

        def worker(progress_cb):
            for i, tid in enumerate(track_ids, start=1):
                if progress_cb:
                    progress_cb({"type": "text", "text": f"Сохранение трека {tid} ({i}/{len(track_ids)})..."})
                    progress_cb({"type": "value", "value": i - 1})

                df_track = self.result_df[self.result_df["track_id"] == tid].copy()
                if not df_track.empty:
                    self.db.replace_points(int(tid), df_track)

                if progress_cb:
                    progress_cb({"type": "value", "value": i})

            return len(track_ids)

        def on_progress(payload):
            t = payload.get("type")
            if t == "text":
                pwin.set_text(payload.get("text", ""))
            elif t == "value":
                pwin.set_value(float(payload.get("value", 0)))

        def on_done(n):
            pwin.close()
            self.set_busy(False)
            self._set_db_status(f"DB: сохранено ✅ | треков: {n}")
            messagebox.showinfo("База данных", f"Сохранено треков: {n}\nТаблица: track_points")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("База данных", f"Ошибка сохранения:\n{err}")

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)


    # ----------------- Обработка -----------------

    def create_tab_process(self):
        tk.Label(
            self.tab_process,
            text="Обработка треков: выполните действия по шагам",
            font=("Arial", 14, "bold"),
        ).pack(pady=10)

        def create_button_with_info(parent, text, command, info_text):
            frame = tk.Frame(parent)
            frame.pack(pady=10)

            btn = self._reg_btn(tk.Button(frame, text=text, width=40, command=command))
            btn.pack(side="left")

            info_btn = self._reg_btn(
                tk.Button(frame, text="?", width=3, command=lambda: messagebox.showinfo("Информация", info_text))
            )
            info_btn.pack(side="left", padx=5)

            frame.pack(anchor="center")

        create_button_with_info(
            self.tab_process,
            "1. Определить регионы",
            self.assign_regions,
            "Определяет географический регион для каждой точки трека.",
        )
        create_button_with_info(
            self.tab_process,
            "2. Добавить сезонность",
            self.add_seasons,
            "Добавляет сезон (зима, весна, лето, осень) для каждой точки трека.",
        )
        create_button_with_info(
            self.tab_process,
            "3. Заполнить температуры",
            self.fill_temperatures,
            "Заполняет температуры для точек без данных через API.",
        )
        create_button_with_info(
            self.tab_process,
            "4. Определение окружения",
            self.add_environment,
            "Считает окружение по картинке basemap для каждой точки.",
        )
        create_button_with_info(
            self.tab_process,
            "4b. Как считается окружение (по картинке)",
            self.show_environment_debug,
            "Открывает наглядную визуализацию: basemap + круг 500м + patch + доминирующие цвета.\n"
            "Окружение берётся по картинке и цветам.",
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
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
            return

        track_ids = sorted(self.result_df["track_id"].unique())
        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Регионы", text="Определение регионов...", determinate=True, maximum=len(track_ids))

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
            messagebox.showinfo("Успех", "Регионы определены!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def add_seasons(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
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
            messagebox.showinfo("Успех", "Сезонность добавлена!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error)

    def fill_temperatures(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Температуры", text="Заполнение температур...", determinate=True, maximum=len(self.result_df))

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
            messagebox.showinfo("Успех", "Температуры заполнены!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def add_environment(self):
        """Окружение считается ПО КАРТИНКЕ трека (maps/ или augmented_maps/)."""
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
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
            messagebox.showinfo("Успех", "Окружение добавлено (по картинкам)!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    # ----------------- Просмотр -----------------

    def create_tab_view(self):
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

        save_csv_button = tk.Button(self.tab_view, text="Сохранить датасет в CSV", command=self.save_dataset_to_csv)
        save_csv_button.pack(pady=5)

        self.btn_show_df = self._reg_btn(
            tk.Button(self.tab_view, text="Показать DataFrame трека", command=self.show_dataframe)
        )
        self.btn_show_df.pack(pady=5)

        # --- КНОПКИ СИНХРОНИЗАЦИИ С БД ---
        self.btn_save_dataset_to_db = self._reg_btn(
            tk.Button(
                self.tab_view,
                text="Сохранить dataset в БД ",
                command=self.save_dataset_to_single_table,
                width=45
            )
        )
        self.btn_save_dataset_to_db.pack(pady=8)

    def save_dataset_to_csv(self):
        if self.result_df is not None and not self.result_df.empty:
            # Создаем папку "exports", если она не существует
            export_folder = "exports"
            if not os.path.exists(export_folder):
                os.makedirs(export_folder)

            # Формируем имя файла с текущей датой, чтобы избежать перезаписи
            current_time = datetime.now().strftime("%Y%m%d_%H%M%S")
            file_name = f"track_data_{current_time}.csv"
            file_path = os.path.join(export_folder, file_name)

            try:
                # Сохраняем DataFrame в CSV
                self.result_df.to_csv(file_path, index=False)
                messagebox.showinfo("Успех", f"Данные успешно сохранены в {file_path}!")
            except Exception as e:
                messagebox.showerror("Ошибка", f"Ошибка при сохранении данных: {e}")
        else:
            messagebox.showwarning("Предупреждение", "Нет данных для сохранения.")

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
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
            return

        track_id = self.track_combo.get()
        if not track_id:
            messagebox.showwarning("Ошибка", "Выберите трек")
            return

        track_id = int(track_id)

        try:
            # 1) если есть аугментированная картинка — покажем её
            aug_path = os.path.join(AUG_MAPS_DIR, f"track_{track_id}_augmented.png")
            if os.path.exists(aug_path):
                self._open_image_window(aug_path, f"Аугментированный трек {track_id}")
                return

            # 2) если есть combined — показываем его
            combined_path = os.path.join(MAPS_DIR, f"track_{track_id}_combined.png")
            if os.path.exists(combined_path):
                self._open_image_window(combined_path, f"Карта трека {track_id}")
                return

            # 3) если нет готовых картинок — строим на лету (fallback)
            map_agent = GPXMapAgent(self.result_df)
            png_path = map_agent.plot_track_to_png(track_id, save_folder=MAPS_DIR)
            self._open_image_window(png_path, f"Карта трека {track_id}")

        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось показать карту:\n{e}")

    def show_dataframe(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
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
    def save_all_tracks_to_csv(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Нечего сохранять: сначала загрузите/аугментируйте треки")
            return

        # Диалог выбора файла
        default_name = "all_tracks.csv"
        file_path = filedialog.asksaveasfilename(
            title="Сохранить все треки в CSV",
            defaultextension=".csv",
            initialfile=default_name,
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )

        if not file_path:
            return  # пользователь отменил

        try:
            df = self.result_df.copy()

            # Приведём time к строке, чтобы CSV был стабильным
            if "time" in df.columns:
                df["time"] = pd.to_datetime(df["time"], errors="coerce")
                # ISO формат (с таймзоной, если есть)
                df["time"] = df["time"].dt.strftime("%Y-%m-%dT%H:%M:%S%z")

            df.to_csv(file_path, index=False, encoding="utf-8-sig")
            messagebox.showinfo("Готово", f"Сохранено в файл:\n{file_path}")
        except Exception as e:
            messagebox.showerror("Ошибка сохранения", str(e))

    # ----------------- Аугментация -----------------

    def create_tab_augment(self):
        tk.Label(self.tab_augment, text="Аугментация треков").pack(pady=5)

        self.btn_augment_all = self._reg_btn(
            tk.Button(
                self.tab_augment,
                text="Аугментировать ВСЕ треки (фон 180° + окружение по картинке)",
                command=self.augment_all_tracks,
                width=72,
            )
        )
        self.btn_augment_all.pack(pady=8)

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
            tk.Button(self.tab_augment, text="Показать DataFrame выбранного трека", command=self.show_selected_track_dataframe)
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
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
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
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
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
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
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
            messagebox.showinfo("Успех", "Аугментация завершена!")

        def on_error(err):
            pwin.close()
            self.set_busy(False)
            messagebox.showerror("Ошибка", str(err))

        self.runner.run(worker, on_done=on_done, on_error=on_error, on_progress=on_progress)

    def show_significant_attributes(self):
        if self.result_df is None or self.result_df.empty:
            messagebox.showwarning("Ошибка", "Сначала загрузите треки")
            return

        self.set_busy(True)
        pwin = ProgressWindow(self.master, title="Анализ", text="Строим heatmap и выбираем признаки...", determinate=False)

        def worker(_progress_cb):
            res = compute_heatmap_and_pick_features_from_existing_df(
                self.result_df,
                top_k=12,
                strong_corr_threshold=0.45,
                drop_corr_threshold=0.85,
            )
            return res

        def on_done(res):
            pwin.close()
            self.set_busy(False)

            if res is None:
                messagebox.showerror(
                    "Ошибка",
                    "Недостаточно подходящих числовых/булевых атрибутов для корреляционного анализа.\n"
                    "Подсказка: сначала посчитай окружение (forest_nearby и т.п.) и убедись, что есть числовые поля.",
                )
                return

            win = tk.Toplevel(self.master)
            win.title("Значимые атрибуты (heatmap Spearman)")

            # heatmap image
            img_path = res["heatmap_path"]
            if os.path.exists(img_path):
                img = Image.open(img_path)
                max_w, max_h = 900, 650
                w, h = img.size
                k = min(max_w / w, max_h / h, 1.0)
                if k < 1.0:
                    img = img.resize((int(w * k), int(h * k)))

                img_tk = ImageTk.PhotoImage(img)
                lbl = tk.Label(win, image=img_tk)
                lbl.image = img_tk
                lbl.pack(padx=10, pady=10)

            box = scrolledtext.ScrolledText(win, width=120, height=18)
            box.pack(fill="both", expand=True, padx=10, pady=(0, 10))

            lines = []
            lines.append("Выбор значимых атрибутов по корреляции (Spearman)")
            lines.append("")
            lines.append("Как выбирались признаки:")
            lines.append("1) Взяли только существующие колонки DataFrame, которые являются числовыми или булевыми.")
            lines.append("2) Построили корреляционную матрицу Spearman (устойчива к выбросам).")
            lines.append("3) Для каждого признака посчитали 'связность' = среднее(|corr|) с другими признаками.")
            lines.append("4) Выбрали top по связности и убрали дубли, если |corr| между выбранными > 0.85.")
            lines.append("")
            lines.append("Рекомендуемые атрибуты для обучения модели (можно брать как features):")
            for f in res["selected_features"]:
                lines.append(f"- {f}")
            lines.append("")
            lines.append("Конкретное обоснование выбора (с численными корреляциями):")
            lines.extend(res["explanations"])
            lines.append("")
            lines.append(
                "Примечание: корреляция показывает совместную изменчивость признаков. "
                "Если признак сильно связан с несколькими другими, он отражает общий фактор "
                "и полезен для группировки/схожести участков."
            )

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

        # заменим разделители на перенос строк
        s = raw_text.replace(";", "\n").replace(",", "\n").replace("\t", "\n")

        # пробелы тоже считаем разделителями, но аккуратно:
        # сначала разделим по строкам, потом внутри строк по пробелам
        parts = []
        for line in s.splitlines():
            line = line.strip()
            if not line:
                continue
            for token in line.split():
                token = token.strip()
                if token:
                    parts.append(token)

        # финальная очистка
        parts = [p.strip() for p in parts if p.strip()]
        return parts

    def get_links_from_ui(self):
        raw = self.text_area.get("1.0", tk.END)
        links = self.parse_links_from_text(raw)
        # убираем placeholder если остался
        links = [u for u in links if not u.startswith("Вставьте ссылки сюда")]
        return links

    def update_links_counter(self):
        links = self.get_links_from_ui()
        uniq = list(dict.fromkeys(links))  # сохраняем порядок
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

        # перезаписываем как “одна ссылка на строку”
        self.text_area.delete("1.0", tk.END)
        self.text_area.insert("1.0", "\n".join(merged))
        self.update_links_counter()

    def clear_links_ui(self):
        self.text_area.delete("1.0", tk.END)
        self.update_links_counter()


    def _set_db_status(self, text: str):
        """Безопасно обновляет статус-бар из любого потока."""
        def _apply():
            try:
                self.db_status_var.set(text)
            except Exception:
                pass

        try:
            self.master.after(0, _apply)
        except Exception:
            # на случай если master уже закрыт
            pass





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

        # дубликаты
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

    # --- дальше у тебя идёт show_environment_debug / _db_save_track_bundle / _ensure_track_combined_image / _set_db_status ---
    # Я их могу так же полностью отформатировать, но они уже почти норм по структуре.
    # Если хочешь — просто скинь оставшийся хвост (или файл целиком), и я прогоню весь файл единообразно.


# ==========================================================
# MAIN
# ==========================================================

if __name__ == "__main__":
    root = tk.Tk()
    app = GPXAppGUI(root)

    try:
        if hasattr(app, "db") and app.db is not None:
            app.db.close()
    except Exception:
        pass

    def on_close():
        cleanup_image_folders()
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()
ы
