import colorsys
import csv
import io
import json
import calendar
import array
import wave
import threading
import math
import random
import re
import shutil
import sys
import time
import functools
import unicodedata
import types as _types
import uuid
import webbrowser
import zipfile
from collections import Counter, OrderedDict
from datetime import date, datetime, timedelta
from pathlib import Path
import tkinter as tk
from tkinter import colorchooser, filedialog, messagebox

import customtkinter as ctk
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont, ImageOps, ImageTk

try:
    from PIL import ImageGrab      # colar imagem da área de transferência
except ImportError:                # algumas instalações do Linux não têm
    ImageGrab = None

# ---------- constantes ----------
APP_DIR = Path.home() / ".leitura_foda"
SETTINGS_FILE = APP_DIR / "settings.json"
GOLD = (255, 194, 51, 255)
GOLD_HEX = "#ffc233"
DANGER = "#e5484d"
PINK = "#ff5c8a"

STATUS = {"lendo": "Lendo", "completo": "Completo", "planejo": "Quero ler",
          "pausado": "Pausado", "largado": "Largado"}
STATUS_BY_LABEL = {v: k for k, v in STATUS.items()}
TYPES = ["Mangá", "Manhwa", "Webtoon", "Livro", "Outro"]
SORTS = ["Mais recentes", "Última atualização", "Nome (A–Z)", "Maior nota",
         "Mais capítulos lidos", "Data de início"]
ACCENTS = ["#8b5cf6", "#3b82f6", "#10b981", "#ec4899", "#f97316", "#ef4444"]
MIN_CARD, MAX_CARD = 170, 290
MIN_POSTER, MAX_POSTER = 190, 330
VIEWS = ["Grade", "Lista", "Pôster", "Prateleiras"]
COVER_RATIO = 250 / 180
SIDE_OPEN, SIDE_CLOSED = 240, 76

DARK = dict(bg="#0c0c15", side="#08080f", surface="#12121c", surface2="#1c1c2b", border="#23233a",
            text="#eceaf7", muted="#8d8ba8", empty=(52, 52, 80, 255),
            status=dict(lendo="#4fd1a1", completo="#a78bfa", planejo="#8d8ba8",
                        pausado="#e0a94a", largado="#ff7b6b"))
LIGHT = dict(bg="#f3f3fa", side="#ffffff", surface="#ffffff", surface2="#e9eaf5", border="#dcdcee",
             text="#1b1d3a", muted="#666a90", empty=(205, 208, 230, 255),
             status=dict(lendo="#1f9e74", completo="#6d4bd8", planejo="#6b6f8d",
                         pausado="#b7791f", largado="#d13f3f"))

def _theme(base, **kw):
    t = dict(base)
    t.update(kw)
    return t


THEMES = {
    "Escuro": _theme(DARK, dark=True, accent="#8b5cf6"),
    "Preto total": _theme(DARK, dark=True, accent="#a78bfa", bg="#000000", side="#000000", surface="#0b0b0d",
                          surface2="#17171b", border="#26262c", text="#f4f4f6", muted="#8b8b96",
                          empty=(44, 44, 52, 255)),
    "Sakura": _theme(DARK, dark=True, accent="#ff7eb6", bg="#150d12", side="#0f080d", surface="#1e121a",
                     surface2="#2b1a25", border="#3d2535", text="#fbe9f1", muted="#c79bb2",
                     empty=(70, 44, 60, 255)),
    "Oceano": _theme(DARK, dark=True, accent="#38bdf8", bg="#08121c", side="#050d15", surface="#0e1b2a",
                     surface2="#16293d", border="#21394f", text="#e6f3ff", muted="#8fb0cc",
                     empty=(36, 58, 82, 255)),
    "Floresta": _theme(DARK, dark=True, accent="#34d399", bg="#0a130e", side="#070e0a", surface="#112019",
                       surface2="#1b3024", border="#274133", text="#e8f5ec", muted="#93b59f",
                       empty=(38, 62, 48, 255)),
    "Pôr do sol": _theme(DARK, dark=True, accent="#fb923c", bg="#150d0b", side="#0f0807", surface="#201311",
                         surface2="#33201b", border="#482b24", text="#fff0e8", muted="#d1a595",
                         empty=(76, 48, 40, 255)),
    "Papel": _theme(LIGHT, dark=False, accent="#b45309", bg="#f4efe6", side="#ebe4d6", surface="#fbf8f2",
                    surface2="#e9e1d0", border="#d9cfba", text="#2b2418", muted="#7a6e58",
                    empty=(214, 205, 186, 255)),
    "Claro": _theme(LIGHT, dark=False, accent="#7c3aed"),
}

# cores por tipo de obra (etiquetas, filtros e gráficos)
TYPE_COLORS = {"Mangá": "#ff6b81", "Manhwa": "#4dabf7", "Webtoon": "#51cf66", "Livro": "#ffa94d",
               "Outro": "#9aa0c0"}
LABEL_COLORS = ["#f87171", "#fb923c", "#fbbf24", "#4ade80", "#2dd4bf", "#60a5fa", "#a78bfa", "#f472b6",
                "#ef4444", "#f97316", "#eab308", "#22c55e", "#14b8a6", "#3b82f6", "#8b5cf6", "#ec4899",
                "#fca5a5", "#fdba74", "#fde047", "#86efac", "#99f6e4", "#93c5fd", "#c4b5fd", "#f9a8d4",
                "#a3e635", "#06b6d4", "#6366f1", "#d946ef", "#fb7185", "#a8a29e", "#94a3b8", "#e2e8f0",
                "#b45309", "#65a30d", "#0e7490", "#4338ca", "#9333ea", "#be123c", "#78716c", "#475569"]


def type_color(t):
    return TYPE_COLORS.get(t, TYPE_COLORS["Outro"])


S = {}   # configurações
P = {}   # paleta atual


def resource_path(name):
    """Acha arquivos ao lado do script (ou dentro do .exe criado pelo PyInstaller)."""
    base = getattr(sys, "_MEIPASS", None) or Path(__file__).resolve().parent
    return Path(base) / name


UI_SCALES = {"Automático": None, "80%": 0.8, "90%": 0.9, "100%": 1.0, "110%": 1.1, "125%": 1.25, "150%": 1.5}
UI = {"dpi": 1.0, "ws": 1.0}     # escala do Windows (dpi) e escala escolhida no app (ws)


def scale_k():
    return UI["dpi"] * UI["ws"]


def px(n):
    """Pixels 'lógicos' -> pixels reais (para canvas e tudo que fica fora do customtkinter)."""
    return max(1, int(round(n * scale_k())))


def lw(v):
    """Pixels reais (winfo_width, e.width) -> pixels lógicos usados nas decisões de layout."""
    return v / scale_k()


def fpt(n):
    return max(7, int(round(n * UI["ws"])))


def ss():
    """Fator de nitidez das imagens (gera maiores quando a tela tem escala alta)."""
    return max(1.0, min(2.0, scale_k()))


def detect_dpi(win):
    try:
        return max(1.0, float(ctk.ScalingTracker.get_window_scaling(win)))
    except Exception:
        pass
    try:
        return max(1.0, win.winfo_fpixels("1i") / 96.0)
    except Exception:
        return 1.0


def auto_ws(win, dpi):
    """Tamanho ideal da interface para a resolução da tela (em pixels lógicos)."""
    lh = win.winfo_screenheight() / dpi
    lwd = win.winfo_screenwidth() / dpi
    if lh < 800 or lwd < 1200:
        return 0.9
    if lh < 1100:
        return 1.0
    if lh < 1450:
        return 1.1
    return 1.25


# ---------- configurações e tema ----------
def hex_shade(h, f):
    h = h.lstrip("#")
    r, g, b = (int(h[i:i + 2], 16) for i in (0, 2, 4))
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(c * f))) for c in (r, g, b))


def mix(a, b, t):
    ca = [int(a.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4)]
    cb = [int(b.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4)]
    return "#%02x%02x%02x" % tuple(int(x + (y - x) * t) for x, y in zip(ca, cb))


def hex_rgba(h, a=255):
    h = h.lstrip("#")
    return (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16), a)


def load_settings():
    s = dict(data_dir=str(APP_DIR), theme="Escuro", accent=ACCENTS[0], view="Grade", goal=20, collapsed=False,
             stall_days=30, daily=5, sounds=True)
    try:
        s.update(json.loads(SETTINGS_FILE.read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass
    if s["accent"] == "#7c5cff":      # roxo da versão anterior
        s["accent"] = ACCENTS[0]
    s["theme"] = {"dark": "Escuro", "light": "Claro"}.get(s["theme"], s["theme"])
    return s


DATA = {"v": 0}          # versão dos dados: sobe a cada gravação (as telas guardadas se refazem sozinhas)
SCROLL = {"until": 0.0}  # enquanto a tela rola, os efeitos de passar o mouse ficam em espera


def touch():
    DATA["v"] += 1


def scrolling():
    return time.time() < SCROLL["until"]


def save_settings():
    APP_DIR.mkdir(exist_ok=True)
    SETTINGS_FILE.write_text(json.dumps(S, ensure_ascii=False, indent=2), encoding="utf-8")


def apply_palette():
    name = {"dark": "Escuro", "light": "Claro"}.get(S.get("theme", "Escuro"), S.get("theme", "Escuro"))
    if name not in THEMES:
        name = "Escuro"
    S["theme"] = name
    base = THEMES[name]
    P.clear()
    P.update(base)
    P["accent"] = S["accent"]
    P["accent_hover"] = hex_shade(S["accent"], 0.82)
    ctk.set_appearance_mode("dark" if base.get("dark", True) else "light")


# ---------- dados ----------
def data_dir():
    return Path(S["data_dir"])


def data_file():
    return data_dir() / "data.json"


def covers_dir():
    return data_dir() / "covers"


def profile_file():
    return data_dir() / "profile.json"


def profile_dir():
    return data_dir() / "profile"


def shots_dir():
    return data_dir() / "shots"


DEFAULTS = dict(url="", author="", year="", tags=[], favorite=False, notes="", started="",
                finished="", rereads=0, rating=0.0, seen=0, total=0, cover=None,
                crit=dict(story=0.0, art=0.0, chars=0.0), lists=[], vol_total=0, vol_owned=[],
                minutes=0, progressed=0, ongoing=False, quotes=[], history=[], labels=[], shots=[])


def fresh(v):
    return list(v) if isinstance(v, list) else dict(v) if isinstance(v, dict) else v


def load_items():
    try:
        items = json.loads(data_file().read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return []
    for it in items:
        for k, v in DEFAULTS.items():
            it.setdefault(k, fresh(v))
        it.setdefault("created", 0)
        it.setdefault("updated", it["created"])
        if not it["progressed"]:
            it["progressed"] = it["updated"]
    return items


def save_items(items):
    touch()
    data_dir().mkdir(parents=True, exist_ok=True)
    data_file().write_text(json.dumps(items, ensure_ascii=False, indent=2), encoding="utf-8")


def new_item(**kw):
    it = {k: fresh(v) for k, v in DEFAULTS.items()}
    now = time.time()
    it.update(id=uuid.uuid4().hex, created=now, updated=now, progressed=now,
              title="", type="Outro", status="planejo")
    it.update(kw)
    return it


# ---- prints (galeria): imagens salvas por obra ----
SHOT_MAX, SHOT_TH = 2600, 520
_SHT, _SHF = OrderedDict(), OrderedDict()


def shot_file(s):
    return shots_dir() / s["file"]


def shot_thumb_file(s):
    return shots_dir() / ("t_" + s["id"] + ".jpg")


def save_shot_image(img):
    """Grava a imagem e a miniatura na pasta de prints; devolve o registro do print."""
    shots_dir().mkdir(parents=True, exist_ok=True)
    try:
        img = ImageOps.exif_transpose(img)
    except Exception:
        pass
    alpha = img.mode in ("RGBA", "LA") or (img.mode == "P" and "transparency" in img.info)
    img = img.convert("RGBA" if alpha else "RGB")
    if max(img.size) > SHOT_MAX:
        img.thumbnail((SHOT_MAX, SHOT_MAX), Image.LANCZOS)
    sid = uuid.uuid4().hex[:12]
    s = dict(id=sid, file=f"{sid}.{'png' if alpha else 'jpg'}", ch=None, cap="", fav=False, ts=time.time(),
             w=img.width, h=img.height)
    if alpha:
        img.save(shot_file(s), "PNG")
    else:
        img.save(shot_file(s), "JPEG", quality=92)
    th = img.convert("RGB") if not alpha else Image.alpha_composite(Image.new("RGBA", img.size, (11, 11, 19, 255)), img).convert("RGB")
    th.thumbnail((SHOT_TH, SHOT_TH), Image.LANCZOS)
    th.save(shot_thumb_file(s), "JPEG", quality=86)
    return s


def add_shot(app, it, img, ch=None):
    s = save_shot_image(img)
    s["ch"] = it["seen"] if ch is None else ch
    it.setdefault("shots", []).append(s)
    app.commit(it["id"])
    return s


def shot_thumb(s):
    got = _SHT.get(s["id"])
    if got is not None:
        _SHT.move_to_end(s["id"])
        return got
    try:
        im = Image.open(shot_thumb_file(s)).convert("RGB")
    except OSError:
        try:
            im = Image.open(shot_file(s)).convert("RGB")
            im.thumbnail((SHOT_TH, SHOT_TH), Image.LANCZOS)
        except OSError:
            im = Image.new("RGB", (320, 220), (28, 26, 48))
    _SHT[s["id"]] = im
    while len(_SHT) > 120:
        _SHT.popitem(last=False)
    return im


def shot_full(s):
    got = _SHF.get(s["id"])
    if got is not None:
        _SHF.move_to_end(s["id"])
        return got
    try:
        im = Image.open(shot_file(s)).convert("RGB")
    except OSError:
        im = shot_thumb(s)
    _SHF[s["id"]] = im
    while len(_SHF) > 3:
        _SHF.popitem(last=False)
    return im


def shot_size(s):
    if not s.get("w") or not s.get("h"):
        t = shot_thumb(s)
        return t.width, t.height
    return s["w"], s["h"]


def del_shot_files(s):
    for f in (shot_file(s), shot_thumb_file(s)):
        try:
            f.unlink(missing_ok=True)
        except OSError:
            pass
    _SHT.pop(s["id"], None)
    _SHF.pop(s["id"], None)


def purge_shots(it):
    for s in it.get("shots", []):
        del_shot_files(s)


def clipboard_images():
    """Imagens que estão na área de transferência (print de tela ou arquivos copiados)."""
    try:
        from PIL import ImageGrab
        got = ImageGrab.grabclipboard()
    except Exception:
        return []
    if isinstance(got, Image.Image):
        return [got]
    out = []
    if isinstance(got, (list, tuple)):
        for f in got:
            try:
                if str(f).lower().endswith((".png", ".jpg", ".jpeg", ".webp", ".bmp", ".gif")):
                    im = Image.open(f)
                    im.load()
                    out.append(im)
            except (OSError, ValueError):
                pass
    return out


def shot_tile_pil(s, w, h, hot=False, label="", k=None):
    """Miniatura arredondada com etiqueta do capítulo (e estrela, se favorita)."""
    k = k or K
    W_, H_ = w * k, h * k
    im = ImageOps.fit(shot_thumb(s), (W_, H_), Image.LANCZOS).convert("RGBA")
    if hot:
        ov = Image.new("RGBA", im.size, (0, 0, 0, 0))
        od = ImageDraw.Draw(ov)
        y0 = int(H_ * .45)
        for y in range(y0, H_):
            od.line([(0, y), (W_, y)], fill=(6, 5, 16, int(215 * ((y - y0) / (H_ - y0)) ** 1.3)))
        im.alpha_composite(ov)
    d = ImageDraw.Draw(im)
    cap = f"cap. {s['ch']}" if s.get("ch") is not None else "sem cap."
    fnt = get_font(max(8, int(12 * k)), True)
    tw = d.textlength(cap, font=fnt)
    cy1 = H_ - 10 * k
    d.rounded_rectangle([10 * k, cy1 - 24 * k, 10 * k + tw + 20 * k, cy1], radius=12 * k, fill=(10, 8, 24, 235))
    try:
        d.text((20 * k, cy1 - 12 * k), cap, font=fnt, fill="#ffffff", anchor="lm")
    except (TypeError, ValueError):
        d.text((20 * k, cy1 - 22 * k), cap, font=fnt, fill="#ffffff")
    if hot:
        f2 = get_font(max(8, int(13 * k)), True)
        txt = (label or s.get("cap") or "")
        if label and s.get("cap"):
            txt = f"{label} — {s['cap']}"
        if txt:
            txt = _fit_text(d, txt, f2, W_ - 24 * k)
            try:
                d.text((12 * k, cy1 - 36 * k), txt, font=f2, fill="#ffffff", anchor="ls")
            except (TypeError, ValueError):
                d.text((12 * k, cy1 - 52 * k), txt, font=f2, fill="#ffffff")
    if s.get("fav"):
        r_ = 15 * k
        cx, cy = W_ - 10 * k - r_, 10 * k + r_
        d.ellipse([cx - r_, cy - r_, cx + r_, cy + r_], fill=(10, 8, 24, 235))
        st = star_pil(int(18 * k), 1, (0, 0, 0, 0))
        im.alpha_composite(st, (int(cx - st.width / 2), int(cy - st.height / 2)))
        d = ImageDraw.Draw(im)
    if hot:
        d.rounded_rectangle([0, 0, W_ - 1, H_ - 1], radius=14 * k, outline=P["accent"], width=3 * k)
    m = Image.new("L", (W_, H_), 0)
    ImageDraw.Draw(m).rounded_rectangle([0, 0, W_ - 1, H_ - 1], radius=14 * k, fill=255)
    out = Image.new("RGBA", (W_, H_), (0, 0, 0, 0))
    out.paste(im, (0, 0), m)
    return out


# ---- histórico de leitura (capítulos e minutos por dia) ----
def activity_file():
    return data_dir() / "activity.json"


def load_activity():
    try:
        a = json.loads(activity_file().read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return a if isinstance(a, dict) else {}


def save_activity(a):
    touch()
    data_dir().mkdir(parents=True, exist_ok=True)
    activity_file().write_text(json.dumps(a, ensure_ascii=False), encoding="utf-8")


def log_activity(a, ch=0, minutes=0, day=None, hour=None):
    e = a.setdefault((day or date.today()).isoformat(), {"ch": 0, "min": 0})
    e["ch"] = e.get("ch", 0) + ch
    e["min"] = e.get("min", 0) + minutes
    h = hour if hour is not None else (datetime.now().hour if day is None else 12)
    if ch > 0 and 0 <= h < 5:                 # leitura de madrugada
        e["night"] = e.get("night", 0) + ch
    if ch > 0 and 5 <= h < 9:                 # leitura de manhã cedo
        e["morning"] = e.get("morning", 0) + ch


def active_days(a):
    out = set()
    for k, v in a.items():
        try:
            if v.get("ch", 0) > 0 or v.get("min", 0) > 0:
                out.add(date.fromisoformat(k))
        except (ValueError, AttributeError):
            pass
    return out


def streaks(a):
    """(sequência atual, maior sequência) de dias seguidos com leitura."""
    days = active_days(a)
    longest = run = 0
    prev = None
    for d in sorted(days):
        run = run + 1 if prev and (d - prev).days == 1 else 1
        longest = max(longest, run)
        prev = d
    d = date.today()
    if d not in days:
        d -= timedelta(days=1)
    cur = 0
    while d in days:
        cur += 1
        d -= timedelta(days=1)
    return cur, longest


def sum_activity(a, prefix="", key="ch"):
    return sum(v.get(key, 0) for k, v in a.items() if k.startswith(prefix))


def fmt_minutes(m):
    m = int(m)
    return f"{m // 60}h {m % 60:02d}m" if m >= 60 else f"{m}m"


def stalled_days(it):
    """Dias sem avançar numa leitura 'Lendo' (0 se não está parada)."""
    if it["status"] != "lendo":
        return 0
    if it.get("ongoing") and it["total"] and it["seen"] >= it["total"]:
        return 0          # em dia com os lançamentos: não está parada, só esperando capítulo novo
    ts = it.get("progressed") or it.get("updated") or it.get("created") or time.time()
    d = int((time.time() - ts) / 86400)
    return d if d >= S.get("stall_days", 30) else 0


def parse_ranges(text):
    """'1-5, 7, 9' -> [1, 2, 3, 4, 5, 7, 9]"""
    out = set()
    for part in str(text).replace(";", ",").split(","):
        part = part.strip()
        if not part:
            continue
        try:
            if "-" in part:
                a, b = (int(x) for x in part.split("-", 1))
                out.update(range(min(a, b), min(max(a, b), 2000) + 1))
            else:
                out.add(int(part))
        except ValueError:
            continue
    return sorted(n for n in out if 0 < n <= 2000)


def format_ranges(nums):
    nums = sorted(set(nums))
    out, i = [], 0
    while i < len(nums):
        j = i
        while j + 1 < len(nums) and nums[j + 1] == nums[j] + 1:
            j += 1
        out.append(str(nums[i]) if i == j else f"{nums[i]}-{nums[j]}")
        i = j + 1
    return ", ".join(out)


# ---- CSV ----
CSV_COLS = ["titulo", "tipo", "status", "capitulo_atual", "total", "nota", "autor", "ano", "generos", "link",
            "inicio", "fim", "favorito", "releituras", "listas", "volumes_total", "volumes", "anotacoes",
            "em_lancamento", "etiquetas"]


def export_csv(items, path):
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(CSV_COLS)
        for i in items:
            w.writerow([i["title"], i["type"], STATUS[i["status"]], i["seen"], i["total"],
                        f"{i['rating']:g}".replace(".", ","), i["author"], i["year"], "; ".join(i["tags"]),
                        i["url"], i["started"], i["finished"], "sim" if i["favorite"] else "", i["rereads"],
                        "; ".join(i["lists"]), i["vol_total"], format_ranges(i["vol_owned"]), i["notes"],
                        "sim" if i.get("ongoing") else "", "; ".join(i.get("labels", []))])


def _norm(s):
    s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().lower().strip()
    return s.replace(" ", "_").replace("-", "_")


CSV_ALIASES = {_norm(k): v for k, v in {
    "titulo": "titulo", "title": "titulo", "nome": "titulo", "name": "titulo", "series_title": "titulo",
    "tipo": "tipo", "type": "tipo", "media_type": "tipo",
    "status": "status", "my_status": "status", "estado": "status", "exclusive shelf": "status",
    "capitulo_atual": "capitulo_atual", "capitulo": "capitulo_atual", "progress": "capitulo_atual",
    "progresso": "capitulo_atual", "chapters read": "capitulo_atual", "my read chapters": "capitulo_atual",
    "total": "total", "chapters": "total", "capitulos": "total", "total chapters": "total",
    "nota": "nota", "score": "nota", "rating": "nota", "my score": "nota", "my rating": "nota",
    "autor": "autor", "author": "autor", "ano": "ano", "year": "ano",
    "generos": "generos", "genres": "generos", "tags": "generos", "link": "link", "url": "link",
    "inicio": "inicio", "start date": "inicio", "started": "inicio", "my start date": "inicio",
    "fim": "fim", "end date": "fim", "finished": "fim", "my finish date": "fim",
    "favorito": "favorito", "favorite": "favorito", "releituras": "releituras", "rereads": "releituras",
    "listas": "listas", "lists": "listas", "volumes_total": "volumes_total", "volumes": "volumes",
    "anotacoes": "anotacoes", "notes": "anotacoes", "review": "anotacoes",
    "em_lancamento": "em_lancamento", "ongoing": "em_lancamento", "publishing": "em_lancamento",
    "etiquetas": "etiquetas", "labels": "etiquetas"}.items()}

STATUS_ALIASES = {_norm(k): v for k, v in {
    "lendo": "lendo", "reading": "lendo", "currently reading": "lendo", "em andamento": "lendo",
    "completo": "completo", "completa": "completo", "completed": "completo", "complete": "completo",
    "lido": "completo", "read": "completo", "finalizado": "completo",
    "quero ler": "planejo", "planejo": "planejo", "plan to read": "planejo", "to read": "planejo",
    "to-read": "planejo", "want to read": "planejo",
    "pausado": "pausado", "on hold": "pausado", "paused": "pausado",
    "largado": "largado", "dropped": "largado", "abandonado": "largado"}.items()}

TYPE_ALIASES = {"manga": "Mangá", "manhwa": "Manhwa", "webtoon": "Webtoon", "livro": "Livro",
                "book": "Livro", "novel": "Livro", "light_novel": "Livro"}


def _num(s, default=0.0):
    try:
        return float(str(s).strip().replace(",", "."))
    except ValueError:
        return default


def _date(s):
    s = str(s or "").strip()
    for fmt in ("%d/%m/%Y", "%Y-%m-%d", "%d-%m-%Y"):
        try:
            return datetime.strptime(s, fmt).strftime("%d/%m/%Y")
        except ValueError:
            continue
    return ""


def import_csv(path):
    """Lê um CSV (português ou inglês) e devolve a lista de leituras novas."""
    raw = Path(path).read_bytes().decode("utf-8-sig", errors="replace")
    try:
        dialect = csv.Sniffer().sniff(raw[:4096], delimiters=";,\t")
    except csv.Error:
        dialect = csv.excel
    out = []
    for row in csv.DictReader(io.StringIO(raw), dialect=dialect):
        r = {}
        for k, v in row.items():
            key = CSV_ALIASES.get(_norm(k))
            if key and key not in r:
                r[key] = (v or "").strip() if isinstance(v, str) else ""
        title = r.get("titulo", "")
        if not title:
            continue
        score = _num(r.get("nota"))
        score = max(0.0, min(5.0, round((score / 2 if score > 5 else score) * 2) / 2))
        out.append(new_item(
            title=title, type=TYPE_ALIASES.get(_norm(r.get("tipo")), "Outro"),
            status=STATUS_ALIASES.get(_norm(r.get("status")), "planejo"),
            seen=int(_num(r.get("capitulo_atual"))), total=int(_num(r.get("total"))), rating=score,
            author=r.get("autor", ""), year=r.get("ano", ""),
            tags=[t.strip() for t in re.split(r"[;|,]", r.get("generos", "")) if t.strip()],
            url=r.get("link", ""), started=_date(r.get("inicio")), finished=_date(r.get("fim")),
            favorite=_norm(r.get("favorito")) in ("sim", "s", "1", "true", "yes", "x"),
            rereads=int(_num(r.get("releituras"))),
            lists=[t.strip() for t in re.split(r"[;|,]", r.get("listas", "")) if t.strip()],
            vol_total=int(_num(r.get("volumes_total"))), vol_owned=parse_ranges(r.get("volumes", "")),
            notes=r.get("anotacoes", ""),
            ongoing=_norm(r.get("em_lancamento")) in ("sim", "s", "1", "true", "yes", "x", "ongoing"),
            labels=[t.strip() for t in re.split(r"[;|,]", r.get("etiquetas", "")) if t.strip()]))
    return out


# ---- histórico (diário) de cada obra ----
EVENT_STYLE = {
    "add": ("Adicionada à biblioteca", "#9296c0"), "start": ("Começou a ler", "#4fd1a1"),
    "resume": ("Retomou a leitura", "#4fd1a1"), "pause": ("Pausou a leitura", "#e0a94a"),
    "drop": ("Largou a leitura", "#ff7b6b"), "done": ("Terminou a leitura", "#a78bfa"),
    "reread": ("Releitura", "#c084fc"), "rate": ("Nota", "#ffc233"),
    "ongoing": ("Em lançamento", "#2dd4bf"), "note": ("Diário", "#60a5fa"),
}


# ---- sons suaves (gerados aqui mesmo, sem arquivos de áudio) ----
_SND = {}
SOUND_NOTES = {"done": [(523.25, 0.00), (659.25, 0.11), (783.99, 0.22)],
               "badge": [(783.99, 0.00), (987.77, 0.10), (1174.66, 0.20), (1567.98, 0.32)]}


def _tone_wav(kind):
    rate = 22050
    notes = SOUND_NOTES[kind]
    dur = notes[-1][1] + 0.9
    buf = array.array("h", [0] * int(rate * dur))
    for f, t0 in notes:
        n0 = int(t0 * rate)
        for k in range(int(rate * 0.8)):
            t = k / rate
            env = min(1.0, k / (rate * 0.008)) * math.exp(-t * 5.5)
            v = (math.sin(2 * math.pi * f * t) + 0.25 * math.sin(2 * math.pi * f * 2 * t)) * env
            i = n0 + k
            if i < len(buf):
                buf[i] = max(-32000, min(32000, buf[i] + int(v * 4200)))
    bio = io.BytesIO()
    with wave.open(bio, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(buf.tobytes())
    return bio.getvalue()


def play_sound(kind):
    """Toque curto e suave (só no Windows; nos outros sistemas fica em silêncio)."""
    if not S.get("sounds", True):
        return

    def run():
        try:
            import winsound
            if kind not in _SND:
                _SND[kind] = _tone_wav(kind)
            winsound.PlaySound(_SND[kind], winsound.SND_MEMORY | winsound.SND_ASYNC)
        except Exception:
            pass
    threading.Thread(target=run, daemon=True).start()


def add_event(it, kind, text=""):
    it.setdefault("history", []).append({"ts": time.time(), "kind": kind, "text": text})
    del it["history"][:-500]
    if kind == "done":
        play_sound("done")


def status_event(old, new):
    """Qual evento do histórico corresponde a uma troca de status (ou None)."""
    if new == old:
        return None
    if new == "lendo":
        return "resume" if old in ("pausado", "largado") else "start"
    return {"completo": "done", "pausado": "pause", "largado": "drop"}.get(new)


def label_color(app, name):
    """Cor da etiqueta (atribui uma da paleta se ainda não tiver)."""
    d = app.profile.setdefault("labels", {})
    if name not in d:
        d[name] = LABEL_COLORS[len(d) % len(LABEL_COLORS)]
        save_profile(app.profile)
    return d[name]


def load_profile():
    p = dict(name="Leitor", handle="@leitor", bio="Clique em “Editar perfil” para contar quem você é.",
             avatar="", banner="")
    try:
        p.update(json.loads(profile_file().read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass
    return p


def save_profile(p):
    touch()
    data_dir().mkdir(parents=True, exist_ok=True)
    profile_file().write_text(json.dumps(p, ensure_ascii=False, indent=2), encoding="utf-8")


def parse_date(s):
    try:
        return datetime.strptime(s.strip(), "%d/%m/%Y").date()
    except (ValueError, AttributeError):
        return None


def open_url(u):
    u = (u or "").strip()
    if u:
        webbrowser.open(u if "://" in u else "https://" + u)


def backup_members():
    out = [(f, n) for f, n in ((data_file(), "data.json"), (profile_file(), "profile.json"),
                               (activity_file(), "activity.json")) if f.exists()]
    for d, pre in ((covers_dir(), "covers"), (profile_dir(), "profile"), (shots_dir(), "shots")):
        if d.exists():
            out += [(p, f"{pre}/{p.name}") for p in d.iterdir() if p.is_file()]
    return out


def make_backup(zip_path):
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as z:
        for src, name in backup_members():
            z.write(src, name)


# ---------- imagens ----------
def star_pil(size, fill, empty):
    """Estrela suave; fill = 0, 0.5 ou 1 (parte preenchida, da esquerda p/ direita)."""
    s = size * 4
    pts = []
    for i in range(10):
        r = s / 2 - 2 if i % 2 == 0 else (s / 2 - 2) * 0.45
        a = -math.pi / 2 + i * math.pi / 5
        pts.append((s / 2 + r * math.cos(a), s / 2 + r * math.sin(a)))
    mask = Image.new("L", (s, s), 0)
    ImageDraw.Draw(mask).polygon(pts, fill=255)
    base = Image.new("RGBA", (s, s), empty)
    if fill > 0:
        base.paste(Image.new("RGBA", (int(s * fill), s), GOLD), (0, 0))
    out = Image.new("RGBA", (s, s), (0, 0, 0, 0))
    out.paste(base, (0, 0), mask)
    return out.resize((size, size), Image.LANCZOS)


_star_cache = {}


def star_images(size):
    key = (size, P["empty"])
    if key not in _star_cache:
        _star_cache[key] = [ImageTk.PhotoImage(star_pil(size, f, P["empty"])) for f in (0, 0.5, 1)]
    return _star_cache[key]


def placeholder(title):
    h = (sum(ord(c) * (i + 1) for i, c in enumerate(title)) % 360) / 360
    c1 = tuple(int(x * 255) for x in colorsys.hls_to_rgb(h, 0.42, 0.55))
    c2 = tuple(int(x * 255) for x in colorsys.hls_to_rgb((h + 0.12) % 1, 0.2, 0.55))
    img = Image.new("RGB", (360, 500))
    d = ImageDraw.Draw(img)
    for y in range(500):
        t = y / 499
        d.line([(0, y), (360, y)], fill=tuple(int(a + (b - a) * t) for a, b in zip(c1, c2)))
    ini = "".join(w[0] for w in title.split()[:2]).upper()
    try:
        try:
            font = ImageFont.load_default(size=120)
        except TypeError:
            font = ImageFont.load_default()
        d.text((180, 250), ini, fill="white", font=font, anchor="mm")
    except Exception:
        pass
    return img


def dominant_color(img):
    """Cor mais marcante da capa (ajustada para não ficar escura/apagada demais)."""
    try:
        q = img.convert("RGB").resize((48, 48)).quantize(colors=6)
        pal = q.getpalette()[:18]
        best, score = None, -1.0
        for cnt, idx in q.getcolors():
            r, g, b = pal[idx * 3: idx * 3 + 3]
            h, l, sat = colorsys.rgb_to_hls(r / 255, g / 255, b / 255)
            sc = cnt * (0.25 + sat) * (1 - abs(l - 0.5))
            if sc > score:
                best, score = (r, g, b), sc
        h, l, sat = colorsys.rgb_to_hls(*(c / 255 for c in best))
        r, g, b = colorsys.hls_to_rgb(h, min(0.64, max(0.46, l)), max(sat, 0.42))
        return "#%02x%02x%02x" % (int(r * 255), int(g * 255), int(b * 255))
    except Exception:
        return "#8b5cf6"


HERO_H = 130
DETAIL_HERO = 64


def hero_pil(img, w, h, color, bg):
    """Faixa do topo da tela de detalhes: a capa desfocada, com a cor dela, dissolvendo no fundo."""
    base = ImageOps.fit(img.convert("RGB"), (w, h), centering=(0.5, 0.3))
    base = base.filter(ImageFilter.GaussianBlur(radius=max(8, w // 70)))
    base = Image.blend(base, Image.new("RGB", (w, h), color), .40)
    base = Image.blend(base, Image.new("RGB", (w, h), bg), .30)
    mask = Image.new("L", (1, h))
    for y in range(h):
        t = (y - 0.30 * h) / (0.70 * h)
        mask.putpixel((0, y), int(255 * max(0, min(1, t))))
    return Image.composite(Image.new("RGB", (w, h), bg), base, mask.resize((w, h)))


def backdrop_pil(img, W, H, color, bg, x0, x1, hh, off=0):
    """Fundo da tela de detalhes: a capa desfocada ocupando a largura toda, dissolvendo no fundo.
    Dentro da coluna (x0..x1) some em `hh` px (a faixa do topo); nas laterais desce devagar até o fim."""
    small = ImageOps.fit(img.convert("RGB"), (max(8, W // 8), max(8, H // 8)), centering=(0.5, 0.3))
    small = small.filter(ImageFilter.GaussianBlur(radius=max(2, W // 700)))
    base = small.resize((W, H), Image.BICUBIC)
    base = Image.blend(base, Image.new("RGB", (W, H), color), .40)
    base = Image.blend(base, Image.new("RGB", (W, H), bg), .30)
    side = Image.new("L", (1, H))
    col = Image.new("L", (1, H))
    for y in range(H):
        t = y / max(1, H - 1)
        side.putpixel((0, y), int(255 * min(1.0, 0.10 + 0.62 * t)))
        c = (y - off - 0.30 * hh) / (0.70 * hh)
        col.putpixel((0, y), int(255 * max(0.0, min(1.0, c))))
    # nas laterais o fundo ganha força aos poucos, a partir da borda da coluna (sem corte seco)
    x0, x1 = max(0, x0), min(W, x1)
    wm = Image.new("L", (W, 1))
    for x in range(W):
        if x < x0:
            d = (x0 - x) / max(1, x0)
        elif x >= x1:
            d = (x - x1) / max(1, W - x1)
        else:
            d = 0.0
        d = max(0.0, min(1.0, d))
        d = d ** 0.8
        wm.putpixel((x, 0), int(255 * d * d * (3 - 2 * d)))
    mask = Image.composite(side.resize((W, H)), col.resize((W, H)), wm.resize((W, H)))
    return Image.composite(Image.new("RGB", (W, H), bg), base, mask)


_icon_cache = {}


def icon_pil(name, size=20, color=None):
    """Ícone de linha desenhado com Pillow (4x maior, para ficar nítido)."""
    color = color or P["muted"]
    s = size * 4
    im = Image.new("RGBA", (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    w = max(3, int(s * 0.085))

    def line(pts, close=False):
        pts = [(x * s, y * s) for x, y in pts]
        d.line(pts + ([pts[0]] if close else []), fill=color, width=w, joint="curve")

    def box(a, b, c, e):
        d.rounded_rectangle([a * s, b * s, c * s, e * s], radius=w, outline=color, width=w)

    if name == "user":
        d.ellipse([.32 * s, .1 * s, .68 * s, .46 * s], outline=color, width=w)
        d.arc([.14 * s, .56 * s, .86 * s, 1.22 * s], 180, 360, fill=color, width=w)
    elif name == "image":
        box(.1, .18, .9, .82)
        d.ellipse([.27 * s, .31 * s, .41 * s, .45 * s], outline=color, width=w)
        line([(.14, .76), (.40, .52), (.58, .68), (.72, .54), (.88, .72)])
    elif name in ("library", "book"):
        box(.12, .18, .34, .84)
        box(.40, .18, .62, .84)
        line([(.69, .26), (.87, .2), (.98, .76), (.80, .82)], close=True)
    elif name == "home":
        line([(.08, .50), (.5, .12), (.92, .50)])
        line([(.2, .42), (.2, .88), (.8, .88), (.8, .42)])
        line([(.42, .88), (.42, .62), (.58, .62), (.58, .88)])
    elif name == "chart":
        box(.12, .56, .32, .86)
        box(.40, .34, .60, .86)
        box(.68, .14, .88, .86)
    elif name == "gear":
        c = s / 2
        d.ellipse([c - .27 * s, c - .27 * s, c + .27 * s, c + .27 * s], outline=color, width=w)
        d.ellipse([c - .1 * s, c - .1 * s, c + .1 * s, c + .1 * s], outline=color, width=w)
        for k in range(8):
            a = k * math.pi / 4
            d.line([(c + .31 * s * math.cos(a), c + .31 * s * math.sin(a)),
                    (c + .44 * s * math.cos(a), c + .44 * s * math.sin(a))], fill=color, width=int(w * 1.7))
    elif name == "collapse":
        line([(.52, .2), (.27, .5), (.52, .8)])
        line([(.84, .2), (.59, .5), (.84, .8)])
    elif name == "expand":
        line([(.16, .2), (.41, .5), (.16, .8)])
        line([(.48, .2), (.73, .5), (.48, .8)])
    elif name == "check":
        line([(.16, .52), (.40, .76), (.84, .26)])
    elif name == "flag":
        line([(.2, .1), (.2, .92)])
        line([(.2, .14), (.82, .14), (.62, .36), (.82, .58), (.2, .58)])
    elif name == "clock":
        d.ellipse([.1 * s, .1 * s, .9 * s, .9 * s], outline=color, width=w)
        line([(.5, .28), (.5, .5), (.68, .6)])
    elif name == "play":
        line([(.28, .16), (.82, .5), (.28, .84)], close=True)
    elif name == "chevron":
        line([(.25, .38), (.5, .64), (.75, .38)])
    elif name == "star":
        pts = []
        for i in range(10):
            r = .46 if i % 2 == 0 else .2
            a = -math.pi / 2 + i * math.pi / 5
            pts.append((.5 + r * math.cos(a), .55 + r * math.sin(a)))
        line(pts, close=True)
    elif name == "heart":
        pts = []
        for k in range(63):
            t = k * 0.1
            x = 16 * math.sin(t) ** 3
            y = 13 * math.cos(t) - 5 * math.cos(2 * t) - 2 * math.cos(3 * t) - math.cos(4 * t)
            pts.append((.5 + x / 36, .44 - y / 36))
        line(pts, close=True)
    elif name == "list":
        for yy in (.25, .5, .75):
            d.ellipse([.08 * s, (yy - .05) * s, .18 * s, (yy + .05) * s], fill=color)
            line([(.32, yy), (.92, yy)])
    elif name == "back":
        line([(.62, .2), (.32, .5), (.62, .8)])
    elif name == "search":
        d.ellipse([.14 * s, .14 * s, .64 * s, .64 * s], outline=color, width=w)
        line([(.58, .58), (.86, .86)])
    elif name == "heart_fill":
        pts = []
        for k in range(63):
            t = k * 0.1
            x = 16 * math.sin(t) ** 3
            y = 13 * math.cos(t) - 5 * math.cos(2 * t) - 2 * math.cos(3 * t) - math.cos(4 * t)
            pts.append(((.5 + x / 36) * s, (.44 - y / 36) * s))
        d.polygon(pts, fill=color)
    elif name == "plus":
        line([(.5, .2), (.5, .8)])
        line([(.2, .5), (.8, .5)])
    elif name == "edit":
        line([(.2, .82), (.26, .6), (.68, .18), (.82, .32), (.4, .74), (.2, .82)])
        line([(.58, .28), (.72, .42)])
    elif name == "share":
        for cx, cy in ((.76, .22), (.24, .5), (.76, .78)):
            d.ellipse([(cx - .11) * s, (cy - .11) * s, (cx + .11) * s, (cy + .11) * s], outline=color, width=w)
        line([(.34, .45), (.66, .27)])
        line([(.34, .55), (.66, .73)])
    elif name == "close":
        line([(.26, .26), (.74, .74)])
        line([(.74, .26), (.26, .74)])
    elif name == "lock":
        box(.24, .46, .76, .86)
        d.arc([.32 * s, .12 * s, .68 * s, .62 * s], 180, 360, fill=color, width=w)
    elif name == "forward":
        line([(.38, .2), (.68, .5), (.38, .8)])
    elif name == "dot":
        d.ellipse([.24 * s, .24 * s, .76 * s, .76 * s], fill=color)
    elif name == "moon":
        m = Image.new("L", (s, s), 0)
        md = ImageDraw.Draw(m)
        md.ellipse([.14 * s, .12 * s, .86 * s, .84 * s], fill=255)
        md.ellipse([.34 * s, .0 * s, .98 * s, .64 * s], fill=0)
        im.paste(Image.new("RGBA", (s, s), color), (0, 0), m)
    elif name == "sun":
        d.ellipse([.31 * s, .31 * s, .69 * s, .69 * s], outline=color, width=w)
        for k in range(8):
            a = k * math.pi / 4
            line([(.5 + .27 * math.cos(a), .5 + .27 * math.sin(a)), (.5 + .42 * math.cos(a), .5 + .42 * math.sin(a))])
    elif name == "flame":
        line([(.5, .06), (.74, .38), (.82, .62), (.7, .86), (.5, .94), (.3, .86), (.18, .62), (.28, .42), (.42, .52)],
             close=True)
    elif name == "trophy":
        line([(.24, .12), (.76, .12), (.7, .46), (.5, .6), (.3, .46)], close=True)
        line([(.5, .6), (.5, .8)])
        line([(.32, .88), (.68, .88)])
        d.arc([.06 * s, .16 * s, .32 * s, .42 * s], 90, 270, fill=color, width=w)
        d.arc([.68 * s, .16 * s, .94 * s, .42 * s], 270, 450, fill=color, width=w)
    elif name == "quote":
        for ox in (.10, .52):
            d.ellipse([ox * s, .22 * s, (ox + .36) * s, .58 * s], fill=color)
            d.polygon([(ox * s, .40 * s), ((ox + .20) * s, .50 * s), ((ox - .02) * s, .80 * s)], fill=color)
    elif name == "crown":
        line([(.1, .8), (.1, .3), (.3, .52), (.5, .18), (.7, .52), (.9, .3), (.9, .8)], close=True)
    elif name == "tag":
        line([(.12, .12), (.52, .12), (.9, .5), (.52, .9), (.12, .5)], close=True)
        d.ellipse([.24 * s, .24 * s, .36 * s, .36 * s], fill=color)
    elif name == "gem":
        line([(.28, .18), (.72, .18), (.92, .42), (.5, .88), (.08, .42)], close=True)
        line([(.08, .42), (.92, .42)])
        line([(.38, .42), (.5, .88), (.62, .42)])
    elif name == "target":
        d.ellipse([.1 * s, .1 * s, .9 * s, .9 * s], outline=color, width=w)
        d.ellipse([.3 * s, .3 * s, .7 * s, .7 * s], outline=color, width=w)
        d.ellipse([.44 * s, .44 * s, .56 * s, .56 * s], fill=color)
    return im


def icon(name, size=20, color=None):
    color = color or P["muted"]
    key = (name, size, color)
    if key not in _icon_cache:
        _icon_cache[key] = ctk.CTkImage(icon_pil(name, int(size * ss()), color), size=(size, size))
    return _icon_cache[key]


def avatar_pil(path, name, size, bg, ring=None):
    s = size * 3
    im = None
    try:
        if path and Path(path).exists():
            im = ImageOps.fit(Image.open(path).convert("RGB"), (s, s))
    except OSError:
        im = None
    if im is None:
        im = ImageOps.fit(placeholder(name or "?"), (s, s))
    rw = int(s * 0.05) if ring else 0
    mask = Image.new("L", (s, s), 0)
    ImageDraw.Draw(mask).ellipse([rw, rw, s - rw - 1, s - rw - 1], fill=255)
    out = Image.new("RGB", (s, s), bg)
    if ring:
        ImageDraw.Draw(out).ellipse([0, 0, s - 1, s - 1], fill=ring)
    out.paste(im, (0, 0), mask)
    return out.resize((size, size), Image.LANCZOS)


def avatar_img(path, name, size, bg, ring=None):
    return ctk.CTkImage(avatar_pil(path, name, int(size * ss()), bg, ring), size=(size, size))


def banner_pil(path, w, h, bg, accent, fade=(0.18, 0.42)):
    """Banner que se dissolve na cor de fundo na parte de baixo."""
    w = max(300, int(w))
    base = None
    try:
        if path and Path(path).exists():
            base = ImageOps.fit(Image.open(path).convert("RGB"), (w, h))
    except OSError:
        base = None
    if base is None:
        c1, c2 = hex_shade(accent, 0.95), hex_shade(accent, 0.22)
        base = Image.new("RGB", (w, h))
        d = ImageDraw.Draw(base)
        for x in range(0, w, 2):
            d.line([(x, 0), (x, h)], fill=mix(c1, c2, x / w), width=2)
    mask = Image.new("L", (1, h))
    for y in range(h):
        t = (y - fade[0] * h) / (fade[1] * h)
        mask.putpixel((0, y), int(255 * max(0, min(1, t))))
    mask = mask.resize((w, h))
    return Image.composite(Image.new("RGB", (w, h), bg), base, mask)


def banner_img(path, w, h, bg, accent):
    w = max(300, int(w))
    img = banner_pil(path, int(w * ss()), int(h * ss()), bg, accent)
    return ctk.CTkImage(img, size=(w, h))


TIER_COLOR = {"bronze": "#cd7f32", "prata": "#c3cad9", "ouro": "#ffc233"}


_BADGE_CACHE = {}


def badge_pil(ic, tier, earned, size=56, prog=None):
    """Medalha: anel com degradê da cor do nível (ouro tem borda recortada), miolo escuro, brilho e, se ainda
    não foi conquistada, um arco de progresso."""
    key = (ic, tier, earned, size, None if prog is None else round(prog, 2), P["surface"], P["accent"])
    got = _BADGE_CACHE.get(key)
    if got is not None:
        return got
    s = size * 4
    base = TIER_COLOR[tier]
    if earned:
        light, dark, glyph_c = mix(base, "#ffffff", .5), mix(base, "#000000", .38), mix(base, "#ffffff", .5)
        core = mix(base, "#000000", .80)
    else:
        light, dark = mix(P["muted"], P["surface"], .5), mix(P["muted"], P["surface"], .8)
        glyph_c, core = mix(P["muted"], P["surface"], .35), P["surface2"]
    cx = cy = s / 2
    R = s / 2 - s * 0.05
    mask = Image.new("L", (s, s), 0)
    md = ImageDraw.Draw(mask)
    if tier == "ouro" and earned:
        pts = []
        for k in range(180):
            a_ = k * 2 * math.pi / 180
            r = R * (0.955 + 0.045 * math.cos(14 * a_))
            pts.append((cx + r * math.cos(a_), cy + r * math.sin(a_)))
        md.polygon(pts, fill=255)
    else:
        md.ellipse([cx - R, cy - R, cx + R, cy + R], fill=255)
    grad = ImageOps.flip(Image.linear_gradient("L").resize((s, s)))
    ring = ImageOps.colorize(grad, dark, light).convert("RGBA")
    im = Image.new("RGBA", (s, s), (0, 0, 0, 0))
    im.paste(ring, (0, 0), mask)
    d = ImageDraw.Draw(im)
    r2 = R * 0.80
    d.ellipse([cx - r2, cy - r2, cx + r2, cy + r2], fill=core)
    d.ellipse([cx - r2, cy - r2, cx + r2, cy + r2], outline=mix(light, dark, .45), width=max(2, int(s * 0.012)))
    if earned:
        hl = Image.new("RGBA", (s, s), (0, 0, 0, 0))                       # luz suave no alto do miolo
        ImageDraw.Draw(hl).ellipse([cx - r2 * .78, cy - r2 * .98, cx + r2 * .78, cy - r2 * .05],
                                   fill=(255, 255, 255, 38))
        hlm = Image.new("L", (s, s), 0)
        ImageDraw.Draw(hlm).ellipse([cx - r2, cy - r2, cx + r2, cy + r2], fill=255)
        hl = hl.filter(ImageFilter.GaussianBlur(s * 0.045))
        hl.putalpha(ImageChops.multiply(hl.getchannel("A"), hlm))
        im.alpha_composite(hl)
        glow = Image.new("RGBA", (s, s), (0, 0, 0, 0))
        gd = ImageDraw.Draw(glow)
        gd.ellipse([cx - r2 * .9, cy - r2 * .9, cx + r2 * .9, cy + r2 * .9], fill=hex_rgba(base, 46))
        im.alpha_composite(glow.filter(ImageFilter.GaussianBlur(s * 0.05)))
        d = ImageDraw.Draw(im)
        d.arc([cx - R * .92, cy - R * .92, cx + R * .92, cy + R * .92], 200, 290, fill=(255, 255, 255, 120),
              width=max(3, int(s * 0.03)))
    if prog is not None and not earned and prog > 0:
        d.arc([cx - R * .90, cy - R * .90, cx + R * .90, cy + R * .90], -90, -90 + 360 * min(1.0, prog),
              fill=P["accent"], width=max(4, int(s * 0.065)))
    g = int(size * 0.46)
    glyph = icon_pil(ic, g, "#ffffff")
    gw = glyph.size[0]
    alpha = glyph.getchannel("A").filter(ImageFilter.MaxFilter(3))          # traço um pouco mais grosso
    off = (s - gw) // 2
    shadow = Image.new("RGBA", (gw, gw), (0, 0, 0, 0))
    shadow.paste((0, 0, 0, 150), (0, 0), alpha)
    shadow = shadow.filter(ImageFilter.GaussianBlur(max(2, s * 0.012)))
    im.alpha_composite(shadow, (off, off + int(s * 0.014)))
    gl = ImageOps.colorize(ImageOps.flip(Image.linear_gradient("L").resize((gw, gw))),
                           mix(glyph_c, "#000000", .22), mix(glyph_c, "#ffffff", .55)).convert("RGBA")
    gl.putalpha(alpha)
    im.alpha_composite(gl, (off, off))
    out = im.resize((size, size), Image.LANCZOS)
    if len(_BADGE_CACHE) > 400:
        _BADGE_CACHE.clear()
    _BADGE_CACHE[key] = out
    return out


def medal_frames(ic, tier, earned, size, prog=None, n=12):
    """Animação ao passar o mouse: a medalha dá um pulinho, balança um pouco e recebe um brilho que a atravessa."""
    R = size
    base = badge_pil(ic, tier, earned, R * 2, prog)
    C = int(R * 1.5)
    alpha = base.getchannel("A")
    frames = []
    for f in range(n):
        t = f / (n - 1)
        sc = 1 + 0.12 * min(1.0, t * 3) + 0.10 * math.sin(math.pi * min(1.0, t * 1.6))
        ang = 9 * math.sin(2 * math.pi * t * 1.5) * (1 - t)
        fr = base.copy()
        if earned:
            pos = (-0.25 + 1.5 * t) * R * 4
            band = Image.new("L", base.size, 0)
            bd = ImageDraw.Draw(band)
            wd = R * 0.5
            bd.polygon([(pos, 0), (pos + wd, 0), (pos + wd - R * 2, R * 2), (pos - R * 2, R * 2)], fill=150)
            band = band.filter(ImageFilter.GaussianBlur(R * 0.12))
            band = ImageChops.multiply(band, alpha)
            fr.alpha_composite(Image.merge("RGBA", (Image.new("L", base.size, 255),) * 3 + (band,)))
        fr = fr.rotate(ang, resample=Image.BICUBIC)
        d_ = max(2, int(R * sc))
        fr = fr.resize((d_, d_), Image.LANCZOS)
        canvas = Image.new("RGBA", (C, C), (0, 0, 0, 0))
        canvas.alpha_composite(fr, ((C - d_) // 2, (C - d_) // 2))
        frames.append(canvas)
    return frames


def badge_img(ic, tier, earned, size=56, prog=None):
    return ctk.CTkImage(badge_pil(ic, tier, earned, int(size * ss()), prog), size=(size, size))


@functools.lru_cache(maxsize=256)
def get_font(size, bold=False):
    names = (["segoeuib.ttf", "arialbd.ttf", "DejaVuSans-Bold.ttf", "Helvetica.ttc"] if bold
             else ["segoeui.ttf", "arial.ttf", "DejaVuSans.ttf", "Helvetica.ttc"])
    for n in names:
        try:
            return ImageFont.truetype(n, size)
        except OSError:
            continue
    try:
        return ImageFont.load_default(size=size)
    except TypeError:
        return ImageFont.load_default()


CHIP_STYLE = {"dark": ((11, 11, 18, 215), "#ffffff"), "gold": ((11, 11, 18, 215), "#ffc233"),
              "warn": ((224, 169, 74, 240), "#1a1206")}


def overlay_chips(img, chips):
    """Etiquetas (tipo, capítulo, nota...) desenhadas direto na capa, com cantos suaves."""
    if not chips:
        return img
    img = img.convert("RGBA")
    W, H = img.size
    size = max(16, min(30, int(W * 0.085)))
    font = get_font(size, True)
    m = int(size * 0.6)
    for pos, text, style in chips:
        d = ImageDraw.Draw(img, "RGBA")
        try:
            l, t, r, b = d.textbbox((0, 0), text, font=font)
        except Exception:
            continue
        star = int(size * 1.05) if style == "gold" else 0
        padx, pady = int(size * .6), int(size * .34)
        bw = (r - l) + 2 * padx + ((star + int(size * .3)) if star else 0)
        bh = (b - t) + 2 * pady
        x = m if pos in ("tl", "bl") else W - m - bw
        y = m if pos in ("tl", "tr") else H - m - bh
        fill, fg = CHIP_STYLE.get(style) or (hex_rgba(style, 235), "#0b0b12")
        d.rounded_rectangle([x, y, x + bw, y + bh], radius=bh // 2, fill=fill)
        tx = x + padx
        if star:
            st = star_pil(star, 1, (0, 0, 0, 0))
            img.paste(st, (int(tx), int(y + (bh - star) / 2)), st)
            d = ImageDraw.Draw(img, "RGBA")
            tx += star + int(size * .3)
        d.text((tx - l, y + pady - t), text, font=font, fill=fg)
    return img


def logo_pil(size, accent):
    s = size * 4
    bg = Image.new("RGB", (s, s))
    d = ImageDraw.Draw(bg)
    c1, c2 = hex_shade(accent, 1.0), hex_shade(accent, .42)
    for y in range(s):
        d.line([(0, y), (s, y)], fill=mix(c1, c2, y / (s - 1)))
    mask = Image.new("L", (s, s), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, s - 1, s - 1], radius=int(s * .22), fill=255)
    out = Image.new("RGBA", (s, s), (0, 0, 0, 0))
    out.paste(bg, (0, 0), mask)
    g, w = ImageDraw.Draw(out), max(3, int(s * .06))
    for a, b, c, e in ((.2, .24, .38, .78), (.43, .24, .61, .78)):
        g.rounded_rectangle([a * s, b * s, c * s, e * s], radius=int(s * .03), outline="white", width=w)
    pts = [(x * s, y * s) for x, y in ((.68, .30), (.84, .25), (.95, .73), (.79, .78))]
    g.line(pts + [pts[0]], fill="white", width=w, joint="curve")
    return out.resize((size, size), Image.LANCZOS)


def _fit_text(d, text, font, maxw):
    if d.textlength(text, font=font) <= maxw:
        return text
    while text and d.textlength(text + "…", font=font) > maxw:
        text = text[:-1]
    return text.rstrip() + "…"


def _wrap(d, text, font, maxw, maxlines):
    lines, cur = [], ""
    for w in text.split():
        t = (cur + " " + w).strip()
        if d.textlength(t, font=font) <= maxw:
            cur = t
        else:
            if cur:
                lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    if len(lines) > maxlines:
        lines = lines[:maxlines]
        lines[-1] = _fit_text(d, lines[-1] + "…", font, maxw)
    return lines


def make_share_image(app, path):
    """Imagem do perfil para postar (1080x1440): o banner vira o fundo e os dados ficam em painéis translúcidos."""
    W, H = 1080, 1440
    pal, accent = DARK, S["accent"]
    bg, pr, items = pal["bg"], app.profile, app.items
    navy = "#0a0c18"
    ac = hex_rgba(accent, 255)[:3]
    bp = profile_dir() / pr["banner"] if pr.get("banner") else None
    try:
        raw = Image.open(bp).convert("RGB") if bp and bp.exists() else None
    except OSError:
        raw = None
    if raw is None:                       # sem banner: degradê na cor de destaque
        raw = banner_pil(None, W, 700, bg, accent, fade=(2, 1))
    # fundo: capa do banner desfocada no corpo todo + banner nítido no alto, dissolvendo
    back = ImageOps.fit(raw, (W, H)).filter(ImageFilter.GaussianBlur(26))
    back = Image.blend(back, Image.new("RGB", (W, H), navy), .62)
    top = ImageOps.fit(raw, (W, 760))
    fm = Image.new("L", (1, 760))
    for y in range(760):
        fm.putpixel((0, y), int(255 * max(0, min(1, (760 - y) / 330)) ** 1.1))
    back.paste(top, (0, 0), fm.resize((W, 760)))
    sh = Image.new("L", (1, H))
    for y in range(H):
        sh.putpixel((0, y), int(150 * max(0, (y - 560) / (H - 560)) ** 1.2))
    back = Image.composite(Image.new("RGB", (W, H), "#05060d"), back, sh.resize((W, H)))
    img = back.convert("RGBA")
    d = ImageDraw.Draw(img)

    def T(xy, text, size, fill, bold=False, anchor="la"):
        font = get_font(size, bold)
        try:
            d.text(xy, text, font=font, fill=fill, anchor=anchor)
        except (TypeError, ValueError):
            d.text(xy, text, font=font, fill=fill)

    def panel_(box, r=34, a=175, border=True, fill=None):
        nonlocal img, d
        ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ImageDraw.Draw(ov).rounded_rectangle(box, radius=r, fill=(fill or (9, 8, 22)) + (a,),
                                             outline=(ac + (130,)) if border else None, width=3)
        img = Image.alpha_composite(img, ov)
        d = ImageDraw.Draw(img)

    def put(im, xy):
        nonlocal img, d
        im = im.convert("RGBA")
        img.alpha_composite(im, (int(xy[0]), int(xy[1])))
        d = ImageDraw.Draw(img)

    def ico(name, size, color):
        return icon_pil(name, size, color).convert("RGBA").resize((size, size), Image.LANCZOS)

    show = showcase_badges(app)
    if show:
        bs, gp = 92, 14
        pw_ = len(show) * bs + (len(show) - 1) * gp + 44
        panel_([W - 44 - pw_, 40, W - 44, 40 + bs + 40], r=34, a=185)
        for n_, b in enumerate(show):
            bi = badge_pil(b["icon"], b["tier"], True, bs * 2).resize((bs, bs), Image.LANCZOS)
            put(bi, (W - 44 - pw_ + 22 + n_ * (bs + gp), 40 + 20))

    # painel do perfil
    PY0, PY1 = 330, 640
    panel_([44, PY0, W - 44, PY1], r=40, a=190)
    AV = 220
    ap = profile_dir() / pr["avatar"] if pr.get("avatar") else None
    lv = level_info(xp_breakdown(app)[1])
    av = avatar_pil(ap, pr["name"], AV, navy, accent)
    am = Image.new("L", (AV * 4, AV * 4), 0)
    ImageDraw.Draw(am).ellipse([0, 0, AV * 4 - 1, AV * 4 - 1], fill=255)
    gl = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ImageDraw.Draw(gl).ellipse([82 - 6, PY0 + 40 - 6, 82 + AV + 6, PY0 + 40 + AV + 6], fill=ac + (150,))
    img = Image.alpha_composite(img, gl.filter(ImageFilter.GaussianBlur(14)))
    img.paste(av, (82, PY0 + 40), am.resize((AV, AV), Image.LANCZOS))
    d = ImageDraw.Draw(img)
    X = 82 + AV + 40
    maxw = W - X - 70
    T((X, PY0 + 34), _fit_text(d, pr["name"], get_font(76, True), maxw), 76, "#ffffff", True)
    uy = PY0 + 126
    d.line([X, uy, X + min(maxw, 360), uy], fill=ac + (255,), width=4)
    handle = _fit_text(d, pr["handle"], get_font(32), maxw)
    T((X, uy + 14), handle, 32, "#c9cde6")
    ttl_, tcol_ = display_title(app, lv)
    lab_lv = f"Nível {lv['level']} • {ttl_}"
    cfont = get_font(26, True)
    ly = uy + 66
    lwid = d.textlength(lab_lv, font=cfont)
    if lwid + 100 > maxw:
        lab_lv = f"Nível {lv['level']}"
        lwid = d.textlength(lab_lv, font=cfont)
    d.rounded_rectangle([X, ly, X + lwid + 82, ly + 48], radius=24, fill=mix(tcol_, navy, .82), outline=tcol_, width=2)
    put(ico("crown", 28, tcol_), (X + 16, ly + 10))
    T((X + 54, ly + 24), lab_lv, 26, tcol_, True, "lm")
    bio = (pr.get("bio") or "").strip()
    if bio and not bio.startswith("Clique em"):
        for k, line in enumerate(_wrap(d, bio, get_font(28), maxw, 2)):
            T((X, ly + 64 + k * 38), line, 28, "#9aa0c0")

    # números
    rated = [i["rating"] for i in items if i["rating"]]
    stats = [("library", str(len(items)), "leituras"),
             ("check", str(sum(1 for i in items if i["status"] == "completo")), "completas"),
             ("star", f"{sum(rated) / len(rated):.1f}".replace(".", ",") if rated else "–", "nota média"),
             ("clock", fmt_minutes(sum_activity(app.activity, "", "min")), "de leitura")]
    SY0, SY1 = 668, 826
    panel_([44, SY0, W - 44, SY1], r=34, a=180)
    cw_ = (W - 88) / 4
    for k, (ic, val, lab) in enumerate(stats):
        cx_ = 44 + cw_ * k + cw_ / 2
        if k:
            d.line([44 + cw_ * k, SY0 + 28, 44 + cw_ * k, SY1 - 28], fill=ac + (90,), width=2)
        put(ico(ic, 34, "#c9cde6"), (cx_ - 17, SY0 + 18))
        size = 54
        while size > 28 and d.textlength(val, font=get_font(size, True)) > cw_ - 30:
            size -= 4
        T((cx_, SY0 + 90), val, size, "#ffffff", True, "mm")
        T((cx_, SY0 + 130), lab, 25, "#aab0cc", False, "mm")

    # gêneros
    gy = 858
    top3 = [t for t, _ in Counter(t for i in items for t in i["tags"]).most_common(3)]
    if top3:
        put(ico("library", 34, "#aab0cc"), (50, gy + 8))
        T((98, gy + 25), "Gêneros", 28, "#aab0cc", False, "lm")
        cx = 98 + d.textlength("Gêneros", font=get_font(28)) + 30
        cf = get_font(28, True)
        for n_, t in enumerate(top3):
            label = _fit_text(d, t, cf, 230)
            lw_ = d.textlength(label, font=cf)
            panel_([cx, gy, cx + lw_ + 96, gy + 58], r=29, a=200, fill=tuple(mix(accent, navy, .8) and hex_rgba(mix(accent, navy, .8), 255)[:3]))
            put(ico(("flame", "target", "gem")[n_ % 3], 28, accent), (cx + 20, gy + 15))
            T((cx + 62, gy + 29), label, 28, "#ffffff", True, "lm")
            cx += lw_ + 96 + 14
    # favoritos
    ranked = sorted(items, key=lambda i: (-i["rating"], -i["seen"]))
    favs = [i for i in ranked if i["favorite"]]
    title = "Minhas leituras favoritas" if favs else "Destaques"
    favs = (favs + [i for i in ranked if not i["favorite"]])[:5]
    ty = 940
    put(ico("star", 44, accent), (52, ty))
    T((112, ty + 22), title, 44, "#ffffff", True, "lm")
    CW, CH = 176, 244
    cgap = (W - 100 - 5 * CW) // 4
    cy = ty + 78
    rmask = Image.new("L", (CW * 4, CH * 4), 0)
    ImageDraw.Draw(rmask).rounded_rectangle([0, 0, CW * 4 - 1, CH * 4 - 1], radius=64, fill=255)
    rmask = rmask.resize((CW, CH), Image.LANCZOS)
    if not favs:
        panel_([50, cy, W - 50, cy + CH], r=30, a=150)
        T((W / 2, cy + CH / 2), "Adicione e favorite leituras para elas aparecerem aqui", 28, "#aab0cc", False, "mm")
    for k, it in enumerate(favs):
        x = 50 + k * (CW + cgap)
        try:
            cp = covers_dir() / it["cover"] if it.get("cover") else None
            cov = Image.open(cp).convert("RGB") if cp and cp.exists() else placeholder(it["title"])
        except OSError:
            cov = placeholder(it["title"])
        cov = ImageOps.fit(cov.convert("RGB"), (CW * 2, CH * 2))
        if it["rating"]:
            cov = overlay_chips(cov, [("bl", f"{it['rating']:g}".replace(".", ","), "gold")])
        sh_ = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ImageDraw.Draw(sh_).rounded_rectangle([x, cy + 10, x + CW, cy + CH + 10], radius=22, fill=(0, 0, 0, 170))
        img = Image.alpha_composite(img, sh_.filter(ImageFilter.GaussianBlur(10)))
        c_ = cov.convert("RGB").resize((CW, CH), Image.LANCZOS)
        img.paste(c_, (x, cy), rmask)
        d = ImageDraw.Draw(img)
        T((x, cy + CH + 14), _fit_text(d, it["title"], get_font(24), CW), 24, "#c9cde6")

    # rodapé
    FY = 1342
    panel_([44, FY, W - 44, FY + 84], r=30, a=170, border=False)
    logo = logo_pil(60, accent)
    put(logo, (62, FY + 12))
    T((140, FY + 24), "Leitura Foda", 32, "#ffffff", True, "lm")
    T((140, FY + 58), "Descubra o próximo capítulo da sua história.", 20, "#9aa0c0", False, "lm")
    yr = str(date.today().year)
    yw = d.textlength(yr, font=get_font(30, True)) + 84
    panel_([W - 62 - yw, FY + 12, W - 62, FY + 72], r=30, a=200, fill=tuple(hex_rgba(mix(accent, navy, .75), 255)[:3]))
    x0 = W - 62 - yw + 20
    d.rounded_rectangle([x0, FY + 28, x0 + 30, FY + 56], radius=6, outline="#ffffff", width=3)
    d.line([x0, FY + 38, x0 + 30, FY + 38], fill="#ffffff", width=3)
    T((x0 + 46, FY + 43), yr, 30, "#ffffff", True, "lm")
    img.convert("RGB").save(path, "PNG")


# ---------- widgets ----------
def section(parent, text, size=16):
    """Título de seção com a barrinha colorida ao lado, como na referência."""
    f = ctk.CTkFrame(parent, fg_color="transparent")
    ctk.CTkFrame(f, width=3, height=size + 6, fg_color=P["accent"], corner_radius=0).pack(side="left", padx=(0, 10))
    ctk.CTkLabel(f, text=text, text_color=P["text"], font=ctk.CTkFont(size=size, weight="bold")).pack(side="left")
    return f


def rounded(img, r):
    """Cantos arredondados (com transparência) para as capas."""
    img = img.convert("RGBA")
    m = Image.new("L", img.size, 0)
    ImageDraw.Draw(m).rounded_rectangle([0, 0, img.size[0] - 1, img.size[1] - 1], radius=max(2, int(r)), fill=255)
    img.putalpha(m)
    return img


def entry(parent, ph="", **kw):
    kw.setdefault("height", 36)
    e = ctk.CTkEntry(parent, placeholder_text=ph, fg_color=P["surface2"], border_width=1,
                     border_color=P["surface2"], corner_radius=10, text_color=P["text"], **kw)
    e.bind("<FocusIn>", lambda ev: e.configure(border_color=P["accent"]), add="+")
    e.bind("<FocusOut>", lambda ev: e.configure(border_color=P["surface2"]), add="+")
    return e


def menu(parent, values, command=None, width=140, fg=None, **kw):
    kw.setdefault("corner_radius", 10)
    kw.setdefault("dynamic_resizing", False)
    return ctk.CTkOptionMenu(parent, values=values, command=command, width=width,
                             fg_color=fg or P["surface"], button_color=P["surface2"],
                             button_hover_color=P["accent"], text_color=P["text"],
                             dropdown_fg_color=P["surface"], dropdown_text_color=P["text"],
                             dropdown_hover_color=P["surface2"], **kw)


def flat_button(parent, text, command, **kw):
    kw.setdefault("height", 36)
    kw.setdefault("corner_radius", 10)
    return ctk.CTkButton(parent, text=text, command=command, fg_color=P["surface2"],
                         hover_color=mix(P["surface2"], P["accent"], .38), text_color=P["text"], **kw)


def accent_button(parent, text, command, **kw):
    kw.setdefault("height", 36)
    kw.setdefault("corner_radius", 10)
    kw.setdefault("font", ctk.CTkFont(weight="bold"))
    return ctk.CTkButton(parent, text=text, command=command, fg_color=P["accent"],
                         hover_color=P["accent_hover"], text_color="white", **kw)


def ghost_button(parent, text, command, **kw):
    kw.setdefault("height", 36)
    kw.setdefault("corner_radius", 10)
    return ctk.CTkButton(parent, text=text, command=command, fg_color="transparent", border_width=1,
                         border_color=P["border"], hover_color=P["surface2"], text_color=P["muted"], **kw)


def danger_button(parent, text, command, **kw):
    kw.setdefault("height", 36)
    kw.setdefault("corner_radius", 10)
    return ctk.CTkButton(parent, text=text, command=command, fg_color="transparent", border_width=1,
                         border_color=DANGER, hover_color=mix(DANGER, P["bg"], .8), text_color=DANGER, **kw)


def toggle_chip(parent, text, var, command=None, ic=None, **kw):
    """Botão liga/desliga (filtro) que acende na cor de destaque quando ativo."""
    holder = {}

    def paint():
        on = bool(var.get())
        col = PINK if (ic == "heart" and on) else P["accent"]
        b = holder["b"]
        b.configure(fg_color=mix(col, P["surface"], .78) if on else P["surface"],
                    border_color=col if on else P["border"], text_color=P["text"] if on else P["muted"])
        if ic:
            b.configure(image=icon("heart_fill" if (ic == "heart" and on) else ic, 16, col if on else P["muted"]))

    def click():
        var.set(not var.get())
        paint()
        if command:
            command()

    holder["b"] = ctk.CTkButton(parent, text=text, command=click, height=38, corner_radius=10, border_width=1,
                                fg_color=P["surface"], border_color=P["border"], hover_color=P["surface2"],
                                text_color=P["muted"], image=icon(ic, 16) if ic else None, compound="left", **kw)
    paint()
    return holder["b"]


def check(parent, text, var, command=None, **kw):
    return ctk.CTkCheckBox(parent, text=text, variable=var, command=command, fg_color=P["accent"],
                           hover_color=P["accent_hover"], border_color=P["muted"], border_width=2,
                           corner_radius=6, checkbox_width=20, checkbox_height=20, text_color=P["text"], **kw)


def action_btn(parent, text, ic, command, hot=None, on=False, height=40):
    """Botão de ação com ícone (coluna da esquerda da tela de detalhes)."""
    base, tint = P["surface2"], hot or P["accent"]
    return ctk.CTkButton(parent, text=" " + text, image=icon(ic, 16, tint if on else P["text"]),
                         compound="left", command=command, height=height, corner_radius=10,
                         fg_color=mix(base, tint, .22) if on else base, hover_color=mix(base, tint, .38),
                         text_color=P["text"], font=ctk.CTkFont(size=13))


def empty_state(parent, ic, title, sub="", action=None):
    f = ctk.CTkFrame(parent, fg_color="transparent")
    ctk.CTkLabel(f, text="", image=icon(ic, 44, mix(P["muted"], P["bg"], .45))).pack(pady=(0, 10))
    ctk.CTkLabel(f, text=title, text_color=P["text"], font=ctk.CTkFont(size=18, weight="bold")).pack()
    if sub:
        ctk.CTkLabel(f, text=sub, text_color=P["muted"], wraplength=360, justify="center").pack(pady=(4, 0))
    if action:
        action(f).pack(pady=(14, 0))
    return f


def hover_card(card, normal=None, hot=None):
    """Destaca a borda do cartão quando o mouse passa por cima (ou por cima de qualquer item dele)."""
    normal = normal or P["border"]
    hot = hot or P["accent"]
    state = {"on": False}

    def inside(e):
        try:
            w = card.winfo_containing(e.x_root, e.y_root)
        except (KeyError, tk.TclError):
            return False
        while w is not None:
            if w is card:
                return True
            w = getattr(w, "master", None)
        return False

    def enter(e):
        if not state["on"] and not scrolling():
            state["on"] = True
            card.configure(border_color=hot)

    def leave(e):
        if state["on"] and not inside(e):
            state["on"] = False
            card.configure(border_color=normal)

    def bind_tree(w):
        try:
            w.bind("<Enter>", enter, add="+")
            w.bind("<Leave>", leave, add="+")
        except Exception:
            return
        for c in w.winfo_children():
            bind_tree(c)

    bind_tree(card)


class Tip:
    """Dica flutuante: aparece quando o mouse fica parado em cima (o texto vem de uma função)."""

    def __init__(self, widget, text_fn):
        self.w, self.text_fn, self.tw, self.job = widget, text_fn, None, None
        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._leave, add="+")
        widget.bind("<ButtonPress>", self._leave, add="+")

    def _enter(self, e=None):
        self._leave()
        self.job = self.w.after(450, self._show)

    def _show(self):
        self.job = None
        text = self.text_fn()
        if not text:
            return
        try:
            x = self.w.winfo_rootx() + self.w.winfo_width() + 8
            y = self.w.winfo_rooty() + max(0, (self.w.winfo_height() - px(26)) // 2)
            self.tw = tk.Toplevel(self.w)
            self.tw.wm_overrideredirect(True)
            self.tw.wm_geometry(f"+{x}+{y}")
            tk.Label(self.tw, text=text, bg=P["surface2"], fg=P["text"], padx=10, pady=4,
                     font=("TkDefaultFont", fpt(10)), bd=1, relief="solid").pack()
        except Exception:
            self.tw = None

    def _leave(self, e=None):
        if self.job:
            try:
                self.w.after_cancel(self.job)
            except Exception:
                pass
            self.job = None
        if self.tw is not None:
            try:
                self.tw.destroy()
            except Exception:
                pass
            self.tw = None


class ScrollFrame(tk.Frame):
    """Área rolável própria: roda do mouse suave em qualquer ponto, barra no tema e rolagem só quando precisa."""

    def __init__(self, master, **kw):
        self.virtual = None                  # grade desenhada direto no canvas (VGrid), quando ativa
        self.win_w = None                    # largura (lógica) da coluna, se menor que a área (fundo nas laterais)
        self.on_canvas = None
        self.top_off = 0                   # deslocamento do conteúdo para baixo (barra desenhada no canvas)
        self._outer = ctk.CTkFrame(master, fg_color="transparent", corner_radius=0)
        self.canvas = tk.Canvas(self._outer, highlightthickness=0, bd=0, bg=P["bg"])
        self.bar = ctk.CTkScrollbar(self._outer, orientation="vertical", command=self.canvas.yview, width=12,
                                    fg_color="transparent", button_color=P["bg"], button_hover_color=P["bg"])
        self.canvas.configure(yscrollcommand=self._on_scroll)
        self.bar.pack(side="right", fill="y", padx=(0, 2), pady=2)
        self.canvas.pack(side="left", fill="both", expand=True)
        tk.Frame.__init__(self, self.canvas, bg=P["bg"], bd=0, highlightthickness=0)
        self._win = self.canvas.create_window(0, 0, window=self, anchor="nw")
        self._region_h, self._target, self._anim, self._thumb_on, self._dead = 1, 0.0, False, None, False
        self.canvas._scroll_owner = self
        self._scroll_owner = self
        tk.Frame.bind(self, "<Configure>", self._on_inner, "+")
        self.canvas.bind("<Configure>", self._on_canvas)

    # ---- aparência e tamanho ----
    def _on_scroll(self, lo, hi):
        lo, hi = float(lo), float(hi)
        self.bar.set(lo, hi)
        if self.virtual is not None:
            self.virtual.sync()
        need = not (lo <= 0.0 and hi >= 1.0)
        if need != self._thumb_on:
            self._thumb_on = need
            idle = getattr(self, "idle", None) or P["bg"]
            self.bar.configure(button_color=P["surface2"] if need else idle,
                               button_hover_color=P["accent"] if need else idle)

    def _on_inner(self, e):
        if self.virtual is not None:
            return
        self._region_h = max(1, e.height + self.top_off)
        self.canvas.configure(scrollregion=(0, 0, max(e.width, self.canvas.winfo_width()), e.height + self.top_off))

    def _on_canvas(self, e):
        if self.win_w:
            ww = min(e.width, px(self.win_w))
            self.canvas.coords(self._win, (e.width - ww) // 2, self.top_off)
            self.canvas.itemconfigure(self._win, width=ww)
        else:
            self.canvas.itemconfigure(self._win, width=e.width)
        if self.on_canvas:
            self.on_canvas(e.width)
        if self.virtual is not None:
            self.virtual.resized()

    def reflow(self):
        """Volta a medir a área rolável pelo conteúdo de widgets (ao sair do modo virtual)."""
        try:
            self.update_idletasks()
            self._region_h = max(1, self.winfo_reqheight())
            self.canvas.configure(scrollregion=(0, 0, max(1, self.winfo_width()), self._region_h))
        except tk.TclError:
            pass

    @property
    def _parent_canvas(self):
        return self.canvas

    # ---- rolagem suave ----
    def wheel(self, e, step=None):
        if step is not None:
            dy = -step * 80
        elif sys.platform == "darwin":
            dy = -e.delta * 6
        else:
            dy = -e.delta / 120.0 * 80
        try:
            view = self.canvas.winfo_height()
            cur = self._target if self._anim else self.canvas.canvasy(0)
            edge = self._region_h <= view + 1 or (dy < 0 and cur <= 0.5) or (dy > 0 and cur >= self._region_h - view - 0.5)
            if edge and getattr(self, "chain", False):
                w = self._outer.master
                while w is not None:
                    po = getattr(w, "_scroll_owner", None)
                    if po is not None and po is not self:
                        return po.wheel(e, step)
                    w = getattr(w, "master", None)
        except tk.TclError:
            pass
        self.scroll_by(dy)

    def scroll_by(self, dy):
        try:
            view = self.canvas.winfo_height()
            if self._region_h <= view + 1:
                return
            SCROLL["until"] = time.time() + 0.25
            base = self._target if self._anim else self.canvas.canvasy(0)
            self._target = max(0.0, min(float(self._region_h - view), base + dy))
            if not self._anim:
                self._anim = True
                self._step()
        except tk.TclError:
            self._anim = False

    def _step(self):
        try:
            cur = self.canvas.canvasy(0)
            diff = self._target - cur
            if abs(diff) < 1.0:
                self.canvas.yview_moveto(self._target / self._region_h)
                self._anim = False
                return
            t0 = time.time()
            self.canvas.yview_moveto((cur + diff * 0.3) / self._region_h)
            self.canvas.update_idletasks()
            if time.time() - t0 > 0.05:             # tela pesada: pula a animação em vez de acumular quadros
                self.canvas.yview_moveto(self._target / self._region_h)
                self._anim = False
                return
            self.canvas.after(10, self._step)
        except tk.TclError:
            self._anim = False

    # ---- o frame interno se comporta como se fosse a área inteira ----
    def bind(self, sequence=None, func=None, add=None):
        if sequence == "<Configure>":
            add = "+"
        return tk.Frame.bind(self, sequence, func, add)

    def pack(self, **kw):
        return self._outer.pack(**kw)

    def pack_forget(self):
        return self._outer.pack_forget()

    def grid(self, **kw):
        return self._outer.grid(**kw)

    def grid_forget(self):
        return self._outer.grid_forget()

    def place(self, **kw):
        return self._outer.place(**kw)

    def place_forget(self):
        return self._outer.place_forget()

    def destroy(self):
        if self._dead:
            return
        self._dead = True
        try:
            tk.Frame.destroy(self)
        except tk.TclError:
            pass
        try:
            self._outer.destroy()
        except Exception:
            pass


class HShelf(ctk.CTkFrame):
    """Prateleira que rola para o lado (setas, Shift + roda do mouse ou botões)."""

    def __init__(self, master, height, bg=None):
        super().__init__(master, fg_color="transparent")
        bg = bg or P["bg"]
        self.canvas = tk.Canvas(self, height=px(height), bg=bg, highlightthickness=0, bd=0)
        self.canvas.pack(fill="x")
        self.inner = tk.Frame(self.canvas, bg=bg, bd=0, highlightthickness=0)
        self.canvas.create_window(0, 0, window=self.inner, anchor="nw")
        self._cw, self._target, self._anim = 1, 0.0, False
        self.inner.bind("<Configure>", self._on_inner)
        self.canvas._hscroll_owner = self
        self.inner._hscroll_owner = self

    def _on_inner(self, e):
        self._cw = max(1, e.width)
        self.canvas.configure(scrollregion=(0, 0, e.width, e.height))

    def wheel(self, e, step=None):
        if step is not None:
            dx = -step * 180
        elif sys.platform == "darwin":
            dx = -e.delta * 8
        else:
            dx = -e.delta / 120.0 * 180
        self.scroll_by(dx)

    def scroll_by(self, dx):
        try:
            view = self.canvas.winfo_width()
            if self._cw <= view + 1:
                return
            SCROLL["until"] = time.time() + 0.25
            base = self._target if self._anim else self.canvas.canvasx(0)
            self._target = max(0.0, min(float(self._cw - view), base + dx))
            if not self._anim:
                self._anim = True
                self._step()
        except tk.TclError:
            self._anim = False

    def _step(self):
        try:
            cur = self.canvas.canvasx(0)
            diff = self._target - cur
            if abs(diff) < 1.0:
                self.canvas.xview_moveto(self._target / self._cw)
                self._anim = False
                return
            self.canvas.xview_moveto((cur + diff * 0.28) / self._cw)
            self.canvas.update_idletasks()
            self.canvas.after(8, self._step)
        except tk.TclError:
            self._anim = False


# ---- prévia ao passar o mouse (notas, gêneros, última citação) ----
PV = {"job": None, "tw": None, "root": None}


def preview_hide():
    root = PV["root"]
    if PV["job"] is not None and root is not None:
        try:
            root.after_cancel(PV["job"])
        except Exception:
            pass
    PV["job"] = None
    if PV["tw"] is not None:
        try:
            PV["tw"].destroy()
        except Exception:
            pass
        PV["tw"] = None


def preview_has_content(it):
    return bool(it.get("tags") or it.get("notes") or it.get("quotes") or it.get("labels"))


def preview_show(app, it):
    PV["job"] = None
    if not S.get("preview", True):
        return
    try:
        tw = tk.Toplevel(app)
        tw.wm_overrideredirect(True)
        try:
            tw.wm_attributes("-topmost", True)
        except Exception:
            pass
        outer = tk.Frame(tw, bg=app.item_color(it), padx=1, pady=1)
        outer.pack()
        body = tk.Frame(outer, bg=P["surface"], padx=px(12), pady=px(10))
        body.pack()

        def line(text, size=10, bold=False, fg=None, pad=0):
            tk.Label(body, text=text, bg=P["surface"], fg=fg or P["text"], justify="left", anchor="w",
                     font=("TkDefaultFont", fpt(size), "bold" if bold else "normal"),
                     wraplength=px(300)).pack(anchor="w", pady=(pad, 0))

        line(it["title"], 12, True)
        line("  •  ".join(x for x in (it["type"], it["author"], str(it["year"]) if it["year"] else "") if x),
             9, fg=P["muted"])
        line(f"{STATUS[it['status']]} · {cap_text(it)}", 9, fg=P["status"][it["status"]], pad=2)
        if it["tags"]:
            line(" · ".join(it["tags"][:6]), 9, fg=app.item_color(it), pad=4)
        if it["labels"]:
            line("  ".join(f"[{n}]" for n in it["labels"][:4]), 9, fg=P["muted"], pad=2)
        if it["notes"]:
            line(it["notes"][:150] + ("…" if len(it["notes"]) > 150 else ""), 10, pad=6)
        if it["quotes"]:
            q = max(it["quotes"], key=lambda q: q.get("ts", 0))
            line(f"“{q['text'][:110]}”  — cap. {q.get('ch', 0)}", 9, fg=P["muted"], pad=6)
        tw.update_idletasks()
        w, h = tw.winfo_reqwidth(), tw.winfo_reqheight()
        x = min(app.winfo_pointerx() + 18, app.winfo_screenwidth() - w - 8)
        y = min(app.winfo_pointery() + 16, app.winfo_screenheight() - h - 56)
        tw.wm_geometry(f"+{max(0, x)}+{max(0, y)}")
        PV["tw"] = tw
    except Exception:
        PV["tw"] = None


def shelf_tip_show(app, it):
    """Cartão rápido da estante: capa, título completo, nota e capítulo."""
    PV["job"] = None
    try:
        tw = tk.Toplevel(app)
        tw.wm_overrideredirect(True)
        try:
            tw.wm_attributes("-topmost", True)
        except Exception:
            pass
        col = app.item_color(it)
        outer = tk.Frame(tw, bg=col, padx=1, pady=1)
        outer.pack()
        body = tk.Frame(outer, bg=P["surface"], padx=px(10), pady=px(10))
        body.pack()
        cw_, ch_ = 78, 110
        try:
            ph = ImageTk.PhotoImage(app.cover_pil(it, cw_, ch_).resize((px(cw_), px(ch_)), Image.BICUBIC))
            lb = tk.Label(body, image=ph, bg=P["surface"], bd=0)
            lb.image = ph
            lb.pack(side="left", anchor="n", padx=(0, px(10)))
        except Exception:
            pass
        right = tk.Frame(body, bg=P["surface"])
        right.pack(side="left", anchor="n")
        tk.Label(right, text=it["title"], bg=P["surface"], fg=P["text"], justify="left", anchor="w",
                 font=("TkDefaultFont", fpt(12), "bold"), wraplength=px(230)).pack(anchor="w")
        tk.Label(right, text=f"{it['type']} · {STATUS[it['status']]}", bg=P["surface"], fg=P["muted"],
                 font=("TkDefaultFont", fpt(9))).pack(anchor="w", pady=(2, 0))
        r = it.get("rating") or 0
        if r:
            full = int(r)
            stars = "★" * full + ("½" if r - full >= .5 else "")
            tk.Label(right, text=f"{stars}  {r:g}", bg=P["surface"], fg="#ffc233",
                     font=("TkDefaultFont", fpt(11), "bold")).pack(anchor="w", pady=(4, 0))
        else:
            tk.Label(right, text="sem nota", bg=P["surface"], fg=P["muted"],
                     font=("TkDefaultFont", fpt(9))).pack(anchor="w", pady=(4, 0))
        tk.Label(right, text=cap_text(it), bg=P["surface"], fg=P["text"],
                 font=("TkDefaultFont", fpt(10), "bold")).pack(anchor="w", pady=(4, 0))
        tw.update_idletasks()
        w, h = tw.winfo_reqwidth(), tw.winfo_reqheight()
        x = min(app.winfo_pointerx() + 16, app.winfo_screenwidth() - w - 8)
        y = min(app.winfo_pointery() + 18, app.winfo_screenheight() - h - 56)
        tw.wm_geometry(f"+{max(0, x)}+{max(0, y)}")
        PV["tw"] = tw
    except Exception:
        PV["tw"] = None


def attach_preview(app, widget, it):
    if not preview_has_content(it):
        return
    state = {"in": False}

    def inside(e):
        try:
            w = widget.winfo_containing(e.x_root, e.y_root)
        except (KeyError, tk.TclError):
            return False
        while w is not None:
            if w is widget:
                return True
            w = getattr(w, "master", None)
        return False

    def enter(e):
        if state["in"] or not S.get("preview", True) or scrolling():
            return
        state["in"] = True
        preview_hide()
        PV["root"] = app
        PV["job"] = app.after(650, lambda: preview_show(app, it))

    def leave(e):
        if state["in"] and not inside(e):
            state["in"] = False
            preview_hide()

    def bind_tree(w):
        try:
            w.bind("<Enter>", enter, add="+")
            w.bind("<Leave>", leave, add="+")
            w.bind("<ButtonPress>", lambda e: preview_hide(), add="+")
        except Exception:
            return
        for c in w.winfo_children():
            bind_tree(c)

    bind_tree(widget)


# ---- animações sutis (podem ser desligadas em Configurações) ----
def animate_number(lbl, target, fmt=None, steps=14):
    """Número que 'conta' até o valor final."""
    fmt = fmt or (lambda v: f"{int(round(v))}")
    if (not S.get("anim", True)) or isinstance(target, bool) or not isinstance(target, (int, float)) or target < 2:
        return

    def step(i=1):
        try:
            if not lbl.winfo_exists():
                return
            t = 1 - (1 - i / steps) ** 3
            lbl.configure(text=fmt(target * t) if i < steps else fmt(target))
            if i < steps:
                lbl.after(26, lambda: step(i + 1))
        except tk.TclError:
            pass

    lbl.configure(text=fmt(0))
    lbl.after(30, step)


def animate_bar(bar, target, steps=16):
    """Barra de progresso que enche."""
    if (not S.get("anim", True)) or target <= 0.01:
        bar.set(target)
        return
    bar.set(0)

    def step(i=1):
        try:
            if not bar.winfo_exists():
                return
            bar.set(target * (1 - (1 - i / steps) ** 3))
            if i < steps:
                bar.after(24, lambda: step(i + 1))
        except tk.TclError:
            pass

    bar.after(40, step)


# ---- tela de abertura ----
def show_splash(root):
    try:
        sp = tk.Toplevel(root)
        sp.wm_overrideredirect(True)
        sp.configure(bg=P["bg"])
        w, h = px(340), px(250)
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        sp.wm_geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 2 - 20)}")
        logo = ImageTk.PhotoImage(logo_pil(px(96), S["accent"]))
        lab = tk.Label(sp, image=logo, bg=P["bg"])
        lab.image = logo
        lab.pack(pady=(px(34), px(10)))
        tk.Label(sp, text="Leitura Foda", bg=P["bg"], fg=P["text"],
                 font=("TkDefaultFont", fpt(20), "bold")).pack()
        tk.Label(sp, text="sua estante, do seu jeito", bg=P["bg"], fg=P["muted"],
                 font=("TkDefaultFont", fpt(10))).pack(pady=(4, 0))
        tk.Label(sp, text="Carregando…", bg=P["bg"], fg=P["muted"],
                 font=("TkDefaultFont", fpt(9))).pack(pady=(px(14), 0))
        tk.Frame(sp, bg=P["surface2"], height=px(3)).place(x=0, y=h - px(3), relwidth=1.0)
        bar = tk.Frame(sp, bg=P["accent"], height=px(3))
        bar.place(x=0, y=h - px(3), relwidth=0.08)
        sp._bar = bar
        try:
            sp.wm_attributes("-topmost", True)
        except Exception:
            pass
        sp.update()
        return sp
    except Exception:
        return None


def splash_step(sp, frac):
    """Avança a barra da tela de abertura (e deixa ela pintar enquanto o app carrega)."""
    if sp is None:
        return
    try:
        sp._bar.place_configure(relwidth=max(0.08, min(1.0, frac)))
        sp.update()
    except Exception:
        pass


def new_scroll(master):
    try:
        return ScrollFrame(master)
    except Exception:       # se algo der errado, cai para a área rolável padrão do customtkinter
        return ctk.CTkScrollableFrame(master, fg_color="transparent")


def segmented(parent, values, command, **kw):
    return ctk.CTkSegmentedButton(parent, values=values, command=command, fg_color=P["surface"],
                                  selected_color=P["accent"], selected_hover_color=P["accent_hover"],
                                  unselected_color=P["surface"], unselected_hover_color=P["surface2"],
                                  text_color=P["text"], **kw)


def fmt_rating(v):
    return "sem nota" if not v else f"{v:g} / 5".replace(".", ",")


def cap_text(it):
    """'cap. 12/50'; em obras em lançamento que estão em dia: 'cap. 100 · em dia'."""
    t = f"cap. {it['seen']}"
    if it.get("total"):
        if it.get("ongoing") and it["seen"] >= it["total"]:
            return t + " · em dia"
        return t + f"/{it['total']}"
    return t


def balanced_cols(total, width_logical, cell=96):
    """Quantas colunas usar para os números ficarem em linhas equilibradas (sem 1 sozinho na última)."""
    nmax = max(2, min(total, int(width_logical) // cell))
    rows = -(-total // nmax)
    for n in range(-(-total // rows), nmax + 1):       # menor n que ainda cabe nessas linhas
        if total - (rows - 1) * n != 1:                # evita deixar uma célula sozinha na última linha
            return n
    return nmax


def to_int(widget):
    try:
        return max(0, int(widget.get().strip() or 0))
    except ValueError:
        return None


def reflow(widgets, width, gap=8):
    """Distribui os widgets em linhas, quebrando quando não cabe (width em pixels reais)."""
    for w in widgets:
        w.grid_forget()
    x = row = col = 0
    for w in widgets:
        need = w.winfo_reqwidth() + px(gap)
        if col and x + need > width:
            row, col, x = row + 1, 0, 0
        w.grid(row=row, column=col, padx=(0, gap), pady=4, sticky="w")
        x += need
        col += 1


class StarRating(tk.Canvas):
    """Estrelas de 0,5 a 5. Passe o mouse para prever, clique para fixar."""

    def __init__(self, parent, bg, value=0.0, size=30, interactive=True,
                 on_change=None, on_hover=None):
        size = px(size)
        self.star_sz, self.gap = size, px(4)
        super().__init__(parent, width=5 * size + 4 * self.gap, height=size,
                         bg=bg, highlightthickness=0, bd=0)
        self.imgs = star_images(size)
        self.items = [self.create_image(i * (size + self.gap), 0, anchor="nw") for i in range(5)]
        self.value = value
        self.on_change, self.on_hover = on_change, on_hover
        self.draw(value)
        if interactive:
            self.configure(cursor="hand2")
            self.bind("<Motion>", self._motion)
            self.bind("<Leave>", self._leave)
            self.bind("<Button-1>", self._click)

    def draw(self, v):
        for i, item in enumerate(self.items):
            k = 2 if v >= i + 1 else 1 if v >= i + 0.5 else 0
            self.itemconfigure(item, image=self.imgs[k])

    def _value_at(self, x):
        step = self.star_sz + self.gap
        i = min(4, max(0, int(x // step)))
        return i + (0.5 if (x - i * step) < self.star_sz / 2 else 1.0)

    def _motion(self, e):
        v = self._value_at(e.x)
        self.draw(v)
        if self.on_hover:
            self.on_hover(v)

    def _leave(self, _):
        self.draw(self.value)
        if self.on_hover:
            self.on_hover(self.value)

    def _click(self, e):
        v = self._value_at(e.x)
        self.value = 0.0 if v == self.value else v   # clicar de novo limpa
        self.draw(self.value)
        if self.on_change:
            self.on_change(self.value)
        if self.on_hover:
            self.on_hover(self.value)


# ---------- gráficos ----------
def _canvas(parent, height):
    return tk.Canvas(parent, width=10, height=height, bg=P["surface"], highlightthickness=0, bd=0)


def bars(parent, data, height=150, colors=None):
    height = px(height)
    k = scale_k()
    c = _canvas(parent, height)
    fs = ("TkDefaultFont", fpt(9))

    def draw(width):
        c.delete("all")
        mx = max([v for _, v in data] + [1])
        bw = max(1, width) / len(data)
        y1 = height - 20 * k
        for i, (lab, v) in enumerate(data):
            x0, x1 = i * bw + 5 * k, (i + 1) * bw - 5 * k
            h = (height - 46 * k) * v / mx
            col = colors[i] if colors else P["accent"]
            if v:
                top = y1 - h
                c.create_rectangle(x0, top, x1, y1, fill=col, width=0)
                c.create_text((x0 + x1) / 2, top - 9 * k, text=f"{v:g}", fill=P["text"], font=fs)
            else:
                c.create_line(x0, y1, x1, y1, fill=P["border"], width=max(1, int(2 * k)))
            c.create_text((x0 + x1) / 2, y1 + 10 * k, text=lab, fill=P["muted"], font=fs)

    c.bind("<Configure>", lambda e: draw(e.width))
    return c


def hist(parent, counts, height=110):
    """Histograma de notas (0,5 a 5 estrelas)."""
    height = px(height)
    k = scale_k()
    c = _canvas(parent, height)
    fs = ("TkDefaultFont", fpt(9))

    def draw(W):
        c.delete("all")
        mx = max(counts + [1])
        bw = max(1, W) / len(counts)
        base = height - 24 * k
        for i, v in enumerate(counts):
            x0, x1 = i * bw + 3 * k, (i + 1) * bw - 3 * k
            if v:
                top = base - (base - 8 * k) * v / mx
                c.create_rectangle(x0, top, x1, base, fill=P["accent"], width=0)
            else:
                c.create_line(x0, base, x1, base, fill=P["border"], width=max(1, int(2 * k)))
        c.create_text(4 * k, height - 9 * k, text="0,5 ★", anchor="w", fill=P["muted"], font=fs)
        c.create_text(W - 4 * k, height - 9 * k, text="5 ★", anchor="e", fill=P["muted"], font=fs)

    c.bind("<Configure>", lambda e: draw(e.width))
    return c


def radar(parent, labels, values, height=250):
    """Gráfico radar (teia) com valores de 0 a 1."""
    height = px(height)
    k = scale_k()
    c = _canvas(parent, height)
    n = len(labels)
    ang = [-math.pi / 2 + i * 2 * math.pi / n for i in range(n)]
    fs = ("TkDefaultFont", fpt(10))

    def draw(W, H):
        c.delete("all")
        cx, cy = W / 2, H / 2
        R = max(30 * k, min(W / 2 - 78 * k, H / 2 - 28 * k))
        for lvl in (1, .66, .33):
            pts = [v for a in ang for v in (cx + R * lvl * math.cos(a), cy + R * lvl * math.sin(a))]
            c.create_polygon(*pts, outline=P["border"], fill="", width=1)
        for a in ang:
            c.create_line(cx, cy, cx + R * math.cos(a), cy + R * math.sin(a), fill=P["border"])
        pts = [(cx + R * max(.14, v) * math.cos(a), cy + R * max(.14, v) * math.sin(a)) for v, a in zip(values, ang)]
        c.create_polygon(*[v for p in pts for v in p], fill=mix(P["accent"], P["surface"], .62),
                         outline=P["accent"], width=max(1, int(2 * k)))
        for x, y in pts:
            c.create_oval(x - 4 * k, y - 4 * k, x + 4 * k, y + 4 * k, fill=P["accent"], outline=P["accent"])
        for lab, a in zip(labels, ang):
            cs, sn = math.cos(a), math.sin(a)
            ax = "w" if cs > .3 else "e" if cs < -.3 else ""
            ay = "s" if sn < -.3 else "n" if sn > .3 else ""
            c.create_text(cx + (R + 12 * k) * cs, cy + (R + 12 * k) * sn, text=lab[:14],
                          anchor=(ay + ax) or "center", fill=P["muted"], font=fs)

    c.bind("<Configure>", lambda e: draw(e.width, e.height))
    return c


def smooth_pts(pts, steps=10):
    """Suaviza uma linha (interpolação em cosseno: sem 'estourar' acima dos pontos)."""
    out = []
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        for i in range(steps):
            t = i / steps
            m = (1 - math.cos(t * math.pi)) / 2
            out.append((x0 + (x1 - x0) * t, y0 * (1 - m) + y1 * m))
    out.append(pts[-1])
    return out


def linechart(parent, data, height=170):
    """Linha suave com área preenchida (ex.: capítulos por mês)."""
    height = px(height)
    k = scale_k()
    c = _canvas(parent, height)
    fs = ("TkDefaultFont", fpt(9))

    def draw(W):
        c.delete("all")
        n = len(data)
        if n < 2:
            return
        left, right, top, base = 16 * k, 16 * k, 22 * k, height - 24 * k
        mx = max([v for _, v in data] + [1])
        step = (W - left - right) / (n - 1)
        pts = [(left + i * step, base - (base - top) * v / mx) for i, (_, v) in enumerate(data)]
        sm = smooth_pts(pts)
        area = [(pts[0][0], base)] + sm + [(pts[-1][0], base)]
        c.create_polygon(*[v for p in area for v in p], fill=mix(P["accent"], P["surface"], .82), outline="")
        c.create_line(left, base, W - right, base, fill=P["border"])
        c.create_line(*[v for p in sm for v in p], fill=P["accent"], width=max(2, int(3 * k)),
                      capstyle="round", joinstyle="round")
        for i, ((lab, v), (x, y)) in enumerate(zip(data, pts)):
            c.create_oval(x - 4 * k, y - 4 * k, x + 4 * k, y + 4 * k, fill=P["surface"], outline=P["accent"],
                          width=max(2, int(2 * k)))
            c.create_text(x, base + 12 * k, text=lab, fill=P["muted"], font=fs)
            if v and v == mx:
                c.create_text(x, y - 13 * k, text=f"{v:g}", fill=P["text"], font=fs)

    c.bind("<Configure>", lambda e: draw(e.width))
    return c


def donut(parent, data, height=190, center="leituras"):
    """Gráfico de rosca. data = [(rótulo, valor, cor)]"""
    height = px(height)
    k = scale_k()
    c = _canvas(parent, height)
    fs = ("TkDefaultFont", fpt(10))
    fb = ("TkDefaultFont", fpt(20), "bold")

    def draw(W, H):
        c.delete("all")
        total = sum(v for _, v, _ in data)
        size = min(H - 16 * k, W * 0.46)
        cx, cy = 20 * k + size / 2, H / 2
        th = size * 0.17
        box = (cx - size / 2 + th / 2, cy - size / 2 + th / 2, cx + size / 2 - th / 2, cy + size / 2 - th / 2)
        if total <= 0:
            c.create_arc(*box, start=90, extent=359.9, style="arc", outline=P["surface2"], width=th)
        else:
            start = 90.0
            for lab, v, col in data:
                if v <= 0:
                    continue
                ext = -360.0 * v / total
                c.create_arc(*box, start=start, extent=ext + min(2.0, abs(ext) / 4), style="arc", outline=col,
                             width=th)
                start += ext
        c.create_text(cx, cy - 8 * k, text=str(total), fill=P["text"], font=fb)
        c.create_text(cx, cy + 14 * k, text=center, fill=P["muted"], font=fs)
        lx = cx + size / 2 + 30 * k
        y = max(16 * k, cy - len(data) * 13 * k + 13 * k)
        for lab, v, col in data:
            c.create_oval(lx, y - 6 * k, lx + 12 * k, y + 6 * k, fill=col, outline="")
            c.create_text(lx + 20 * k, y, text=lab, anchor="w", fill=P["text"], font=fs)
            c.create_text(W - 16 * k, y, text=str(v), anchor="e", fill=P["muted"], font=fs)
            y += 26 * k

    c.bind("<Configure>", lambda e: draw(e.width, e.height))
    return c


def panel(parent, title):
    f = ctk.CTkFrame(parent, fg_color=P["surface"], corner_radius=14, border_width=1, border_color=P["border"])
    head = ctk.CTkFrame(f, fg_color="transparent")
    head.pack(fill="x", padx=16, pady=(14, 8))
    section(head, title, 15).pack(side="left")
    return f, head


def year_of(s):
    d = parse_date(s)
    return d.year if d else None


def panel_year(parent, app):
    year = date.today().year
    items, act = app.items, app.activity
    added = sum(1 for i in items if i["created"] and datetime.fromtimestamp(i["created"]).year == year)
    started = sum(1 for i in items if year_of(i["started"]) == year)
    done = sum(1 for i in items if i["status"] == "completo" and year_of(i["finished"]) == year)
    f, _ = panel(parent, str(year))
    g = ctk.CTkFrame(f, fg_color="transparent")
    g.pack(fill="x", padx=12)
    cells = [("book", added, "Adicionadas"), ("play", started, "Iniciadas"),
             ("check", done, "Completas"), ("flag", f"{done}/{S['goal']}", "Meta do ano"),
             ("chart", sum_activity(act, str(year), "ch"), "Capítulos lidos"),
             ("clock", fmt_minutes(sum_activity(act, str(year), "min")), "Tempo de leitura")]
    for k, (ic, val, lab) in enumerate(cells):
        c = ctk.CTkFrame(g, fg_color="transparent")
        c.grid(row=k // 2, column=k % 2, sticky="w", padx=6, pady=8)
        ctk.CTkLabel(c, text="", image=icon(ic, 20), width=26).pack(side="left", anchor="n", padx=(0, 8))
        t = ctk.CTkFrame(c, fg_color="transparent")
        t.pack(side="left")
        nl = ctk.CTkLabel(t, text=str(val), text_color=P["text"], font=ctk.CTkFont(size=18, weight="bold"),
                          anchor="w")
        nl.pack(anchor="w")
        animate_number(nl, val)
        ctk.CTkLabel(t, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=12), anchor="w").pack(anchor="w")
    g.grid_columnconfigure((0, 1), weight=1)
    ctk.CTkButton(f, text="Ver biblioteca", image=icon("chevron", 16, P["accent"]), compound="right",
                  fg_color="transparent", hover_color=P["surface2"], text_color=P["accent"], anchor="w",
                  command=lambda: app.nav("library")).pack(fill="x", padx=12, pady=(2, 12))
    return f


def panel_ratings(parent, items):
    rated = [i["rating"] for i in items if i["rating"]]
    f, head = panel(parent, "Avaliações")
    if rated:
        ctk.CTkLabel(head, text=f"({len(rated)})", text_color=P["muted"], font=ctk.CTkFont(size=11)).pack(side="right")
        ctk.CTkLabel(head, text=f"★ {sum(rated) / len(rated):.1f}".replace(".", ","), text_color=GOLD_HEX,
                     font=ctk.CTkFont(size=15, weight="bold")).pack(side="right", padx=6)
    hist(f, [sum(1 for i in items if i["rating"] == (k + 1) / 2) for k in range(10)]).pack(
        fill="x", padx=16, pady=(0, 14))
    return f


def panel_genres(parent, items):
    top = Counter(t for i in items for t in i["tags"]).most_common(5)
    f, _ = panel(parent, "Principais gêneros")
    if len(top) < 3:
        ctk.CTkLabel(f, text="Cadastre pelo menos 3 gêneros diferentes nas suas leituras para ver este gráfico.",
                     text_color=P["muted"], wraplength=280, justify="left").pack(anchor="w", padx=16, pady=(0, 18))
    else:
        mx = top[0][1]
        radar(f, [t for t, _ in top], [n / mx for _, n in top]).pack(fill="x", padx=10, pady=(0, 10))
    return f


def panel_types(parent, items):
    f, _ = panel(parent, "Por tipo")
    bars(f, [(t, sum(1 for i in items if i["type"] == t)) for t in TYPES],
         colors=[type_color(t) for t in TYPES]).pack(fill="x", padx=16, pady=(0, 14))
    return f


def panel_status(parent, items):
    f, _ = panel(parent, "Por status")
    donut(f, [(STATUS[k], sum(1 for i in items if i["status"] == k), P["status"][k]) for k in STATUS]).pack(
        fill="x", padx=16, pady=(0, 14))
    return f


def panel_chapters_month(parent, app):
    f, _ = panel(parent, "Capítulos por mês")
    today = date.today()
    data = []
    for back in range(11, -1, -1):
        mm, yy = today.month - back, today.year
        while mm <= 0:
            mm += 12
            yy -= 1
        data.append((MESES[mm - 1], sum_activity(app.activity, f"{yy:04d}-{mm:02d}", "ch")))
    linechart(f, data).pack(fill="x", padx=16, pady=(0, 14))
    return f


def panel_months(parent, items):
    year = date.today().year
    f, _ = panel(parent, f"Completas por mês em {year}")
    mes = ["J", "F", "M", "A", "M", "J", "J", "A", "S", "O", "N", "D"]
    done = [parse_date(i["finished"]) for i in items if i["status"] == "completo"]
    bars(f, [(m, sum(1 for d in done if d and d.year == year and d.month == n + 1))
             for n, m in enumerate(mes)]).pack(fill="x", padx=16, pady=(0, 6))
    ctk.CTkLabel(f, text="Só entram leituras com data de fim preenchida.", text_color=P["muted"],
                 font=ctk.CTkFont(size=11)).pack(anchor="w", padx=16, pady=(0, 12))
    return f


def panel_goal(parent, app):
    year = date.today().year
    n = sum(1 for i in app.items if i["status"] == "completo" and year_of(i["finished"]) == year)
    f, _ = panel(parent, f"Meta de {year}")
    lbl = ctk.CTkLabel(f, text="", text_color=P["muted"])
    lbl.pack(anchor="w", padx=16)
    bar = ctk.CTkProgressBar(f, height=10, fg_color=P["surface2"], progress_color=P["accent"])
    bar.pack(fill="x", padx=16, pady=8)
    g = ctk.CTkFrame(f, fg_color="transparent")
    g.pack(fill="x", padx=16, pady=(0, 14))
    ctk.CTkLabel(g, text="Meta:", text_color=P["muted"]).pack(side="left")
    ent = entry(g, width=64)
    ent.insert(0, str(S["goal"]))
    ent.pack(side="left", padx=8)

    def show():
        lbl.configure(text=f"{n} de {S['goal']} leituras completas este ano")
        animate_bar(bar, min(1, n / max(1, S["goal"])))

    def setgoal():
        try:
            S["goal"] = max(1, int(ent.get()))
        except ValueError:
            return
        save_settings()
        touch()
        show()

    accent_button(g, "Salvar", setgoal, width=80).pack(side="left")
    show()
    return f


MESES = ["jan", "fev", "mar", "abr", "mai", "jun", "jul", "ago", "set", "out", "nov", "dez"]
MESES_LONGOS = ["janeiro", "fevereiro", "março", "abril", "maio", "junho", "julho", "agosto", "setembro",
                "outubro", "novembro", "dezembro"]


def stat_strip(parent, items, act=None):
    f = ctk.CTkFrame(parent, fg_color=P["surface"], corner_radius=14, border_width=1, border_color=P["border"])
    rated = [i["rating"] for i in items if i["rating"]]
    cells = [("Leituras", len(items)), ("Lendo", sum(1 for i in items if i["status"] == "lendo")),
             ("Completas", sum(1 for i in items if i["status"] == "completo")),
             ("Favoritas", sum(1 for i in items if i["favorite"])),
             ("Capítulos lidos", sum(i["seen"] for i in items)),
             ("Nota média", f"{sum(rated) / len(rated):.1f}".replace(".", ",") if rated else "–")]
    if act is not None:
        cells.append(("Tempo lido", fmt_minutes(sum_activity(act, "", "min"))))
    boxes = []
    for lab, val in cells:
        b = ctk.CTkFrame(f, fg_color="transparent")
        nl = ctk.CTkLabel(b, text=str(val), text_color=P["text"], font=ctk.CTkFont(size=20, weight="bold"))
        nl.pack()
        animate_number(nl, val)
        ctk.CTkLabel(b, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=11)).pack()
        boxes.append(b)

    def relay(e):
        n = balanced_cols(len(boxes), lw(e.width))
        for k, b in enumerate(boxes):
            b.grid_forget()
            b.grid(row=k // n, column=k % n, sticky="ew", padx=6, pady=10)
        for c in range(8):
            f.grid_columnconfigure(c, weight=1 if c < n else 0)

    f.bind("<Configure>", relay)
    return f


def heatmap(parent, act):
    """Calendário de atividade (um quadradinho por dia, estilo GitHub), ajustado à largura do cartão."""
    k = scale_k()
    gap = px(3)
    c = _canvas(parent, int(7 * (px(18) + gap) + 30 * k))
    fs = ("TkDefaultFont", fpt(9))

    def draw(W):
        c.delete("all")
        avail = max(60.0, W - 8 * k)
        weeks = 53
        cell = avail / weeks - gap
        if cell < px(9):
            cell = px(9)
            weeks = max(8, int(avail // (cell + gap)))
        cell = min(cell, px(18))
        c.configure(height=int(7 * (cell + gap) + 30 * k))
        today = date.today()
        start = today - timedelta(days=today.weekday() + 7 * (weeks - 1))
        shades = [mix(P["surface2"], P["accent"], t) for t in (0, .3, .55, .8, 1)]
        last_m = None
        for w in range(weeks):
            for d in range(7):
                day = start + timedelta(days=7 * w + d)
                if day > today:
                    continue
                e = act.get(day.isoformat(), {})
                v = e.get("ch", 0) + e.get("min", 0) / 20
                lv = 0 if v <= 0 else 1 if v < 3 else 2 if v < 6 else 3 if v < 10 else 4
                x, y = 4 * k + w * (cell + gap), 22 * k + d * (cell + gap)
                c.create_rectangle(x, y, x + cell, y + cell, fill=shades[lv], width=0)
            m = (start + timedelta(days=7 * w)).month
            if m != last_m:
                c.create_text(4 * k + w * (cell + gap), 8 * k, text=MESES[m - 1], anchor="w", fill=P["muted"],
                              font=fs)
                last_m = m

    c.bind("<Configure>", lambda e: draw(e.width))
    return c


def panel_activity(parent, app):
    act = app.activity
    cur, longest = streaks(act)
    since = (date.today() - timedelta(days=29)).isoformat()
    last30 = sum(v.get("ch", 0) for k, v in act.items() if k >= since)
    f, _ = panel(parent, "Atividade de leitura")
    row = ctk.CTkFrame(f, fg_color="transparent")
    row.pack(fill="x", padx=12, pady=(0, 6))
    for val, lab in ((f"{cur} dias", "Sequência atual"), (f"{longest} dias", "Maior sequência"),
                     (str(last30), "Capítulos em 30 dias"), (fmt_minutes(sum_activity(act, "", "min")), "Tempo total")):
        c = ctk.CTkFrame(row, fg_color="transparent")
        c.pack(side="left", expand=True, padx=6)
        ctk.CTkLabel(c, text=val, text_color=P["text"], font=ctk.CTkFont(size=20, weight="bold")).pack()
        ctk.CTkLabel(c, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=11)).pack()
    heatmap(f, act).pack(fill="x", padx=16, pady=(4, 14))
    return f


def panel_recent(parent, app):
    f, _ = panel(parent, "Capítulos nos últimos 14 dias")
    today = date.today()
    days = [today - timedelta(days=13 - k) for k in range(14)]
    bars(f, [(str(d.day), app.activity.get(d.isoformat(), {}).get("ch", 0)) for d in days]).pack(
        fill="x", padx=16, pady=(0, 14))
    return f


def panel_criteria(parent, items):
    def avg(vals):
        return round(sum(vals) / len(vals), 1) if vals else 0

    f, _ = panel(parent, "Médias das suas notas")
    data = [("História", avg([i["crit"].get("story", 0) for i in items if i["crit"].get("story")])),
            ("Arte", avg([i["crit"].get("art", 0) for i in items if i["crit"].get("art")])),
            ("Persona.", avg([i["crit"].get("chars", 0) for i in items if i["crit"].get("chars")])),
            ("Geral", avg([i["rating"] for i in items if i["rating"]]))]
    bars(f, data).pack(fill="x", padx=16, pady=(0, 14))
    return f


def panel_review(parent, app):
    f, _ = panel(parent, "Retrospectiva do ano")
    ctk.CTkLabel(f, text="Um resumo do que você leu: melhores leituras, gênero favorito, mês mais ativo e mais.",
                 text_color=P["muted"], wraplength=300, justify="left").pack(anchor="w", padx=16)
    accent_button(f, f"Ver retrospectiva de {date.today().year}", lambda: app.open_sub(YearReviewPage),
                  height=34).pack(anchor="w", padx=16, pady=(10, 14))
    return f


# ---- conquistas ----
BADGES = [
    ("primeira", "Primeira leitura", "Adicione sua primeira leitura à lista", "book", "bronze", "n_items", 1),
    ("completa1", "Primeira completa", "Termine uma leitura", "check", "bronze", "done", 1),
    ("completa10", "Dez completas", "Termine 10 leituras", "check", "prata", "done", 10),
    ("completa50", "Leitor veterano", "Termine 50 leituras", "trophy", "ouro", "done", 50),
    ("meta", "Meta batida", "Bata a meta de leituras completas do ano", "flag", "prata", "done_year", None),
    ("seq7", "Semana inteira", "Leia por 7 dias seguidos", "flame", "prata", "longest", 7),
    ("seq30", "Mês sem parar", "Leia por 30 dias seguidos", "flame", "ouro", "longest", 30),
    ("mes100", "Maratonista", "Leia 100 capítulos em um único mês", "chart", "prata", "best_month", 100),
    ("cap1000", "Mil capítulos", "Some 1000 capítulos lidos", "book", "ouro", "chapters", 1000),
    ("hora10", "Dez horas", "Registre 10 horas no cronômetro de leitura", "clock", "bronze", "hours", 10),
    ("hora100", "Cem horas", "Registre 100 horas no cronômetro de leitura", "clock", "ouro", "hours", 100),
    ("critico", "Crítico", "Dê nota a 10 leituras", "star", "prata", "rated", 10),
    ("ecletico", "Eclético", "Leia 4 tipos diferentes de obra", "library", "prata", "types", 4),
    ("colecao", "Colecionador", "Marque 50 volumes como seus", "library", "prata", "owned", 50),
    ("releitor", "Releitor", "Releia uma obra", "play", "bronze", "rereads", 1),
    ("favoritos", "Coração mole", "Favorite 5 leituras", "heart", "bronze", "favs", 5),
    ("matinal", "Matinal", "Leia de manhã cedo (entre 5h e 9h)", "sun", "bronze", "morning", 1),
    ("dia20", "Dia de foco", "Leia 20 capítulos num único dia", "chart", "bronze", "max_day", 20),
    ("epico200", "Épico", "Termine uma obra com 200 ou mais capítulos", "check", "prata", "big_done", 1),
    ("saga500", "Saga completa", "Termine uma obra com 500 ou mais capítulos", "trophy", "ouro", "huge_done", 1),
    ("cap5000", "Cinco mil capítulos", "Some 5000 capítulos lidos", "book", "ouro", "chapters", 5000),
    ("completa100", "Centenário", "Termine 100 leituras", "crown", "ouro", "done", 100),
    ("completa25", "Quarto de cem", "Termine 25 leituras", "trophy", "prata", "done", 25),
    ("cap10000", "Dez mil capítulos", "Some 10000 capítulos lidos", "crown", "ouro", "chapters", 10000),
    ("hora50", "Cinquenta horas", "Registre 50 horas no cronômetro de leitura", "clock", "prata", "hours", 50),
    ("hora500", "Quinhentas horas", "Registre 500 horas no cronômetro de leitura", "clock", "ouro", "hours", 500),
    ("seq14", "Quinzena", "Leia por 14 dias seguidos", "flame", "prata", "longest", 14),
    ("seq100", "Cem dias", "Leia por 100 dias seguidos", "flame", "ouro", "longest", 100),
    ("mes300", "Maratonista supremo", "Leia 300 capítulos em um único mês", "chart", "ouro", "best_month", 300),
    ("critico50", "Crítico veterano", "Dê nota a 50 leituras", "star", "ouro", "rated", 50),
    ("obraprima", "Obra-prima", "Dê nota 5 a 5 leituras", "gem", "prata", "rated5", 5),
    ("colecao200", "Biblioteca de volumes", "Marque 200 volumes como seus", "library", "ouro", "owned", 200),
    ("semfronteiras", "Sem fronteiras", "Leia os 5 tipos de obra", "target", "ouro", "types", 5),
    ("favoritos20", "Muito amor", "Favorite 20 leituras", "heart", "prata", "favs", 20),
    ("estante100", "Estante cheia", "Tenha 100 leituras na lista", "library", "prata", "n_items", 100),
    ("estante250", "Acervo gigante", "Tenha 250 leituras na lista", "library", "ouro", "n_items", 250),
    ("citacoes10", "Caçador de frases", "Salve 10 citações ou anotações", "quote", "bronze", "quotes", 10),
    ("citacoes50", "Colecionador de frases", "Salve 50 citações ou anotações", "quote", "prata", "quotes", 50),
    ("listas3", "Organizado", "Use 3 listas diferentes", "list", "bronze", "lists", 3),
    ("releitor5", "Fã incondicional", "Some 5 releituras", "play", "prata", "rereads", 5),
    ("explorador", "Explorador de gêneros", "Leia obras de 10 gêneros diferentes", "tag", "prata", "tags", 10),
    ("relampago", "Relâmpago", "Comece e termine uma obra de 20+ capítulos no mesmo dia", "flame", "prata",
     "done_same_day", 1),
    ("velocista", "Velocista", "Termine uma obra de 50+ capítulos em até 7 dias", "flame", "ouro", "done_fast", 1),
    ("multitarefa", "Multitarefa", "Tenha 5 leituras em andamento ao mesmo tempo", "list", "bronze", "n_reading", 5),
    ("terror", "Outubro de terror", "Leia 3 obras de terror ou suspense em outubro", "moon", "prata", "terror_oct", 3),
    ("fimdeano", "Maratona de fim de ano", "Leia 50 capítulos entre 26 e 31 de dezembro", "star", "prata",
     "yearend", 50),
    ("hora1000", "Dedicação total", "Registre 1000 horas no cronômetro de leitura", "clock", "ouro", "hours", 1000),
    ("ultra1000", "Ultramaratonista", "Leia 1000 capítulos de uma única obra", "flame", "ouro", "max_seen", 1000),
    ("enciclopedia", "Enciclopédia de gêneros", "Leia obras de 25 gêneros diferentes", "tag", "ouro", "tags", 25),
    ("diarista", "Diarista", "Escreva 20 anotações no diário das obras", "quote", "prata", "notes", 20),
    ("mesperfeito", "Mês perfeito", "Leia todos os dias de um mês", "star", "ouro", "perfect_month", 1),
    ("fimsemana", "Leitor de fim de semana", "Leia no sábado e no domingo em 4 fins de semana", "sun", "bronze",
     "weekends", 4),
    ("veterano", "Veterano", "Use o app há mais de um ano", "crown", "prata", "age_days", 365),
    ("nemperfeito", "Nem tudo é perfeito", "Dê nota 2 ou menos a 3 leituras", "star", "bronze", "low_rated", 3),
    ("semculpa", "Sem culpa", "Abandone 5 leituras sem remorso", "play", "bronze", "dropped", 5),
    ("persistente", "Persistente", "Retome leituras paradas 3 vezes", "play", "prata", "resumes", 3),
    ("primepica", "Primeira épica", "Ganhe sua primeira carta épica (nota 4,5 ou mais)", "gem", "bronze",
     "epic_cards", 1),
    ("epicas10", "Dez cartas épicas", "Tenha 10 cartas épicas no álbum", "gem", "ouro", "epic_cards", 10),
    ("lendarias3", "Três cartas lendárias", "Tenha 3 cartas lendárias (nota 5)", "crown", "ouro", "legend_cards", 3),
    ("lendarias10", "Dez cartas lendárias", "Tenha 10 cartas lendárias (nota 5)", "crown", "ouro", "legend_cards", 10),
    ("albumfull", "Álbum completo", "Termine todas as leituras da lista (mínimo de 20)", "trophy", "ouro",
     "album_full", 1),
    ("mestre10", "Colecionador de medalhas", "Conquiste 10 medalhas", "trophy", "bronze", "badges", 10),
    ("mestre25", "Mestre das conquistas", "Conquiste 25 medalhas", "trophy", "prata", "badges", 25),
    ("mestre40", "Lenda das conquistas", "Conquiste 40 medalhas", "crown", "ouro", "badges", 40),
    # ---- grande atualização: cartas, citações, perfil e mini janela ----
    ("raras10", "Cartas raras", "Tenha 10 cartas raras ou melhores (nota 3,5 ou mais)", "gem", "bronze",
     "rare_cards", 10),
    ("raras30", "Álbum brilhante", "Tenha 30 cartas raras ou melhores", "gem", "prata", "rare_cards", 30),
    ("epicas25", "Vinte e cinco épicas", "Tenha 25 cartas épicas no álbum", "gem", "ouro", "epic_cards", 25),
    ("lendarias25", "Panteão", "Tenha 25 cartas lendárias (nota 5)", "crown", "ouro", "legend_cards", 25),
    ("completa200", "Bicentenário", "Termine 200 leituras", "crown", "ouro", "done", 200),
    ("fraseamada", "Frase favorita", "Marque uma citação como favorita", "quote", "bronze", "fav_quotes", 1),
    ("frases10", "Antologia", "Tenha uma citação favorita em 10 obras", "quote", "prata", "fav_quotes", 10),
    ("critico3d", "Olhar completo", "Avalie história, arte e personagens em 5 obras", "star", "prata",
     "crit_full", 5),
    ("critico3d25", "Crítico detalhista", "Avalie história, arte e personagens em 25 obras", "star", "ouro",
     "crit_full", 25),
    ("titulado", "Com título", "Escolha um título para o seu perfil", "trophy", "bronze", "title_set", 1),
    ("perfilcara", "Cara de perfil", "Coloque avatar e banner no seu perfil", "user", "bronze", "customized", 1),
    ("vitrine3", "Vitrine completa", "Deixe 3 medalhas na vitrine do perfil", "crown", "bronze", "showcase", 3),
    ("minijanela", "Olhar de canto", "Abra a mini janela", "clock", "bronze", "mini_uses", 1),
    ("minijanela50", "Sempre à mão", "Abra a mini janela 50 vezes", "clock", "prata", "mini_uses", 50),
    ("divulgador", "Divulgador", "Salve uma imagem de compartilhar (perfil ou obra)", "share", "bronze",
     "shares", 1),
    ("divulgador10", "Influenciador", "Salve 10 imagens de compartilhar", "share", "prata", "shares", 10),
    ("metadia7", "Meta em dia", "Bata a meta diária de capítulos em 7 dias", "target", "bronze", "daily_hit", 7),
    ("metadia30", "Meta de ferro", "Bata a meta diária de capítulos em 30 dias", "target", "prata", "daily_hit", 30),
    ("metadia100", "Meta inabalável", "Bata a meta diária de capítulos em 100 dias", "target", "ouro",
     "daily_hit", 100),
    ("listas10", "Curador de listas", "Use 10 listas diferentes", "list", "prata", "lists", 10),
]


SECRET_BADGES = [
    ("coruja", "Coruja", "Leia de madrugada (entre meia-noite e 5h)", "moon", "prata", "night", 1),
    ("maratona50", "Maratona", "Leia 50 capítulos num único dia", "chart", "ouro", "max_day", 50),
    ("trinca", "Trinca", "Termine 3 obras na mesma semana", "check", "ouro", "week_done", 3),
    ("anonovo", "Ano novo, leitura nova", "Leia no dia 1º de janeiro", "star", "prata", "newyear", 1),
    ("natal", "Leitura de Natal", "Leia no dia 25 de dezembro", "gem", "prata", "christmas", 1),
    ("coruja20", "Coruja veterana", "Leia 20 capítulos de madrugada", "moon", "ouro", "night", 20),
    ("voltaporcima", "Volta por cima", "Retome uma leitura parada há mais de 1 ano", "play", "ouro", "comeback", 1),
    ("domingo", "Domingo de leitura", "Leia 30 capítulos num domingo", "sun", "prata", "sunday", 30),
    ("sexta13", "Sexta-feira 13", "Leia numa sexta-feira 13", "gem", "prata", "friday13", 1),
    ("sortudo", "Sorte de principiante", "Dê nota 5 à primeira obra que você completar", "star", "prata",
     "first5", 1),
    ("mini200", "Janela viciada", "Abra a mini janela 200 vezes", "clock", "ouro", "mini_uses", 200),
    ("foto50", "Fotógrafo", "Salve 50 imagens de compartilhar", "share", "ouro", "shares", 50),
]

LEGENDARY = {"albumfull", "lendarias10", "hora1000", "mestre40", "seq100", "hora500", "completa100", "estante250", "cap10000", "saga500", "coruja20", "semfronteiras",
             "mes300", "voltaporcima", "completa200", "lendarias25"}
RARITY = {"Comum": "#9296c0", "Rara": "#4dd0e1", "Épica": "#b86bff", "Lendária": "#ffc233"}
CATS = ["Leitura", "Tempo", "Sequências", "Coleção", "Avaliação", "Datas"]
KEY_CAT = {"done": "Leitura", "done_year": "Leitura", "big_done": "Leitura", "huge_done": "Leitura",
           "chapters": "Leitura", "max_day": "Leitura", "best_month": "Leitura", "week_done": "Leitura",
           "done_same_day": "Leitura", "done_fast": "Leitura", "n_reading": "Leitura", "types": "Leitura",
           "tags": "Leitura", "rereads": "Leitura", "hours": "Tempo", "morning": "Tempo", "night": "Tempo",
           "longest": "Sequências", "comeback": "Sequências", "n_items": "Coleção", "owned": "Coleção",
           "lists": "Coleção", "rated": "Avaliação", "rated5": "Avaliação", "quotes": "Avaliação",
           "favs": "Avaliação", "newyear": "Datas", "christmas": "Datas", "terror_oct": "Datas",
           "yearend": "Datas", "sunday": "Datas", "friday13": "Datas",
           "max_seen": "Leitura", "notes": "Avaliação", "perfect_month": "Sequências", "weekends": "Datas",
           "age_days": "Datas", "low_rated": "Avaliação", "dropped": "Coleção", "resumes": "Sequências",
           "badges": "Coleção", "epic_cards": "Coleção", "legend_cards": "Coleção", "album_full": "Coleção",
           "rare_cards": "Coleção", "fav_quotes": "Avaliação", "crit_full": "Avaliação", "title_set": "Coleção",
           "customized": "Coleção", "showcase": "Coleção", "mini_uses": "Tempo", "shares": "Coleção",
           "daily_hit": "Sequências", "first5": "Avaliação"}
FAMILY = {"chapters": "Capítulos lidos", "hours": "Horas de leitura", "done": "Leituras completas",
          "longest": "Dias seguidos", "best_month": "Capítulos no mês", "rated": "Notas dadas",
          "favs": "Favoritas", "owned": "Volumes", "n_items": "Tamanho da lista", "quotes": "Citações",
          "rereads": "Releituras"}


BADGE_TITLES = {
    "primeira": "Novato curioso", "completa1": "Finalizador", "completa10": "Terminador",
    "completa25": "Veterano das páginas", "completa50": "Leitor veterano", "completa100": "Centurião",
    "meta": "Cumpridor de metas", "seq7": "Constante", "seq14": "Disciplinado", "seq30": "Imparável",
    "seq100": "Inabalável", "mes100": "Maratonista", "mes300": "Titã dos capítulos", "cap1000": "Milheiro",
    "cap5000": "Devorador de séries", "cap10000": "Lenda dos capítulos", "hora10": "Cronometrista",
    "hora50": "Dedicado", "hora100": "Mestre do tempo", "hora500": "Senhor do tempo",
    "hora1000": "Eterno leitor", "critico": "Crítico", "critico50": "Crítico veterano", "obraprima": "Olho de ouro",
    "ecletico": "Eclético", "semfronteiras": "Sem fronteiras", "colecao": "Colecionador",
    "colecao200": "Bibliotecário", "releitor": "Releitor", "releitor5": "Fã incondicional",
    "favoritos": "Coração mole", "favoritos20": "Apaixonado", "matinal": "Madrugador", "dia20": "Focado",
    "epico200": "Épico", "saga500": "Saga viva", "estante100": "Estante cheia", "estante250": "Curador",
    "citacoes10": "Caçador de frases", "citacoes50": "Poeta da estante", "listas3": "Organizado",
    "explorador": "Explorador", "relampago": "Relâmpago", "velocista": "Velocista", "multitarefa": "Malabarista",
    "terror": "Filho das trevas", "fimdeano": "Fim de ano sem pausa", "ultra1000": "Ultramaratonista",
    "enciclopedia": "Enciclopédia viva", "diarista": "Diarista", "mesperfeito": "Mês perfeito",
    "fimsemana": "Leitor de domingo", "veterano": "Veterano do app", "nemperfeito": "Crítico sincero",
    "semculpa": "Sem culpa", "persistente": "Persistente", "mestre10": "Caçador de medalhas",
    "primepica": "Carta na manga", "epicas10": "Mestre das cartas",
    "raras10": "Colecionador de raridades", "raras30": "Álbum brilhante", "epicas25": "Rei das épicas",
    "lendarias25": "Panteão vivo", "completa200": "Bicentenário", "fraseamada": "Amante de frases",
    "frases10": "Antologista", "critico3d": "Olhar completo", "critico3d25": "Crítico detalhista",
    "titulado": "Com título", "perfilcara": "Cara de perfil", "vitrine3": "Vitrine cheia",
    "minijanela": "Olhar de canto", "minijanela50": "Sempre à mão", "divulgador": "Divulgador",
    "divulgador10": "Influenciador", "metadia7": "Meta em dia", "metadia30": "Meta de ferro",
    "metadia100": "Inabalável da meta", "listas10": "Curador de listas",
    "sortudo": "Sortudo", "mini200": "Janela viciada", "foto50": "Fotógrafo", "lendarias3": "Dono de lendas",
    "lendarias10": "Lenda viva", "albumfull": "Completista", "mestre25": "Mestre das conquistas", "mestre40": "Lenda das conquistas",
    "coruja": "Coruja", "maratona50": "Maratonista de um dia", "trinca": "Trinca de ases",
    "anonovo": "Ano novo, vida nova", "natal": "Espírito natalino", "coruja20": "Coruja veterana",
    "voltaporcima": "Volta por cima", "domingo": "Domingueiro", "sexta13": "Azarão"}


def badge_rarity(b):
    return "Lendária" if b["id"] in LEGENDARY else {"bronze": "Comum", "prata": "Rara", "ouro": "Épica"}[b["tier"]]


def _wd(k):
    try:
        return date.fromisoformat(k).weekday()
    except ValueError:
        return -1


def _yearend(act):
    out = Counter()
    for k, v in act.items():
        if k[5:7] == "12" and k[8:10] >= "26":
            out[k[:4]] += v.get("ch", 0)
    return out


def badge_status(app):
    items, act = app.items, app.activity
    dates = app.profile.get("badge_dates", {})
    year = date.today().year
    months = Counter()
    for k, v in act.items():
        months[k[:7]] += v.get("ch", 0)
    weeks = Counter()
    for i in items:
        d = parse_date(i["finished"]) if i["status"] == "completo" else None
        if d:
            weeks[tuple(d.isocalendar())[:2]] += 1
    ctx = dict(
        n_items=len(items), done=sum(1 for i in items if i["status"] == "completo"),
        done_year=sum(1 for i in items if i["status"] == "completo" and year_of(i["finished"]) == year),
        longest=streaks(act)[1], best_month=max(list(months.values()) or [0]),
        chapters=sum(i["seen"] for i in items), hours=sum_activity(act, "", "min") / 60,
        rated=sum(1 for i in items if i["rating"]), types=len({i["type"] for i in items if i["seen"] > 0}),
        owned=sum(len(i["vol_owned"]) for i in items), rereads=sum(i["rereads"] for i in items),
        favs=sum(1 for i in items if i["favorite"]),
        night=sum_activity(act, "", "night"), morning=sum_activity(act, "", "morning"),
        big_done=sum(1 for i in items if i["status"] == "completo" and max(i["total"], i["seen"]) >= 200),
        huge_done=sum(1 for i in items if i["status"] == "completo" and max(i["total"], i["seen"]) >= 500), max_day=max([v.get("ch", 0) for v in act.values()] or [0]),
        week_done=max(list(weeks.values()) or [0]),
        quotes=sum(len(i["quotes"]) for i in items), lists=len({n for i in items for n in i["lists"]}),
        tags=len({t.strip().lower() for i in items if i["seen"] > 0 for t in i["tags"] if t.strip()}),
        rated5=sum(1 for i in items if i["rating"] >= 5),
        christmas=1 if any(k.endswith("-12-25") and (v.get("ch", 0) > 0 or v.get("min", 0) > 0)
                           for k, v in act.items()) else 0,
        done_same_day=sum(1 for i in items if i["status"] == "completo" and max(i["total"], i["seen"]) >= 20
                          and parse_date(i["started"]) and parse_date(i["started"]) == parse_date(i["finished"])),
        done_fast=sum(1 for i in items if i["status"] == "completo" and max(i["total"], i["seen"]) >= 50
                      and parse_date(i["started"]) and parse_date(i["finished"])
                      and 0 <= (parse_date(i["finished"]) - parse_date(i["started"])).days <= 7),
        n_reading=sum(1 for i in items if i["status"] == "lendo"),
        comeback=1 if any(e["kind"] == "resume" and n > 0 and e["ts"] - ev[n - 1]["ts"] >= 365 * 86400
                          for i in items for ev in [sorted(i.get("history", []), key=lambda e: e["ts"])]
                          for n, e in enumerate(ev)) else 0,
        terror_oct=sum(1 for i in items if i["seen"] > 0
                       and any(t.strip().lower() in ("terror", "horror", "suspense") for t in i["tags"])
                       and any(d_ and d_.month == 10 for d_ in (parse_date(i["started"]), parse_date(i["finished"])))),
        yearend=max(list(_yearend(act).values()) or [0]),
        sunday=max([v.get("ch", 0) for k, v in act.items() if _wd(k) == 6] or [0]),
        friday13=1 if any(_wd(k) == 4 and k.endswith("-13") and (v.get("ch", 0) > 0 or v.get("min", 0) > 0)
                          for k, v in act.items()) else 0,
        newyear=1 if any(k.endswith("-01-01") and (v.get("ch", 0) > 0 or v.get("min", 0) > 0)
                         for k, v in act.items()) else 0)
    adays = active_days(act)
    pm = Counter((d_.year, d_.month) for d_ in adays)
    created = [i["created"] for i in items if i.get("created")]
    wk = Counter()
    for d_ in adays:
        if d_.weekday() == 5 and (d_ + timedelta(days=1)) in adays:
            wk[d_] += 1
    ctx.update(
        max_seen=max([i["seen"] for i in items] or [0]),
        notes=sum(1 for i in items for q in i.get("quotes", []) if q.get("kind") == "nota"),
        perfect_month=1 if any(n >= calendar.monthrange(y_, m_)[1] for (y_, m_), n in pm.items()) else 0,
        weekends=len(wk),
        age_days=(date.today() - datetime.fromtimestamp(min(created)).date()).days if created else 0,
        low_rated=sum(1 for i in items if 0 < i["rating"] <= 2),
        epic_cards=sum(1 for i in items if i["status"] == "completo" and i["rating"] >= 4.5),
        legend_cards=sum(1 for i in items if i["status"] == "completo" and i["rating"] >= 5),
        album_full=1 if len(items) >= 20 and all(i["status"] == "completo" for i in items) else 0,
        dropped=sum(1 for i in items if i["status"] == "largado"),
        rare_cards=sum(1 for i in items if i["status"] == "completo" and i["rating"] >= 3.5),
        fav_quotes=sum(1 for i in items if any(q.get("fav") and q.get("kind", "citação") == "citação"
                                               for q in i.get("quotes", []))),
        crit_full=sum(1 for i in items if isinstance(i.get("crit"), dict)
                      and all(i["crit"].get(k_) for k_ in ("story", "art", "chars"))),
        title_set=1 if app.profile.get("title") else 0,
        customized=1 if app.profile.get("avatar") and app.profile.get("banner") else 0,
        showcase=len(app.profile.get("showcase", [])),
        mini_uses=app.profile.get("usage", {}).get("mini", 0),
        shares=app.profile.get("usage", {}).get("share", 0),
        daily_hit=sum(1 for v in act.values() if v.get("ch", 0) >= max(1, S.get("daily", 5))),
        first5=1 if next(iter(sorted((i for i in items if i["status"] == "completo"),
                                     key=lambda i: (parse_date(i["finished"]) or date.max))), {}).get("rating", 0)
                 >= 5 else 0,
        resumes=sum(1 for i in items for e in i.get("history", []) if e.get("kind") == "resume"),
        badges=0)
    ctx["badges"] = sum(1 for lst in (BADGES, SECRET_BADGES) for b_ in lst if b_[5] != "badges"
                        and ctx[b_[5]] >= (b_[6] if b_[6] is not None else max(1, S["goal"])))
    out = []
    for secret, lst in ((False, BADGES), (True, SECRET_BADGES)):
        for bid, title, desc, ic, tier, key, need in lst:
            need = need if need is not None else max(1, S["goal"])
            have = ctx[key]
            out.append(dict(id=bid, title=title, desc=desc, icon=ic, tier=tier, have=have, need=need,
                            earned=have >= need, secret=secret, key=key, cat=KEY_CAT.get(key, "Leitura"),
                            date=dates.get(bid, ""), ptitle=BADGE_TITLES.get(bid, title)))
    return out


def badge_status_cached(app):
    c = getattr(app, "_bs_cache", None)
    if c and c[0] == DATA["v"]:
        return c[1]
    r = badge_status(app)
    app._bs_cache = (DATA["v"], r)
    return r


def showcase_badges(app):
    by = {b["id"]: b for b in badge_status_cached(app)}
    return [by[i] for i in app.profile.get("showcase", []) if i in by and by[i]["earned"]][:3]


def fmt_badge_date(iso):
    try:
        return date.fromisoformat(iso).strftime("%d/%m/%Y")
    except ValueError:
        return ""


def panel_badges(parent, app, limit=8):
    st = badge_status(app)
    visible = [b for b in st if not b["secret"] or b["earned"]]
    hidden = len(st) - len(visible)
    got = sum(1 for b in visible if b["earned"])
    f, head = panel(parent, "Conquistas")
    ctk.CTkLabel(head, text=f"{got} de {len(visible)}", text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(
        side="right")
    g = ctk.CTkFrame(f, fg_color="transparent")
    g.pack(fill="x", padx=10)
    for k, b in enumerate(sorted(visible, key=lambda b: not b["earned"])[:limit]):
        c = ctk.CTkFrame(g, fg_color="transparent")
        c.grid(row=k // 4, column=k % 4, padx=4, pady=6)
        ctk.CTkLabel(c, text="", image=badge_img(b["icon"], b["tier"], b["earned"], 52)).pack()
        ctk.CTkLabel(c, text=b["title"], text_color=P["text"] if b["earned"] else P["muted"], wraplength=70,
                     font=ctk.CTkFont(size=10)).pack()
    for c in range(4):
        g.grid_columnconfigure(c, weight=1)
    if hidden:
        ctk.CTkLabel(f, text=f"+ {hidden} conquistas secretas por descobrir", text_color=P["muted"],
                     font=ctk.CTkFont(size=11)).pack(anchor="w", padx=16, pady=(2, 0))
    ctk.CTkButton(f, text="Ver todas as conquistas", image=icon("chevron", 16, P["accent"]), compound="right",
                  fg_color="transparent", hover_color=P["surface2"], text_color=P["accent"], anchor="w",
                  command=lambda: app.open_sub(BadgesPage)).pack(fill="x", padx=12, pady=(2, 12))
    return f


# ---- nível de leitor ----
LEVEL_TITLES = [(1, "Iniciante"), (5, "Leitor"), (10, "Devorador de capítulos"), (20, "Mestre da estante"),
                (35, "Lenda"), (40, "Guardião das Histórias"), (50, "Mestre dos Capítulos"),
                (60, "Sábio dos Volumes"), (70, "Arquivista Lendário"), (80, "Oráculo das Páginas"),
                (90, "Guardião da Grande Biblioteca"), (100, "Bibliotecário Supremo")]
LEVEL_COLORS = [(1, "#9296c0"), (5, "#cd7f32"), (10, "#c3cad9"), (20, "#ffc233"), (35, "#ff5c8a"),
                (50, "#b86bff"), (70, "#4dd0e1"), (90, "#7cf0a8"), (100, "#ffe27a")]


def display_title(app, lv):
    """(texto, cor) do título mostrado no perfil: o escolhido nas conquistas ou o do nível."""
    bid = app.profile.get("title", "")
    if bid:
        try:
            b = next((b for b in badge_status_cached(app) if b["id"] == bid and b["earned"]), None)
        except Exception:
            b = None
        if b:
            return b["ptitle"], RARITY[badge_rarity(b)]
    return lv["title"], lv["color"]


def xp_breakdown(app):
    items, act = app.items, app.activity
    parts = [("Capítulos lidos", sum(i["seen"] for i in items) * 10),
             ("Tempo de leitura", sum_activity(act, "", "min") * 2),
             ("Leituras completas", sum(1 for i in items if i["status"] == "completo") * 150),
             ("Conquistas", sum(1 for b in badge_status(app) if b["earned"]) * 100),
             ("Citações e notas", sum(len(i.get("quotes", [])) for i in items) * 5)]
    return parts, sum(v for _, v in parts)


def level_info(xp):
    xp = max(0, int(xp))
    L = int(math.sqrt(xp / 60)) + 1
    cur, nxt = 60 * (L - 1) ** 2, 60 * L ** 2
    title = [t for lvl, t in LEVEL_TITLES if L >= lvl][-1]
    col = [c for lvl, c in LEVEL_COLORS if L >= lvl][-1]
    return dict(level=L, title=title, color=col, cur=cur, nxt=nxt, xp=xp, frac=(xp - cur) / (nxt - cur))


def panel_level(parent, app):
    parts, xp = xp_breakdown(app)
    lv = level_info(xp)
    f, _ = panel(parent, "Nível de leitor")
    r = ctk.CTkFrame(f, fg_color="transparent")
    r.pack(fill="x", padx=16)
    ctk.CTkLabel(r, text=f"  Nível {lv['level']}  ", fg_color=lv["color"], text_color="#14120a", corner_radius=10,
                 height=30, font=ctk.CTkFont(size=15, weight="bold")).pack(side="left")
    ctk.CTkLabel(r, text=lv["title"], text_color=P["text"], font=ctk.CTkFont(size=15, weight="bold")).pack(
        side="left", padx=10)
    bar = ctk.CTkProgressBar(f, height=8, fg_color=P["surface2"], progress_color=lv["color"])
    bar.pack(fill="x", padx=16, pady=(10, 4))
    animate_bar(bar, lv["frac"])
    ctk.CTkLabel(f, text=f"{xp - lv['cur']} / {lv['nxt'] - lv['cur']} XP para o nível {lv['level'] + 1}",
                 text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(anchor="w", padx=16)
    box = ctk.CTkFrame(f, fg_color="transparent")
    box.pack(fill="x", padx=16, pady=(8, 14))
    for lab, v in parts:
        row = ctk.CTkFrame(box, fg_color="transparent")
        row.pack(fill="x", pady=1)
        ctk.CTkLabel(row, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(side="left")
        ctk.CTkLabel(row, text=f"+{v} XP", text_color=P["text"], font=ctk.CTkFont(size=12, weight="bold")).pack(
            side="right")
    return f


# ---- estante virtual ----
def spine_dims(it, k):
    n = max(it.get("total") or 0, it["seen"], 12)
    w = int((32 + min(n, 240) / 8) * k)
    h = int((190 + (sum(ord(c) for c in it["title"]) % 6) * 10) * k)
    return w, h


def text_on(color):
    r, g, b = (int(color.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4))
    return "#14120a" if 0.299 * r + 0.587 * g + 0.114 * b > 150 else "#ffffff"


def shelf_label(title, w, k):
    """Lombada fina: só a primeira palavra (ou sigla); o nome completo vai no tooltip."""
    return title          # o nome completo (cortado com … só se não couber)
    words = [x for x in re.split(r"\s+", title.strip()) if x]
    if not words:
        return title
    first = words[0]
    if len(first) <= 3 and len(words) > 1:
        return "".join(x[0] for x in words[:3]).upper()
    return first


_SPINE = OrderedDict()


def spine_art(it, w, h, k, col, cover):
    """Lombada ilustrada: um recorte da capa (como um marcador de página), escurecido e com relevo."""
    key = (it["id"], w, h, col)
    got = _SPINE.get(key)
    if got is not None:
        _SPINE.move_to_end(key)
        return got
    try:
        art = ImageOps.fit(cover(it).convert("RGB"), (w, h), centering=(0.5, 0.28))
    except Exception:
        return None
    art = Image.blend(art, Image.new("RGB", (w, h), "#000000"), .22)
    shade = Image.new("L", (w, 1))                       # arredondado: claro no meio, escuro nas bordas
    for xx in range(w):
        t_ = abs((xx + .5) / w - .5) * 2
        shade.putpixel((xx, 0), int(70 * t_ ** 2))
    shade = shade.resize((w, h))
    art = Image.composite(Image.new("RGB", (w, h), "#000000"), art, shade)
    d = ImageDraw.Draw(art, "RGBA")
    for y0, y1 in ((int(10 * k), int(14 * k)), (h - int(14 * k), h - int(10 * k))):   # faixas douradas/escuras
        d.rectangle([0, y0, w, y1], fill=(0, 0, 0, 120))
        d.line([(0, y0), (w, y0)], fill=(255, 255, 255, 40), width=1)
    _SPINE[key] = art
    while len(_SPINE) > 120:
        _SPINE.popitem(last=False)
    return art


def shelf_pil(entries, width, k, pull=None, cover=None):
    """Estante com lombadas. entries = [(leitura, cor)]. Devolve (imagem, [(x0, y0, x1, y1, leitura)])."""
    margin, gap, plank = int(18 * k), int(4 * k), int(16 * k)
    rows, cur, x = [], [], margin
    for it, col in entries:
        w, h = spine_dims(it, k)
        if cur and x + w > width - margin:
            rows.append(cur)
            cur, x = [], margin
        cur.append((it, col, w, h))
        x += w + gap
    if cur:
        rows.append(cur)
    rows = rows[:5]
    heights = [max(h for _, _, _, h in r) for r in rows] or [int(120 * k)]
    total = sum(heights) + max(1, len(rows)) * (plank + int(14 * k)) + int(10 * k)
    img = Image.new("RGB", (width, total), P["surface"])
    d = ImageDraw.Draw(img)
    hits, y = [], int(10 * k)
    pull_px = int(10 * k)
    for r, row in enumerate(rows or [[]]):
        base = y + heights[r]
        x = margin
        for it, col, w, h in row:
            col = mix(col, "#000000", .12)
            out_ = pull_px if (pull is not None and it["id"] == pull) else 0
            if out_:
                col = mix(col, "#ffffff", .14)
            top = base - h - out_
            if out_:
                d.rounded_rectangle([x + int(3 * k), top + int(5 * k), x + w + int(3 * k), base + int(3 * k)],
                                    radius=int(4 * k), fill=mix(P["surface"], "#000000", .45))
            hh = h + out_                                    # a lombada puxada fica mais alta (sem vão embaixo)
            art = spine_art(it, w, hh, k, col, cover) if cover else None
            if art is not None:
                tile = art if not out_ else Image.blend(art, Image.new("RGB", art.size, "#ffffff"), .12)
                mask = Image.new("L", art.size, 0)
                ImageDraw.Draw(mask).rounded_rectangle([0, 0, w - 1, hh - 1], radius=int(4 * k), fill=255)
                img.paste(tile, (x, top), mask)
                d.rounded_rectangle([x, top, x + w, base], radius=int(4 * k), outline=mix(col, "#000000", .5),
                                    width=max(1, int(k)))
            else:
                d.rounded_rectangle([x, top, x + w, base], radius=int(4 * k), fill=col)
                band = mix(col, "#000000", .28)
                d.rectangle([x, top + int(10 * k), x + w, top + int(14 * k)], fill=band)
                d.rectangle([x, base - int(14 * k), x + w, base - int(10 * k)], fill=band)
            fs = max(int(11 * k), int(min(w * 0.40, 15 * k)))
            txt = _fit_text(d, shelf_label(it["title"], w, k), get_font(fs, True), h - int(50 * k))
            font2 = get_font(fs * 2, True)             # desenha em dobro e reduz: letras suaves, sem serrilhado
            try:
                l, t_, rr, bb = d.textbbox((0, 0), txt, font=font2)
                tw_, th_ = rr - l + 8, bb - t_ + 10
            except Exception:
                l, t_, tw_, th_ = 0, 0, 120, 32
            tim = Image.new("RGBA", (max(1, tw_), max(1, th_)), (0, 0, 0, 0))
            if art is not None:                          # texto branco com contorno escuro: lê bem sobre qualquer arte
                ImageDraw.Draw(tim).text((4 - l, 4 - t_), txt, font=font2, fill="#ffffff", stroke_width=4,
                                         stroke_fill="#0a0a10")
            else:
                ImageDraw.Draw(tim).text((4 - l, 4 - t_), txt, font=font2, fill=text_on(col))
            tim = tim.rotate(270, expand=True, resample=Image.BICUBIC)
            tim = tim.resize((max(1, tim.size[0] // 2), max(1, tim.size[1] // 2)), Image.LANCZOS)
            img.paste(tim, (x + (w - tim.size[0]) // 2, top + int(20 * k)), tim)
            gem = max(2, int(3 * k))                    # brilhinho no topo da lombada
            d.ellipse([x + w // 2 - gem, top + int(5 * k) - gem // 2, x + w // 2 + gem, top + int(5 * k) + gem + gem // 2],
                      fill=mix(col, "#ffffff", .6))
            hits.append((x, base - h, x + w, base, it))
            x += w + gap
        d.rectangle([margin // 2, base, width - margin // 2, base + plank], fill=mix(P["surface2"], P["text"], .12))
        d.line([(margin // 2, base), (width - margin // 2, base)], fill=mix(P["surface2"], P["text"], .3),
               width=max(1, int(2 * k)))
        y = base + plank + int(14 * k)
    return img, hits


# ---- tier list ----
TIERS = ["S", "A", "B", "C", "D"]
TIER_COLORS = {"S": "#ff7f7f", "A": "#ffbf7f", "B": "#ffdf7f", "C": "#bfff7f", "D": "#7fbfff"}


def make_tier_image(app, path):
    """Imagem da tier list (1080 px de largura; a altura se ajusta ao número de obras)."""
    W = 1080
    pal, accent = DARK, S["accent"]
    bg = pal["bg"]
    tiers = app.profile.get("tiers", {})
    by_id = {i["id"]: i for i in app.items}
    cw, ch, gap, lab_w = 112, 156, 12, 150
    per_row = max(1, (W - 64 - lab_w - 24) // (cw + gap))
    rows = []
    for t in TIERS:
        ids = [x for x in tiers.get(t, []) if x in by_id]
        rows.append((t, ids, max(1, -(-len(ids) // per_row))))
    head_h = 190
    H = head_h + sum(n * (ch + gap) + gap + 24 for _, _, n in rows) + 110
    img = Image.new("RGB", (W, H), bg)
    d = ImageDraw.Draw(img)

    def T(xy, text, size, fill, bold=False, anchor="la"):
        font = get_font(size, bold)
        try:
            d.text(xy, text, font=font, fill=fill, anchor=anchor)
        except (TypeError, ValueError):
            d.text(xy, text, font=font, fill=fill)

    logo = logo_pil(76, accent)
    img.paste(logo, (40, 52), logo)
    T((136, 44), "Minha Tier List", 66, pal["text"], True)
    T((138, 124), f"por {app.profile['name']}", 30, accent)
    rmask = Image.new("L", (cw * 4, ch * 4), 0)
    ImageDraw.Draw(rmask).rounded_rectangle([0, 0, cw * 4 - 1, ch * 4 - 1], radius=64, fill=255)
    rmask = rmask.resize((cw, ch), Image.LANCZOS)
    y = head_h
    for t, ids, n_lines in rows:
        rh = n_lines * (ch + gap) + gap + 12
        d.rounded_rectangle([32, y, W - 32, y + rh], radius=22, fill=pal["surface"], outline=pal["border"], width=2)
        d.rounded_rectangle([32, y, 32 + lab_w, y + rh], radius=22, fill=TIER_COLORS[t])
        d.rectangle([32 + lab_w - 30, y, 32 + lab_w, y + rh], fill=TIER_COLORS[t])
        T((32 + lab_w / 2, y + rh / 2), t, 86, "#1a1206", True, "mm")
        for n, id_ in enumerate(ids):
            it = by_id[id_]
            r, c = divmod(n, per_row)
            x, yy = 32 + lab_w + 24 + c * (cw + gap), y + gap + 6 + r * (ch + gap)
            try:
                cp = covers_dir() / it["cover"] if it.get("cover") else None
                cov = Image.open(cp).convert("RGB") if cp and cp.exists() else placeholder(it["title"])
            except OSError:
                cov = placeholder(it["title"])
            cov = ImageOps.fit(cov.convert("RGB"), (cw * 2, ch * 2))
            if it["rating"]:
                cov = overlay_chips(cov, [("bl", f"{it['rating']:g}".replace(".", ","), "gold")])
            img.paste(cov.convert("RGB").resize((cw, ch), Image.LANCZOS), (x, yy), rmask)
        y += rh + 12
    d.line([(40, H - 92), (W - 40, H - 92)], fill=pal["border"], width=2)
    T((40, H - 70), "Leitura Foda", 36, accent, True)
    T((W - 40, H - 66), str(date.today().year), 30, pal["muted"], False, "ra")
    img.save(path, "PNG")


def best_quote(it):
    """Citação com estrela; senão a citação mais recente. Anotações (tipo “nota”) nunca entram."""
    qs = [q for q in (it.get("quotes") or []) if q.get("kind") == "citação" and (q.get("text") or "").strip()]
    if not qs:
        return None
    return max([q for q in qs if q.get("fav")] or qs, key=lambda q: q.get("ts", 0))


def make_work_card(app, it, path):
    """Imagem 1080x1440 de uma leitura só (capa empilhada, título, nota, situação e citação) para postar."""
    W, H = 1080, 1440
    acc = app.item_color(it)
    if not isinstance(acc, str) or not acc.startswith("#"):
        acc = S["accent"]
    ar = hex_rgba(acc, 255)[:3]
    navy = "#0b0f1d"
    cov = app._load_cover(it).convert("RGB")
    # fundo: capa desfocada e escurecida + vinheta
    back = ImageOps.fit(cov, (W, H)).filter(ImageFilter.GaussianBlur(34))
    back = Image.blend(back, Image.new("RGB", (W, H), navy), .74)
    vg = Image.new("L", (1, H))
    for y in range(H):
        t = y / H
        vg.putpixel((0, y), int(235 * max(max(0, 1 - t / .22) ** 1.5, max(0, (t - .72) / .28) ** 1.3)))
    img = Image.composite(Image.new("RGB", (W, H), "#05070f"), back, vg.resize((W, H))).convert("RGBA")
    glow = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ImageDraw.Draw(glow).ellipse([-200, 120, 620, 900], fill=ar + (70,))
    img = Image.alpha_composite(img, glow.filter(ImageFilter.GaussianBlur(120)))
    d = ImageDraw.Draw(img)

    def T(xy, text, size, fill, bold=False, anchor="la"):
        font = get_font(size, bold)
        try:
            d.text(xy, text, font=font, fill=fill, anchor=anchor)
        except (TypeError, ValueError):
            d.text(xy, text, font=font, fill=fill)

    # capa: pilha de cartões inclinados com contorno
    cw, ch = 380, 560
    cx, cy = 70 + 20, 170
    cover = ImageOps.fit(cov, (cw, ch))

    def tile(angle, dark, outline_a):
        m = rounded(cover, 26).convert("RGBA")
        if dark:
            m = Image.alpha_composite(m, Image.new("RGBA", m.size, (6, 9, 18, int(255 * dark))))
        ImageDraw.Draw(m).rounded_rectangle([1, 1, cw - 2, ch - 2], radius=26, outline=ar + (outline_a,), width=4)
        return m.rotate(angle, resample=Image.BICUBIC, expand=True)

    for ang, dx, dy, dk, oa in ((9, 46, 26, .62, 150), (-8, -30, 34, .5, 190)):
        t_ = tile(ang, dk, oa)
        img.alpha_composite(t_, (cx + dx + (cw - t_.width) // 2, cy + dy + (ch - t_.height) // 2))
    sh = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ImageDraw.Draw(sh).rounded_rectangle([cx - 4, cy + 18, cx + cw + 4, cy + ch + 26], radius=30, fill=(0, 0, 0, 190))
    img = Image.alpha_composite(img, sh.filter(ImageFilter.GaussianBlur(24)))
    front = tile(0, 0, 255)
    img.alpha_composite(front, (cx, cy))
    d = ImageDraw.Draw(img)

    # coluna da direita
    rx = cx + cw + 90
    rw = W - 60 - rx
    title = it["title"].strip()
    size = 76
    while True:
        font = get_font(size, True)
        lines = wrap_px(d, title, font, rw, 4)
        if len(lines) <= 3 or size <= 52:
            break
        size -= 6
    lines = lines[:4]
    if len(lines) == 1 and " " in lines[0]:
        w_ = lines[0].split()
        h_ = (len(w_) + 1) // 2
        lines = [" ".join(w_[:h_]), " ".join(w_[h_:])]
    first_acc = len(lines) // 2 if len(lines) > 1 else 0
    y = cy + 6
    for n, line in enumerate(lines):
        T((rx, y), line, size, acc if (len(lines) > 1 and n >= first_acc) else "#ffffff", True)
        y += int(size * 1.12)
    y += 22
    meta = "  •  ".join(x for x in (it["type"], it["author"], str(it["year"]) if it["year"] else "") if x).upper()
    T((rx, y), _fit_text(d, meta, get_font(26, True), rw), 26, "#aab0cc", True)
    y += 62
    r = it["rating"] or 0
    if r:
        sz, gap = 52, 10
        for i in range(5):
            f = 1 if r >= i + 1 else (.5 if r >= i + .5 else 0)
            st = star_pil(sz, f, (255, 255, 255, 50))
            img.alpha_composite(st, (rx + i * (sz + gap), int(y)))
        d = ImageDraw.Draw(img)
        T((rx + 5 * (sz + gap) + 14, y + sz / 2), f"{r:g}".replace(".", ",") + " / 5", 32, "#ffffff", True, "lm")
        y += sz + 34
    else:
        y += 6
    stt = STATUS[it["status"]]
    cap = f"cap. {it['seen']}" + (f" de {it['total']}" if it["total"] and not it.get("ongoing") else "")
    chip = f"{stt}  •  {cap}"
    sc = P["status"][it["status"]]
    fnt = get_font(30, True)
    tw_ = d.textlength(chip, font=fnt)
    pw = int(tw_ + 56 + 56)
    pw = min(pw, rw)
    d.rounded_rectangle([rx, y, rx + pw, y + 68], radius=34, fill=mix(sc, navy, .84), outline=sc, width=3)
    ic = icon_pil("library", 30, sc).convert("RGBA").resize((32, 32), Image.LANCZOS)
    img.alpha_composite(ic, (rx + 22, int(y + 18)))
    d = ImageDraw.Draw(img)
    T((rx + 70, y + 34), chip, 30, "#ffffff", True, "lm")

    # citação
    q = best_quote(it)
    qy = cy + ch + 120
    if q:
        txt = q["text"].strip()
        qf = get_font(40)
        lines = wrap_px(d, txt, qf, W - 70 * 2 - 150, 4)
        bh = len(lines) * 56 + 160
        qy = min(qy, H - 210 - bh)
        x0, x1, y0, y1 = 70, W - 70, qy, qy + bh
        panel_ = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ImageDraw.Draw(panel_).rounded_rectangle([x0, y0, x1, y1], radius=22, fill=(8, 11, 22, 205))
        img = Image.alpha_composite(img, panel_)
        # cantos neon inclinados
        g = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        gd = ImageDraw.Draw(g)
        L = 150
        for pts in (((x0, y0 + L), (x0, y0 + 26), (x0 + 26, y0), (x0 + L + 40, y0)),
                    ((x1, y1 - L), (x1, y1 - 26), (x1 - 26, y1), (x1 - L - 40, y1))):
            gd.line(pts, fill=ar + (255,), width=6, joint="curve")
        img = Image.alpha_composite(img, g.filter(ImageFilter.GaussianBlur(9)))
        img = Image.alpha_composite(img, g)
        d = ImageDraw.Draw(img)
        T((x0 + 40, y0 + 6), "“", 130, acc, True)
        for n, line in enumerate(lines):
            T((x0 + 100, y0 + 84 + n * 56), line, 40, "#ffffff")
        by = y1 - 52
        cap_t = f"cap. {q.get('ch', 0)}"
        cwid = d.textlength(cap_t, font=get_font(28))
        T((x1 - 44, by), cap_t, 28, "#c5c9de", False, "ra")
        d.line([x1 - 44 - cwid - 100, by + 16, x1 - 44 - cwid - 16, by + 16], fill=ar + (255,), width=3)

    # rodapé
    fy = H - 150
    d.line([70, fy - 24, W - 70, fy - 24], fill=(70, 74, 98), width=2)
    lg = logo_pil(84, S["accent"])
    img.alpha_composite(lg.convert("RGBA"), (70, fy))
    d = ImageDraw.Draw(img)
    T((178, fy + 4), "Leitura Foda", 40, "#ffffff", True)
    T((178, fy + 54), "Descubra o próximo capítulo da sua história.", 24, "#9aa0c0")
    h = app.profile.get("handle", "")
    if h:
        T((W - 70, fy + 42), h, 30, S["accent"], True, "rm")
    img.convert("RGB").save(path, "PNG")


# ---------- base das páginas (ficam dentro da janela principal) ----------
class Page(ctk.CTkFrame):
    MAXW = 720

    def __init__(self, app, title=None, back=False):
        super().__init__(app.main, fg_color="transparent")
        self.app = app
        self.top = None
        if title or back:
            top = self.top = ctk.CTkFrame(self, fg_color="transparent")
            top.pack(fill="x", padx=22, pady=(18, 6))
            if back:
                ghost_button(top, " Voltar", app.go_back, image=icon("back", 16), compound="left", width=96,
                             height=34).pack(side="left", padx=(0, 14))
            if title:
                section(top, title, 26).pack(side="left")
        self.footer = ctk.CTkFrame(self, fg_color="transparent", height=1)   # sem height ocupava 200 px vazios
        self.footer.pack(side="bottom", fill="x", padx=20, pady=0)
        self.scroll = new_scroll(self)
        self.scroll.pack(fill="both", expand=True, padx=4, pady=(0, 2))
        self.scroll.grid_columnconfigure(0, weight=1)
        self.col = ctk.CTkFrame(self.scroll, fg_color="transparent")
        self.col.grid(row=0, column=0, sticky="ew", padx=14, pady=8)
        self.scroll.bind("<Configure>", self._fit)

    def _fit(self, e):
        self.col.grid_configure(padx=max(14, int((lw(e.width) - self.MAXW) // 2)))

    def card(self, title):
        f, _ = panel(self.col, title)
        f.pack(fill="x", pady=8)
        return f


# ---------- perfil e estatísticas desenhados em imagem ----------
# Cada painel vira UMA imagem no canvas (nada de dezenas de widgets para o Windows borrar na rolagem).
K = 2          # mesmo valor de K_IMG (as imagens são geradas com o dobro do tamanho)
_ICO = {}


def _ico(name, size, color):
    key = (name, size, color)
    if key not in _ICO:
        _ICO[key] = icon_pil(name, size, color).resize((size * K, size * K), Image.LANCZOS)
    return _ICO[key]


def T(d, x, y, text, size, fill, bold=False, anchor="la"):
    font = get_font(max(8, int(round(size * K))), bold)
    try:
        d.text((x * K, y * K), str(text), font=font, fill=fill, anchor=anchor)
    except (ValueError, TypeError):          # fonte simples (sem âncoras): desenha sem centralizar
        d.text((x * K, y * K), str(text), font=font, fill=fill)


def TW(d, text, size, bold=False):
    return d.textlength(str(text), font=get_font(max(8, int(round(size * K))), bold)) / K


def wrap_l(text, size, maxw, bold=False, maxlines=8):
    tmp = ImageDraw.Draw(Image.new("RGB", (4, 4)))
    return wrap_px(tmp, text, get_font(max(8, int(round(size * K))), bold), maxw * K, maxlines)


def paste_ico(img, name, size, color, x, y):
    ic = _ico(name, size, color)
    img.paste(ic, (int(x * K), int(y * K)), ic)


def paste_star(img, size, x, y):
    st = star_pil(size * K, 1, P["empty"])
    img.paste(st, (int(x * K), int(y * K)), st)


def draw_btn(img, box, text, fill, fg, ic=None, size=13, radius=10):
    d = ImageDraw.Draw(img)
    x0, y0, x1, y1 = box
    d.rounded_rectangle([x0 * K, y0 * K, x1 * K, y1 * K], radius=radius * K, fill=fill)
    tw_ = TW(d, text, size, True)
    total = tw_ + ((16 + 6) if ic else 0)
    x = (x0 + x1) / 2 - total / 2
    cy = (y0 + y1) / 2
    if ic:
        paste_ico(img, ic[0], 16, ic[1], x, cy - 8)
        x += 22
    T(d, x, cy, text, size, fg, True, "lm")


def panel_img(w, h, title=None):
    img = Image.new("RGBA", (w * K, h * K), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle([0, 0, w * K - 1, h * K - 1], radius=14 * K, fill=P["surface"], outline=P["border"], width=K)
    if title:
        d.rectangle([16 * K, 17 * K, 19 * K - 1, 38 * K], fill=P["accent"])
        T(d, 29, 14, title, 15, P["text"], True)
    return img, d


HEAD = 46


# ---- gráficos (desenhados com Pillow) ----
def c_bars(d, x, y, w, h, data, colors=None):
    mx = max([v for _, v in data] + [1])
    bw = w / len(data)
    y1 = y + h - 20
    for i, (lab, v) in enumerate(data):
        x0, x1 = x + i * bw + 5, x + (i + 1) * bw - 5
        col = colors[i] if colors else P["accent"]
        if v:
            top = y1 - (h - 46) * v / mx
            d.rectangle([x0 * K, top * K, x1 * K, y1 * K], fill=col)
            T(d, (x0 + x1) / 2, top - 9, f"{v:g}", 12, P["text"], anchor="mm")
        else:
            d.line([(x0 * K, y1 * K), (x1 * K, y1 * K)], fill=P["border"], width=2 * K)
        T(d, (x0 + x1) / 2, y1 + 10, lab, 12, P["muted"], anchor="mm")


def c_hist(img, d, x, y, w, h, counts):
    mx = max(counts + [1])
    bw = w / len(counts)
    base = y + h - 24
    for i, v in enumerate(counts):
        x0, x1 = x + i * bw + 3, x + (i + 1) * bw - 3
        if v:
            top = base - (base - y - 8) * v / mx
            d.rectangle([x0 * K, top * K, x1 * K, base * K], fill=P["accent"])
        else:
            d.line([(x0 * K, base * K), (x1 * K, base * K)], fill=P["border"], width=2 * K)
    T(d, x + 4, y + h - 9, "0,5", 12, P["muted"], anchor="lm")
    paste_star(img, 11, x + 4 + TW(d, "0,5", 12) + 3, y + h - 15)
    T(d, x + w - 4 - 14, y + h - 9, "5", 12, P["muted"], anchor="rm")
    paste_star(img, 11, x + w - 4 - 11, y + h - 15)


def c_radar(d, x, y, w, h, labels, values):
    n = len(labels)
    ang = [-math.pi / 2 + i * 2 * math.pi / n for i in range(n)]
    cx, cy = x + w / 2, y + h / 2
    R = max(30, min(w / 2 - 78, h / 2 - 28))
    for lvl in (1, .66, .33):
        pts = [((cx + R * lvl * math.cos(a)) * K, (cy + R * lvl * math.sin(a)) * K) for a in ang]
        d.line(pts + [pts[0]], fill=P["border"], width=K)
    for a in ang:
        d.line([(cx * K, cy * K), ((cx + R * math.cos(a)) * K, (cy + R * math.sin(a)) * K)], fill=P["border"], width=K)
    pts = [((cx + R * max(.14, v) * math.cos(a)) * K, (cy + R * max(.14, v) * math.sin(a)) * K)
           for v, a in zip(values, ang)]
    d.polygon(pts, fill=mix(P["accent"], P["surface"], .62))
    d.line(pts + [pts[0]], fill=P["accent"], width=2 * K, joint="curve")
    for px_, py_ in pts:
        d.ellipse([px_ - 4 * K, py_ - 4 * K, px_ + 4 * K, py_ + 4 * K], fill=P["accent"])
    for lab, a in zip(labels, ang):
        cs, sn = math.cos(a), math.sin(a)
        ax = "l" if cs > .3 else "r" if cs < -.3 else "m"
        ay = "s" if sn < -.3 else "a" if sn > .3 else "m"
        T(d, cx + (R + 12) * cs, cy + (R + 12) * sn, lab[:14], 13, P["muted"], anchor=ax + ay)


def c_donut(d, x, y, w, h, data):
    total = sum(v for _, v, _ in data)
    size = min(h - 16, w * 0.46)
    cx, cy = x + 20 + size / 2, y + h / 2
    th = size * 0.17
    box = [(cx - size / 2 + th / 2) * K, (cy - size / 2 + th / 2) * K, (cx + size / 2 - th / 2) * K,
           (cy + size / 2 - th / 2) * K]
    if total <= 0:
        d.arc(box, 0, 359.9, fill=P["surface2"], width=int(th * K))
    else:
        acc = 270.0
        for lab, v, col in data:
            if v <= 0:
                continue
            ext = 360.0 * v / total
            d.arc(box, acc, acc + ext + min(2.0, ext / 4), fill=col, width=int(th * K))
            acc += ext
    T(d, cx, cy - 8, str(total), 20, P["text"], True, "mm")
    T(d, cx, cy + 14, "leituras", 13, P["muted"], anchor="mm")
    lx = cx + size / 2 + 30
    yy = max(y + 16, cy - len(data) * 13 + 13)
    for lab, v, col in data:
        d.ellipse([lx * K, (yy - 6) * K, (lx + 12) * K, (yy + 6) * K], fill=col)
        T(d, lx + 20, yy, lab, 13, P["text"], anchor="lm")
        T(d, x + w - 16, yy, v, 13, P["muted"], anchor="rm")
        yy += 26


def c_line(d, x, y, w, h, data):
    n = len(data)
    left, right, top, base = x + 16, x + w - 16, y + 22, y + h - 24
    mx = max([v for _, v in data] + [1])
    step = (right - left) / (n - 1)
    pts = [(left + i * step, base - (base - top) * v / mx) for i, (_, v) in enumerate(data)]
    sm = smooth_pts(pts)
    area = [(pts[0][0] * K, base * K)] + [(a * K, b * K) for a, b in sm] + [(pts[-1][0] * K, base * K)]
    d.polygon(area, fill=mix(P["accent"], P["surface"], .82))
    d.line([(left * K, base * K), (right * K, base * K)], fill=P["border"], width=K)
    d.line([(a * K, b * K) for a, b in sm], fill=P["accent"], width=3 * K, joint="curve")
    for (lab, v), (px_, py_) in zip(data, pts):
        d.ellipse([(px_ - 4) * K, (py_ - 4) * K, (px_ + 4) * K, (py_ + 4) * K], fill=P["surface"],
                  outline=P["accent"], width=2 * K)
        T(d, px_, base + 12, lab, 12, P["muted"], anchor="mm")
        if v and v == mx:
            T(d, px_, py_ - 13, f"{v:g}", 12, P["text"], anchor="mm")


def heat_geom(w):
    gap = 3
    avail = max(60.0, w - 8)
    weeks = 53
    cell = avail / weeks - gap
    if cell < 9:
        cell = 9
        weeks = max(8, int(avail // (cell + gap)))
    cell = min(cell, 18)
    return gap, weeks, cell, int(7 * (cell + gap) + 30)


def c_heat(d, x, y, w, act):
    gap, weeks, cell, _h = heat_geom(w)
    today = date.today()
    start = today - timedelta(days=today.weekday() + 7 * (weeks - 1))
    shades = [mix(P["surface2"], P["accent"], t) for t in (0, .3, .55, .8, 1)]
    last_m = None
    for wk in range(weeks):
        for dd in range(7):
            day = start + timedelta(days=7 * wk + dd)
            if day > today:
                continue
            e = act.get(day.isoformat(), {})
            v = e.get("ch", 0) + e.get("min", 0) / 20
            lv = 0 if v <= 0 else 1 if v < 3 else 2 if v < 6 else 3 if v < 10 else 4
            px_, py_ = x + 4 + wk * (cell + gap), y + 22 + dd * (cell + gap)
            d.rectangle([px_ * K, py_ * K, (px_ + cell) * K, (py_ + cell) * K], fill=shades[lv])
        m = (start + timedelta(days=7 * wk)).month
        if m != last_m:
            T(d, x + 4 + wk * (cell + gap), y + 8, MESES[m - 1], 12, P["muted"], anchor="lm")
            last_m = m


# ---- blocos e a "tela" que os mostra ----
class Blk:
    medals = ()      # medalhas que ganham animação ao passar o mouse: [{name, cx, cy, size, spec}]
    tip = None  # função(nome da região) -> obra, para o cartão rápido da estante
    move = None  # função(x, y) -> imagem: bloco que acompanha o mouse (inclinação das cartas)

    def __init__(self, key, x, y, w, h, draw, regs=(), act=None, item=None):
        self.key, self.x, self.y, self.w, self.h = key, x, y, int(w), int(h)
        self.draw, self.regs, self.act, self.item = draw, list(regs), act, item


class BlockView:
    """Mostra uma lista de blocos (cada um uma imagem) num canvas rolável; só os visíveis existem."""

    def __init__(self, app, sf, layout_fn):
        self.app, self.sf, self.cv, self.fn = app, sf, sf.canvas, layout_fn
        self.blocks, self.live, self.refs, self.photos = [], {}, {}, OrderedDict()
        self.hov, self._job, self._rz = (None, None), None, None
        self._an, self._fcache = None, OrderedDict()
        sf.virtual = self
        try:
            self.cv.itemconfigure(sf._win, state="hidden")
        except tk.TclError:
            pass
        self.cv.bind("<Motion>", self._motion, add="+")
        self.cv.bind("<Leave>", self._leave, add="+")
        self.cv.bind("<Button-1>", self._click, add="+")

    def alive(self):
        try:
            return self.cv.winfo_exists() and self.sf.virtual is self
        except tk.TclError:
            return False

    def place(self):
        cw = self.cv.winfo_width()
        if cw < 60:
            return False
        self.blocks = sorted(self.fn(lw(cw)), key=lambda b: b.y)
        k = scale_k()
        total = int(max([b.y + b.h for b in self.blocks] + [1]) * k) + int(24 * k)
        self.sf._region_h = total
        self.cv.configure(scrollregion=(0, 0, max(1, cw), total))
        return True

    def _an_stop(self):
        an, self._an = self._an, None
        if an:
            try:
                self.app.after_cancel(an["job"])
            except Exception:
                pass
            try:
                self.cv.delete(an["item"])
            except tk.TclError:
                pass

    def _an_check(self, i, name):
        if i is None or not name or not str(name).startswith("m") or not self.blocks[i].medals:
            return self._an_stop()
        if self._an and self._an["key"] == (i, name):
            return
        m = next((m for m in self.blocks[i].medals if m["name"] == name), None)
        if m is None:
            return self._an_stop()
        self._an_stop()
        k = scale_k()
        b = self.blocks[i]
        size = max(8, int(m["size"] * k))
        ic, tier, earned, prog = m["spec"]
        fk = (ic, tier, earned, size, None if prog is None else round(prog, 2), P["accent"])
        frames = self._fcache.get(fk)
        if frames is None:
            try:
                frames = [ImageTk.PhotoImage(f) for f in medal_frames(ic, tier, earned, size, prog)]
            except Exception:
                return
            self._fcache[fk] = frames
            while len(self._fcache) > 24:
                self._fcache.popitem(last=False)
        else:
            self._fcache.move_to_end(fk)
        item = self.cv.create_image(int((b.x + m["cx"]) * k), int((b.y + m["cy"]) * k), image=frames[0],
                                    anchor="center")
        self._an = {"key": (i, name), "item": item, "job": None}

        def step(n=0):
            if not self._an or self._an["item"] != item:
                return
            try:
                self.cv.itemconfigure(item, image=frames[n])
            except tk.TclError:
                return
            if n < len(frames) - 1:
                self._an["job"] = self.app.after(26, lambda: step(n + 1))
        step()

    def clear_items(self):
        self._an_stop()
        for i in list(self.live):
            try:
                self.cv.delete(self.live[i])
            except tk.TclError:
                pass
        self.live.clear()
        self.refs.clear()
        self.hov = (None, None)
        preview_hide()

    def rebuild(self):
        """Dados mudaram (ou a janela): refaz posições e imagens, mantendo a posição da rolagem."""
        if not self.alive():
            return
        try:
            frac = self.cv.yview()[0]
        except tk.TclError:
            frac = 0
        self.clear_items()
        self.photos.clear()
        if self.place():
            try:
                self.cv.yview_moveto(frac)
            except tk.TclError:
                pass
            self.sync()

    def resized(self):
        if self._rz:
            try:
                self.app.after_cancel(self._rz)
            except Exception:
                pass
        self._rz = self.app.after(60, self._do_resize)

    def _do_resize(self):
        self._rz = None
        if not self.alive():
            return
        try:
            frac = self.cv.yview()[0]
        except tk.TclError:
            frac = 0
        self.clear_items()
        if self.place():
            try:
                self.cv.yview_moveto(frac)
            except tk.TclError:
                pass
            self.sync()

    def _photo(self, i, hov):
        b = self.blocks[i]
        key = (b.key, b.w, b.h, hov)
        ph = self.photos.get(key)
        if ph is not None:
            self.photos.move_to_end(key)
            return ph
        img = b.draw(hov)
        k = scale_k()
        size = (max(1, int(round(b.w * k))), max(1, int(round(b.h * k))))
        if img.size != size:
            img = img.resize(size, Image.BICUBIC)
        ph = ImageTk.PhotoImage(img)
        self.photos[key] = ph
        while len(self.photos) > 40:
            self.photos.popitem(last=False)
        return ph

    def sync(self):
        if not self.blocks or not self.alive():
            return
        k = scale_k()
        try:
            top = self.cv.canvasy(0) / k
            H = self.cv.winfo_height() / k
        except tk.TclError:
            return
        lo, hi = top - H * 0.8, top + H * 1.8
        need = [i for i, b in enumerate(self.blocks) if b.y + b.h >= lo and b.y <= hi]
        want = set(need)
        for i in [i for i in self.live if i not in want]:
            try:
                self.cv.delete(self.live.pop(i))
            except tk.TclError:
                pass
            self.refs.pop(i, None)
        mid = top + H / 2
        need.sort(key=lambda i: abs(self.blocks[i].y + self.blocks[i].h / 2 - mid))
        budget, later = 4, False
        for i in need:
            if i in self.live:
                continue
            if budget <= 0:
                later = True
                break
            ph = self._photo(i, None)
            b = self.blocks[i]
            self.live[i] = self.cv.create_image(int(b.x * k), int(b.y * k), image=ph, anchor="nw")
            self.refs[i] = ph
            budget -= 1
        if later and self._job is None:
            self._job = self.app.after(6, self._more)

    def _more(self):
        self._job = None
        self.sync()

    def _hit(self, e):
        k = scale_k()
        x, y = self.cv.canvasx(e.x) / k, self.cv.canvasy(e.y) / k
        for i in self.live:
            b = self.blocks[i]
            if b.x <= x < b.x + b.w and b.y <= y < b.y + b.h:
                rx, ry = x - b.x, y - b.y
                for x0, y0, x1, y1, name in (b.regs_fn() if getattr(b, 'regs_fn', None) else b.regs):
                    if x0 <= rx < x1 and y0 <= ry < y1:
                        return i, name
                return i, None
        return None, None

    def _set(self, i, hov):
        if i in self.live:
            ph = self._photo(i, hov)
            self.refs[i] = ph
            self.cv.itemconfigure(self.live[i], image=ph)

    def _motion(self, e):
        if not self.alive() or scrolling():
            return
        i, name = self._hit(e)
        old = self.hov
        if (i, name) == old:
            self._tilt(i, name, e)
            return
        self._an_check(i, name)
        self.hov = (i, name)
        if old[0] is not None and old[0] != i:
            self._set(old[0], None)
        if i is not None:
            self._set(i, name)
        try:
            self.cv.configure(cursor="hand2" if name else "")
        except tk.TclError:
            pass
        self._tilt(i, name, e)
        if i != old[0] or (i is not None and name != old[1]):
            preview_hide()
            b = self.blocks[i] if i is not None else None
            if b is not None and b.tip is not None and name:
                try:
                    tit = b.tip(name)
                except Exception:
                    tit = None
                if tit is not None:
                    PV["root"] = self.app
                    PV["job"] = self.app.after(140, lambda it=tit: shelf_tip_show(self.app, it))
            elif b is not None and b.item is not None and name and S.get("preview", True):
                bit = b.item(name) if callable(b.item) else b.item
                if bit is not None and preview_has_content(bit):
                    PV["root"] = self.app
                    PV["job"] = self.app.after(650, lambda it=bit: preview_show(self.app, it))

    def _tilt(self, i, name, e):
        """Blocos com .move (cartas épicas e lendárias) se inclinam seguindo o mouse."""
        if i is None or not name:
            return
        b = self.blocks[i]
        if b.move is None or i not in self.live:
            return
        now = time.time()
        if now - getattr(self, "_tt", 0) < 0.028:
            return
        self._tt = now
        k = scale_k()
        try:
            rx, ry = self.cv.canvasx(e.x) / k - b.x, self.cv.canvasy(e.y) / k - b.y
            img = b.move(rx, ry)
            if img is None:
                return
            size = (max(1, int(round(b.w * k))), max(1, int(round(b.h * k))))
            if img.size != size:
                img = img.resize(size, Image.BILINEAR)
            ph = ImageTk.PhotoImage(img)
            self.refs[i] = ph
            self.cv.itemconfigure(self.live[i], image=ph)
        except (tk.TclError, ValueError):
            pass

    def _leave(self, e):
        if not self.alive() or self.hov == (None, None):
            return
        old = self.hov
        self.hov = (None, None)
        self._an_stop()
        if old[0] is not None:
            self._set(old[0], None)
        preview_hide()
        try:
            self.cv.configure(cursor="")
        except tk.TclError:
            pass

    def _click(self, e):
        if not self.alive():
            return
        i, name = self._hit(e)
        if i is None or not name:
            return
        preview_hide()
        b = self.blocks[i]
        if b.act:
            b.act(name)


# ---- painéis ----
class PanelSpec:
    def __init__(self, title, nat, body, head=None, regs=None, act=None, medals=None):
        self.title, self.nat, self.body, self.head, self.regs, self.act = title, nat, body, head, regs, act
        self.medals = medals

    def block(self, key, x, y, w, h):
        spec = self

        def draw(hov):
            img, d = panel_img(w, h, spec.title)
            if spec.head:
                spec.head(img, d, w)
            spec.body(img, d, w, h, hov)
            return img

        ml = spec.medals(w, h) if spec.medals else []
        regs = [(m["cx"] - m["size"] / 2, m["cy"] - m["size"] / 2, m["cx"] + m["size"] / 2, m["cy"] + m["size"] / 2,
                 m["name"]) for m in ml] + (spec.regs(w, h) if spec.regs else [])
        blk = Blk(key, x, y, w, h, draw, regs, spec.act)
        blk.medals = ml
        return blk


def _link_btn(img, d, x, y, w, text, hov, name):
    """Texto de link com seta (como o botão 'Ver biblioteca ›')."""
    if hov == name:
        d.rounded_rectangle([x * K, y * K, (x + w) * K, (y + 36) * K], radius=8 * K, fill=P["surface2"])
    T(d, x + 12, y + 18, text, 14, P["accent"], False, "lm")
    paste_ico(img, "chevron", 16, P["accent"], x + 12 + TW(d, text, 14) + 6, y + 10)


def spec_year(app):
    items, act = app.items, app.activity
    year = date.today().year
    added = sum(1 for i in items if i["created"] and datetime.fromtimestamp(i["created"]).year == year)
    started = sum(1 for i in items if year_of(i["started"]) == year)
    done = sum(1 for i in items if i["status"] == "completo" and year_of(i["finished"]) == year)
    cells = [("book", added, "Adicionadas"), ("play", started, "Iniciadas"), ("check", done, "Completas"),
             ("flag", f"{done}/{S['goal']}", "Meta do ano"),
             ("chart", sum_activity(act, str(year), "ch"), "Capítulos lidos"),
             ("clock", fmt_minutes(sum_activity(act, str(year), "min")), "Tempo de leitura")]

    def body(img, d, w, h, hov):
        cw = (w - 24) / 2
        for k_, (ic, val, lab) in enumerate(cells):
            x = 12 + 6 + (k_ % 2) * cw
            y = HEAD + (k_ // 2) * 56 + 4
            paste_ico(img, ic, 20, P["muted"], x, y + 3)
            T(d, x + 34, y, val, 18, P["text"], True)
            T(d, x + 34, y + 26, lab, 12, P["muted"])
        _link_btn(img, d, 12, h - 48, w - 24, "Ver biblioteca", hov, "lib")

    return PanelSpec(str(year), lambda w: HEAD + 3 * 56 + 2 + 36 + 14, body,
                     regs=lambda w, h: [(12, h - 48, w - 12, h - 12, "lib")],
                     act=lambda n: app.nav("library"))


def spec_ratings(app):
    items = app.items
    rated = [i["rating"] for i in items if i["rating"]]
    counts = [sum(1 for i in items if i["rating"] == (k + 1) / 2) for k in range(10)]

    def head(img, d, w):
        if not rated:
            return
        x = w - 16
        t = f"({len(rated)})"
        T(d, x, 24, t, 11, P["muted"], anchor="rm")
        x -= TW(d, t, 11) + 8
        avg = f"{sum(rated) / len(rated):.1f}".replace(".", ",")
        T(d, x, 24, avg, 15, GOLD_HEX, True, "rm")
        paste_star(img, 15, x - TW(d, avg, 15, True) - 19, 17)

    return PanelSpec("Avaliações", lambda w: HEAD + 110 + 14,
                     lambda img, d, w, h, hov: c_hist(img, d, 16, HEAD, w - 32, 110, counts), head=head)


def spec_genres(app):
    top = Counter(t for i in app.items for t in i["tags"]).most_common(5)
    if len(top) < 3:
        msg = "Cadastre pelo menos 3 gêneros diferentes nas suas leituras para ver este gráfico."

        def body(img, d, w, h, hov):
            for n, line in enumerate(wrap_l(msg, 13, w - 32)):
                T(d, 16, HEAD + n * 18, line, 13, P["muted"])

        return PanelSpec("Principais gêneros", lambda w: HEAD + len(wrap_l(msg, 13, w - 32)) * 18 + 18, body)
    mx = top[0][1]
    return PanelSpec("Principais gêneros", lambda w: HEAD + 250 + 10,
                     lambda img, d, w, h, hov: c_radar(d, 10, HEAD, w - 20, 250, [t for t, _ in top],
                                                       [n / mx for _, n in top]))


def spec_types(app):
    data = [(t, sum(1 for i in app.items if i["type"] == t)) for t in TYPES]
    cols = [type_color(t) for t in TYPES]
    return PanelSpec("Por tipo", lambda w: HEAD + 150 + 14,
                     lambda img, d, w, h, hov: c_bars(d, 16, HEAD, w - 32, 150, data, cols))


def spec_status(app):
    data = [(STATUS[k], sum(1 for i in app.items if i["status"] == k), P["status"][k]) for k in STATUS]
    return PanelSpec("Por status", lambda w: HEAD + 190 + 14,
                     lambda img, d, w, h, hov: c_donut(d, 16, HEAD, w - 32, 190, data))


def spec_chapters(app):
    today = date.today()
    data = []
    for back in range(11, -1, -1):
        mm, yy = today.month - back, today.year
        while mm <= 0:
            mm += 12
            yy -= 1
        data.append((MESES[mm - 1], sum_activity(app.activity, f"{yy:04d}-{mm:02d}", "ch")))
    return PanelSpec("Capítulos por mês", lambda w: HEAD + 170 + 14,
                     lambda img, d, w, h, hov: c_line(d, 16, HEAD, w - 32, 170, data))


def spec_months(app):
    year = date.today().year
    mes = ["J", "F", "M", "A", "M", "J", "J", "A", "S", "O", "N", "D"]
    done = [parse_date(i["finished"]) for i in app.items if i["status"] == "completo"]
    data = [(m, sum(1 for d_ in done if d_ and d_.year == year and d_.month == n + 1)) for n, m in enumerate(mes)]

    def body(img, d, w, h, hov):
        c_bars(d, 16, HEAD, w - 32, 150, data)
        T(d, 16, HEAD + 156, "Só entram leituras com data de fim preenchida.", 12, P["muted"])

    return PanelSpec(f"Completas por mês em {year}", lambda w: HEAD + 150 + 6 + 20 + 12, body)


def spec_recent(app):
    today = date.today()
    days = [today - timedelta(days=13 - k) for k in range(14)]
    data = [(str(d_.day), app.activity.get(d_.isoformat(), {}).get("ch", 0)) for d_ in days]
    return PanelSpec("Capítulos nos últimos 14 dias", lambda w: HEAD + 150 + 14,
                     lambda img, d, w, h, hov: c_bars(d, 16, HEAD, w - 32, 150, data))


def spec_criteria(app):
    items = app.items

    def avg(vals):
        return round(sum(vals) / len(vals), 1) if vals else 0

    data = [("História", avg([i["crit"].get("story", 0) for i in items if i["crit"].get("story")])),
            ("Arte", avg([i["crit"].get("art", 0) for i in items if i["crit"].get("art")])),
            ("Persona.", avg([i["crit"].get("chars", 0) for i in items if i["crit"].get("chars")])),
            ("Geral", avg([i["rating"] for i in items if i["rating"]]))]
    return PanelSpec("Médias das suas notas", lambda w: HEAD + 150 + 14,
                     lambda img, d, w, h, hov: c_bars(d, 16, HEAD, w - 32, 150, data))


def spec_goal(app, view):
    year = date.today().year
    n = sum(1 for i in app.items if i["status"] == "completo" and year_of(i["finished"]) == year)

    def body(img, d, w, h, hov):
        goal = S["goal"]
        T(d, 16, HEAD, f"{n} de {goal} leituras completas este ano", 13, P["muted"])
        by = HEAD + 26
        d.rounded_rectangle([16 * K, by * K, (w - 16) * K, (by + 10) * K], radius=5 * K, fill=P["surface2"])
        fw = (w - 32) * min(1, n / max(1, goal))
        if fw > 0:
            d.rounded_rectangle([16 * K, by * K, (16 + max(fw, 10)) * K, (by + 10) * K], radius=5 * K,
                                fill=P["accent"])
        ry = by + 26
        T(d, 16, ry + 16, "Meta:", 13, P["muted"], anchor="lm")
        for name, x, txt in (("dec", 70, "−"), ("inc", 70 + 28 + 64 + 12, "+")):
            fill = mix(P["surface2"], P["accent"], .38) if hov == name else P["surface2"]
            d.rounded_rectangle([x * K, (ry + 2) * K, (x + 28) * K, (ry + 30) * K], radius=8 * K, fill=fill)
            T(d, x + 14, ry + 16, txt, 18, P["text"], True, "mm")
        d.rounded_rectangle([(70 + 34) * K, (ry + 2) * K, (70 + 34 + 64) * K, (ry + 30) * K], radius=8 * K,
                            fill=P["surface2"])
        T(d, 70 + 34 + 32, ry + 16, goal, 14, P["text"], True, "mm")

    def regs(w, h):
        ry = HEAD + 26 + 26
        return [(70, ry + 2, 98, ry + 30, "dec"), (70 + 28 + 64 + 12, ry + 2, 70 + 28 + 64 + 40, ry + 30, "inc")]

    def act(name):
        S["goal"] = max(1, S["goal"] + (-1 if name == "dec" else 1))
        save_settings()
        touch()
        view.rebuild()

    return PanelSpec(f"Meta de {year}", lambda w: HEAD + 26 + 36 + 36 + 8, body, regs=regs, act=act)


def spec_activity(app):
    act = app.activity
    cur, longest = streaks(act)
    since = (date.today() - timedelta(days=29)).isoformat()
    last30 = sum(v.get("ch", 0) for k_, v in act.items() if k_ >= since)
    cells = [(f"{cur} dias", "Sequência atual"), (f"{longest} dias", "Maior sequência"),
             (str(last30), "Capítulos em 30 dias"), (fmt_minutes(sum_activity(act, "", "min")), "Tempo total")]

    def body(img, d, w, h, hov):
        cw = (w - 24) / 4
        for i, (val, lab) in enumerate(cells):
            cx = 12 + (i + .5) * cw
            T(d, cx, HEAD + 4, val, 20, P["text"], True, "ma")
            T(d, cx, HEAD + 34, lab, 11, P["muted"], False, "ma")
        c_heat(d, 16, HEAD + 60, w - 32, act)

    return PanelSpec("Atividade de leitura", lambda w: HEAD + 60 + heat_geom(w - 32)[3] + 14, body)


def spec_level(app):
    parts, xp = xp_breakdown(app)
    lv = level_info(xp)

    def body(img, d, w, h, hov):
        t = f"Nível {lv['level']}"
        pw = TW(d, t, 15, True) + 20
        d.rounded_rectangle([16 * K, HEAD * K, (16 + pw) * K, (HEAD + 30) * K], radius=10 * K, fill=lv["color"])
        T(d, 16 + pw / 2, HEAD + 15, t, 15, "#14120a", True, "mm")
        T(d, 16 + pw + 10, HEAD + 15, lv["title"], 15, P["text"], True, "lm")
        by = HEAD + 40
        d.rounded_rectangle([16 * K, by * K, (w - 16) * K, (by + 8) * K], radius=4 * K, fill=P["surface2"])
        fw = (w - 32) * lv["frac"]
        if fw > 0:
            d.rounded_rectangle([16 * K, by * K, (16 + max(fw, 8)) * K, (by + 8) * K], radius=4 * K, fill=lv["color"])
        T(d, 16, by + 14, f"{xp - lv['cur']} / {lv['nxt'] - lv['cur']} XP para o nível {lv['level'] + 1}", 12,
          P["muted"])
        y = by + 40
        for lab, v in parts:
            T(d, 16, y, lab, 12, P["muted"])
            T(d, w - 16, y, f"+{v} XP", 12, P["text"], True, "ra")
            y += 21

    return PanelSpec("Nível de leitor", lambda w: HEAD + 40 + 40 + len(parts) * 21 + 12, body)


def spec_badges(app, view):
    st = badge_status_cached(app)
    visible = [b for b in st if not b["secret"] or b["earned"]]
    hidden = len(st) - len(visible)
    got = sum(1 for b in visible if b["earned"])
    rank = {"ouro": 0, "prata": 1, "bronze": 2}
    best = sorted([b for b in visible if b["earned"]], key=lambda b: rank[b["tier"]])[:4]
    near = sorted([b for b in visible if not b["earned"]], key=lambda b: -min(1, b["have"] / b["need"]))[:4]
    secs = [x for x in (("Em destaque", best), ("Quase lá", near)) if x[1]]
    ROW, SEC = 106, 24

    def total(w):
        return HEAD + len(secs) * (SEC + ROW) + (20 if hidden else 0) + 36 + 14

    def head(img, d, w):
        T(d, w - 16, 24, f"{got} de {len(visible)}", 12, P["muted"], anchor="rm")

    def medals(w, h):
        cw, y, out = (w - 20) / 4, HEAD, []
        for label, lst in secs:
            y += SEC
            for k_, b in enumerate(lst):
                pr = None if b["earned"] else min(1, b["have"] / b["need"])
                out.append(dict(name=f"m{len(out)}", cx=10 + (k_ + .5) * cw, cy=y + 30, size=56,
                                spec=(b["icon"], b["tier"], b["earned"], pr)))
            y += ROW
        return out

    def body(img, d, w, h, hov):
        cw = (w - 20) / 4
        y = HEAD
        for label, lst in secs:
            T(d, 16, y + 4, label, 12, P["muted"], True)
            y += SEC
            for k_, b in enumerate(lst):
                cx = 10 + (k_ + .5) * cw
                pr = None if b["earned"] else min(1, b["have"] / b["need"])
                bi = badge_pil(b["icon"], b["tier"], b["earned"], 56 * K, pr)
                img.paste(bi, (int((cx - 28) * K), int((y + 2) * K)), bi)
                for n, line in enumerate(wrap_l(b["title"], 10, 76, maxlines=2)):
                    T(d, cx, y + 62 + n * 13, line, 11, P["text"] if b["earned"] else P["muted"], False, "ma")
                if not b["earned"]:
                    T(d, cx, y + 90, f"{int(min(b['have'], b['need']))}/{int(b['need'])}", 10, P["accent"], True, "ma")
            y += ROW
        if hidden:
            T(d, 16, y + 2, f"+ {hidden} conquistas secretas por descobrir", 11, P["muted"])
            y += 20
        _link_btn(img, d, 12, y, w - 24, "Ver todas as conquistas", hov, "all")

    def regs(w, h):
        y = HEAD + len(secs) * (SEC + ROW) + (20 if hidden else 0)
        return [(12, y, w - 12, y + 36, "all")]

    return PanelSpec("Conquistas", total, body, head=head, regs=regs, medals=medals,
                     act=lambda n: app.open_sub(BadgesPage))


def spec_review(app):
    msg = "Um resumo do que você leu: melhores leituras, gênero favorito, mês mais ativo e mais."
    label = f"Ver retrospectiva de {date.today().year}"
    tmp = ImageDraw.Draw(Image.new("RGB", (4, 4)))
    bw = TW(tmp, label, 13, True) + 32

    def top(w):
        return HEAD + len(wrap_l(msg, 13, w - 32)) * 18 + 10

    def body(img, d, w, h, hov):
        for n, line in enumerate(wrap_l(msg, 13, w - 32)):
            T(d, 16, HEAD + n * 18, line, 13, P["muted"])
        y = top(w)
        draw_btn(img, (16, y, 16 + bw, y + 34), label, P["accent_hover"] if hov == "go" else P["accent"], "#ffffff")

    return PanelSpec("Retrospectiva do ano", lambda w: top(w) + 34 + 14, body,
                     regs=lambda w, h: [(16, top(w), 16 + bw, top(w) + 34, "go")],
                     act=lambda n: app.open_sub(YearReviewPage))


def spec_strip(app):
    items, act = app.items, app.activity
    rated = [i["rating"] for i in items if i["rating"]]
    cells = [("Leituras", len(items)), ("Lendo", sum(1 for i in items if i["status"] == "lendo")),
             ("Completas", sum(1 for i in items if i["status"] == "completo")),
             ("Favoritas", sum(1 for i in items if i["favorite"])),
             ("Capítulos lidos", sum(i["seen"] for i in items)),
             ("Nota média", f"{sum(rated) / len(rated):.1f}".replace(".", ",") if rated else "–"),
             ("Tempo lido", fmt_minutes(sum_activity(act, "", "min")))]

    def nat(w):
        return -(-len(cells) // balanced_cols(len(cells), w)) * 60 + 8

    def body(img, d, w, h, hov):
        n = balanced_cols(len(cells), w)
        cw = (w - 12) / n
        for k_, (lab, val) in enumerate(cells):
            cx = 6 + (k_ % n + .5) * cw
            y = 14 + (k_ // n) * 60
            T(d, cx, y, val, 20, P["text"], True, "ma")
            T(d, cx, y + 28, lab, 11, P["muted"], False, "ma")

    spec = PanelSpec(None, nat, body)
    return spec


# ---------- perfil ----------
HBH = 300          # altura do cabeçalho do perfil


def _hdr_geom(app, w, pr, lv):
    """Posições do cabeçalho (compartilhadas entre o desenho e as áreas de clique/animação)."""
    AV = 116
    ix = 26 + AV + 22
    right = 190                              # largura reservada à direita (nível, favoritos...)
    bio = wrap_l(pr["bio"], 14, max(160, w - ix - right - 24), maxlines=2) if pr["bio"] else []
    total = 44 + 34 + (len(bio) * 20 + 4 if bio else 0) + 28
    y0 = max(24, HBH - 22 - total)
    handle_w = TW(ImageDraw.Draw(Image.new("RGB", (4, 4))), pr["handle"], 15)
    medals = []
    for n_, b in enumerate(showcase_badges(app)):
        medals.append(dict(name=f"m{n_}", cx=ix + handle_w + 20 + 15 + n_ * 34, cy=y0 + 44 + 15, size=30,
                           spec=(b["icon"], b["tier"], True, None), badge=b))
    return dict(AV=AV, ix=ix, bio=bio, y0=y0, medals=medals, right=right)


def profile_header(app, w, hov, pr, lv, m=0):
    """Cabeçalho do perfil. `w` é a largura total (o banner vai de ponta a ponta); o conteúdo
    (avatar, nome, botões) fica numa coluna com margem `m` de cada lado."""
    full, w, mx = w, w - 2 * m, m
    BH, g = HBH, _hdr_geom(app, w, pr, lv)
    AV, ix, y0, bio = g["AV"], g["ix"], g["y0"], g["bio"]
    bg = P["bg"]
    items = app.items

    def path(key):
        n = pr.get(key)
        return profile_dir() / n if n else None

    img = Image.new("RGBA", (full * K, BH * K), bg)
    img.paste(banner_pil(path("banner"), full * K, BH * K, bg, P["accent"], fade=(0.62, 0.38)), (0, 0))
    shade_ = Image.new("RGBA", img.size, (0, 0, 0, 0))                  # escurece a metade de baixo p/ o texto
    sd = ImageDraw.Draw(shade_)
    for yy in range(int(BH * K * .38), BH * K):
        t = (yy - BH * K * .38) / (BH * K * .62)
        sd.line([(0, yy), (full * K, yy)], fill=(8, 8, 14, int(150 * min(1, t * 1.2))))
    img.alpha_composite(shade_)
    base = img
    img = Image.new("RGBA", (w * K, BH * K), (0, 0, 0, 0))              # camada do conteúdo (coluna central)
    # avatar
    av = avatar_pil(path("avatar"), pr["name"], AV * K, bg, lv["color"])
    am = Image.new("L", (AV * K * 4, AV * K * 4), 0)
    ImageDraw.Draw(am).ellipse([0, 0, AV * K * 4 - 1, AV * K * 4 - 1], fill=255)
    img.paste(av, (26 * K, (BH - AV - 22) * K), am.resize((AV * K, AV * K), Image.LANCZOS))
    d = ImageDraw.Draw(img)
    # linha 1: nome + título do nível
    T(d, ix, y0, pr["name"], 32, "#ffffff", True)
    nw = TW(d, pr["name"], 32, True)
    ttl, tcol = display_title(app, lv)
    chip = f" {ttl} "
    cw_ = TW(d, chip, 12, True) + 8
    cx0 = ix + nw + 14
    d.rounded_rectangle([cx0 * K, (y0 + 10) * K, (cx0 + cw_) * K, (y0 + 32) * K], radius=6 * K,
                        fill=mix(tcol, "#000000", .55), outline=mix(tcol, "#000000", .15), width=K)
    T(d, cx0 + cw_ / 2, y0 + 21, chip, 12, mix(tcol, "#ffffff", .25), True, "mm")
    # linha 2: @ e vitrine
    T(d, ix, y0 + 44, pr["handle"], 15, P["accent"], False, "lm")
    d2 = d
    for m in g["medals"]:
        bi = badge_pil(m["spec"][0], m["spec"][1], True, 30 * K)
        img.paste(bi, (int((m["cx"] - 15) * K), int((m["cy"] - 15) * K)), bi)
    # bio
    yy = y0 + 70
    for line in bio:
        T(d, ix, yy, line, 14, "#c9cbe0")
        yy += 20
    # contagens
    yy += 6 if bio else 0
    done = sum(1 for i in items if i["status"] == "completo")
    nlists = len({n for i in items for n in i["lists"]})
    x = ix
    for val, lab in ((len(items), "Leituras"), (done, "Completas"), (nlists, "Listas")):
        T(d, x, yy + 10, str(val), 15, "#ffffff", True, "lm")
        x += TW(d, str(val), 15, True) + 5
        T(d, x, yy + 10, lab, 14, "#a9acc6", False, "lm")
        x += TW(d, lab, 14) + 22
    # botões de ícone no canto
    ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
    od = ImageDraw.Draw(ov)
    bx = w - 16 - 3 * 42 - 2 * 8
    for n_, (name, ic) in enumerate((("tier", "star"), ("share", "share"), ("edit", "edit"))):
        x0 = bx + n_ * 50
        od.rounded_rectangle([x0 * K, 16 * K, (x0 + 42) * K, 58 * K], radius=10 * K,
                             fill=(P["accent"] if hov == name else (10, 10, 18, 185)),
                             outline=(255, 255, 255, 40), width=K)
    img.alpha_composite(ov)
    for n_, (name, ic) in enumerate((("tier", "star"), ("share", "share"), ("edit", "edit"))):
        paste_ico(img, ic, 20, "#ffffff", bx + n_ * 50 + 11, 27)
    # caixa do nível (direita)
    d = ImageDraw.Draw(img)
    rx = w - 16 - 164
    ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
    od = ImageDraw.Draw(ov)
    od.rounded_rectangle([rx * K, (BH - 140) * K, (rx + 164) * K, (BH - 76) * K], radius=10 * K, fill=(10, 10, 18, 185),
                         outline=(255, 255, 255, 40), width=K)
    favs = sum(1 for i in items if i["favorite"])
    od.rounded_rectangle([rx * K, (BH - 68) * K, (rx + 164) * K, (BH - 36) * K], radius=10 * K, fill=(10, 10, 18, 185),
                         outline=(255, 255, 255, 40), width=K)
    img.alpha_composite(ov)
    d = ImageDraw.Draw(img)
    T(d, rx + 82, BH - 124, f"Nível {lv['level']}", 18, "#ffffff", True, "mm")
    d.rounded_rectangle([(rx + 20) * K, (BH - 106) * K, (rx + 144) * K, (BH - 100) * K], radius=3 * K, fill=P["surface2"])
    fw = 124 * lv["frac"]
    if fw > 0:
        d.rounded_rectangle([(rx + 20) * K, (BH - 106) * K, (rx + 20 + max(fw, 6)) * K, (BH - 100) * K], radius=3 * K,
                            fill=lv["color"])
    T(d, rx + 82, BH - 90, f"{lv['xp'] - lv['cur']}/{lv['nxt'] - lv['cur']} XP", 11, "#a9acc6", False, "mm")
    paste_ico(img, "heart_fill", 16, PINK, rx + 44, BH - 60)
    T(d, rx + 68, BH - 52, f"{favs} favorito{'s' if favs != 1 else ''}", 14, "#ffffff", True, "lm")
    born = [i["created"] for i in items if i.get("created")]
    if born:
        dt = datetime.fromtimestamp(min(born))
        T(d, w - 16, BH - 18, f"Desde {MESES[dt.month - 1]}. de {dt.year}", 13, "#a9acc6", anchor="rm")
    base.alpha_composite(img, (mx * K, 0))
    return base


class ImgPage(Page):
    """Página cujo conteúdo é uma lista de imagens (blocos) desenhadas direto no canvas."""

    def __init__(self, app, title=None, back=False):
        super().__init__(app, title, back=back)
        self.view = BlockView(app, self.scroll, self.layout)
        self.after(40, self.view.rebuild)


BANNER_H = 96


def head_banner(holder, W, ico, title, sub, btns=(), hov=None, chip=None):
    """Cabeçalho em banner (igual ao da Coleção). btns: [(rótulo, nome, primário)] da direita p/ esquerda.
    chip: (texto, cor, ícone) — pílula à direita. Devolve (imagem, regiões em px lógicos)."""
    if not hasattr(holder, "_bn"):
        holder._bn = OrderedDict()
    acc = P["accent"]
    img = CollectionPage._banner_img(holder, W, BANNER_H).copy()
    d = ImageDraw.Draw(img)
    paste_ico(img, ico, 30, mix(acc, "#ffffff", .25), 34, 33)
    d = ImageDraw.Draw(img)
    md = ImageDraw.Draw(Image.new("RGB", (4, 4)))
    T(d, 82, 34, title, 30, "#ffffff", True, "lm")
    T(d, 82, 66, sub, 15, mix(acc, "#ffffff", .5), True, "lm")
    bx, regs = W - 24, []
    if chip:
        txt, col, ic = chip
        cw_ = TW(md, txt, 14, True) + 52
        d.rounded_rectangle([(bx - cw_) * K, 28 * K, bx * K, 68 * K], radius=20 * K, fill=mix(col, "#000000", .72),
                            outline=mix(col, "#000000", .35), width=K)
        paste_ico(img, ic, 20, col, bx - cw_ + 14, 38)
        d = ImageDraw.Draw(img)
        T(d, bx - cw_ + 42, 48, txt, 14, "#ffffff", True, "lm")
        bx -= cw_ + 10
    for lab, nm, prim in btns:
        bw = TW(md, lab, 14, True) + 40
        x0 = bx - bw
        col = acc if prim else P["surface"]
        if hov == nm:
            col = P["accent_hover"] if prim else mix(P["surface"], acc, .3)
        d.rounded_rectangle([x0 * K, 28 * K, bx * K, 68 * K], radius=20 * K, fill=col,
                            outline=None if prim else P["border"], width=2 * K)
        T(d, (x0 + bx) / 2, 48, lab, 14, "#ffffff", True, "mm")
        regs.append((x0, 28, bx, 68, nm))
        bx = x0 - 10
    return img, regs


class ProfilePage(ImgPage):
    MAXW = 1800

    def __init__(self, app):
        items = app.items
        stall = sorted([i for i in items if stalled_days(i)], key=lambda i: -stalled_days(i))
        favs = sorted([i for i in items if i["favorite"]], key=lambda i: (-i["rating"], -i["updated"]))
        now = sorted([i for i in items if i["status"] == "lendo"], key=lambda i: -i["updated"])
        lv = level_info(xp_breakdown(app)[1])
        super().__init__(app)
        self.pr, self.lv, self.stall, self.favs, self.now = app.profile, lv, stall, favs, now
        self.specs = {"strip": spec_strip(app), "year": spec_year(app), "ratings": spec_ratings(app),
                      "genres": spec_genres(app), "badges": spec_badges(app, self.view)}
        self._shelf = (None, None, None)
        self.off, self.cur, self._an, self._tc = {}, {}, {}, {}    # fileiras com setas: início, posição animada

    # ---- fileiras com setas: a faixa desliza (sem refazer a página) ----
    def _blk_index(self, key):
        for i, b in enumerate(self.view.blocks):
            if b.key == key:
                return i
        return None

    def _refresh(self, *keys):
        v = self.view
        for key in keys:
            i = self._blk_index(key)
            if i is None:
                continue
            b = v.blocks[i]
            for kk in [kk for kk in v.photos if kk[0] == b.key]:
                v.photos.pop(kk, None)
            if i in v.live:
                try:
                    v._set(i, v.hov[1] if v.hov[0] == i else None)
                except tk.TclError:
                    pass

    def _go(self, key, delta, total, cols):
        top = max(0, total - cols)
        old = self.off.get(key, 0)
        new = max(0, min(top, old + delta))
        if new == old:
            return
        self.off[key] = new
        self._refresh(f"ar-{key}-back", f"ar-{key}-forward")
        st = self._an.setdefault(key, {})
        st.update(frm=self.cur.get(key, float(old)), to=float(new), t0=time.time(), dur=.22)
        if not st.get("run"):
            st["run"] = True
            self._frame(key)

    def _frame(self, key):
        st = self._an.get(key)
        try:
            if st is None or not self.view.alive():
                return
            t = min(1.0, (time.time() - st["t0"]) / st["dur"])
            e = 1 - (1 - t) ** 3
            self.cur[key] = st["frm"] + (st["to"] - st["frm"]) * e
            self._refresh(f"car-{key}")
            if t >= 1.0:
                st["run"] = False
                self.cur[key] = st["to"]
                return
            self.after(14, lambda: self._frame(key))
        except tk.TclError:
            if st:
                st["run"] = False

    def _arrows(self, key, total, cols, xr, y, out):
        """Duas setas (e o intervalo mostrado) à direita do título da fileira."""
        if total <= cols:
            return
        for n, (nm, d_) in enumerate((("back", -1), ("forward", 1))):
            def on_(d_=d_):
                st = self.off.get(key, 0)
                return st > 0 if d_ < 0 else st + cols < total

            def draw(hov, nm=nm, on_=on_):
                on = on_()
                img = Image.new("RGBA", (34 * K, 30 * K), (0, 0, 0, 0))
                dd = ImageDraw.Draw(img)
                col = P["accent"] if (hov and on) else P["border"]
                dd.rounded_rectangle([0, 0, 34 * K - 1, 30 * K - 1], radius=9 * K, fill=P["surface"], outline=col,
                                     width=2)
                ic = _ico(nm, 14, P["text"] if on else P["border"])
                img.alpha_composite(ic, (int((34 * K - ic.width) / 2), int((30 * K - ic.height) / 2)))
                return img
            bx = xr - 34 - (1 - n) * 40
            out.append(Blk(f"ar-{key}-{nm}", bx, y - 1, 34, 30, draw, [(0, 0, 34, 30, "go")],
                           lambda n_, d_=d_: self._go(key, d_, total, cols)))

    def _strip(self, key, lst, empty, x, y, cols, tw, LW, out):
        if not lst:
            out.append(self._note(key + "-e", empty, x, y))
            return y + 30
        app = self.app
        th = tile_height(tw)
        step = tw + 22
        H_ = th + 12
        self.off[key] = min(self.off.get(key, 0), max(0, len(lst) - cols))
        if not (self._an.get(key) or {}).get("run"):
            self.cur[key] = float(self.off[key])
        tc = self._tc

        def tile(it, hot):
            kk = (it["id"], tw, hot, P["bg"])
            if kk not in tc:
                tc[kk] = tile_pil(app, it, tw, tile_chips(it, False), hot, P["bg"])
                if len(tc) > 80:
                    tc.pop(next(iter(tc)))
            return tc[kk]

        def draw(hov, key=key, lst=lst):
            cur = self.cur.get(key, 0.0)
            img = Image.new("RGBA", (LW * K, H_ * K), P["bg"])
            hot_i = int(hov[1:]) if hov and hov.startswith("t") else -1
            j0 = max(0, int(cur) - 1)
            for j in range(j0, min(len(lst), int(cur) + cols + 2)):
                it = lst[j]
                t_ = tile(it, app.item_color(it) if j == hot_i else P["bg"])
                img.paste(t_, (int(((j - cur) * step + 6) * K), 6 * K), t_)
            return img

        regs = [((j - self.off[key]) * step + 6, 6, (j - self.off[key]) * step + 6 + tw + 10, th + 6, f"t{j}")
                for j in range(self.off[key], min(len(lst), self.off[key] + cols))]

        def act(n_, lst=lst):
            if n_.startswith("t"):
                app.open_detail(lst[int(n_[1:])])
        blk = Blk(f"car-{key}", x, y, LW, H_, draw, [], act)
        blk.item = lambda n_, lst=lst: lst[int(n_[1:])] if n_ and n_.startswith("t") else None
        # as regiões acompanham o deslocamento atual (mudam quando a faixa termina de deslizar)
        blk.regs_fn = lambda key=key, lst=lst: [
            ((j - self.off[key]) * step + 6, 6, (j - self.off[key]) * step + 6 + tw + 10, th + 6, f"t{j}")
            for j in range(self.off[key], min(len(lst), self.off[key] + cols))]
        blk.regs = regs
        out.append(blk)
        return y + H_ + 6

    def _title(self, key, text, x, y):
        def draw(hov):
            img = Image.new("RGBA", (560 * K, 28 * K), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.rectangle([0, 3 * K, 3 * K - 1, 27 * K], fill=P["accent"])
            T(d, 13, 1, text, 18, P["text"], True)
            return img
        return Blk(key, x, y, 560, 28, draw)

    def _note(self, key, text, x, y):
        def draw(hov):
            img = Image.new("RGBA", (600 * K, 24 * K), (0, 0, 0, 0))
            T(ImageDraw.Draw(img), 0, 2, text, 14, P["muted"])
            return img
        return Blk(key, x, y, 600, 24, draw)

    def _tiles(self, key, items, empty, x, y, cols, tw, out, rows_max=2):
        if not items:
            out.append(self._note(key + "-e", empty, x, y))
            return y + 30
        th = tile_height(tw)
        app = self.app
        lim = cols * rows_max if rows_max else len(items)
        start = min(getattr(self, "off", {}).get(key, 0), max(0, len(items) - lim))
        for n, it in enumerate(items[start:start + lim]):
            r, c = divmod(n, cols)
            hot = app.item_color(it)

            def draw(hov, it=it, hot=hot):
                return tile_pil(app, it, tw, tile_chips(it, False), hot if hov else P["bg"], P["bg"])
            out.append(Blk(f"{key}-{it['id']}-{tw}", x + c * (tw + 22) + 6, y + r * (th + 12) + 6, tw + 10, th, draw,
                           [(0, 0, tw + 10, th, "go")], lambda n_, it=it: app.open_detail(it), item=it))
        rows = -(-min(len(items) - start, lim) // cols)
        return y + rows * (th + 12) + 12

    def layout(self, avail):
        app, items = self.app, self.app.items
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        two = W >= 1000
        LW = W - 18 - 330 if two else W
        out, y = [], 0
        pr, lv = self.pr, self.lv
        full = int(avail)

        def hdr_draw(hov):
            return profile_header(app, full, hov, pr, lv, pad)
        BH = HBH
        bx0 = pad + W - 16 - 3 * 42 - 2 * 8
        g = _hdr_geom(app, W, pr, lv)
        g["medals"] = [dict(m_, cx=m_["cx"] + pad) for m_ in g["medals"]]
        hb = Blk(f"hdr-{len(g['medals'])}-{full}", 0, y, full, BH, hdr_draw,
                 [(m["cx"] - m["size"] / 2, m["cy"] - m["size"] / 2, m["cx"] + m["size"] / 2, m["cy"] + m["size"] / 2,
                   m["name"]) for m in g["medals"]] +
                 [(bx0, 16, bx0 + 42, 58, "tier"), (bx0 + 50, 16, bx0 + 92, 58, "share"),
                  (bx0 + 100, 16, bx0 + 142, 58, "edit")],
                 lambda n: {"edit": lambda: app.open_sub(ProfileEditPage), "share": app.share_image,
                            "tier": lambda: app.open_sub(TierPage)}.get(n, lambda: app.open_sub(BadgesPage))())
        hb.medals = g["medals"]
        out.append(hb)
        y += BH + 10
        sp = self.specs["strip"]
        h = sp.nat(LW)
        out.append(sp.block("strip", pad, y, LW, h))
        y += h
        cols = max(2, LW // 172)
        tw = max(90, min(190, (LW // cols - 22) // 10 * 10))
        sections = [("fav", "Leituras favoritas", self.favs, "Marque leituras com o coração para elas aparecerem aqui."),
                    ("now", "Lendo agora", self.now, "Nenhuma leitura em andamento.")]
        if self.stall:
            sections.append(("stall", "Retomar leitura", self.stall, ""))
        for key, title, lst, empty in sections:
            y += 22
            out.append(self._title("t-" + key, title, pad, y))
            self._arrows(key, len(lst), cols, pad + LW - 6, y, out)
            y += 28 + 10
            y = self._strip(key, lst, empty, pad, y, cols, tw, LW, out)
        if len(items) >= 3:
            y += 18
            out.append(self._title("t-shelf", "Minha estante", pad, y))
            y += 28 + 10
            ranked = sorted(items, key=lambda i: (not i["favorite"], -i["rating"], i["title"].lower()))
            if self._shelf[0] != LW or self._shelf[1] is None:
                img, hits = shelf_pil([(i, app.item_color(i)) for i in ranked[:60]], int(LW * K), K, cover=app._load_cover)
                self._shelf = (LW, img, hits)
            _, simg, hits = self._shelf
            sh = -(-simg.size[1] // K)
            regs = [(a / K, b / K, c / K, e_ / K, f"it{n}") for n, (a, b, c, e_, _it) in enumerate(hits)]

            ents = [(i, app.item_color(i)) for i in ranked[:60]]

            def sdraw(hov, simg=simg, ents=ents, hits=hits):
                if hov:
                    try:
                        pid = hits[int(hov[2:])][4]["id"]
                        return shelf_pil(ents, int(LW * K), K, pull=pid, cover=app._load_cover)[0].convert("RGBA")
                    except Exception:
                        pass
                return simg.convert("RGBA")
            sb = Blk(f"shelf-{LW}", pad, y, LW, sh, sdraw, regs,
                     lambda n_, hits=hits: app.open_detail(hits[int(n_[2:])][4]))
            sb.tip = lambda n_, hits=hits: hits[int(n_[2:])][4]
            out.append(sb)
            y += sh + 20
        # coluna da direita
        if two:
            rx, ry, rw = pad + LW + 18, BH + 10, 330
        else:
            rx, ry, rw = pad, y + 10, W
        for name in ("year", "ratings", "genres", "badges"):
            sp = self.specs[name]
            h = sp.nat(rw)
            out.append(sp.block(name, rx, ry, rw, h))
            ry += h + 14
        return out



# ---------- cartas colecionáveis ----------
CARD_W, CARD_H = 360, 500
CARD_RAR = {"Comum": ("#9aa0b8", "#5a5f78"), "Rara": ("#6ad0ff", "#2a6aa8"),
            "Épica": ("#c58bff", "#6a2fc0"), "Lendária": ("#ffd95a", "#c27a10")}
RAR_ORDER = ["Comum", "Rara", "Épica", "Lendária"]
_CARDC = OrderedDict()


def card_rarity(it):
    r = it.get("rating", 0)
    return "Lendária" if r >= 5 else "Épica" if r >= 4.5 else "Rara" if r >= 3.5 else "Comum"


def card_numbers(items):
    order = sorted(items, key=lambda i: (i.get("created") or 0, str(i["id"])))
    return {i["id"]: n + 1 for n, i in enumerate(order)}


def _rounded_mask(size, r):
    m = Image.new("L", size, 0)
    ImageDraw.Draw(m).rounded_rectangle([0, 0, size[0] - 1, size[1] - 1], radius=r, fill=255)
    return m


def _TS(d, x, y, text, size, fill, bold=False, anchor="la", stroke=2):
    """Texto com contorno escuro (legível em cima da arte)."""
    font = get_font(max(8, int(round(size * K))), bold)
    sw = max(1, int(stroke * K * .6))
    try:
        d.text((x * K, y * K), str(text), font=font, fill=fill, anchor=anchor, stroke_width=sw, stroke_fill="#05050c")
    except (ValueError, TypeError):
        d.text((x * K, y * K), str(text), font=font, fill=fill)


def _spark(d, cx, cy, r, fill):
    pts = [(cx, cy - r), (cx + r * .22, cy - r * .22), (cx + r, cy), (cx + r * .22, cy + r * .22),
           (cx, cy + r), (cx - r * .22, cy + r * .22), (cx - r, cy), (cx - r * .22, cy - r * .22)]
    d.polygon([(x * K, y * K) for x, y in pts], fill=fill)


def _rainbow(size, hue0, span, alpha=255, step=3):
    """Faixas diagonais de arco-íris (reflexo holográfico)."""
    w, h = size
    im = Image.new("RGBA", size, (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    for k in range(-h, w, step * K):
        hue = (hue0 + (k + h) / (w + h) * span) % 1
        r, g, b = [int(v * 255) for v in colorsys.hsv_to_rgb(hue, .65, 1)]
        d.polygon([(k, 0), (k + step * K + 1, 0), (k + step * K + 1 + h * .6, h), (k + h * .6, h)], fill=(r, g, b, alpha))
    return im


def card_pil(app, it, num, total, shine=0):
    """Carta no estilo de carta de Pokémon (arte cobrindo tudo), 360x500 em K=2. shine>0 realça o reflexo."""
    key = (it["id"], it.get("updated"), it["rating"], it["seen"], it["finished"], str(it.get("crit")), num, total,
           shine, P["bg"], "v2")
    got = _CARDC.get(key)
    if got is not None:
        _CARDC.move_to_end(key)
        return got
    rar = card_rarity(it)
    hi, lo = CARD_RAR[rar]
    W, H = CARD_W, CARD_H
    WK, HK = W * K, H * K
    BW = 9                                            # espessura da moldura
    im = Image.new("RGBA", (WK, HK), (0, 0, 0, 0))
    outer = _rounded_mask(im.size, 20 * K)
    # moldura
    if rar == "Lendária":
        fr = _rainbow(im.size, 0.0, 1.5, 255, 2)
    elif rar == "Épica":
        fr = _rainbow(im.size, 0.70, 0.55, 255, 2)
    else:
        fr = Image.new("RGBA", im.size)
        fd = ImageDraw.Draw(fr)
        for y in range(HK):
            fd.line([(0, y), (WK, y)], fill=mix(hi, lo, y / HK))
        if rar == "Rara":
            fr.alpha_composite(_rainbow(im.size, 0.5, 0.15, 55, 4))
    im.paste(fr, (0, 0), outer)
    # arte (a capa preenchendo o miolo)
    inner = (BW * K, BW * K, WK - BW * K, HK - BW * K)
    iw, ih = inner[2] - inner[0], inner[3] - inner[1]
    try:
        cov = app._load_cover(it).convert("RGB")
    except Exception:
        cov = placeholder(it["title"]).convert("RGB")
    art = ImageOps.fit(cov, (iw, ih), centering=(.5, .3)).convert("RGBA")
    # escurecimento (topo e base) para o texto aparecer
    sh = Image.new("RGBA", (iw, ih), (0, 0, 0, 0))
    sd = ImageDraw.Draw(sh)
    for y in range(int(ih * .16)):
        sd.line([(0, y), (iw, y)], fill=(5, 5, 12, int(150 * (1 - y / (ih * .16)))))
    y0 = int(ih * .56)
    for y in range(y0, ih):
        t = (y - y0) / (ih - y0)
        sd.line([(0, y), (iw, y)], fill=(5, 5, 12, int(225 * min(1, t * 1.25) ** 1.1)))
    art.alpha_composite(sh)
    # reflexo holográfico + brilhos
    if rar in ("Lendária", "Épica") or shine:
        base_a = (62 if rar == "Lendária" else 38 if rar == "Épica" else 0) + shine
        art.alpha_composite(_rainbow((iw, ih), (0.0 if rar == "Lendária" else 0.72) + shine / 500,
                                     1.6 if rar == "Lendária" else .6, min(190, base_a), 3))
    if rar != "Comum":
        rnd = random.Random(str(it["id"]))
        sp = ImageDraw.Draw(art)
        for _ in range({"Rara": 3, "Épica": 6, "Lendária": 10}[rar]):
            x, y = rnd.uniform(.12, .88) * iw / K, rnd.uniform(.14, .6) * ih / K
            r = rnd.uniform(4, 9)
            sd2 = ImageDraw.Draw(art)
            pts = [(x, y - r), (x + r * .22, y - r * .22), (x + r, y), (x + r * .22, y + r * .22),
                   (x, y + r), (x - r * .22, y + r * .22), (x - r, y), (x - r * .22, y - r * .22)]
            sd2.polygon([(px_ * K, py_ * K) for px_, py_ in pts], fill=(255, 255, 255, 215))
    im.paste(art, (inner[0], inner[1]), _rounded_mask((iw, ih), 12 * K))
    d = ImageDraw.Draw(im)
    pad = BW + 8
    # ---- topo: tipo, título, autor, nota ----
    typ = it.get("type", "").upper()
    tw_ = TW(d, typ, 9, True) + 16
    d.rounded_rectangle([pad * K, (pad + 4) * K, (pad + tw_) * K, (pad + 22) * K], radius=5 * K, fill=(238, 240, 248))
    T(d, pad + tw_ / 2, pad + 13, typ, 9, "#16161f", True, "mm")
    hp_w = 92
    tx = pad + tw_ + 8
    title = it["title"]
    size = 21
    while TW(d, title, size, True) > W - tx - hp_w - pad and size > 14:
        size -= 1
    while TW(d, title, size, True) > W - tx - hp_w - pad and len(title) > 4:
        title = title[:-2].rstrip()
        if not title.endswith("…"):
            title += "…"
    _TS(d, tx, pad + 1, title, size, "#ffffff", True, "la", 2.5)
    auth = " • ".join(x for x in (str(it.get("author") or "").strip(), str(it.get("year") or "").strip()) if x) or "Sem autor"
    rb = tx
    rw = min(TW(d, auth, 9) + 26, W - tx - hp_w - pad)
    d.polygon([(rb * K, (pad + 31) * K), ((rb + rw) * K, (pad + 31) * K), ((rb + rw - 8) * K, (pad + 45) * K),
               (rb * K, (pad + 45) * K)], fill=(214, 218, 232, 235))
    T(d, rb + 8, pad + 38, auth if TW(d, auth, 9) < rw - 20 else auth[:int(rw / 6)] + "…", 9, "#20212c", False, "lm")
    # nota (como o HP)
    rtxt = f"{it['rating']:g}".replace(".", ",") if it["rating"] else "–"
    _TS(d, W - pad - 40, pad + 2, rtxt, 28, "#ffffff", True, "ra", 2.5)
    _TS(d, W - pad - 44 - TW(d, rtxt, 28, True), pad + 24, "NOTA", 8.5, "#ffffff", True, "rm", 1.6)
    cx, cy = W - pad - 17, pad + 20
    d.ellipse([(cx - 15) * K, (cy - 15) * K, (cx + 15) * K, (cy + 15) * K], fill=(250, 250, 255), outline=hi, width=2 * K)
    st = star_pil(20 * K, 1, "#cfd2e0")
    im.alpha_composite(st, (int((cx - 10) * K), int((cy - 10) * K)))
    d = ImageDraw.Draw(im)
    # ---- base: habilidade (citação) ----
    q = None
    qs = [x for x in it.get("quotes", []) if x.get("kind") == "citação" and (x.get("text") or "").strip()]
    if qs:
        q = max([x for x in qs if x.get("fav")] or qs, key=lambda x: x.get("ts", 0))
    y = 296
    lab = "Citação"
    lw_ = TW(d, lab, 10, True) + 24
    d.rounded_rectangle([pad * K, y * K, (pad + lw_) * K, (y + 20) * K], radius=10 * K, fill=(176, 28, 40),
                        outline=(255, 190, 190), width=K)
    T(d, pad + lw_ / 2, y + 10, lab, 10, "#ffffff", True, "mm")
    _TS(d, pad + lw_ + 8, y + 10, "Frase favorita" if q and q.get("fav") else "Frase da obra", 15, "#ff8a8a", True,
        "lm", 2.2)
    if q:
        txt = " ".join(str(q["text"]).split())
        for k_, ln in enumerate(wrap_l(txt, 11.5, W - 2 * pad, maxlines=3)):
            _TS(d, pad, y + 26 + k_ * 15, ln, 11.5, "#ffffff", False, "la", 1.8)
    else:
        _TS(d, pad, y + 26, "Salve uma citação na página da obra.", 11.5, "#c7c9dc", False, "la", 1.8)
    # ---- ataque: capítulos ----
    ay = 372
    n_c = max(1, min(5, int(math.ceil(it["rating"])))) if it["rating"] else 1
    xx = pad
    for _ in range(n_c):
        d.ellipse([xx * K, ay * K, (xx + 19) * K, (ay + 19) * K], fill=mix(hi, "#ffffff", .15), outline="#ffffff", width=K)
        stc = star_pil(11 * K, 1, "#ffffff")
        im.alpha_composite(stc, (int((xx + 4) * K), int((ay + 4) * K)))
        xx += 22
    d = ImageDraw.Draw(im)
    _TS(d, xx + 6, ay + 10, "Capítulos lidos", 16, "#ffffff", True, "lm", 2.2)
    _TS(d, W - pad, ay + 10, str(it["seen"]), 24, "#ffffff", True, "rm", 2.5)
    # ---- critérios em "pílulas" ----
    crit = it.get("crit") or {}
    py_ = 400
    pw = (W - 2 * pad - 2 * 6) / 3
    for k_, (lab, k2) in enumerate((("História", "story"), ("Arte", "art"), ("Personagens", "chars"))):
        x0 = pad + k_ * (pw + 6)
        d.rounded_rectangle([x0 * K, py_ * K, (x0 + pw) * K, (py_ + 22) * K], radius=6 * K, fill=(232, 234, 244, 235))
        v = crit.get(k2, 0) or 0
        T(d, x0 + 8, py_ + 11, lab if pw > 90 or len(lab) < 8 else lab[:5] + ".", 9.5, "#34364a", False, "lm")
        T(d, x0 + pw - 8, py_ + 11, f"{v:g}".replace(".", ",") if v else "–", 12, "#14141c", True, "rm")
    # ---- faixa (regra ex): gêneros ----
    by = 432
    tags = " · ".join(t for t in it.get("tags", [])[:3]) or rar
    d.polygon([((pad + 10) * K, by * K), ((W - pad) * K, by * K), ((W - pad - 8) * K, (by + 26) * K),
               ((pad + 2) * K, (by + 26) * K)], fill=mix(hi, "#ffffff", .1))
    d.polygon([((pad + 10) * K, by * K), ((pad + 74) * K, by * K), ((pad + 66) * K, (by + 26) * K),
               ((pad + 2) * K, (by + 26) * K)], fill=(14, 14, 22))
    T(d, pad + 36, by + 13, rar.upper(), 10, hi, True, "mm")
    tg = tags if TW(d, tags, 11, True) < W - 2 * pad - 96 else tags[:28] + "…"
    T(d, pad + 84, by + 13, tg, 11, "#14141c", True, "lm")
    # ---- rodapé ----
    fy = 470
    T(d, pad, fy, f"nº {num:03d}/{total:03d}", 10, "#ffffff", True, "lm")
    T(d, W - pad, fy, ("Fim " + it["finished"]) if it.get("finished") else "", 10, "#d5d7e6", False, "rm")
    # brilho da borda
    if rar != "Comum":
        g = Image.new("RGBA", im.size, (0, 0, 0, 0))
        ImageDraw.Draw(g).rounded_rectangle([0, 0, WK - 1, HK - 1], radius=20 * K, outline=hex_rgba(hi, 150), width=2 * K)
        im.alpha_composite(g.filter(ImageFilter.GaussianBlur(2 * K)))
    _CARDC[key] = im
    while len(_CARDC) > 90:
        _CARDC.popitem(last=False)
    return im


def card_ghost(it, num, w, h, hov=False):
    """Carta ainda não conquistada: silhueta escura com o número."""
    img = Image.new("RGBA", (w * K, h * K), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    col = mix(P["surface"], P["accent"], .22) if hov else P["surface"]
    d.rounded_rectangle([0, 0, w * K - 1, h * K - 1], radius=int(26 * w / CARD_W * K), fill=col,
                        outline=mix(P["border"], P["accent"], .5) if hov else P["border"], width=K)
    d.rounded_rectangle([14 * K, 14 * K, (w - 14) * K, (h - 14) * K], radius=int(18 * w / CARD_W * K),
                        outline=P["surface2"], width=K)
    T(d, w / 2, h * .40, f"nº {num:03d}", max(14, int(w * .12)), P["muted"], True, "mm")
    paste_ico(img, "lock", 28, P["muted"], w / 2 - 14, h * .50 - 6)
    name = it["title"] if len(it["title"]) < 24 else it["title"][:22] + "…"
    T(d, w / 2, h * .66, name, 12, P["muted"], False, "mm")
    prog = {"lendo": f"lendo • cap. {it['seen']}", "planejo": "quero ler", "pausado": "pausado",
            "largado": "largado"}.get(it["status"], "")
    if prog:
        T(d, w / 2, h * .66 + 20, prog, 11, P["muted"], False, "mm")
    return img


def card_back(w, h):
    img = Image.new("RGBA", (w * 2, h * 2), (0, 0, 0, 0))
    g = ImageDraw.Draw(img)
    for y in range(h * 2):
        g.line([(0, y), (w * 2, y)], fill=mix(P["accent"], "#1a1030", y / (h * 2)))
    out = Image.new("RGBA", img.size, (0, 0, 0, 0))
    out.paste(img, (0, 0), _rounded_mask(img.size, int(w * .14)))
    d = ImageDraw.Draw(out)
    d.rounded_rectangle([int(w * .08), int(w * .08), w * 2 - int(w * .08), h * 2 - int(w * .08)],
                        radius=int(w * .1), outline=(255, 255, 255, 90), width=3)
    f = get_font(int(w * .5), True)
    d.text((w, h), "LF", font=f, fill=(255, 255, 255, 190), anchor="mm")
    return out



def _homography(dst, src):
    """Coeficientes da transformação de perspectiva (saída -> entrada) a partir de 4 pontos."""
    A, B = [], []
    for (x, y), (u, v) in zip(dst, src):
        A.append([x, y, 1, 0, 0, 0, -u * x, -u * y])
        B.append(u)
        A.append([0, 0, 0, x, y, 1, -v * x, -v * y])
        B.append(v)
    n = 8
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(A[r][c]))
        A[c], A[p], B[c], B[p] = A[p], A[c], B[p], B[c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for k in range(c, n):
                A[r][k] -= f * A[c][k]
            B[r] -= f * B[c]
    x = [0.0] * n
    for r in range(n - 1, -1, -1):
        x[r] = (B[r] - sum(A[r][k] * x[k] for k in range(r + 1, n))) / A[r][r]
    return x


_GLARE = {}


def tilt_card(src, out_size, center, u, v, maxdeg=14, glare=True):
    """Inclina a carta (u, v entre -1 e 1 = posição do mouse) com perspectiva e um reflexo que segue o cursor."""
    w, h = src.size
    if glare:
        g = _GLARE.get(w)
        if g is None:
            g = Image.radial_gradient("L").resize((int(w * .95), int(w * .95)), Image.BILINEAR)
            g = g.point(lambda p: int(255 * .38 * (max(0, 150 - p) / 150) ** 1.6))
            _GLARE[w] = g
        layer = Image.new("L", src.size, 0)
        layer.paste(g, (int((u + 1) / 2 * w - g.width / 2), int((v + 1) / 2 * h - g.height / 2)))
        base = src.copy()
        wl = Image.new("RGBA", src.size, (255, 255, 255, 0))
        wl.putalpha(layer)
        base.alpha_composite(wl)
        base.putalpha(src.getchannel("A"))
    else:
        base = src
    ay, ax = math.radians(u * maxdeg), math.radians(-v * maxdeg)
    D = 3.2 * max(w, h)
    pts = []
    for x, y in ((-w / 2, -h / 2), (w / 2, -h / 2), (w / 2, h / 2), (-w / 2, h / 2)):
        x1, z1 = x * math.cos(ay), -x * math.sin(ay)
        y2, z2 = y * math.cos(ax) - z1 * math.sin(ax), y * math.sin(ax) + z1 * math.cos(ax)
        sc = D / (D + z2)
        pts.append((center[0] + x1 * sc, center[1] + y2 * sc))
    co = _homography(pts, [(0, 0), (w, 0), (w, h), (0, h)])
    return base.transform(out_size, Image.PERSPECTIVE, co, Image.BICUBIC)


class CardViewPage(Page):
    MAXW = 520

    def __init__(self, app, it):
        super().__init__(app, it["title"] if len(it["title"]) < 34 else it["title"][:32] + "…", back=True)
        self.it = it
        nums = card_numbers(app.items)
        self.img = card_pil(app, it, nums[it["id"]], len(app.items), 0)
        accent_button(self.footer, "Salvar como imagem", self.save, width=170).pack(side="right")
        ghost_button(self.footer, "Abrir obra", lambda: app.open_detail(it), width=110).pack(side="right", padx=8)
        big = self.img.resize((432, 600), Image.LANCZOS)
        ctk.CTkLabel(self.col, text="", image=ctk.CTkImage(big, size=(432, 600))).pack(pady=(10, 0))
        rar = card_rarity(it)
        ctk.CTkLabel(self.col, text=f"Carta {rar.lower()}", text_color=CARD_RAR[rar][0],
                     font=ctk.CTkFont(size=15, weight="bold")).pack(pady=(10, 0))

    def save(self):
        safe = "".join(c if c.isalnum() else "_" for c in self.it["title"])[:40] or "carta"
        p = filedialog.asksaveasfilename(parent=self.app, defaultextension=".png", initialfile=f"carta_{safe}.png",
                                         filetypes=[("PNG", "*.png")])
        if p:
            try:
                self.img.save(p)
                self.app.toast("Carta salva")
            except OSError as e:
                messagebox.showerror("Erro", f"Não consegui salvar:\n{e}", parent=self.app)


class CollectionPage(ImgPage):
    MAXW = 1800

    def __init__(self, app):
        super().__init__(app, None)
        self._small = OrderedDict()
        self.f = {"rar": "Todas", "have": "Todas", "type": "Todos", "year": "Todos", "sort": "Mais recentes"}
        self.q, self.focus, self._qj, self._bn = "", False, None, OrderedDict()
        self.view.cv.bind("<Key>", self._key, add="+")
        self.view.cv.bind("<FocusOut>", lambda e: self._set_focus(False), add="+")

    SORTS = ["Mais recentes", "Número da carta", "Maior nota", "Raridade", "Título (A–Z)"]

    # ---- busca digitada direto na imagem ----
    def _redraw_filters(self):
        v = self.view
        for i, b in enumerate(v.blocks):
            if b.key.startswith("cl-filters"):
                for kk in [kk for kk in v.photos if kk[0] == b.key]:
                    v.photos.pop(kk, None)
                if i in v.live:
                    try:
                        v._set(i, v.hov[1] if v.hov[0] == i else None)
                    except tk.TclError:
                        pass
                return

    def _set_focus(self, on):
        if self.focus != on:
            self.focus = on
            self._redraw_filters()

    def _later(self):
        if self._qj:
            try:
                self.after_cancel(self._qj)
            except Exception:
                pass
        self._qj = self.after(220, self.view.rebuild)

    def _key(self, e):
        if not self.focus:
            return None
        ks = e.keysym
        if ks in ("Return", "Escape"):
            self._set_focus(False)
            return "break"
        if ks == "BackSpace":
            self.q = self.q[:-1]
        elif isinstance(e.state, int) and e.state & 0x4:
            if ks.lower() != "v":
                return None
            try:
                self.q = (self.q + self.clipboard_get().splitlines()[0])[:60]
            except (tk.TclError, IndexError):
                return "break"
        elif e.char and e.char.isprintable() and len(self.q) < 60:
            self.q += e.char
        else:
            return None
        self._redraw_filters()
        self._later()
        return "break"

    # ---- cabeçalho com banner ----
    def _banner_img(self, W, h):
        pr = self.app.profile
        key = (W, h, P["accent"], pr.get("banner"))
        got = self._bn.get(key)
        if got is not None:
            return got
        bp = profile_dir() / pr["banner"] if pr.get("banner") else None
        try:
            base = ImageOps.fit(Image.open(bp).convert("RGB"), (W * K, h * K)) if bp and bp.exists() else None
        except OSError:
            base = None
        if base is None:
            c1, c2 = hex_shade(P["accent"], .95), hex_shade(P["accent"], .22)
            base = Image.new("RGB", (W * K, h * K))
            dd = ImageDraw.Draw(base)
            for x in range(0, W * K, 2):
                dd.line([(x, 0), (x, h * K)], fill=mix(c2, c1, x / (W * K)), width=2)
        base = Image.blend(base, Image.new("RGB", base.size, P["bg"]), .25)
        fade = Image.new("L", (W * K, 1))
        for x in range(W * K):
            fade.putpixel((x, 0), int(255 * max(0.0, min(1.0, (x / (W * K) - .28) / .5)) ** 1.2))
        img = Image.composite(base, Image.new("RGB", base.size, P["bg"]), fade.resize(base.size)).convert("RGBA")
        m = Image.new("L", img.size, 0)
        ImageDraw.Draw(m).rounded_rectangle([0, 0, W * K - 1, h * K - 1], radius=20 * K, fill=255)
        out = Image.new("RGBA", img.size, (0, 0, 0, 0))
        out.paste(img, (0, 0), m)
        ImageDraw.Draw(out).rounded_rectangle([0, 0, W * K - 1, h * K - 1], radius=20 * K, outline=P["border"], width=K)
        self._bn[key] = out
        while len(self._bn) > 3:
            self._bn.pop(next(iter(self._bn)))
        return out

    def layout(self, avail):
        app, items = self.app, self.app.items
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        nums = card_numbers(items)
        total = len(items)
        done = [i for i in items if i["status"] == "completo"]
        tally = Counter(card_rarity(i) for i in done)
        out, y = [], 8

        accent = P["accent"]
        HH = 96

        def head(hov):
            img = self._banner_img(W, HH).copy()
            d = ImageDraw.Draw(img)
            lc = mix(accent, "#ffffff", .25)
            d.rounded_rectangle([34 * K, 36 * K, 56 * K, 68 * K], radius=5 * K, outline=mix(accent, "#000000", .15), width=2 * K)
            d.rounded_rectangle([44 * K, 28 * K, 66 * K, 60 * K], radius=5 * K, outline=lc, width=2 * K,
                                fill=hex_rgba(P["bg"], 140))
            T(d, 92, 34, "Coleção", 30, "#ffffff", True, "lm")
            T(d, 92, 66, f"{len(done)} de {total} cartas", 15, mix(accent, "#ffffff", .5), True, "lm")
            md = ImageDraw.Draw(Image.new("RGB", (4, 4)))
            widths = [24 + TW(md, str(tally.get(r, 0)), 14, True) for r in RAR_ORDER]
            pw = sum(widths) + 22 * len(RAR_ORDER) + 6
            x0 = W - 24 - pw
            ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
            ImageDraw.Draw(ov).rounded_rectangle([x0 * K, 26 * K, (W - 24) * K, 70 * K], radius=16 * K,
                                                 fill=(9, 8, 20, 190), outline=hex_rgba(P["border"], 255), width=K)
            img.alpha_composite(ov)
            d = ImageDraw.Draw(img)
            x = x0 + 18
            for r in RAR_ORDER:
                d.ellipse([x * K, 42 * K, (x + 12) * K, 54 * K], fill=CARD_RAR[r][0])
                T(d, x + 20, 48, str(tally.get(r, 0)), 14, "#ffffff", True, "lm")
                x += 22 + 24 + TW(md, str(tally.get(r, 0)), 14, True) - 6
            return img
        out.append(Blk(f"cl-head-{len(done)}-{total}-{W}-{accent}", pad, y, W, HH, head))
        y += HH + 14
        types = [t for t in TYPES if any(i["type"] == t for i in items)]
        years = sorted({year_of(i["finished"]) for i in done if year_of(i["finished"])}, reverse=True)[:8]
        groups = [("gem", "Raridade", "rar", ["Todas"] + RAR_ORDER),
                  ("eye", "Mostrar", "have", ["Todas", "Conquistadas", "Faltando"])]
        if len(types) > 1:
            groups.append(("book", "Tipo", "type", ["Todos"] + types))
        if years:
            groups.append(("cal", "Ano", "year", ["Todos"] + [str(a) for a in years]))
        md = ImageDraw.Draw(Image.new("RGB", (4, 4)))
        CH_, GAP = 30, 6
        glay = []
        for ic, lab, key, vals in groups:
            cw_ = [TW(md, v, 12, True) + 26 for v in vals]
            gw = max(sum(cw_) + GAP * (len(vals) - 1), 24 + TW(md, lab, 13, True))
            glay.append((ic, lab, key, vals, cw_, gw))
        SW, FB, SP = 250, 44, 12
        rows_g, cur_, used = [[]], 0, 0
        for g_ in glay:
            lim = W - 40 - (SW + SP + FB + 24 if len(rows_g) == 1 else 0)
            if rows_g[-1] and used + g_[5] > lim:
                rows_g.append([])
                used = 0
            rows_g[-1].append(g_)
            used += g_[5] + 26
        FH = 28 + len(rows_g) * 62 + (len(rows_g) - 1) * 6
        f = self.f
        active = any(f[k] != d_ for k, d_ in (("rar", "Todas"), ("have", "Todas"), ("type", "Todos"), ("year", "Todos"))) \
            or bool(self.q)
        regs, spots = [], []
        for ri, row in enumerate(rows_g):
            ry = 14 + ri * 68
            gx = 22
            for gi, (ic, lab, key, vals, cw_, gw) in enumerate(row):
                spots.append((ic, lab, gx, ry, key, vals, cw_, gw, gi < len(row) - 1))
                cx_ = gx
                for v, w_ in zip(vals, cw_):
                    regs.append((cx_, ry + 26, cx_ + w_, ry + 26 + CH_, f"c|{key}|{v}"))
                    cx_ += w_ + GAP
                gx += gw + 26
        sx0 = W - 20 - FB - SP - SW
        sy0 = 14 + 14
        regs += [(sx0, sy0, sx0 + SW, sy0 + 40, "search"), (W - 20 - FB, sy0, W - 20, sy0 + 40, "clear")]

        def filters(hov):
            img = Image.new("RGBA", (W * K, FH * K), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.rounded_rectangle([0, 0, W * K - 1, FH * K - 1], radius=20 * K, fill=P["surface"], outline=P["border"], width=K)
            for ic, lab, gx, ry, key, vals, cw_, gw, div in spots:
                if ic == "eye":
                    cx0, cy0 = gx + 8, ry + 8
                    d.ellipse([(cx0 - 8) * K, (cy0 - 5) * K, (cx0 + 8) * K, (cy0 + 5) * K], outline=P["muted"], width=int(1.6 * K))
                    d.ellipse([(cx0 - 2.5) * K, (cy0 - 2.5) * K, (cx0 + 2.5) * K, (cy0 + 2.5) * K], fill=P["muted"])
                elif ic == "cal":
                    d.rounded_rectangle([gx * K, (ry + 1) * K, (gx + 15) * K, (ry + 15) * K], radius=3 * K, outline=P["muted"], width=int(1.6 * K))
                    d.line([(gx * K, (ry + 6) * K), ((gx + 15) * K, (ry + 6) * K)], fill=P["muted"], width=int(1.6 * K))
                else:
                    paste_ico(img, ic, 16, P["muted"], gx, ry)
                T(d, gx + 24, ry + 8, lab, 13, P["text"], True, "lm")
                cx_ = gx
                for v, w_ in zip(vals, cw_):
                    on = f[key] == v
                    nm = f"c|{key}|{v}"
                    col = accent if on else (mix(P["surface2"], accent, .3) if hov == nm else P["surface2"])
                    d.rounded_rectangle([cx_ * K, (ry + 26) * K, (cx_ + w_) * K, (ry + 26 + CH_) * K], radius=15 * K, fill=col)
                    T(d, cx_ + w_ / 2, ry + 26 + CH_ / 2, v, 12, "#ffffff" if on else P["text"], True, "mm")
                    cx_ += w_ + GAP
                if div:
                    lx = gx + gw + 13
                    d.line([(lx * K, (ry + 2) * K), (lx * K, (ry + 56) * K)], fill=P["border"], width=K)
            # busca
            fo = self.focus
            d.rounded_rectangle([sx0 * K, sy0 * K, (sx0 + SW) * K, (sy0 + 40) * K], radius=20 * K, fill=P["bg"],
                                outline=accent if (fo or hov == "search") else P["border"], width=2 * K if fo else K)
            paste_ico(img, "search", 16, P["muted"], sx0 + 14, sy0 + 12)
            if self.q:
                txt = self.q
                while TW(md, txt, 14) > SW - 64 and len(txt) > 1:
                    txt = txt[1:]
                T(d, sx0 + 40, sy0 + 20, txt, 14, P["text"], False, "lm")
                cxp = sx0 + 40 + TW(md, txt, 14) + 2
            else:
                T(d, sx0 + 40, sy0 + 20, "Buscar na coleção...", 14, P["muted"], False, "lm")
                cxp = sx0 + 40
            if fo:
                d.line([(cxp * K, (sy0 + 11) * K), (cxp * K, (sy0 + 29) * K)], fill=P["text"], width=int(1.6 * K))
            # filtro (limpar)
            fx = W - 20 - FB
            on = active
            d.rounded_rectangle([fx * K, sy0 * K, (fx + FB) * K, (sy0 + 40) * K], radius=14 * K,
                                fill=accent if on else (mix(P["surface2"], accent, .3) if hov == "clear" else P["surface2"]))
            cx0, cy0 = fx + FB / 2, sy0 + 20
            fcol = "#ffffff" if on else P["text"]
            d.polygon([((cx0 - 8) * K, (cy0 - 7) * K), ((cx0 + 8) * K, (cy0 - 7) * K), ((cx0 + 2) * K, (cy0 + 1) * K),
                       ((cx0 + 2) * K, (cy0 + 8) * K), ((cx0 - 2) * K, (cy0 + 5) * K), ((cx0 - 2) * K, (cy0 + 1) * K)], fill=fcol)
            return img

        def fact(n):
            if n == "search":
                self.focus = True
                self.view.cv.focus_set()
                self._redraw_filters()
                return
            self.focus = False
            if n == "clear":
                self.f.update(rar="Todas", have="Todas", type="Todos", year="Todos")
                self.q = ""
            elif n.startswith("c|"):
                _, k_, v_ = n.split("|", 2)
                self.f[k_] = v_
            self.view.rebuild()
        out.append(Blk(f"cl-filters-{W}-{FH}", pad, y, W, FH, filters, regs, fact))
        y += FH + 24

        def stitle(hov):
            img = Image.new("RGBA", (W * K, 44 * K), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.rectangle([0, 6 * K, 3 * K - 1, 38 * K], fill=accent)
            T(d, 16, 22, "Suas Cartas", 24, "#ffffff", True, "lm")
            bw = 200
            bx = W - bw
            d.rounded_rectangle([bx * K, 3 * K, (bx + bw) * K, 41 * K], radius=14 * K,
                                fill=mix(P["surface"], accent, .15) if hov == "sort" else P["surface"], outline=P["border"], width=K)
            for k_, ww in enumerate((12, 9, 6)):
                d.line([((bx + 16) * K, (16 + k_ * 6) * K), ((bx + 16 + ww) * K, (16 + k_ * 6) * K)], fill=P["muted"], width=int(1.8 * K))
            T(d, bx + 40, 22, self.f["sort"], 14, P["text"], False, "lm")
            cx0 = bx + bw - 22
            d.line([((cx0 - 5) * K, 20 * K), (cx0 * K, 25 * K), ((cx0 + 5) * K, 20 * K)], fill=P["muted"], width=int(1.8 * K))
            return img

        def sact(n):
            self.focus = False
            m = tk.Menu(self, tearoff=0, bg=P["surface"], fg=P["text"], activebackground=P["surface2"],
                        activeforeground=P["text"], bd=0, relief="flat", font=("TkDefaultFont", fpt(11)))
            for o in self.SORTS:
                m.add_command(label=("✓  " if o == self.f["sort"] else "      ") + o,
                              command=lambda o=o: (self.f.update(sort=o), self.view.rebuild()))
            try:
                m.tk_popup(self.winfo_pointerx(), self.winfo_pointery())
            finally:
                m.grab_release()
        out.append(Blk(f"cl-sort-{W}-{self.f['sort']}", pad, y, W, 44, stitle, [(W - 200, 3, W, 41, "sort")], sact))
        y += 44 + 12
        sel = []
        qn = unicodedata.normalize("NFKD", self.q).encode("ascii", "ignore").decode().lower().strip()

        def hay(it):
            return unicodedata.normalize("NFKD", " ".join([it["title"], it.get("author") or "", " ".join(it["tags"])])
                                         ).encode("ascii", "ignore").decode().lower()

        def fin(it):
            d_ = parse_date(it["finished"]) if it["status"] == "completo" else None
            return d_.toordinal() if d_ else 0
        rank = {r_: n_ for n_, r_ in enumerate(RAR_ORDER)}
        skeys = {"Mais recentes": lambda i: (i["status"] != "completo", -fin(i), -(i.get("updated") or 0)),
                 "Número da carta": lambda i: nums[i["id"]],
                 "Maior nota": lambda i: (-(i["rating"] or 0), nums[i["id"]]),
                 "Raridade": lambda i: (i["status"] != "completo", -rank[card_rarity(i)], nums[i["id"]]),
                 "Título (A–Z)": lambda i: i["title"].lower()}
        for it in sorted(items, key=skeys.get(f["sort"], skeys["Mais recentes"])):
            is_done = it["status"] == "completo"
            if qn and qn not in hay(it):
                continue
            if f["type"] != "Todos" and it["type"] != f["type"]:
                continue
            if f["have"] == "Conquistadas" and not is_done:
                continue
            if f["have"] == "Faltando" and is_done:
                continue
            if f["rar"] != "Todas" and (not is_done or card_rarity(it) != f["rar"]):
                continue
            if f["year"] != "Todos" and (not is_done or str(year_of(it["finished"])) != f["year"]):
                continue
            sel.append(it)
        if not sel:
            msg = ("Nenhuma carta encontrada." if (total and (self.q or any(
                self.f[k_] != d_ for k_, d_ in (("rar", "Todas"), ("have", "Todas"), ("type", "Todos"), ("year", "Todos")))))
                   else "Nenhuma carta aqui ainda." if total else "Adicione leituras e termine-as para ganhar cartas.")
            out.append(Blk("cl-empty", pad, y, 600, 30,
                           lambda hov: (lambda im: (T(ImageDraw.Draw(im), 0, 4, msg, 15, P["muted"]), im)[1])(
                               Image.new("RGBA", (600 * K, 30 * K), (0, 0, 0, 0)))))
            return out
        gap = 18
        cols = max(2, (W + gap) // (230 + gap))
        cell = (W - (cols - 1) * gap) / cols
        cw = int(cell - 16)
        ch = int(cw * CARD_H / CARD_W)
        for n, it in enumerate(sel):
            r, c = divmod(n, cols)
            bx, by = pad + c * (cell + gap), y + r * (ch + 28)
            is_done = it["status"] == "completo"
            num = nums[it["id"]]

            def draw(hov, it=it, num=num, is_done=is_done):
                img = Image.new("RGBA", (int(cell) * K, (ch + 20) * K), (0, 0, 0, 0))
                oy = 4 if hov else 12
                if is_done:
                    rar = card_rarity(it)
                    sh = Image.new("RGBA", img.size, (0, 0, 0, 0))
                    ImageDraw.Draw(sh).rounded_rectangle([8 * K, (oy + 8) * K, (8 + cw) * K, (oy + ch + 8) * K],
                                                         radius=int(24 * K * cw / CARD_W),
                                                         fill=hex_rgba(CARD_RAR[rar][0], 90) if hov and rar != "Comum"
                                                         else (0, 0, 0, 120))
                    img.alpha_composite(sh.filter(ImageFilter.GaussianBlur(9 * K)))
                    src = card_pil(app, it, num, total, 45 if (hov and rar in ("Épica", "Lendária")) else
                                   (20 if hov else 0))
                    small = src.resize((cw * K, ch * K), Image.LANCZOS)
                    img.alpha_composite(small, (8 * K, oy * K))
                else:
                    gh = card_ghost(it, num, cw, ch, bool(hov))
                    img.alpha_composite(gh, (8 * K, oy * K))
                return img
            blk = Blk(f"card-{it['id']}-{cw}-{is_done}", bx, by, int(cell), ch + 20, draw,
                      [(0, 0, int(cell), ch + 20, "go")],
                      (lambda n_, it=it, d_=is_done: app.open_sub(CardViewPage, it) if d_ else app.open_detail(it)))
            if is_done and card_rarity(it) in ("Épica", "Lendária"):
                def move(rx, ry, it=it, num=num, cell=cell, cw=cw, ch=ch):
                    key = (it["id"], it.get("updated"), it["rating"], cw)
                    small = self._small.get(key)
                    if small is None:
                        small = card_pil(app, it, num, total, 30).resize((cw * K, ch * K), Image.LANCZOS)
                        self._small[key] = small
                        while len(self._small) > 8:
                            self._small.pop(next(iter(self._small)))
                    u = max(-1, min(1, (rx - cell / 2) / (cw / 2)))
                    v = max(-1, min(1, (ry - (4 + ch / 2)) / (ch / 2)))
                    canvas = (int(cell) * K, (ch + 20) * K)
                    img = Image.new("RGBA", canvas, (0, 0, 0, 0))
                    rar = card_rarity(it)
                    sh = Image.new("RGBA", canvas, (0, 0, 0, 0))
                    ImageDraw.Draw(sh).rounded_rectangle(
                        [(cell - cw) / 2 * K + (-u * 8) * K, (12 - v * 6) * K,
                         ((cell + cw) / 2) * K + (-u * 8) * K, (12 + ch - v * 6) * K], radius=22 * K,
                        fill=hex_rgba(CARD_RAR[rar][0], 110))
                    img.alpha_composite(sh.filter(ImageFilter.GaussianBlur(10 * K)))
                    img.alpha_composite(tilt_card(small, canvas, (cell / 2 * K, (4 + ch / 2) * K), u, v))
                    return img
                blk.move = move
            out.append(blk)
        rows_n = -(-len(sel) // cols)
        out.append(Blk("cl-end", pad, y + rows_n * (ch + 28), 10, 10, lambda hov: Image.new("RGBA", (10 * K, 10 * K))))
        return out


# ---------- visualizador de prints ----------
class ShotViewPage(ctk.CTkFrame):
    """Print em tela grande: setas, zoom com a roda do mouse, arrastar, favoritar, capítulo e legenda."""

    def __init__(self, app, entries, idx=0):
        super().__init__(app.main, fg_color=P["bg"])
        self.app = app
        self.entries = list(entries)
        self.i = max(0, min(idx, len(self.entries) - 1))
        self.full, self.z, self.cx, self.cy, self._ph, self._drag = None, 1.0, 0.0, 0.0, None, None
        top = ctk.CTkFrame(self, fg_color="transparent")
        top.pack(fill="x", padx=22, pady=(18, 6))
        ghost_button(top, " Voltar", app.go_back, image=icon("back", 16), compound="left", width=96,
                     height=34).pack(side="left", padx=(0, 14))
        self.ttl = ctk.CTkLabel(top, text="", text_color=P["text"], font=ctk.CTkFont(size=17, weight="bold"))
        self.ttl.pack(side="left")
        self.cnt = ctk.CTkLabel(top, text="", text_color=P["muted"])
        self.cnt.pack(side="right")
        self.cv = tk.Canvas(self, bg=P["bg"], highlightthickness=0, bd=0)
        self.cv.pack(fill="both", expand=True, padx=22)
        bar = ctk.CTkFrame(self, fg_color=P["surface"], corner_radius=16, border_width=1, border_color=P["border"])
        bar.pack(fill="x", padx=22, pady=(8, 16))
        row = ctk.CTkFrame(bar, fg_color="transparent")
        row.pack(fill="x", padx=12, pady=10)
        ghost_button(row, "", lambda: self.go(-1), image=icon("back", 14), width=34, height=34).pack(side="left")
        ghost_button(row, "", lambda: self.go(1), image=icon("forward", 14), width=34, height=34).pack(
            side="left", padx=(6, 10))
        self.fav_b = ghost_button(row, "", self.toggle_fav, image=icon("star", 16), width=40, height=34)
        self.fav_b.pack(side="left", padx=(0, 10))
        ctk.CTkLabel(row, text="cap.", text_color=P["muted"]).pack(side="left", padx=(0, 4))
        self.ch_e = entry(row, "", width=58, height=34)
        self.ch_e.pack(side="left", padx=(0, 10))
        self.cap_e = entry(row, "Legenda (opcional)...", height=34)
        self.cap_e.pack(side="left", fill="x", expand=True, padx=(0, 10))
        for e in (self.ch_e, self.cap_e):
            e.bind("<Return>", lambda ev: (self.save_meta(), self.cv.focus_set()), add="+")
            e.bind("<FocusOut>", lambda ev: self.save_meta(), add="+")
        ghost_button(row, "Ir para a obra", lambda: app.open_detail(self.cur()[0]), height=34, width=110).pack(
            side="left", padx=(0, 6))
        ghost_button(row, "Salvar como...", self.save_as, height=34, width=112).pack(side="left", padx=(0, 6))
        danger_button(row, "Excluir", self.delete, height=34, width=80).pack(side="left")
        cv = self.cv
        cv.bind("<Configure>", lambda e: self._render())
        cv.bind("<MouseWheel>", self._wheel)
        cv.bind("<Button-4>", lambda e: self._wheel(e, 1))
        cv.bind("<Button-5>", lambda e: self._wheel(e, -1))
        cv.bind("<ButtonPress-1>", self._down)
        cv.bind("<B1-Motion>", self._move)
        cv.bind("<Double-Button-1>", lambda e: self._reset())
        cv.bind("<Left>", lambda e: self.go(-1))
        cv.bind("<Right>", lambda e: self.go(1))
        cv.bind("<Delete>", lambda e: self.delete())
        self._load()
        self.after(80, cv.focus_set)

    def cur(self):
        return self.entries[self.i]

    def go(self, d):
        if len(self.entries) > 1:
            self.save_meta()
            self.i = (self.i + d) % len(self.entries)
            self._load()

    def _load(self):
        it, s = self.cur()
        self.full = shot_full(s)
        self._reset(False)
        self.ttl.configure(text=it["title"])
        self.cnt.configure(text=f"print {self.i + 1} de {len(self.entries)}")
        self.ch_e.delete(0, "end")
        if s.get("ch") is not None:
            self.ch_e.insert(0, str(s["ch"]))
        self.cap_e.delete(0, "end")
        self.cap_e.insert(0, s.get("cap", ""))
        self._fav_icon()
        self._render()

    def _fav_icon(self):
        on = bool(self.cur()[1].get("fav"))
        self.fav_b.configure(image=icon("star", 16, GOLD_HEX if on else P["muted"]),
                             border_color=GOLD_HEX if on else P["border"])

    def _reset(self, render=True):
        if self.full is not None:
            self.z, self.cx, self.cy = 1.0, self.full.width / 2, self.full.height / 2
        if render:
            self._render()

    def _base(self):
        cw, ch = max(50, self.cv.winfo_width()), max(50, self.cv.winfo_height())
        return min(cw / self.full.width, ch / self.full.height, 1.0 if False else 99)

    def _render(self, fast=False):
        if self.full is None or not self.winfo_exists():
            return
        cw, ch = max(50, self.cv.winfo_width()), max(50, self.cv.winfo_height())
        iw, ih = self.full.size
        base = min((cw - 8) / iw, (ch - 8) / ih)
        sc = base * self.z
        vw, vh = cw / sc, ch / sc
        x0 = 0 if vw >= iw else max(0, min(iw - vw, self.cx - vw / 2))
        y0 = 0 if vh >= ih else max(0, min(ih - vh, self.cy - vh / 2))
        if vw < iw:
            self.cx = x0 + vw / 2
        if vh < ih:
            self.cy = y0 + vh / 2
        box = (int(x0), int(y0), int(min(iw, x0 + vw) + 1), int(min(ih, y0 + vh) + 1))
        box = (box[0], box[1], min(iw, box[2]), min(ih, box[3]))
        size = (max(1, round((box[2] - box[0]) * sc)), max(1, round((box[3] - box[1]) * sc)))
        im = self.full.crop(box).resize(size, Image.BILINEAR if fast else Image.LANCZOS)
        self._ph = ImageTk.PhotoImage(im)
        self.cv.delete("all")
        self.cv.create_image(cw // 2, ch // 2, image=self._ph, anchor="center")

    def _wheel(self, e, step=None):
        if self.full is None:
            return
        up = (step > 0) if step is not None else e.delta > 0
        cw, ch = max(50, self.cv.winfo_width()), max(50, self.cv.winfo_height())
        base = min((cw - 8) / self.full.width, (ch - 8) / self.full.height)
        old = base * self.z
        nz = max(1.0, min(10.0, self.z * (1.2 if up else 1 / 1.2)))
        new = base * nz
        mx, my = e.x - cw / 2, e.y - ch / 2
        ix, iy = self.cx + mx / old, self.cy + my / old
        self.z = nz
        if nz <= 1.0001:
            self._reset(False)
        else:
            self.cx, self.cy = ix - mx / new, iy - my / new
        self._render(fast=True)
        if getattr(self, "_zj", None):
            self.after_cancel(self._zj)
        self._zj = self.after(160, self._render)

    def _down(self, e):
        self.cv.focus_set()
        self._drag = (e.x, e.y)

    def _move(self, e):
        if not self._drag or self.z <= 1.0001:
            return
        cw, ch = max(50, self.cv.winfo_width()), max(50, self.cv.winfo_height())
        sc = min((cw - 8) / self.full.width, (ch - 8) / self.full.height) * self.z
        self.cx -= (e.x - self._drag[0]) / sc
        self.cy -= (e.y - self._drag[1]) / sc
        self._drag = (e.x, e.y)
        self._render(fast=True)

    def save_meta(self):
        try:
            it, s = self.cur()
        except IndexError:
            return
        raw = self.ch_e.get().strip()
        ch = int(raw) if raw.isdigit() else None
        cap = self.cap_e.get().strip()
        if ch != s.get("ch") or cap != s.get("cap", ""):
            s["ch"], s["cap"] = ch, cap
            self.app.commit(it["id"])

    def toggle_fav(self):
        it, s = self.cur()
        s["fav"] = not s.get("fav")
        self.app.commit(it["id"])
        self._fav_icon()

    def save_as(self):
        it, s = self.cur()
        safe = "".join(c if c.isalnum() else "_" for c in it["title"])[:30] or "print"
        ext = Path(s["file"]).suffix
        p = filedialog.asksaveasfilename(parent=self.app, defaultextension=ext, initialfile=f"{safe}_print{ext}",
                                         filetypes=[("Imagem", f"*{ext}"), ("Todos", "*.*")])
        if not p:
            return
        try:
            shutil.copy(shot_file(s), p)
        except OSError:
            self.app.toast("Não consegui salvar.", "err")
            return
        self.app.toast("Imagem salva")

    def delete(self):
        it, s = self.cur()
        if not messagebox.askyesno("Excluir print", "Excluir este print?", parent=self.app):
            return
        if s in it.get("shots", []):
            it["shots"].remove(s)
        del_shot_files(s)
        self.app.commit(it["id"])
        self.entries.pop(self.i)
        if not self.entries:
            return self.app.go_back()
        self.i = min(self.i, len(self.entries) - 1)
        self._load()


# ---------- galeria (todos os prints) ----------
class GalleryPage(ImgPage):
    MAXW = 1800
    SORTS = ["Mais recentes", "Mais antigos", "Por obra", "Por capítulo"]
    _banner_img = CollectionPage._banner_img
    _redraw_filters = CollectionPage._redraw_filters
    _set_focus = CollectionPage._set_focus
    _later = CollectionPage._later
    _key = CollectionPage._key

    def __init__(self, app, obra=None):
        super().__init__(app, None, back=bool(obra))
        self.obra = obra
        self.f = {"fav": "Todos", "type": "Todos", "sort": "Mais recentes"}
        self.q, self.focus, self._qj, self._bn = "", False, None, OrderedDict()
        self.view.cv.bind("<Key>", self._key, add="+")
        self.view.cv.bind("<FocusOut>", lambda e: self._set_focus(False), add="+")

    def _menu_obra(self):
        cnt = Counter()
        for i in self.app.items:
            if i.get("shots"):
                cnt[i["id"]] = len(i["shots"])
        its = sorted([i for i in self.app.items if cnt[i["id"]]], key=lambda i: (-cnt[i["id"]], i["title"].lower()))[:40]
        m = tk.Menu(self, tearoff=0, bg=P["surface"], fg=P["text"], activebackground=P["surface2"],
                    activeforeground=P["text"], bd=0, relief="flat", font=("TkDefaultFont", fpt(11)))

        def pick(i):
            self.obra = i
            self.view.rebuild()
        m.add_command(label=("✓  " if self.obra is None else "      ") + "Todas as obras", command=lambda: pick(None))
        for i in its:
            t = i["title"] if len(i["title"]) < 40 else i["title"][:38] + "…"
            m.add_command(label=("✓  " if self.obra is i else "      ") + f"{t}  ({cnt[i['id']]})",
                          command=lambda i=i: pick(i))
        try:
            m.tk_popup(self.winfo_pointerx(), self.winfo_pointery())
        finally:
            m.grab_release()

    def layout(self, avail):
        app, items = self.app, self.app.items
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        accent, f = P["accent"], self.f
        allp = [(i, s) for i in items for s in i.get("shots", [])]
        pool = [(i, s) for i, s in allp if self.obra is None or i is self.obra]
        nobras = len({i["id"] for i, _s in allp})
        out, y = [], 8
        HH = 96

        def head(hov):
            img = self._banner_img(W, HH).copy()
            d = ImageDraw.Draw(img)
            paste_ico(img, "image", 30, mix(accent, "#ffffff", .25), 34, 33)
            d = ImageDraw.Draw(img)
            ttl = self.obra["title"] if self.obra is not None else "Galeria"
            md_ = ImageDraw.Draw(Image.new("RGB", (4, 4)))
            while TW(md_, ttl, 30, True) > W - 560 and len(ttl) > 6:
                ttl = ttl[:-2]
            if self.obra is not None and ttl != self.obra["title"]:
                ttl += "…"
            T(d, 82, 34, ttl, 30, "#ffffff", True, "lm")
            sub = (f"{len(pool)} print{'s' if len(pool) != 1 else ''}" +
                   (f"  •  {nobras} obra{'s' if nobras != 1 else ''}" if self.obra is None else ""))
            T(d, 82, 66, sub, 15, mix(accent, "#ffffff", .5), True, "lm")
            bx = W - 24
            for lab, nm, prim in (("+ Adicionar", "add", True), ("Colar  (Ctrl+V)", "paste", False)):
                bw = TW(md_, lab, 14, True) + 40
                bx0 = bx - bw
                col = accent if prim else P["surface"]
                if hov == nm:
                    col = P["accent_hover"] if prim else mix(P["surface"], accent, .3)
                d.rounded_rectangle([bx0 * K, 28 * K, bx * K, 68 * K], radius=20 * K, fill=col,
                                    outline=None if prim else P["border"], width=2 * K)
                T(d, (bx0 + bx) / 2, 48, lab, 14, "#ffffff", True, "mm")
                bx = bx0 - 10
            return img
        md = ImageDraw.Draw(Image.new("RGB", (4, 4)))
        bw1 = TW(md, "+ Adicionar", 14, True) + 40
        bw2 = TW(md, "Colar  (Ctrl+V)", 14, True) + 40
        hregs = [(W - 24 - bw1, 28, W - 24, 68, "add"), (W - 34 - bw1 - bw2, 28, W - 34 - bw1, 68, "paste")]
        out.append(Blk(f"gl-head-{len(pool)}-{W}-{accent}-{id(self.obra)}", pad, y, W, HH, head, hregs,
                       lambda n: app.add_shot_files(self.obra) if n == "add" else app.paste_shots(self.obra)))
        y += HH + 14
        types = [t for t in TYPES if any(i["type"] == t for i, _s in allp)]
        groups = [("star", "Mostrar", "fav", ["Todos", "Favoritos"], "chips")]
        groups.append(("image", "Obra", "obra", [self.obra["title"] if self.obra is not None else "Todas as obras"],
                       "drop"))
        if len(types) > 1:
            groups.append(("book", "Tipo", "type", ["Todos"] + types, "chips"))
        CH_, GAP = 30, 6
        glay = []
        for ic, lab, key, vals, kind in groups:
            if kind == "drop":
                v0 = vals[0] if len(vals[0]) < 26 else vals[0][:24] + "…"
                cw_ = [min(250, TW(md, v0, 12, True) + 52)]
                vals = [v0]
            else:
                cw_ = [TW(md, v, 12, True) + 26 for v in vals]
            gw = max(sum(cw_) + GAP * (len(vals) - 1), 24 + TW(md, lab, 13, True))
            glay.append((ic, lab, key, vals, cw_, gw, kind))
        SW, FB, SP = 250, 44, 12
        rows_g, used = [[]], 0
        for g_ in glay:
            lim = W - 40 - (SW + SP + FB + 24 if len(rows_g) == 1 else 0)
            if rows_g[-1] and used + g_[5] > lim:
                rows_g.append([])
                used = 0
            rows_g[-1].append(g_)
            used += g_[5] + 26
        FH = 28 + len(rows_g) * 62 + (len(rows_g) - 1) * 6
        active = f["fav"] != "Todos" or f["type"] != "Todos" or bool(self.q) or self.obra is not None
        regs, spots = [], []
        for ri, row in enumerate(rows_g):
            ry = 14 + ri * 68
            gx = 22
            for gi, (ic, lab, key, vals, cw_, gw, kind) in enumerate(row):
                spots.append((ic, lab, gx, ry, key, vals, cw_, gw, gi < len(row) - 1, kind))
                cx_ = gx
                for v, w_ in zip(vals, cw_):
                    regs.append((cx_, ry + 26, cx_ + w_, ry + 26 + CH_, "obra" if kind == "drop" else f"c|{key}|{v}"))
                    cx_ += w_ + GAP
                gx += gw + 26
        sx0 = W - 20 - FB - SP - SW
        sy0 = 28
        regs += [(sx0, sy0, sx0 + SW, sy0 + 40, "search"), (W - 20 - FB, sy0, W - 20, sy0 + 40, "clear")]

        def filters(hov):
            img = Image.new("RGBA", (W * K, FH * K), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.rounded_rectangle([0, 0, W * K - 1, FH * K - 1], radius=20 * K, fill=P["surface"], outline=P["border"], width=K)
            for ic, lab, gx, ry, key, vals, cw_, gw, div, kind in spots:
                paste_ico(img, ic, 16, P["muted"], gx, ry)
                T(d, gx + 24, ry + 8, lab, 13, P["text"], True, "lm")
                cx_ = gx
                for v, w_ in zip(vals, cw_):
                    if kind == "drop":
                        on = self.obra is not None
                        nm = "obra"
                        col = mix(P["surface2"], accent, .45) if on else (mix(P["surface2"], accent, .3) if hov == nm else P["surface2"])
                    else:
                        on = f[key] == v
                        nm = f"c|{key}|{v}"
                        col = accent if on else (mix(P["surface2"], accent, .3) if hov == nm else P["surface2"])
                    d.rounded_rectangle([cx_ * K, (ry + 26) * K, (cx_ + w_) * K, (ry + 26 + CH_) * K], radius=15 * K, fill=col)
                    if kind == "drop":
                        T(d, cx_ + 14, ry + 26 + CH_ / 2, v, 12, "#ffffff" if on else P["text"], True, "lm")
                        ax = cx_ + w_ - 18
                        d.line([((ax - 4) * K, (ry + 39) * K), (ax * K, (ry + 43) * K), ((ax + 4) * K, (ry + 39) * K)],
                               fill="#ffffff" if on else P["muted"], width=int(1.8 * K))
                    else:
                        T(d, cx_ + w_ / 2, ry + 26 + CH_ / 2, v, 12, "#ffffff" if on else P["text"], True, "mm")
                    cx_ += w_ + GAP
                if div:
                    lx = gx + gw + 13
                    d.line([(lx * K, (ry + 2) * K), (lx * K, (ry + 56) * K)], fill=P["border"], width=K)
            fo = self.focus
            d.rounded_rectangle([sx0 * K, sy0 * K, (sx0 + SW) * K, (sy0 + 40) * K], radius=20 * K, fill=P["bg"],
                                outline=accent if (fo or hov == "search") else P["border"], width=2 * K if fo else K)
            paste_ico(img, "search", 16, P["muted"], sx0 + 14, sy0 + 12)
            if self.q:
                txt = self.q
                while TW(md, txt, 14) > SW - 64 and len(txt) > 1:
                    txt = txt[1:]
                T(d, sx0 + 40, sy0 + 20, txt, 14, P["text"], False, "lm")
                cxp = sx0 + 40 + TW(md, txt, 14) + 2
            else:
                T(d, sx0 + 40, sy0 + 20, "Buscar legenda ou obra...", 14, P["muted"], False, "lm")
                cxp = sx0 + 40
            if fo:
                d.line([(cxp * K, (sy0 + 11) * K), (cxp * K, (sy0 + 29) * K)], fill=P["text"], width=int(1.6 * K))
            fx = W - 20 - FB
            d.rounded_rectangle([fx * K, sy0 * K, (fx + FB) * K, (sy0 + 40) * K], radius=14 * K,
                                fill=accent if active else (mix(P["surface2"], accent, .3) if hov == "clear" else P["surface2"]))
            cx0, cy0 = fx + FB / 2, sy0 + 20
            fcol = "#ffffff" if active else P["text"]
            d.polygon([((cx0 - 8) * K, (cy0 - 7) * K), ((cx0 + 8) * K, (cy0 - 7) * K), ((cx0 + 2) * K, (cy0 + 1) * K),
                       ((cx0 + 2) * K, (cy0 + 8) * K), ((cx0 - 2) * K, (cy0 + 5) * K), ((cx0 - 2) * K, (cy0 + 1) * K)], fill=fcol)
            return img

        def fact(n):
            if n == "search":
                self.focus = True
                self.view.cv.focus_set()
                self._redraw_filters()
                return
            self.focus = False
            if n == "obra":
                return self._menu_obra()
            if n == "clear":
                self.f.update(fav="Todos", type="Todos")
                self.q, self.obra = "", None
            elif n.startswith("c|"):
                _, k_, v_ = n.split("|", 2)
                self.f[k_] = v_
            self.view.rebuild()
        out.append(Blk(f"cl-filters-gl-{W}-{FH}", pad, y, W, FH, filters, regs, fact))
        y += FH + 24

        def stitle(hov):
            img = Image.new("RGBA", (W * K, 44 * K), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            d.rectangle([0, 6 * K, 3 * K - 1, 38 * K], fill=accent)
            T(d, 16, 22, "Suas imagens", 24, "#ffffff", True, "lm")
            bw = 200
            bx = W - bw
            d.rounded_rectangle([bx * K, 3 * K, (bx + bw) * K, 41 * K], radius=14 * K,
                                fill=mix(P["surface"], accent, .15) if hov == "sort" else P["surface"], outline=P["border"], width=K)
            for k_, ww in enumerate((12, 9, 6)):
                d.line([((bx + 16) * K, (16 + k_ * 6) * K), ((bx + 16 + ww) * K, (16 + k_ * 6) * K)], fill=P["muted"], width=int(1.8 * K))
            T(d, bx + 40, 22, f["sort"], 14, P["text"], False, "lm")
            cx0 = bx + bw - 22
            d.line([((cx0 - 5) * K, 20 * K), (cx0 * K, 25 * K), ((cx0 + 5) * K, 20 * K)], fill=P["muted"], width=int(1.8 * K))
            return img

        def sact(n):
            self.focus = False
            m = tk.Menu(self, tearoff=0, bg=P["surface"], fg=P["text"], activebackground=P["surface2"],
                        activeforeground=P["text"], bd=0, relief="flat", font=("TkDefaultFont", fpt(11)))
            for o in self.SORTS:
                m.add_command(label=("✓  " if o == f["sort"] else "      ") + o,
                              command=lambda o=o: (f.update(sort=o), self.view.rebuild()))
            try:
                m.tk_popup(self.winfo_pointerx(), self.winfo_pointery())
            finally:
                m.grab_release()
        out.append(Blk(f"cl-sort-gl-{W}-{f['sort']}", pad, y, W, 44, stitle, [(W - 200, 3, W, 41, "sort")], sact))
        y += 44 + 12
        fold = lambda t: unicodedata.normalize("NFKD", t or "").encode("ascii", "ignore").decode().lower()
        qn = fold(self.q).strip()
        sel = []
        for i, s in pool:
            if f["fav"] == "Favoritos" and not s.get("fav"):
                continue
            if f["type"] != "Todos" and i["type"] != f["type"]:
                continue
            if qn and qn not in fold(f"{i['title']} {s.get('cap', '')}"):
                continue
            sel.append((i, s))
        srt = f["sort"]
        if srt == "Mais antigos":
            sel.sort(key=lambda e: e[1]["ts"])
        elif srt == "Por obra":
            sel.sort(key=lambda e: (e[0]["title"].lower(), e[1].get("ch") if e[1].get("ch") is not None else 10 ** 9, e[1]["ts"]))
        elif srt == "Por capítulo":
            sel.sort(key=lambda e: (e[1].get("ch") if e[1].get("ch") is not None else 10 ** 9, e[1]["ts"]))
        else:
            sel.sort(key=lambda e: -e[1]["ts"])
        if not sel:
            msg = ("Nenhum print encontrado." if allp else
                   "Nenhum print ainda. Abra uma obra e cole um print (Ctrl+V), ou use “+ Adicionar”.")
            out.append(Blk("gl-empty", pad, y + 10, 760, 30,
                           lambda hov: (lambda im: (T(ImageDraw.Draw(im), 0, 4, msg, 15, P["muted"]), im)[1])(
                               Image.new("RGBA", (760 * K, 30 * K), (0, 0, 0, 0)))))
            return out
        gap = 14
        cols = max(2, (W + gap) // (250 + gap))
        cw = int((W - (cols - 1) * gap) / cols)
        ys = [y] * cols
        for n, (i, s) in enumerate(sel):
            c = min(range(cols), key=lambda k_: ys[k_])
            iw, ih = shot_size(s)
            h = int(cw * max(.55, min(1.45, ih / max(1, iw))))
            bx = pad + c * (cw + gap)

            def draw(hov, s=s, i=i, h=h):
                return shot_tile_pil(s, cw, h, bool(hov), i["title"])
            out.append(Blk(f"shot-{s['id']}-{cw}-{h}", bx, ys[c], cw, h, draw, [(0, 0, cw, h, "go")],
                           lambda n_, n=n: app.open_sub(ShotViewPage, sel, n)))
            ys[c] += h + gap
        out.append(Blk("gl-end", pad, max(ys), 10, 10, lambda hov: Image.new("RGBA", (10 * K, 10 * K))))
        return out


# ---------- início ----------
DIAS_SEM = ["segunda-feira", "terça-feira", "quarta-feira", "quinta-feira", "sexta-feira", "sábado", "domingo"]
QUOTE_SECS = 8


def ago_text(iso):
    try:
        n = (date.today() - date.fromisoformat(iso)).days
    except ValueError:
        return "desbloqueada"
    if n <= 0:
        return "hoje"
    if n == 1:
        return "ontem"
    if n < 60:
        return f"há {n} dias"
    return f"há {n // 30} meses"


class HomePage(ImgPage):
    MAXW = 1800

    def __init__(self, app):
        super().__init__(app)
        self.pairs, self._bgc, self._fade = [], {}, None
        self.qi, self._qc = 0, None
        self.reshuffle(False)
        self.after(QUOTE_SECS * 1000, self._tick)

    def reshuffle(self, redraw=True):
        """3 frases sorteadas (de obras diferentes, quando der) a cada vez que a aba é aberta."""
        pool = [(i, q) for i in self.app.items for q in i.get("quotes", []) if (q.get("text") or "").strip()
                and q.get("kind") == "citação"]            # só citações; anotações ficam de fora
        random.shuffle(pool)
        pick, seen = [], set()
        for p in pool:
            if p[0]["id"] not in seen:
                pick.append(p)
                seen.add(p[0]["id"])
            if len(pick) == 3:
                break
        for p in pool:
            if len(pick) >= 3:
                break
            if p not in pick:
                pick.append(p)
        self.pairs, self.qi, self._qc, self._fade = pick, 0, None, None
        if redraw:
            try:
                self.view.rebuild()
            except Exception:
                pass

    # ---- carrossel de frases ----
    def _qbg(self, it, w, h):
        key = (it["id"], w, h)
        got = self._bgc.get(key)
        if got is None:
            cov = self.app._load_cover(it).convert("RGB")
            small = ImageOps.fit(cov, (max(8, w // 10), max(8, h // 10)), centering=(0.5, 0.3))
            small = small.filter(ImageFilter.GaussianBlur(3))
            base = small.resize((w * K, h * K), Image.BICUBIC)
            col = self.app.item_color(it)
            base = Image.blend(base, Image.new("RGB", base.size, col), .42)
            base = Image.blend(base, Image.new("RGB", base.size, P["bg"]), .48)
            got = self._bgc[key] = base
            while len(self._bgc) > 6:
                self._bgc.pop(next(iter(self._bgc)))
        return got

    def _quote_img(self, w, h, hov=None):
        app = self.app
        hov = bool(hov)
        key = (self.qi, w, h, P["accent"], hov, tuple(id(p[1]) for p in self.pairs))
        if self._qc and self._qc[0] == key:
            return self._qc[1]
        img = Image.new("RGBA", (w * K, h * K), (0, 0, 0, 0))
        mask = Image.new("L", img.size, 0)
        ImageDraw.Draw(mask).rounded_rectangle([0, 0, w * K - 1, h * K - 1], radius=18 * K, fill=255)
        if not self.pairs:
            bg = Image.new("RGB", img.size, mix(P["surface"], P["accent"], .16))
            img.paste(bg, (0, 0), mask)
            d = ImageDraw.Draw(img)
            T(d, 34, 6, "“", 130, mix(P["accent"], P["surface"], .35), True)
            T(d, 90, h / 2 - 34, "Suas frases favoritas passam por aqui", 26, P["text"], True)
            T(d, 90, h / 2 + 8, "Salve citações (tipo “Citação”) nas páginas das obras e elas aparecem sozinhas.", 15,
              P["muted"])
        else:
            it, q = self.pairs[self.qi % len(self.pairs)]
            img.paste(self._qbg(it, w, h), (0, 0), mask)
            d = ImageDraw.Draw(img)
            col = app.item_color(it)
            T(d, 26, 4, "“", 120, mix(col, "#ffffff", .45), True)
            cw_, ch_ = 150, 216
            maxw = w - 70 - (cw_ + 70)
            txt = " ".join(str(q.get("text", "")).split())
            size = 30 if len(txt) < 90 else 26 if len(txt) < 180 else 22 if len(txt) < 300 else 18
            lines = wrap_l(txt, size, maxw, maxlines=7 if size < 26 else 5)
            lh = int(size * 1.4)
            block = len(lines) * lh + 16 + 24 + 20
            y = max(64, (h - block) / 2 + 14)
            for ln in lines:
                T(d, 70, y, ln, size, "#ffffff")
                y += lh
            y += 14
            T(d, 70, y, it["title"] if TW(d, it["title"], 17, True) < maxw else it["title"][:34] + "…", 17,
              mix(col, "#ffffff", .55), True)
            sub = it.get("type", "") + (f" • cap. {q['ch']}" if str(q.get("ch", "")).strip() else "")
            T(d, 70, y + 26, sub, 13, "#c9cbe0")
            cov = app.cover_pil(it, cw_, ch_)
            cx, cy = w - 34 - cw_, (h - ch_) / 2
            sh = Image.new("RGBA", img.size, (0, 0, 0, 0))
            ImageDraw.Draw(sh).rounded_rectangle([cx * K, (cy + 8) * K, (cx + cw_) * K, (cy + ch_ + 8) * K],
                                                 radius=18 * K, fill=(0, 0, 0, 120))
            img.alpha_composite(sh.filter(ImageFilter.GaussianBlur(10 * K)))
            img.paste(cov, (int(cx * K), int(cy * K)), cov)
            d = ImageDraw.Draw(img)
            n = len(self.pairs)
            if 1 < n <= 12:
                x = 70
                for k_ in range(n):
                    on = k_ == self.qi % n
                    wd = 22 if on else 8
                    d.rounded_rectangle([x * K, (h - 30) * K, (x + wd) * K, (h - 22) * K], radius=4 * K,
                                        fill="#ffffff" if on else (255, 255, 255, 90))
                    x += wd + 6
            elif n > 12:
                T(d, 70, h - 26, f"{self.qi % n + 1} / {n}", 12, "#c9cbe0", False, "lm")
        if hov:
            ov = Image.new("RGBA", img.size, (255, 255, 255, 0))
            ImageDraw.Draw(ov).rounded_rectangle([0, 0, w * K - 1, h * K - 1], radius=18 * K, fill=(255, 255, 255, 14))
            img.alpha_composite(Image.composite(ov, Image.new("RGBA", img.size, (0, 0, 0, 0)), mask))
        d = ImageDraw.Draw(img)
        d.rounded_rectangle([0, 0, w * K - 1, h * K - 1], radius=18 * K,
                            outline=P["accent"] if hov else P["border"], width=(2 if hov else 1) * K)
        self._qc = (key, img)
        return img

    def _qblock(self):
        for i, b in enumerate(self.view.blocks):
            if b.key.startswith("quote"):
                return i, b
        return None, None

    def _tick(self):
        try:
            if not self.winfo_exists():
                return
        except Exception:
            return
        self.after(QUOTE_SECS * 1000, self._tick)
        if len(self.pairs) < 2 or not self.winfo_ismapped() or self._fade:
            return
        i, b = self._qblock()
        if b is None or self.view.hov[0] == i:        # mouse em cima: pausa
            return
        self._go(self.qi + 1)

    def _go(self, n):
        i, b = self._qblock()
        old = self._quote_img(b.w, b.h).copy() if b else None
        self.qi = n
        if b is None:
            return
        new = self._quote_img(b.w, b.h)
        v = self.view
        for k in [k for k in v.photos if k[0] == b.key]:
            v.photos.pop(k, None)
        if i not in v.live or not S.get("anim", True):
            if i in v.live:
                self._put(i, b, new)
            return
        steps = 7
        self._fade = True

        def step(t=1):
            if not self.winfo_exists() or i not in v.live:
                self._fade = None
                return
            self._put(i, b, new if t >= steps else Image.blend(old, new, t / steps), keep=t < steps)
            if t < steps:
                self.after(28, lambda: step(t + 1))
            else:
                self._fade = None
        step()

    def _put(self, i, b, img, keep=False):
        v, k = self.view, scale_k()
        size = (max(1, int(round(b.w * k))), max(1, int(round(b.h * k))))
        if img.size != size:
            img = img.resize(size, Image.BICUBIC)
        ph = ImageTk.PhotoImage(img)
        v.refs[i] = ph
        if not keep:
            v.photos[(b.key, b.w, b.h, None)] = ph
        try:
            v.cv.itemconfigure(v.live[i], image=ph)
        except tk.TclError:
            pass

    def _qact(self, name):
        if not self.pairs:
            return
        if name.startswith("d"):
            self._go(int(name[1:]))
        else:
            self.app.open_detail(self.pairs[self.qi % len(self.pairs)][0])

    # ---- painéis ----
    def _head_block(self, x, y, w):
        app = self.app
        now = datetime.now()
        hi = "Bom dia" if now.hour < 12 else "Boa tarde" if now.hour < 18 else "Boa noite"
        sub = f"{hi}, {app.profile['name'].split()[0]}  •  {DIAS_SEM[now.weekday()]}, {now.day} de " \
              f"{MESES_LONGOS[now.month - 1]}"
        cur = streaks(app.activity)[0]

        col = "#ff9f43" if cur else P["muted"]
        chip = (f"{cur} dia{'s' if cur != 1 else ''} seguido{'s' if cur != 1 else ''}", col, "flame")
        return Blk(f"home-head-{w}-{cur}-{P['accent']}", x, y, w, BANNER_H,
                   lambda hov: head_banner(self, w, "home", "Início", sub, chip=chip)[0])

    def _spec_today(self):
        app = self.app
        act = app.activity
        key = date.today().isoformat()
        today = act.get(key, {})
        ch, mins = today.get("ch", 0), today.get("min", 0)
        works = sum(1 for i in app.items if i.get("progressed") and
                    datetime.fromtimestamp(i["progressed"]).date() == date.today())
        year = date.today().year
        n = sum(1 for i in app.items if i["status"] == "completo" and year_of(i["finished"]) == year)
        goal = max(1, S["goal"])
        exp = goal * date.today().timetuple().tm_yday / 365
        diff = n - exp
        pace = "No ritmo da meta" if abs(diff) < 0.5 else (
            f"{int(round(diff))} à frente do ritmo" if diff > 0 else f"{int(round(-diff))} atrás do ritmo")
        daily = max(1, S.get("daily", 5))
        view = self.view

        def bar(d, y, w, frac, col):
            d.rounded_rectangle([16 * K, y * K, (w - 16) * K, (y + 9) * K], radius=5 * K, fill=P["surface2"])
            fw = (w - 32) * min(1, frac)
            if fw > 0:
                d.rounded_rectangle([16 * K, y * K, (16 + max(fw, 9)) * K, (y + 9) * K], radius=5 * K, fill=col)

        def body(img, d, w, h, hov):
            cw = (w - 32) / 3
            for k_, (val, lab) in enumerate(((str(ch), "capítulos"), (fmt_minutes(mins) if mins else "0 min", "de leitura"),
                                              (str(works), "obras"))):
                cx = 16 + (k_ + .5) * cw
                T(d, cx, HEAD + 2, val, 24, P["text"], True, "ma")
                T(d, cx, HEAD + 34, lab, 12, P["muted"], False, "ma")
            y = HEAD + 66
            T(d, 16, y, f"Meta de {year}", 13, P["muted"])
            T(d, w - 16, y, f"{n}/{goal}", 13, P["text"], True, "ra")
            bar(d, y + 24, w, n / goal, P["accent"])
            T(d, 16, y + 40, pace, 12, P["muted"])
            y += 70
            T(d, 16, y, "Meta diária", 13, P["muted"])
            T(d, w - 16, y, f"{ch}/{daily} cap.", 13, P["text"], True, "ra")
            bar(d, y + 24, w, ch / daily, "#7cf0a8" if ch >= daily else P["accent"])
            ry = y + 42
            for name, x, txt in (("dec", 16, "−"), ("inc", 16 + 28 + 44 + 8, "+")):
                fill = mix(P["surface2"], P["accent"], .38) if hov == name else P["surface2"]
                d.rounded_rectangle([x * K, ry * K, (x + 28) * K, (ry + 26) * K], radius=8 * K, fill=fill)
                T(d, x + 14, ry + 13, txt, 17, P["text"], True, "mm")
            d.rounded_rectangle([(16 + 34) * K, ry * K, (16 + 34 + 44) * K, (ry + 26) * K], radius=8 * K,
                                fill=P["surface2"])
            T(d, 16 + 34 + 22, ry + 13, daily, 13, P["text"], True, "mm")

        def regs(w, h):
            ry = HEAD + 66 + 70 + 42
            return [(16, ry, 44, ry + 26, "dec"), (16 + 80, ry, 16 + 108, ry + 26, "inc")]

        def act_(name):
            S["daily"] = max(1, daily + (-1 if name == "dec" else 1))
            save_settings()
            view.rebuild()
        return PanelSpec("Hoje", lambda w: 300, body, regs=regs, act=act_)

    def _spec_reading(self, now):
        app = self.app
        view = self

        def body(img, d, w, h, hov):
            ncols = self._ncols(w)
            colw = (w - 32) / ncols
            if not now:
                T(d, 16, HEAD + 4, "Nenhuma leitura em andamento.", 14, P["muted"])
            for n, it in enumerate(now[:ncols]):
                x = 16 + n * colw
                y = HEAD + 2
                col = app.item_color(it)
                if hov in (f"o{n}", f"p{n}"):
                    d.rounded_rectangle([(x - 8) * K, (y - 6) * K, (x + colw - 10) * K, (y + 152) * K],
                                        radius=14 * K, fill=mix(col, P["surface"], .86),
                                        outline=mix(col, P["surface"], .45), width=K)
                cov = app.cover_pil(it, 100, 144)
                if hov in (f"o{n}", f"p{n}"):
                    gl = Image.new("RGBA", img.size, (0, 0, 0, 0))
                    ImageDraw.Draw(gl).rounded_rectangle([(x - 2) * K, (y - 2) * K, (x + 102) * K, (y + 146) * K],
                                                         radius=18 * K, fill=col + "aa" if len(col) == 7 else col)
                    img.alpha_composite(gl.filter(ImageFilter.GaussianBlur(6 * K)))
                img.paste(cov, (int(x * K), int(y * K)), cov)
                d = ImageDraw.Draw(img)
                tx, tw_ = x + 112, colw - 112 - 12
                for k_, ln in enumerate(wrap_l(it["title"], 14, tw_, True, 3)):
                    T(d, tx, y + 2 + k_ * 19, ln, 14, P["text"], True)
                total = it["total"] or 0
                T(d, tx, y + 70, f"cap. {it['seen']}" + (f"/{total}" if total else ""), 12, P["muted"])
                frac = min(1, it["seen"] / total) if total else 0
                col = app.item_color(it)
                d.rounded_rectangle([tx * K, (y + 92) * K, (tx + tw_) * K, (y + 98) * K], radius=3 * K,
                                    fill=P["surface2"])
                if frac > 0:
                    d.rounded_rectangle([tx * K, (y + 92) * K, (tx + max(tw_ * frac, 6)) * K, (y + 98) * K],
                                        radius=3 * K, fill=col)
                on = hov == f"p{n}"
                d.rounded_rectangle([tx * K, (y + 112) * K, (tx + 54) * K, (y + 136) * K], radius=12 * K,
                                    fill=P["accent"] if on else mix(P["accent"], P["surface"], .7))
                T(d, tx + 27, y + 124, "+1 cap", 12, "#ffffff" if on else P["accent"], True, "mm")

        def regs(w, h):
            ncols = self._ncols(w)
            colw = (w - 32) / ncols
            out = [(w - 140, 6, w - 12, 42, "all")]
            for n in range(min(ncols, len(now))):
                x = 16 + n * colw
                out += [(x + 112, HEAD + 114, x + 112 + 54, HEAD + 138, f"p{n}"),
                        (x - 8, HEAD - 4, x + colw - 10, HEAD + 150, f"o{n}")]
            return out

        def head(img, d, w):
            T(d, w - 40, 24, "Ver todas", 13, P["accent"], False, "rm")
            paste_ico(img, "chevron", 16, P["accent"], w - 36, 16)

        def act_(name):
            if name == "all":
                return app.nav("library")
            n = int(name[1:])
            if n >= len(now):
                return
            if name[0] == "p":
                if app.add_progress(now[n], 1):
                    self.view.rebuild()
            else:
                app.open_detail(now[n])
        return PanelSpec("Lendo agora", lambda w: HEAD + 160 + 10, body, head=head, regs=regs, act=act_)

    def _ncols(self, w):
        return max(1, min(5, int((w - 32) // 260)))

    def _spec_badges(self):
        app = self.app
        st = [b for b in badge_status_cached(app) if b["earned"]]
        rk = {"bronze": 0, "prata": 1, "ouro": 2}
        dated = sorted([b for b in st if b["date"]], key=lambda b: b["date"], reverse=True)[:3]
        rest = sorted([b for b in st if not b["date"]], key=lambda b: -rk[b["tier"]])
        rows = (dated + rest)[:6]

        def layout_(w):                        # em painéis largos as medalhas ocupam duas colunas
            ncol = 2 if w >= 560 else 1
            cwid = (w - 16) / ncol
            return ncol, cwid, [(n, (n // 3) * cwid, HEAD + (n % 3) * 66) for n in range(min(len(rows), 3 * ncol))]

        def body(img, d, w, h, hov):
            if not rows:
                T(d, 16, HEAD + 4, "Suas medalhas vão aparecer aqui.", 14, P["muted"])
            ncol, cwid, pos = layout_(w)
            for n, cx, y in pos:
                b = rows[n]
                if hov == f"b{n}":
                    d.rounded_rectangle([(cx + 8) * K, y * K, (cx + cwid - 4) * K, (y + 62) * K], radius=10 * K,
                                        fill=P["surface2"])
                bi = badge_pil(b["icon"], b["tier"], True, 48 * K)
                img.paste(bi, (int((cx + 20) * K), int((y + 7) * K)), bi)
                rar = badge_rarity(b)
                ttl = b["title"]
                while TW(d, ttl, 15, True) > cwid - 100 and len(ttl) > 4:
                    ttl = ttl[:-2].rstrip() + "…" if not ttl.endswith("…") else ttl[:-2] + "…"
                T(d, cx + 82, y + 8, ttl, 15, P["text"], True)
                T(d, cx + 82, y + 32, f"{ago_text(b['date']) if b['date'] else 'desbloqueada'}  •  {rar}", 12,
                  RARITY[rar])

        def regs_(w, h):
            ncol, cwid, pos = layout_(w)
            return [(cx + 8, y, cx + cwid - 4, y + 62, f"b{n}") for n, cx, y in pos]

        return PanelSpec("Conquistas recentes", lambda w: HEAD + 3 * 66 + 8, body, regs=regs_,
                         act=lambda n: app.open_sub(BadgesPage))

    def _spec_days(self):
        act = self.app.activity
        days = [date.today() - timedelta(days=13 - k) for k in range(14)]
        data = [(str(d_.day), act.get(d_.isoformat(), {}).get("ch", 0)) for d_ in days]
        tot = sum(v for _, v in data)

        def head(img, d, w):
            T(d, w - 16, 24, f"{tot} capítulos", 12, P["muted"], anchor="rm")

        return PanelSpec("Últimos 14 dias", lambda w: HEAD + 3 * 66 + 8,
                         lambda img, d, w, h, hov: c_bars(d, 16, HEAD, w - 32, h - HEAD - 12, data), head=head)

    def _spec_cards(self):
        app = self.app
        done = [i for i in app.items if i["status"] == "completo"]
        done.sort(key=lambda i: (parse_date(i["finished"]) or date.min, i.get("updated", 0)), reverse=True)
        rec = done[:8]
        nums = card_numbers(app.items)
        total = len(app.items)

        def head(img, d, w):
            T(d, w - 150, 24, f"{len(done)} carta{'s' if len(done) != 1 else ''} na coleção", 13, P["muted"], False, "rm")
            T(d, w - 40, 24, "Ver coleção", 13, P["accent"], False, "rm")
            paste_ico(img, "chevron", 16, P["accent"], w - 36, 16)

        def fit(w, h):
            ch = h - HEAD - 16
            cw = int(ch * CARD_W / CARD_H)
            nfit = max(1, min(len(rec), int((w - 40 + 18) // (cw + 18))))
            return ch, cw, nfit

        def body(img, d, w, h, hov):
            if not rec:
                T(d, 16, HEAD + 4, "Termine uma obra para ganhar sua primeira carta.", 14, P["muted"])
                return
            ch, cw, nfit = fit(w, h)
            for n, it in enumerate(rec[:nfit]):
                x, y = 20 + n * (cw + 18), HEAD + (0 if hov == f"k{n}" else 6)
                src = card_pil(app, it, nums[it["id"]], total, 0)
                img.alpha_composite(src.resize((cw * K, ch * K), Image.LANCZOS), (x * K, y * K))

        def regs(w, h):
            ch, cw, nfit = fit(w, h)
            return [(20 + n * (cw + 18), HEAD, 20 + n * (cw + 18) + cw, HEAD + ch, f"k{n}") for n in range(nfit)] + \
                   [(w - 140, 6, w - 12, 42, "all")]

        def act_(name):
            if name == "all" or not name.startswith("k"):
                app.nav("collection")
            else:
                app.open_sub(CardViewPage, rec[int(name[1:])])
        return PanelSpec("Cartas recentes", lambda w: HEAD + 3 * 66 + 8, body, head=head, regs=regs, act=act_)

    def layout(self, avail):
        app = self.app
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        two = W >= 1000
        out, y = [self._head_block(pad, 8, W)], 8 + BANNER_H + 14
        HH = 300
        today = self._spec_today()
        if two:
            hw = W - 18 - 340
            qb = Blk(f"quote-{hw}", pad, y, hw, HH, lambda hov, hw=hw: self._quote_img(hw, HH, hov),
                     [(0, 0, hw, HH, "q")] + ([(70 + k_ * 14, HH - 36, 70 + k_ * 14 + 14, HH - 16, f"d{k_}")
                                              for k_ in range(len(self.pairs))] if 1 < len(self.pairs) <= 12 else []),
                     self._qact)
            out += [qb, today.block("today", pad + hw + 18, y, 340, HH)]
            y += HH + 18
        else:
            qb = Blk(f"quote-{W}", pad, y, W, HH, lambda hov: self._quote_img(W, HH, hov), [(0, 0, W, HH, "q")], self._qact)
            out += [qb, today.block("today", pad, y + HH + 14, W, HH)]
            y += HH * 2 + 32
        now = sorted([i for i in app.items if i["status"] == "lendo"], key=lambda i: -i["updated"])
        sp = self._spec_reading(now)
        h = sp.nat(W)
        out.append(sp.block("reading", pad, y, W, h))
        y += h + 18
        a, b = self._spec_badges(), self._spec_cards()
        if two:
            hw = (W - 18) // 2
            h = a.nat(hw)
            out += [a.block("badges", pad, y, hw, h), b.block("days", pad + hw + 18, y, W - hw - 18, h)]
            y += h
        else:
            h = a.nat(W)
            out += [a.block("badges", pad, y, W, h), b.block("days", pad, y + h + 14, W, h)]
            y += 2 * h + 14
        return out


# ---------- estatísticas ----------
class StatsPage(ImgPage):
    MAXW = 1150

    def __init__(self, app):
        super().__init__(app, "Estatísticas")
        v = self.view
        self.strip = spec_strip(app)
        self.wide = spec_activity(app)
        self.cards = [spec_level(app), spec_year(app), spec_goal(app, v), spec_recent(app), spec_ratings(app),
                      spec_criteria(app), spec_genres(app), spec_types(app), spec_months(app), spec_status(app),
                      spec_chapters(app), spec_badges(app, v), spec_review(app)]

    def layout(self, avail):
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        n = 2 if W >= 760 else 1
        gap = 16
        out, y = [], 8
        for name, sp in (("strip", self.strip), ("wide", self.wide)):
            h = sp.nat(W)
            out.append(sp.block(name, pad, y, W, h))
            y += h + gap
        cw = (W - gap * (n - 1)) // n
        for r0 in range(0, len(self.cards), n):
            grp = self.cards[r0:r0 + n]
            hmax = max(sp.nat(cw) for sp in grp)
            for c, sp in enumerate(grp):
                out.append(sp.block(f"c{r0 + c}", pad + c * (cw + gap), y, cw, hmax))
            y += hmax + gap
        return out





# ---------- editor de imagem (banner e foto de perfil) ----------
class CropDialog(tk.Toplevel):
    """Janela para enquadrar a imagem: arraste para mover, use o controle (ou a rodinha) para ampliar, gire e aplique."""

    def __init__(self, app, img, kind):
        super().__init__(app)
        self.app, self.kind, self.result = app, kind, None
        self.src0 = img.convert("RGB")
        self.src0.thumbnail((3200, 3200))
        self.src = self.src0
        self.round = kind == "avatar"
        self.out = (500, 500) if self.round else (1800, 600)
        self.title("Editar imagem")
        self.withdraw()                                # monta escondida e só mostra no fim
        self.resizable(False, False)
        key = "#010203"                                # cor que o Windows deixa transparente (cantos redondos)
        try:
            self.attributes("-transparentcolor", key)
            rad = 18
        except tk.TclError:
            key, rad = P["bg"], 0
        self.configure(bg=key)
        box = ctk.CTkFrame(self, fg_color=P["bg"], corner_radius=rad, border_width=1, border_color=P["border"])
        box.pack(fill="both", expand=True)
        self.transient(app)
        self.CW, self.CH = px(600), px(380)
        fw = px(250) if self.round else px(540)
        self.fw, self.fh = fw, (fw if self.round else fw // 3)
        self.fx, self.fy = (self.CW - self.fw) // 2, (self.CH - self.fh) // 2
        head = ctk.CTkFrame(box, fg_color="transparent")
        head.pack(fill="x", padx=24, pady=(18, 12))
        try:
            lg = Image.open(resource_path("icone.ico")).convert("RGBA").resize((64, 64), Image.LANCZOS)
            lbl = ctk.CTkLabel(head, text="", image=ctk.CTkImage(lg, size=(26, 26)))
            lbl.pack(side="left", padx=(0, 10))
        except Exception:
            lbl = None
        ttl = ctk.CTkLabel(head, text="Editar imagem", text_color=P["text"], font=ctk.CTkFont(size=20, weight="bold"),
                           anchor="w")
        ttl.pack(side="left")
        ctk.CTkButton(head, text="", image=icon("close", 18, P["muted"]), width=34, height=34, corner_radius=4,
                      fg_color="transparent", hover_color=P["surface2"], command=self.destroy).pack(side="right")
        for w_ in (head, ttl) + ((lbl,) if lbl else ()):      # arrasta a janela pelo topo
            w_.bind("<ButtonPress-1>", lambda e: setattr(self, "_wd", (e.x_root - self.winfo_x(), e.y_root - self.winfo_y())))
            w_.bind("<B1-Motion>", lambda e: self.geometry(f"+{e.x_root - self._wd[0]}+{e.y_root - self._wd[1]}"))
        self.cv = tk.Canvas(box, width=self.CW, height=self.CH, bg=P["surface"], highlightthickness=0, bd=0,
                            cursor="fleur")
        self.cv.pack(padx=24)
        self.item = self.cv.create_image(0, 0, anchor="nw")
        bar = ctk.CTkFrame(box, fg_color="transparent")
        bar.pack(fill="x", padx=24, pady=(14, 0))
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(side="left", expand=True)
        ctk.CTkLabel(inner, text="", image=ctk.CTkImage(_pic_icon(16, P["muted"]), size=(16, 16))).pack(
            side="left", padx=(0, 10))
        self.zoom = ctk.CTkSlider(inner, from_=1.0, to=4.0, number_of_steps=300, command=self._zoom, width=300,
                                  button_color="#ffffff", button_hover_color="#ffffff", progress_color=P["accent"])
        self.zoom.set(1.0)
        self.zoom.pack(side="left")
        ctk.CTkLabel(inner, text="", image=ctk.CTkImage(_pic_icon(26, P["muted"]), size=(26, 26))).pack(
            side="left", padx=(10, 0))
        ctk.CTkButton(bar, text="", image=ctk.CTkImage(_rot_icon(24, P["muted"]), size=(24, 24)), width=38, height=34,
                      corner_radius=4, fg_color="transparent", hover_color=P["surface2"],
                      command=self.rotate).pack(side="right")
        foot = ctk.CTkFrame(box, fg_color="transparent")
        foot.pack(fill="x", padx=24, pady=(16, 20))
        ctk.CTkButton(foot, text="Redefinir", width=80, height=38, corner_radius=4, fg_color="transparent",
                      hover_color=P["surface2"], text_color=P["accent"], command=self.reset).pack(side="left")
        accent_button(foot, "Aplicar", self.apply, width=104, height=38, corner_radius=4).pack(side="right")
        ghost_button(foot, "Cancelar", self.destroy, width=100, height=38, corner_radius=4).pack(side="right", padx=10)
        self.cv.bind("<ButtonPress-1>", self._down)
        self.cv.bind("<B1-Motion>", self._drag)
        self.cv.bind("<MouseWheel>", self._wheel)
        self.cv.bind("<Button-4>", lambda e: self._wheel(e, 120))
        self.cv.bind("<Button-5>", lambda e: self._wheel(e, -120))
        self.bind("<Escape>", lambda e: self.destroy())
        self.bind("<Return>", lambda e: self.apply())
        self.reset()
        self.update_idletasks()
        w_, h_ = self.winfo_reqwidth(), self.winfo_reqheight()
        try:
            x = app.winfo_rootx() + (app.winfo_width() - w_) // 2
            y = app.winfo_rooty() + (app.winfo_height() - h_) // 2
        except tk.TclError:
            x = y = 80
        self.geometry(f"{w_}x{h_}+{max(0, x)}+{max(0, y)}")
        self.overrideredirect(True)                    # sem a barra do Windows
        self.deiconify()
        self.attributes("-topmost", True)
        self.lift()
        self.after(80, self._focus)
        self.after(500, self._check_shown)

    def _check_shown(self):
        """Se o sistema não mostrou a janela sem moldura, volta para a janela normal (nunca fica invisível)."""
        try:
            if not self.winfo_viewable():
                self.overrideredirect(False)
                self.deiconify()
                self.lift()
        except tk.TclError:
            pass

    def _focus(self):
        try:
            self.lift()
            self.focus_force()
        except tk.TclError:
            pass

    # ---- geometria ----
    def _base(self):
        return max(self.fw / self.src.width, self.fh / self.src.height)

    def reset(self):
        self.src = self.src0
        self.z = 1.0
        self.zoom.set(1.0)
        s = self._base()
        self.ox = self.fx + (self.fw - self.src.width * s) / 2
        self.oy = self.fy + (self.fh - self.src.height * s) / 2
        self.draw()

    def rotate(self):
        self.src = self.src.rotate(-90, expand=True)
        self.z = 1.0
        self.zoom.set(1.0)
        s = self._base()
        self.ox = self.fx + (self.fw - self.src.width * s) / 2
        self.oy = self.fy + (self.fh - self.src.height * s) / 2
        self.draw()

    def _scale(self):
        return self._base() * self.z

    def _clamp(self):
        s = self._scale()
        w, h = self.src.width * s, self.src.height * s
        self.ox = min(self.fx, max(self.fx + self.fw - w, self.ox))
        self.oy = min(self.fy, max(self.fy + self.fh - h, self.oy))

    def _zoom(self, v):
        old = self._scale()
        cx, cy = self.fx + self.fw / 2, self.fy + self.fh / 2
        px_, py_ = (cx - self.ox) / old, (cy - self.oy) / old      # ponto da imagem no centro da moldura
        self.z = float(v)
        s = self._scale()
        self.ox, self.oy = cx - px_ * s, cy - py_ * s
        self.draw()

    def _wheel(self, e, d=None):
        d = d if d is not None else e.delta
        v = min(4.0, max(1.0, self.z + (0.12 if d > 0 else -0.12)))
        self.zoom.set(v)
        self._zoom(v)

    def _down(self, e):
        self._d = (e.x - self.ox, e.y - self.oy)

    def _drag(self, e):
        self.ox, self.oy = e.x - self._d[0], e.y - self._d[1]
        self.draw()

    # ---- desenho ----
    def draw(self):
        self._clamp()
        s = self._scale()
        CW, CH = self.CW, self.CH
        coef = (1 / s, 0, -self.ox / s, 0, 1 / s, -self.oy / s)
        full = self.src.transform((CW, CH), Image.AFFINE, coef, Image.BILINEAR, fillcolor=hex_rgba(P["surface"])[:3])
        dim = Image.blend(full, Image.new("RGB", full.size, P["surface"]), .62)
        mask = Image.new("L", (CW * 3, CH * 3), 0)
        md = ImageDraw.Draw(mask)
        box = [self.fx * 3, self.fy * 3, (self.fx + self.fw) * 3, (self.fy + self.fh) * 3]
        md.ellipse(box, fill=255) if self.round else md.rectangle(box, fill=255)
        mask = mask.resize((CW, CH), Image.LANCZOS)
        out = Image.composite(full, dim, mask)
        od = ImageDraw.Draw(out)
        b = [self.fx, self.fy, self.fx + self.fw, self.fy + self.fh]
        od.ellipse(b, outline="#ffffff", width=3) if self.round else od.rectangle(b, outline="#ffffff", width=3)
        self._ph = ImageTk.PhotoImage(out)
        self.cv.itemconfigure(self.item, image=self._ph)

    def apply(self):
        s = self._scale()
        self._clamp()
        x0, y0 = (self.fx - self.ox) / s, (self.fy - self.oy) / s
        x1, y1 = x0 + self.fw / s, y0 + self.fh / s
        box = (max(0, round(x0)), max(0, round(y0)), min(self.src.width, round(x1)), min(self.src.height, round(y1)))
        self.result = self.src.crop(box).resize(self.out, Image.LANCZOS)
        self.destroy()


def _pic_icon(size, color):
    """Ícone de 'imagem' (moldura, sol e montanha) para o controle de zoom."""
    S_ = size * 4
    im = Image.new("RGBA", (S_, S_), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    w = max(3, S_ // 12)
    d.rounded_rectangle([S_ * .08, S_ * .16, S_ * .92, S_ * .84], radius=S_ * .12, outline=color, width=w)
    d.polygon([(S_ * .2, S_ * .76), (S_ * .42, S_ * .44), (S_ * .56, S_ * .62), (S_ * .66, S_ * .5), (S_ * .84, S_ * .76)],
              fill=color)
    d.ellipse([S_ * .62, S_ * .26, S_ * .76, S_ * .4], fill=color)
    return im.resize((size * 2, size * 2), Image.LANCZOS)


def _rot_icon(size, color):
    S_ = size * 4
    im = Image.new("RGBA", (S_, S_), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    w = max(3, S_ // 10)
    d.rounded_rectangle([S_ * .3, S_ * .42, S_ * .86, S_ * .94], radius=S_ * .1, fill=color)
    d.arc([S_ * .08, S_ * .1, S_ * .62, S_ * .64], 180, 330, fill=color, width=w)
    d.polygon([(S_ * .58, S_ * .02), (S_ * .78, S_ * .24), (S_ * .52, S_ * .32)], fill=color)
    return im.resize((size * 2, size * 2), Image.LANCZOS)


def edit_image(app, path, kind):
    """Abre o editor para o arquivo e devolve a imagem recortada (ou None se cancelou)."""
    try:
        img = ImageOps.exif_transpose(Image.open(path)).convert("RGB")
    except (OSError, ValueError):
        messagebox.showerror("Erro", "Não consegui abrir essa imagem.", parent=app)
        return None
    try:
        dlg = CropDialog(app, img, kind)
    except Exception as e:
        messagebox.showerror("Erro", f"Não consegui abrir o editor de imagem:\n{e}", parent=app)
        return None
    try:
        app.wait_window(dlg)
    except tk.TclError:
        pass
    return dlg.result


AUTO_TITLE = "Automático (título do nível)"


def title_picker(app, entries, current, on_pick):
    """Janela para escolher o título do perfil: busca, filtros e lista rolável (aguenta centenas de títulos).
    entries = [(nome, id, fonte, raridade, desbloqueado, requisito)]; current = nome atual."""
    top = tk.Toplevel(app)
    top.title("Título no perfil")
    top.withdraw()
    top.resizable(False, False)
    key = "#010203"                                    # cor transparente no Windows (cantos redondos)
    try:
        top.attributes("-transparentcolor", key)
        rad = 18
    except tk.TclError:
        key, rad = P["bg"], 0
    top.configure(bg=key)
    shell = ctk.CTkFrame(top, fg_color=P["bg"], corner_radius=rad, border_width=1, border_color=P["border"])
    shell.pack(fill="both", expand=True)
    top.transient(app)
    w, h = px(560), px(660)
    top.geometry(f"{w}x{h}+{max(0, app.winfo_rootx() + (app.winfo_width() - w) // 2)}+"
                 f"{max(0, app.winfo_rooty() + (app.winfo_height() - h) // 2)}")
    hd = ctk.CTkFrame(shell, fg_color="transparent")
    hd.pack(fill="x", padx=24, pady=(18, 10))
    try:
        lg = Image.open(resource_path("icone.ico")).convert("RGBA").resize((64, 64), Image.LANCZOS)
        lbl = ctk.CTkLabel(hd, text="", image=ctk.CTkImage(lg, size=(26, 26)))
        lbl.pack(side="left", padx=(0, 10))
    except Exception:
        lbl = None
    ttl = ctk.CTkLabel(hd, text="Título no perfil", text_color=P["text"], font=ctk.CTkFont(size=20, weight="bold"),
                       anchor="w")
    ttl.pack(side="left")
    ctk.CTkButton(hd, text="", image=icon("close", 18, P["muted"]), width=34, height=34, corner_radius=4,
                  fg_color="transparent", hover_color=P["surface2"], command=top.destroy).pack(side="right")
    for w_ in (hd, ttl) + ((lbl,) if lbl else ()):          # arrasta a janela pelo topo
        w_.bind("<ButtonPress-1>", lambda e: top.__dict__.update(_wd=(e.x_root - top.winfo_x(), e.y_root - top.winfo_y())))
        w_.bind("<B1-Motion>", lambda e: top.geometry(f"+{e.x_root - top._wd[0]}+{e.y_root - top._wd[1]}"))
    st = {"q": "", "f": "Todos", "job": None}
    fnt = ("TkDefaultFont", fpt(11))
    fnb = ("TkDefaultFont", fpt(11), "bold")
    fns = ("TkDefaultFont", fpt(9))

    head = tk.Frame(shell, bg=P["bg"])
    head.pack(fill="x", padx=px(22), pady=(0, px(8)))
    box = tk.Frame(head, bg=P["surface2"])
    box.pack(fill="x")
    tk.Label(box, text="🔍", bg=P["surface2"], fg=P["muted"], font=fnt).pack(side="left", padx=(px(8), 0))
    var = tk.StringVar()
    ent = tk.Entry(box, textvariable=var, bg=P["surface2"], fg=P["text"], insertbackground=P["text"], relief="flat",
                   font=fnt, highlightthickness=0)
    ent.pack(side="left", fill="x", expand=True, padx=px(8), ipady=px(7))
    chips = tk.Frame(shell, bg=P["bg"])
    chips.pack(fill="x", padx=px(22), pady=(0, px(8)))
    count = tk.Label(shell, text="", bg=P["bg"], fg=P["muted"], font=fns, anchor="w")
    count.pack(fill="x", padx=px(24))
    foot = ctk.CTkFrame(shell, fg_color="transparent")
    foot.pack(side="bottom", fill="x", padx=24, pady=(8, 18))
    ghost_button(foot, "Cancelar", top.destroy, width=100, height=38, corner_radius=4).pack(side="right")
    body = tk.Frame(shell, bg=P["bg"])
    body.pack(fill="both", expand=True, padx=px(18), pady=(px(4), 0))
    cv = tk.Canvas(body, bg=P["bg"], highlightthickness=0, bd=0)
    sb = tk.Canvas(body, width=px(10), bg=P["bg"], highlightthickness=0, bd=0)
    sbv = {"lo": 0.0, "hi": 1.0, "off": None}

    def sb_draw(lo=None, hi=None):
        if lo is not None:
            sbv["lo"], sbv["hi"] = float(lo), float(hi)
        sb.delete("all")
        H = sb.winfo_height()
        if sbv["hi"] - sbv["lo"] >= 0.999 or H < 10:
            return
        sb.create_line(px(5), px(2), px(5), H - px(2), fill=P["surface2"], width=max(2, px(2)), capstyle="round")
        y0, y1 = sbv["lo"] * H, max(sbv["hi"] * H, sbv["lo"] * H + px(28))
        sb.create_line(px(5), y0 + px(3), px(5), y1 - px(3), fill=P["muted"], width=px(5), capstyle="round")

    def sb_press(e):
        H = max(1, sb.winfo_height())
        lo, hi = sbv["lo"], sbv["hi"]
        sbv["off"] = (e.y / H - lo) if lo <= e.y / H <= hi else (hi - lo) / 2
        sb_move(e)

    def sb_move(e):
        if sbv["off"] is not None:
            cv.yview_moveto(max(0.0, min(1.0, e.y / max(1, sb.winfo_height()) - sbv["off"])))
    cv.configure(yscrollcommand=sb_draw)
    sb.bind("<Configure>", lambda e: sb_draw())
    sb.bind("<ButtonPress-1>", sb_press)
    sb.bind("<B1-Motion>", sb_move)
    sb.pack(side="right", fill="y", padx=(px(6), 0))
    cv.pack(side="left", fill="both", expand=True)
    inner = tk.Frame(cv, bg=P["bg"])
    win = cv.create_window(0, 0, window=inner, anchor="nw")
    inner.bind("<Configure>", lambda e: cv.configure(scrollregion=cv.bbox("all")))
    cv.bind("<Configure>", lambda e: cv.itemconfigure(win, width=e.width))
    top.bind("<MouseWheel>", lambda e: cv.yview_scroll(-1 if e.delta > 0 else 1, "units"))
    top.bind("<Button-4>", lambda e: cv.yview_scroll(-1, "units"))
    top.bind("<Button-5>", lambda e: cv.yview_scroll(1, "units"))
    top.bind("<Escape>", lambda e: top.destroy())

    def choose(name):
        top.destroy()
        on_pick(name)

    def norm(t):
        return "".join(c for c in unicodedata.normalize("NFD", t.lower()) if unicodedata.category(c) != "Mn")

    def match(e):
        f = st["f"]
        if f == "Desbloqueados" and not e[4]:
            return False
        if f == "Bloqueados" and e[4]:
            return False
        if f in ("Bronze", "Prata", "Ouro") and e[3] != f.lower():
            return False
        q = norm(st["q"])
        return not q or q in norm(e[0]) or q in norm(e[2])

    def paint(wd, color):                              # pinta a linha inteira (senão fica um borrão no meio)
        try:
            wd.configure(bg=color)
        except tk.TclError:
            return
        for c in wd.winfo_children():
            paint(c, color)

    def fill():
        st["job"] = None
        for wd in inner.winfo_children():
            wd.destroy()
        rows = [e for e in entries if match(e)]
        count.configure(text=f"{len(rows)} de {len(entries)} títulos")
        for e in rows[:400]:
            name, bid, src, tier, ok, need = e
            sel = name == current
            bg0 = mix(P["surface"], P["accent"], .30) if sel else P["surface"]
            r = tk.Frame(inner, bg=bg0, cursor="hand2" if ok else "arrow")
            r.pack(fill="x", pady=px(2))
            dot = tk.Canvas(r, width=px(14), height=px(14), bg=bg0, highlightthickness=0)
            dot.pack(side="left", padx=(px(10), px(8)), pady=px(10))
            if tier:
                dot.create_oval(px(2), px(2), px(12), px(12), fill=TIER_COLOR.get(tier, P["accent"]) if ok else "",
                                outline=TIER_COLOR.get(tier, P["accent"]), width=1)
            else:
                dot.create_oval(px(2), px(2), px(12), px(12), fill=P["accent"], outline="")
            col = tk.Frame(r, bg=bg0)
            col.pack(side="left", fill="x", expand=True, pady=px(6))
            tk.Label(col, text=name, bg=bg0, fg=P["text"] if ok else P["muted"], font=fnb, anchor="w").pack(fill="x")
            sub = src if ok else f"🔒 {need}"
            if sub:
                tk.Label(col, text=sub, bg=bg0, fg=P["muted"], font=fns, anchor="w").pack(fill="x")
            if sel:
                tk.Label(r, text="✓", bg=bg0, fg=P["text"], font=fnb).pack(side="right", padx=px(12))
            if ok:
                for wd in [r, col, dot] + list(col.winfo_children()):
                    wd.bind("<Button-1>", lambda ev, n=name: choose(n))
                    wd.bind("<Enter>", lambda ev, r=r: paint(r, mix(P["surface"], P["accent"], .18)))
                    wd.bind("<Leave>", lambda ev, r=r, b=bg0: paint(r, b))
        if len(rows) > 400:
            tk.Label(inner, text="Refine a busca para ver os outros…", bg=P["bg"], fg=P["muted"], font=fns).pack(pady=8)
        if not rows:
            tk.Label(inner, text="Nenhum título encontrado.", bg=P["bg"], fg=P["muted"], font=fnt).pack(pady=20)
        cv.yview_moveto(0)

    def soon(*_):
        st["q"] = var.get()
        if st["job"]:
            top.after_cancel(st["job"])
        st["job"] = top.after(120, fill)
    var.trace_add("write", soon)

    btns = {}

    def setf(f):
        st["f"] = f
        for k, b in btns.items():
            b.configure(bg=P["accent"] if k == f else P["surface2"], fg="#ffffff" if k == f else P["text"])
        fill()
    for f in ("Todos", "Desbloqueados", "Bloqueados", "Bronze", "Prata", "Ouro"):
        b = tk.Label(chips, text=f, bg=P["surface2"], fg=P["text"], font=fns, padx=px(10), pady=px(4), cursor="hand2")
        b.pack(side="left", padx=(0, px(6)))
        b.bind("<Button-1>", lambda e, f=f: setf(f))
        btns[f] = b
    setf("Todos")
    def show():
        top.overrideredirect(True)                      # sem a barra do Windows
        top.deiconify()
        top.attributes("-topmost", True)
        top.lift()
        top.after(80, lambda: (top.grab_set(), top.focus_force(), ent.focus_set()))
        top.after(500, check)

    def check():
        try:                                            # se o sistema não mostrou a janela sem moldura, usa a normal
            if not top.winfo_viewable():
                top.overrideredirect(False)
                top.deiconify()
                top.lift()
        except tk.TclError:
            pass
    top.update_idletasks()
    show()
    return top


class ProfileEditPage(Page):
    MAXW = 640

    def __init__(self, app):
        super().__init__(app, "Editar perfil", back=True)
        self.pr = dict(app.profile)
        self.new = {"avatar": None, "banner": None}
        self.remove = {"avatar": False, "banner": False}
        accent_button(self.footer, "Salvar", self.save, width=110).pack(side="right")
        ghost_button(self.footer, "Cancelar", app.go_back, width=96).pack(side="right", padx=8)

        body = ctk.CTkFrame(self.col, fg_color=P["surface"], corner_radius=18)
        body.pack(fill="x")

        def label(t):
            ctk.CTkLabel(body, text=t, text_color=P["muted"], anchor="w").pack(fill="x", padx=18, pady=(14, 2))

        label("Banner")
        self.banner_prev = ctk.CTkLabel(body, text="")
        self.banner_prev.pack(padx=18, anchor="w")
        r = ctk.CTkFrame(body, fg_color="transparent")
        r.pack(fill="x", padx=18, pady=6)
        flat_button(r, "Escolher banner", lambda: self.pick("banner")).pack(side="left", padx=(0, 8))
        flat_button(r, "Ajustar", lambda: self.adjust("banner"), width=80).pack(side="left", padx=(0, 8))
        flat_button(r, "Remover", lambda: self.clear("banner"), width=80).pack(side="left")
        label("Foto de perfil")
        self.avatar_prev = ctk.CTkLabel(body, text="")
        self.avatar_prev.pack(padx=18, anchor="w")
        r = ctk.CTkFrame(body, fg_color="transparent")
        r.pack(fill="x", padx=18, pady=6)
        flat_button(r, "Escolher foto", lambda: self.pick("avatar")).pack(side="left", padx=(0, 8))
        flat_button(r, "Ajustar", lambda: self.adjust("avatar"), width=80).pack(side="left", padx=(0, 8))
        flat_button(r, "Remover", lambda: self.clear("avatar"), width=80).pack(side="left")
        label("Nome")
        self.name = entry(body)
        self.name.pack(fill="x", padx=18)
        label("Usuário")
        self.handle = entry(body)
        self.handle.pack(fill="x", padx=18)
        label("Título no perfil")
        self.title_map = {AUTO_TITLE: ""}
        allb = badge_status(app)
        self._title_src = {b["id"]: b["title"] for b in allb}
        self._title_entries = [(AUTO_TITLE, "", "Mostra o título do seu nível de leitor", "", True, "")]
        for b in sorted([b for b in allb if b["earned"] or not b["secret"]],
                        key=lambda b: (not b["earned"], b["ptitle"].lower())):
            self.title_map[b["ptitle"]] = b["id"]
            self._title_entries.append((b["ptitle"], b["id"], f"Conquista “{b['title']}”", b["tier"], b["earned"],
                                        b["desc"]))
        cur = next((k for k, v in self.title_map.items() if v and v == self.pr.get("title")), AUTO_TITLE)
        self.title_var = tk.StringVar(value=cur)
        self.title_btn = flat_button(body, "", self._open_titles, width=300, anchor="w")
        self.title_btn.pack(anchor="w", padx=18)
        self.title_hint = ctk.CTkLabel(body, text="", text_color=P["muted"], anchor="w",
                                       font=ctk.CTkFont(size=12))
        self.title_hint.pack(fill="x", padx=18, pady=(4, 0))
        self._title_changed(cur)
        label("Sobre você")
        self.bio = ctk.CTkTextbox(body, height=90, fg_color=P["surface2"], text_color=P["text"])
        self.bio.pack(fill="x", padx=18, pady=(0, 18))
        self.name.insert(0, self.pr["name"])
        self.handle.insert(0, self.pr["handle"])
        self.bio.insert("1.0", self.pr["bio"])
        self.previews()

    def _open_titles(self):
        title_picker(self.app, self._title_entries, self.title_var.get(),
                     lambda n: (self.title_var.set(n), self._title_changed(n)))

    def _title_changed(self, v):
        self.title_btn.configure(text=f"{v}   ▾")
        bid = self.title_map.get(v, "")
        self.title_hint.configure(text=f"Vem da conquista “{self._title_src.get(bid, '')}”." if bid else
                                  "Mostra o título do seu nível de leitor. Conquiste medalhas para ganhar outros.")

    def src(self, key):
        if self.new[key]:
            return Path(self.new[key])
        if self.remove[key] or not self.pr.get(key):
            return None
        return profile_dir() / self.pr[key]

    def previews(self):
        self.avatar_prev.configure(image=avatar_img(self.src("avatar"), self.name.get() or "?", 84, P["surface"], P["accent"]))
        try:
            p = self.src("banner")
            img = ImageOps.fit(Image.open(p).convert("RGB"), (440, 110)) if p and p.exists() else None
        except OSError:
            img = None
        if img is None:
            self.banner_prev.configure(image=None, text="Sem banner (usa o degradê padrão)",
                                       text_color=P["muted"], width=440, height=110, fg_color=P["surface2"])
        else:
            self.banner_prev.configure(image=ctk.CTkImage(img, size=(440, 110)), text="",
                                       width=440, height=110, fg_color="transparent")

    def _edit(self, key, path):
        res = edit_image(self.app, path, key)
        if res is None:
            return
        profile_dir().mkdir(parents=True, exist_ok=True)
        tmp = profile_dir() / f"tmp_{key}_{int(time.time() * 1000)}.jpg"
        res.save(tmp, quality=92)
        old = self.new[key]
        if old and Path(old).name.startswith("tmp_"):
            Path(old).unlink(missing_ok=True)
        self.new[key], self.remove[key] = str(tmp), False
        self.previews()

    def pick(self, key):
        p = filedialog.askopenfilename(parent=self.app, filetypes=[("Imagens", "*.png *.jpg *.jpeg *.webp *.bmp *.gif")])
        if p:
            self._edit(key, p)

    def adjust(self, key):
        p = self.src(key)
        if p and Path(p).exists():
            self._edit(key, p)
        else:
            self.pick(key)

    def clear(self, key):
        self.new[key], self.remove[key] = None, True
        self.previews()

    def save(self):
        pr = self.pr
        pr["name"] = self.name.get().strip() or "Leitor"
        pr["handle"] = self.handle.get().strip() or "@leitor"
        pr["bio"] = self.bio.get("1.0", "end").strip()
        pr["title"] = self.title_map.get(self.title_var.get(), "")
        profile_dir().mkdir(parents=True, exist_ok=True)
        for key, box in (("avatar", (500, 500)), ("banner", (1800, 600))):
            if self.remove[key] and pr.get(key):
                (profile_dir() / pr[key]).unlink(missing_ok=True)
                pr[key] = ""
            if self.new[key]:
                img = ImageOps.exif_transpose(Image.open(self.new[key])).convert("RGB")
                img = ImageOps.fit(img, box) if key == "avatar" else img
                img.thumbnail(box)
                pr[key] = f"{key}_{int(time.time())}.jpg"
                img.save(profile_dir() / pr[key], quality=90)
        for f_ in profile_dir().glob("tmp_*.jpg"):
            f_.unlink(missing_ok=True)
        save_profile(pr)
        self.app.profile = pr
        self.app.refresh_user()
        self.app.toast("Perfil salvo")
        self.app.go_back()


# ---------- adicionar / editar leitura ----------
class EditPage(Page):
    MAXW = 640

    def __init__(self, app, item=None):
        super().__init__(app, "Editar leitura" if item else "Nova leitura", back=True)
        self.item = item
        self.new_photo, self.remove_photo, self.new_img = None, False, None
        it = item or {}

        if item:
            danger_button(self.footer, "Excluir", self.delete, width=90).pack(side="left")
        accent_button(self.footer, "Salvar", self.save, width=110).pack(side="right")
        ghost_button(self.footer, "Cancelar", app.go_back, width=96).pack(side="right", padx=8)

        self.body = ctk.CTkFrame(self.col, fg_color=P["surface"], corner_radius=18)
        self.body.pack(fill="x")
        top = ctk.CTkFrame(self.body, fg_color="transparent")
        top.pack(fill="x", padx=18, pady=(16, 0))
        self.preview = ctk.CTkLabel(top, text="", width=100, height=140)
        self.preview.pack(side="left")
        btns = ctk.CTkFrame(top, fg_color="transparent")
        btns.pack(side="left", padx=16)
        flat_button(btns, "Escolher foto", self.pick_photo).pack(fill="x", pady=(0, 6))
        flat_button(btns, "Colar imagem", self.paste_photo).pack(fill="x", pady=(0, 6))
        ctk.CTkButton(btns, text="Remover foto", fg_color="transparent", border_width=1,
                      border_color=P["surface2"], hover_color=P["surface2"], text_color=P["muted"],
                      command=self.clear_photo).pack(fill="x")

        self.name = entry(self.row("Nome"))
        self.type = menu(self.row("Tipo e status"), TYPES, fg=P["surface2"])
        self.status = menu(self.last, list(STATUS.values()), fg=P["surface2"])
        self.author = entry(self.row("Autor e ano"), "Autor")
        self.year = entry(self.last, "Ano", width=90)
        self.seen = entry(self.row("Capítulo atual e total"), "Capítulo atual")
        self.total = entry(self.last, "Total (opcional)")
        self.ongoing = tk.BooleanVar(value=bool(it.get("ongoing", False)))
        check(self.body, "Em lançamento (ainda saem capítulos novos)", self.ongoing).pack(
            anchor="w", padx=18, pady=(8, 0))
        self.url = entry(self.row("Link para continuar lendo"), "https://...")
        self.tags = entry(self.row("Gêneros (separados por vírgula)"), "ação, romance")
        self.started = entry(self.row("Data de início e de fim"), "dd/mm/aaaa")
        self.finished = entry(self.last, "dd/mm/aaaa")
        self.rer = entry(self.row("Quantas vezes releu"), "0", width=90)
        self.lists = entry(self.row("Listas (separadas por vírgula)"), "férias, clássicos")
        self.labels = entry(self.row("Etiquetas coloridas (separadas por vírgula)"), "Já reli, Quero comprar")
        self.quick = ctk.CTkFrame(self.body, fg_color="transparent")
        self.quick.pack(fill="x", padx=18, pady=(4, 0))
        qbtns = []
        for lname, lcol in sorted(self.app.profile.get("labels", {}).items()):
            qbtns.append(ctk.CTkButton(self.quick, text=lname, height=24, width=max(50, 18 + 7 * len(lname)),
                                       corner_radius=12, fg_color=mix(lcol, P["surface"], .72), text_color=lcol,
                                       hover_color=mix(lcol, P["surface"], .5), font=ctk.CTkFont(size=11),
                                       command=lambda n=lname: self.add_label(n)))
        if qbtns:
            self.quick.bind("<Configure>", lambda e: reflow(qbtns, e.width, 6))
        self.vol_total = entry(self.row("Volumes: total e os que você tem"), "Total", width=90)
        self.vol_owned = entry(self.last, "Ex.: 1-5, 7, 9")
        for w in (self.name, self.type, self.status, self.author, self.year, self.seen, self.total,
                  self.url, self.tags, self.started, self.finished, self.rer, self.lists,
                  self.labels, self.vol_total, self.vol_owned):
            w.pack(side="left", expand=w not in (self.year, self.rer, self.vol_total), fill="x", padx=(0, 6))

        fr = self.row("Nota")
        self.rating_lbl = ctk.CTkLabel(fr, text="", text_color=GOLD_HEX, width=80, anchor="w")
        self.stars = StarRating(fr, P["surface"], value=it.get("rating", 0.0), size=34,
                                on_hover=lambda v: self.rating_lbl.configure(text=fmt_rating(v)))
        self.stars.pack(side="left")
        self.rating_lbl.pack(side="left", padx=12)
        self.rating_lbl.configure(text=fmt_rating(self.stars.value))
        ctk.CTkLabel(self.body, text="Passe o mouse para escolher (de meia em meia estrela). "
                     "Clique de novo para limpar.", text_color=P["muted"], font=ctk.CTkFont(size=11),
                     wraplength=360, justify="left").pack(anchor="w", padx=18, pady=(4, 0))
        fr = self.row("Notas por critério")
        self.crit = {}
        for key, lab in (("story", "História"), ("art", "Arte"), ("chars", "Personagens")):
            c = ctk.CTkFrame(fr, fg_color="transparent")
            c.pack(side="left", expand=True, anchor="w")
            ctk.CTkLabel(c, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(anchor="w")
            st = StarRating(c, P["surface"], value=(it.get("crit") or {}).get(key, 0.0), size=20)
            st.pack(anchor="w")
            self.crit[key] = st

        self.fav = tk.BooleanVar(value=it.get("favorite", False))
        check(self.body, "Favorito (aparece no perfil e fica no topo da lista)", self.fav).pack(
            anchor="w", padx=18, pady=(14, 0))
        self.notes = ctk.CTkTextbox(self.row("Anotações"), height=110, fg_color=P["surface2"],
                                    text_color=P["text"])
        self.notes.pack(fill="x", expand=True, pady=(0, 18))

        self.name.insert(0, it.get("title", ""))
        self.type.set(it.get("type", "Mangá"))
        self.status.set(STATUS[it.get("status", "planejo")])
        self.author.insert(0, it.get("author", ""))
        self.year.insert(0, str(it.get("year", "")))
        self.seen.insert(0, str(it.get("seen", 0)))
        self.total.insert(0, str(it.get("total", 0)))
        self.url.insert(0, it.get("url", ""))
        self.tags.insert(0, ", ".join(it.get("tags", [])))
        self.started.insert(0, it.get("started", ""))
        self.finished.insert(0, it.get("finished", ""))
        self.rer.insert(0, str(it.get("rereads", 0)))
        self.lists.insert(0, ", ".join(it.get("lists", [])))
        self.labels.insert(0, ", ".join(it.get("labels", [])))
        self.vol_total.insert(0, str(it.get("vol_total", 0)))
        self.vol_owned.insert(0, format_ranges(it.get("vol_owned", [])))
        self.notes.insert("1.0", it.get("notes", ""))
        self.show_preview()
        self.name.focus()

    def row(self, label):
        ctk.CTkLabel(self.body, text=label, text_color=P["muted"], anchor="w").pack(
            fill="x", padx=18, pady=(12, 0))
        self.last = ctk.CTkFrame(self.body, fg_color="transparent")
        self.last.pack(fill="x", padx=18, pady=(2, 0))
        return self.last

    def show_preview(self):
        cov = (self.item or {}).get("cover")
        if self.new_img is not None:
            img = self.new_img.copy()
        elif self.new_photo:
            img = Image.open(self.new_photo)
        elif cov and not self.remove_photo and (covers_dir() / cov).exists():
            img = Image.open(covers_dir() / cov)
        else:
            img = placeholder(self.name.get() or "?")
        img = ImageOps.fit(img.convert("RGB"), (200, 280))
        self.preview.configure(image=ctk.CTkImage(img, size=(100, 140)))

    def pick_photo(self):
        p = filedialog.askopenfilename(parent=self.app, filetypes=[
            ("Imagens", "*.png *.jpg *.jpeg *.webp *.bmp *.gif")])
        if p:
            self.new_photo, self.remove_photo, self.new_img = p, False, None
            self.show_preview()

    def clear_photo(self):
        self.new_photo, self.remove_photo, self.new_img = None, True, None
        self.show_preview()

    def paste_photo(self):
        if ImageGrab is None:
            return self.warn("Indisponível", "Colar imagem não funciona neste sistema. Use “Escolher foto”.")
        try:
            clip = ImageGrab.grabclipboard()
        except Exception:
            clip = None
        if isinstance(clip, list) and clip:      # arquivos copiados no explorador
            try:
                clip = Image.open(clip[0])
            except OSError:
                clip = None
        if not isinstance(clip, Image.Image):
            return self.warn("Nada para colar", "Copie uma imagem (ou um arquivo de imagem) e tente de novo.")
        self.new_img, self.new_photo, self.remove_photo = clip.convert("RGB"), None, False
        self.show_preview()

    def add_label(self, name):
        cur = [t.strip() for t in self.labels.get().split(",") if t.strip()]
        if name not in cur:
            cur.append(name)
        self.labels.delete(0, "end")
        self.labels.insert(0, ", ".join(cur))

    def warn(self, title, msg):
        messagebox.showwarning(title, msg, parent=self.app)

    def save(self):
        old_seen = self.item["seen"] if self.item else None
        old = (dict(status=self.item["status"], rating=self.item["rating"], rereads=self.item["rereads"],
                    ongoing=bool(self.item.get("ongoing"))) if self.item else None)
        title = self.name.get().strip()
        seen, total, rer = to_int(self.seen), to_int(self.total), to_int(self.rer)
        started, finished = self.started.get().strip(), self.finished.get().strip()
        if not title:
            return self.warn("Falta o nome", "Dê um nome para a leitura.")
        vt = to_int(self.vol_total)
        if None in (seen, total, rer, vt):
            return self.warn("Número inválido", "Capítulos, volumes e releituras precisam ser números.")
        owned = parse_ranges(self.vol_owned.get())
        if vt:
            owned = [n for n in owned if n <= vt]
        elif owned:
            vt = max(owned)
        if any(d and not parse_date(d) for d in (started, finished)):
            return self.warn("Data inválida", "Use o formato dd/mm/aaaa (ex.: 25/12/2026).")
        status = STATUS_BY_LABEL[self.status.get()]
        today = date.today().strftime("%d/%m/%Y")
        if status == "lendo" and not started:
            started = today
        if status == "completo" and not finished:
            finished = today
        if total and seen > total and self.ongoing.get():
            total = seen          # em lançamento: saiu capítulo novo, o total acompanha
        if total and (status == "completo" or seen > total):
            seen = total
        it = self.item or {"id": uuid.uuid4().hex, "created": time.time(), "cover": None}
        it.update(title=title, type=self.type.get(), status=status, seen=seen, total=total,
                  rating=self.stars.value, author=self.author.get().strip(),
                  year=self.year.get().strip(), url=self.url.get().strip(),
                  tags=[t.strip() for t in self.tags.get().split(",") if t.strip()],
                  started=started, finished=finished, rereads=rer, favorite=self.fav.get(),
                  notes=self.notes.get("1.0", "end").strip(), updated=time.time(),
                  lists=[t.strip() for t in self.lists.get().split(",") if t.strip()],
                  vol_total=vt, vol_owned=owned, crit={k: st.value for k, st in self.crit.items()},
                  ongoing=bool(self.ongoing.get()),
                  labels=[t.strip() for t in self.labels.get().split(",") if t.strip()])
        for k, v in DEFAULTS.items():
            it.setdefault(k, fresh(v))
        for n in it["labels"]:
            label_color(self.app, n)
        if old is None:
            add_event(it, "add")
            ev = status_event("planejo", status)
            if ev:
                add_event(it, ev)
        else:
            ev = status_event(old["status"], status)
            if ev:
                add_event(it, ev)
            if rer > old["rereads"]:
                add_event(it, "reread", f"nº {rer}")
            if bool(it["ongoing"]) != old["ongoing"]:
                add_event(it, "ongoing", "ativado" if it["ongoing"] else "desativado")
        if it["rating"] and (old is None or it["rating"] != old["rating"]):
            add_event(it, "rate", fmt_rating(it["rating"]))
        if old_seen is None:
            it["progressed"] = time.time()
        elif seen > old_seen:
            log_activity(self.app.activity, ch=min(seen - old_seen, 500))
            it["progressed"] = time.time()
            save_activity(self.app.activity)
        if self.remove_photo and it.get("cover"):
            (covers_dir() / it["cover"]).unlink(missing_ok=True)
            it["cover"] = None
        if self.new_photo or self.new_img is not None:
            covers_dir().mkdir(parents=True, exist_ok=True)
            img = (self.new_img.convert("RGB") if self.new_img is not None
                   else ImageOps.exif_transpose(Image.open(self.new_photo)).convert("RGB"))
            img.thumbnail((500, 700))
            it["cover"] = f"{it['id']}.jpg"
            img.save(covers_dir() / it["cover"], quality=88)
        if not self.item:
            self.app.items.append(it)
        self.app.commit(it["id"])
        self.app.toast("Leitura salva")
        self.app.go_back()

    def delete(self):
        if messagebox.askyesno("Excluir", f"Excluir “{self.item['title']}”?", parent=self.app):
            if self.item.get("cover"):
                (covers_dir() / self.item["cover"]).unlink(missing_ok=True)
            purge_shots(self.item)
            self.app.items.remove(self.item)
            self.app.commit(self.item["id"])
            self.app.go_home()


# ---------- estatísticas ----------
def chip_row(parent, names, colors=None, color=None):
    """Linha de etiquetinhas. colors = {nome: cor}; color = uma cor para todas; sem cor = cinza neutro."""
    f = ctk.CTkFrame(parent, fg_color="transparent")
    ws = []
    for n in names:
        c = (colors or {}).get(n) or color
        ws.append(ctk.CTkLabel(f, text=f"  {n}  ", fg_color=mix(c, P["bg"], .78) if c else P["surface2"],
                               text_color=c or P["text"], corner_radius=10, height=26,
                               font=ctk.CTkFont(size=12, weight="bold" if c else "normal")))
    f.bind("<Configure>", lambda e: reflow(ws, e.width, 6))
    return f


class DetailPage(Page):
    MAXW = 1000

    def __init__(self, app, it):
        super().__init__(app, it["title"][:42], back=True)
        self.it = it
        self._build_top(app, it)
        self.col.grid_columnconfigure(0, weight=1)
        self.left = ctk.CTkFrame(self.col, fg_color="transparent")
        self.right = ctk.CTkFrame(self.col, fg_color="transparent")
        self.hero = ctk.CTkLabel(self.col, text="")
        self._hw, self.hist_all = 0, False
        self._two, self._wrap, self.wl = False, 520, []
        self._bd_item, self._bd_job, self._bd_w, self._bd_ph = None, None, 0, None
        self.col.grid_configure(pady=(0, 8))
        if isinstance(self.scroll, ScrollFrame):
            self.scroll.win_w = self.MAXW
            self.scroll.on_canvas = self._bd_soon
        self.timer_lbl = self.timer_btn = self.total_lbl = self.status_btn = None
        self.cap_lbl = self.info_lbl = self.pbar = None
        self.vol_btns = {}
        self.render()
        self.col.bind("<Configure>", self._layout)
        self.after(1000, self.tick)

    TOPH = 58

    def _build_top(self, app, it):
        """Sem barra separada: 'Voltar' e o título são desenhados dentro do canvas, em cima do fundo desfocado."""
        if self.top is not None:
            self.top.pack_forget()
        if isinstance(self.scroll, ScrollFrame):
            self.scroll._outer.pack_configure(padx=0)
        self._top_made, self._top_hot = False, False
        if isinstance(self.scroll, ScrollFrame):
            self.scroll.top_off = px(self.TOPH)
        self._top_title = it["title"][:42]

    def _top_make(self, cv, h):
        x0, bw, bh = px(22), px(96), px(34)
        y0 = (h - bh) // 2
        self._top_box = (x0, y0, x0 + bw, y0 + bh)
        r = px(10)
        x1, y1 = x0 + bw, y0 + bh
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1, x0, y1,
               x0, y1 - r, x0, y0 + r, x0, y0]
        self._top_poly = cv.create_polygon(pts, smooth=True, fill="", outline=mix(P["text"], P["bg"], .45), width=1,
                                           tags="topbar")
        self._top_icon = ImageTk.PhotoImage(icon_pil("back", 16, P["text"]).resize((px(16), px(16)), Image.LANCZOS))
        cv.create_image(x0 + px(16), h // 2, image=self._top_icon, anchor="w", tags="topbar")
        cv.create_text(x0 + px(42), h // 2, text="Voltar", fill=P["text"], font=("TkDefaultFont", fpt(11)),
                       anchor="w", tags="topbar")
        bx = x1 + px(16)
        cv.create_rectangle(bx, h // 2 - px(16), bx + px(3), h // 2 + px(16), fill=P["accent"], width=0, tags="topbar")
        self._top_font = ctk.CTkFont(size=26, weight="bold")
        cv.create_text(bx + px(14), h // 2, text=self._top_title, fill=P["text"], font=self._top_font, anchor="w",
                       tags="topbar")
        cv.bind("<Button-1>", self._top_click, add="+")
        cv.bind("<Motion>", self._top_move, add="+")
        self._top_made = True

    def _in_top(self, e):
        cv = self.scroll.canvas
        x0, y0, x1, y1 = self._top_box
        return x0 <= cv.canvasx(e.x) <= x1 and y0 <= cv.canvasy(e.y) <= y1

    def _top_click(self, e):
        if self._top_made and self._in_top(e):
            self.app.go_back()

    def _top_move(self, e):
        if not self._top_made:
            return
        on = self._in_top(e)
        if on != self._top_hot:
            self._top_hot = on
            cv = self.scroll.canvas
            try:
                cv.itemconfigure(self._top_poly, outline=P["accent"] if on else mix(P["text"], P["bg"], .45),
                                 width=2 if on else 1)
                cv.configure(cursor="hand2" if on else "")
            except tk.TclError:
                pass

    def _fit(self, e):
        # a faixa do topo ocupa a largura toda da coluna; só em janelas estreitas sobra margem
        self.col.grid_configure(padx=0 if lw(e.width) >= self.MAXW else 14)

    def _bd_soon(self, cw):
        if self._bd_job:
            try:
                self.after_cancel(self._bd_job)
            except Exception:
                pass
        self._bd_job = self.after(70, lambda: self._bd_apply(cw))

    def _bd_apply(self, cw):
        """Desenha o fundo no canvas (atrás da coluna) e recorta o pedaço da coluna para a faixa do topo."""
        self._bd_job = None
        sc = self.scroll
        try:
            if not self.winfo_exists() or cw < 200:
                return
            k = scale_k()
            ww = min(cw, px(sc.win_w))
            pad = 0 if ww >= px(self.MAXW) else int(14 * k)
            x0 = (cw - ww) // 2 + pad
            colw = ww - 2 * pad
            H = int(1800 * k)
            topp = px(self.TOPH)                       # a barra do topo mostra as primeiras linhas deste mesmo fundo
            img = backdrop_pil(self.app._load_cover(self.it), cw, H, self.app.item_color(self.it), P["bg"],
                               x0, x0 + colw, int(DETAIL_HERO * k), topp)
            self._bd_ph = ImageTk.PhotoImage(img)
            cv = sc.canvas
            if self._bd_item is None:
                self._bd_item = cv.create_image(0, 0, image=self._bd_ph, anchor="nw")
            else:
                cv.itemconfigure(self._bd_item, image=self._bd_ph)
            cv.tag_lower(self._bd_item)
            if not self._top_made:
                self._top_make(cv, topp)
            cv.tag_raise("topbar")
            hero = img.crop((x0, topp, x0 + colw, topp + int(DETAIL_HERO * k)))
            lw_ = max(1, int(round(colw / k)))
            self.hero.configure(image=ctk.CTkImage(hero, size=(lw_, DETAIL_HERO)))
            self.hero._bd_img = None
        except Exception:
            pass

    def _layout(self, e):
        w = int(lw(e.width))
        if abs(w - self._hw) > 24 and self._bd_item is None:
            self._hw = w
            self.hero.configure(image=self.app.hero_image(self.it, max(300, w)))
        two = w >= 820
        self._two = two
        self._wrap = max(260, (w - 262 - 22 - 40) if two else (w - 40))
        for lb in self.wl:
            try:
                lb.configure(wraplength=max(120, self._wrap - getattr(lb, "_wo", 0)))
            except Exception:
                pass
        self._arrange()

    def _arrange(self):
        two = self._two
        self.hero.grid_forget()
        self.left.grid_forget()
        self.right.grid_forget()
        self.hero.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 8))
        if two:
            self.left.grid(row=1, column=0, sticky="n", padx=(0, 22))
            self.right.grid(row=1, column=1, sticky="nsew")
            self.col.grid_columnconfigure(0, weight=0)
            self.col.grid_columnconfigure(1, weight=1)
        else:
            self.left.grid(row=1, column=0, sticky="n", pady=(0, 14))
            self.right.grid(row=2, column=0, sticky="ew")
            self.col.grid_columnconfigure(0, weight=1)
            self.col.grid_columnconfigure(1, weight=0)

    def render(self):
        """Monta o conteúdo novo ao lado do antigo e só então remove o antigo (sem piscar)."""
        old = (self.left, self.right)
        self.left = ctk.CTkFrame(self.col, fg_color="transparent")
        self.right = ctk.CTkFrame(self.col, fg_color="transparent")
        self._build()
        self._arrange()
        for w in old:
            try:
                w.destroy()
            except Exception:
                pass

    def _update_sd(self):
        sd = stalled_days(self.it)
        if sd:
            self.sd_lbl.configure(text=f"parada há {sd} dias")
            if not self._sd_shown:
                self.sd_lbl.pack(side="left")
                self._sd_shown = True
        elif self._sd_shown:
            self.sd_lbl.pack_forget()
            self._sd_shown = False

    def _update_info(self):
        txt = self.info_text()
        if txt:
            self.info_lbl.configure(text=txt)
            if not self._info_shown:
                self.info_lbl.pack(anchor="w", pady=(8, 0), before=self._timer_panel)
                self._info_shown = True
        elif self._info_shown:
            self.info_lbl.pack_forget()
            self._info_shown = False

    def _update_ong(self):
        """Mostra/esconde e atualiza a etiqueta “em lançamento” sem refazer a tela."""
        it = self.it
        if it.get("ongoing"):
            tag = "em lançamento"
            if it["total"]:
                tag += " · em dia" if it["seen"] >= it["total"] else f" · {it['total']} lançados"
            self.ong_lbl.configure(text=f"  {tag}  ")
            if not self._ong_shown:
                kw = {"before": self.sd_lbl} if self._sd_shown else {}
                self.ong_lbl.pack(side="left", padx=(0, 10), **kw)
                self._ong_shown = True
        elif self._ong_shown:
            self.ong_lbl.pack_forget()
            self._ong_shown = False

    def _style_btn(self, btn, text, ic, hot, on):
        base = P["surface2"]
        btn.configure(text=" " + text, image=icon(ic, 16, hot if on else P["text"]),
                      fg_color=mix(base, hot, .22) if on else base, hover_color=mix(base, hot, .38))

    def cap_text(self):
        it = self.it
        return f"capítulo {it['seen']}" + (f" de {it['total']}" if it["total"] and not it.get("ongoing") else "")

    def info_text(self):
        it, info = self.it, []
        if it["started"]:
            info.append(f"Início: {it['started']}")
        if it["finished"]:
            info.append(f"Fim: {it['finished']}")
        if it["rereads"]:
            info.append(f"Releituras: {it['rereads']}")
        return "   •   ".join(info)

    def wrapped(self, parent, off=0, **kw):
        """Texto que quebra linha; 'off' é o espaço (px) ocupado ao lado dele (botões, barras)."""
        lb = ctk.CTkLabel(parent, wraplength=max(120, self._wrap - off), justify="left", anchor="w", **kw)
        lb._wo = off
        self.wl.append(lb)
        return lb

    def _build(self):
        app, it = self.app, self.it
        self.vol_btns = {}
        self.wl = []
        acc = app.item_color(it)
        # coluna da esquerda: capa e ações
        ctk.CTkLabel(self.left, text="", image=app.cover(it, 240, 336)).pack(pady=(0, 12))
        if it["url"]:
            accent_button(self.left, "▶ Continuar lendo", lambda: open_url(it["url"]), height=38).pack(fill="x", pady=3)
        ongoing = bool(it.get("ongoing"))
        action_btn(self.left, "+1 capítulo", "plus", self.plus).pack(fill="x", pady=3)
        self.fav_btn = action_btn(self.left, "Favorito" if it["favorite"] else "Favoritar",
                                  "heart_fill" if it["favorite"] else "heart", self.fav, hot=PINK, on=it["favorite"])
        self.fav_btn.pack(fill="x", pady=3)
        self.ong_btn = action_btn(self.left, "Em lançamento", "check" if ongoing else "clock", self.toggle_ongoing,
                                  on=ongoing, hot=acc)
        self.ong_btn.pack(fill="x", pady=3)
        action_btn(self.left, "Editar", "edit", lambda: app.open_sub(EditPage, it)).pack(fill="x", pady=3)
        action_btn(self.left, "Mini janela", "clock", lambda: app.open_mini(it)).pack(fill="x", pady=3)
        action_btn(self.left, "Cartão para compartilhar", "share", self.share_card).pack(fill="x", pady=3)

        # coluna da direita: informações
        rc = self.right
        self.wrapped(rc, text=it["title"], text_color=P["text"],
                     font=ctk.CTkFont(size=30, weight="bold")).pack(anchor="w")
        mrow = ctk.CTkFrame(rc, fg_color="transparent")
        mrow.pack(anchor="w", pady=(2, 0))
        ctk.CTkLabel(mrow, text=f"  {it['type']}  ", fg_color=mix(type_color(it["type"]), P["bg"], .72),
                     text_color=type_color(it["type"]), corner_radius=8, height=24,
                     font=ctk.CTkFont(size=12, weight="bold")).pack(side="left")
        meta = "  •  ".join(x for x in (it["author"], str(it["year"])) if x)
        if meta:
            ctk.CTkLabel(mrow, text=meta, text_color=P["muted"], anchor="w").pack(side="left", padx=10)
        row = ctk.CTkFrame(rc, fg_color="transparent")
        row.pack(fill="x", pady=(12, 0))
        sc = P["status"][it["status"]]
        self.status_btn = ctk.CTkButton(row, text="●  " + STATUS[it["status"]] + "   ▾", height=30, corner_radius=15,
                                        fg_color=mix(sc, P["bg"], .8), hover_color=mix(sc, P["bg"], .65),
                                        text_color=sc, border_width=1, border_color=mix(sc, P["bg"], .55),
                                        font=ctk.CTkFont(size=13, weight="bold"), command=self.status_menu)
        self.status_btn.pack(side="left")
        self.cap_lbl = ctk.CTkLabel(row, text=self.cap_text(), text_color=P["text"])
        self.cap_lbl.pack(side="left", padx=14)
        self.ong_lbl = ctk.CTkLabel(row, text="", fg_color=P["surface2"], text_color=P["accent"], corner_radius=8,
                                    height=24, font=ctk.CTkFont(size=12, weight="bold"))
        self.sd_lbl = ctk.CTkLabel(row, text="", text_color=P["status"]["pausado"])
        self._sd_shown = self._ong_shown = False
        self._update_ong()
        self._update_sd()
        if it["total"]:
            pb = ctk.CTkProgressBar(rc, height=8, fg_color=P["surface2"], progress_color=acc)
            pb.pack(fill="x", pady=(8, 0))
            self.pbar = pb
            animate_bar(pb, min(1, it["seen"] / it["total"]))
        r = ctk.CTkFrame(rc, fg_color="transparent")
        r.pack(anchor="w", pady=(12, 0))
        rl = ctk.CTkLabel(r, text=fmt_rating(it["rating"]) if it["rating"] else "Dar nota", width=70, anchor="w",
                          text_color=GOLD_HEX if it["rating"] else P["muted"])
        StarRating(r, P["bg"], it["rating"], size=30, interactive=True,
                   on_change=self.set_rating,
                   on_hover=lambda v, rl=rl: rl.configure(text=fmt_rating(v) if v else "Dar nota",
                                                          text_color=GOLD_HEX if v else P["muted"])).pack(side="left")
        rl.pack(side="left", padx=10)
        crit = it.setdefault("crit", {})
        r = ctk.CTkFrame(rc, fg_color="transparent")
        r.pack(anchor="w", pady=(10, 0))
        for key, lab in (("story", "História"), ("art", "Arte"), ("chars", "Personagens")):
            c = ctk.CTkFrame(r, fg_color="transparent")
            c.pack(side="left", padx=(0, 18))
            hd = ctk.CTkFrame(c, fg_color="transparent")
            hd.pack(fill="x")
            ctk.CTkLabel(hd, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(side="left")
            vl = ctk.CTkLabel(hd, text=f"{crit.get(key, 0):g}".replace(".", ",") if crit.get(key) else "",
                              text_color=GOLD_HEX, font=ctk.CTkFont(size=12))
            vl.pack(side="right")
            StarRating(c, P["bg"], crit.get(key, 0.0), size=18, interactive=True,
                       on_change=lambda v, k=key: self.set_crit(k, v),
                       on_hover=lambda v, vl=vl: vl.configure(text=f"{v:g}".replace(".", ",") if v else "")
                       ).pack(anchor="w")
        if it["tags"]:
            chip_row(rc, it["tags"], color=acc).pack(fill="x", pady=(14, 0))
        if it["labels"]:
            chip_row(rc, it["labels"], colors={n: label_color(app, n) for n in it["labels"]}).pack(
                fill="x", pady=(8, 0))
        r = ctk.CTkFrame(rc, fg_color="transparent")
        r.pack(fill="x", pady=(8, 0))
        ctk.CTkLabel(r, text="Listas:", text_color=P["muted"]).pack(side="left")
        ctk.CTkLabel(r, text=", ".join(it["lists"]) if it["lists"] else "nenhuma", text_color=P["text"]).pack(
            side="left", padx=8)
        flat_button(r, "+ Lista", self.add_list, width=70, height=26).pack(side="left")
        self.info_lbl = ctk.CTkLabel(rc, text="", text_color=P["muted"])
        self._info_shown = False

        # cronômetro
        f, _ = panel(rc, "Cronômetro de leitura")
        f.pack(fill="x", pady=(16, 0))
        self._timer_panel = f
        self._update_info()
        running = bool(app.timer and app.timer["id"] == it["id"])
        r = ctk.CTkFrame(f, fg_color="transparent")
        r.pack(fill="x", padx=16, pady=(0, 14))
        self.timer_lbl = ctk.CTkLabel(r, text="00:00:00", text_color=P["text"],
                                      font=ctk.CTkFont(size=28, weight="bold"))
        self.timer_lbl.pack(side="left")
        self.timer_btn = accent_button(r, "Parar e salvar" if running else "Iniciar leitura", self.toggle_timer,
                                       height=36)
        self.timer_btn.pack(side="right")
        self.total_lbl = ctk.CTkLabel(r, text=f"Total nesta leitura: {fmt_minutes(it['minutes'])}",
                                      text_color=P["muted"])
        self.total_lbl.pack(side="right", padx=14)

        # volumes
        if it["vol_total"]:
            f, head = panel(rc, "Volumes")
            f.pack(fill="x", pady=(14, 0))
            self.vol_lbl = ctk.CTkLabel(head, text="", text_color=P["muted"])
            self.vol_lbl.pack(side="right")
            host = ctk.CTkFrame(f, fg_color="transparent")
            host.pack(fill="x", padx=16, pady=(0, 14))
            owned = set(it["vol_owned"])
            btns = []
            for n in range(1, min(it["vol_total"], 300) + 1):
                b = ctk.CTkButton(host, text=str(n), width=40, height=30, corner_radius=8,
                                  fg_color=acc if n in owned else P["surface2"],
                                  hover_color=mix(acc, "#000000", .15), text_color="white" if n in owned else P["muted"])
                b.configure(command=lambda n=n, b=b: self.toggle_vol(n, b))
                btns.append(b)
                self.vol_btns[n] = b
            host.bind("<Configure>", lambda e: reflow(btns, e.width, 6))
            self.show_vols()

        if it["notes"]:
            f, _ = panel(rc, "Anotações")
            f.pack(fill="x", pady=(14, 0))
            self.wrapped(f, text=it["notes"], text_color=P["text"]).pack(anchor="w", padx=16, pady=(0, 14))
        self.quotes_panel(rc, acc)
        self.shots_panel(rc, acc)
        self._hl, self._acc = len(it.get("history", [])), acc      # o histórico segue sendo guardado, só não é mostrado

    # ---- prints da obra ----
    def shots_panel(self, rc, acc):
        f, head = panel(rc, "Prints")
        f.pack(fill="x", pady=(14, 0))
        accent_button(head, "+ Adicionar", lambda: self.app.add_shot_files(self.it), height=30, width=104).pack(
            side="right")
        ghost_button(head, "Colar", lambda: self.app.paste_shots(self.it), height=30, width=64).pack(
            side="right", padx=(0, 6))
        self._scount = ctk.CTkLabel(head, text="", text_color=P["muted"], font=ctk.CTkFont(size=12))
        self._scount.pack(side="right", padx=(0, 10))
        self._shost = ctk.CTkFrame(f, fg_color="transparent")
        self._shost.pack(fill="x", padx=16)
        self._sfoot = ctk.CTkFrame(f, fg_color="transparent")
        self._sfoot.pack(fill="x", padx=12, pady=(2, 10))
        self._shelf = None
        self._fill_shots()

    def _fill_shots(self):
        it = self.it
        for w in self._shost.winfo_children():
            w.destroy()
        for w in self._sfoot.winfo_children():
            w.destroy()
        self._shelf = None
        shots = sorted(it.get("shots", []), key=lambda s: -s["ts"])
        self._scount.configure(text=f"{len(shots)}" if shots else "")
        if not shots:
            box = ctk.CTkFrame(self._shost, fg_color=P["surface2"], corner_radius=14, border_width=1,
                               border_color=P["border"], height=84)
            box.pack(fill="x", pady=(0, 8))
            box.pack_propagate(False)
            ctk.CTkLabel(box, text="Cole um print (Ctrl+V) ou clique em “+ Adicionar”", text_color=P["muted"]).place(
                relx=.5, rely=.5, anchor="center")
            return
        sh = HShelf(self._shost, 148, bg=P["surface"])
        sh.pack(fill="x", pady=(0, 4))
        self._shelf = sh
        entries = [(it, s) for s in shots]
        TW_, TH_ = 200, 140
        for n, s in enumerate(shots[:24]):
            normal = ctk.CTkImage(shot_tile_pil(s, TW_, TH_), size=(TW_, TH_))
            hot = ctk.CTkImage(shot_tile_pil(s, TW_, TH_, True, ""), size=(TW_, TH_))
            lb = ctk.CTkLabel(sh.inner, text="", image=normal, fg_color="transparent")
            lb.pack(side="left", padx=(0, 10), anchor="n")
            lb.bind("<Button-1>", lambda e, n=n: self.app.open_sub(ShotViewPage, entries, n))
            lb.bind("<Enter>", lambda e, lb=lb, hot=hot: lb.configure(image=hot))
            lb.bind("<Leave>", lambda e, lb=lb, normal=normal: lb.configure(image=normal))
            lb._keep = (normal, hot)
        ctk.CTkButton(self._sfoot, text="Ver todos os prints", image=icon("chevron", 16, P["accent"]), compound="right",
                      fg_color="transparent", hover_color=P["surface2"], text_color=P["accent"], anchor="w",
                      command=lambda: self.app.open_sub(GalleryPage, it), width=170).pack(side="left")
        if len(shots) > 4:
            ghost_button(self._sfoot, "", lambda: sh.scroll_by(px(420)), image=icon("forward", 14), width=34,
                         height=30).pack(side="right")
            ghost_button(self._sfoot, "", lambda: sh.scroll_by(-px(420)), image=icon("back", 14), width=34,
                         height=30).pack(side="right", padx=(0, 6))

    # ---- citações e anotações por capítulo ----
    def quotes_panel(self, rc, acc):
        it = self.it
        f, head = panel(rc, "Citações e anotações")
        f.pack(fill="x", pady=(14, 0))
        self._qcount = ctk.CTkLabel(head, text=f"{len(it['quotes'])}", text_color=P["muted"],
                                    font=ctk.CTkFont(size=12))
        self._qcount.pack(side="right")
        self._qscroll = ScrollFrame(f)               # lista com rolagem própria (altura máxima)
        self._qscroll.canvas.configure(bg=P["surface"])
        tk.Frame.configure(self._qscroll, bg=P["surface"])
        self._qscroll.pack(fill="x", padx=(16, 6))
        self._qhost = self._qscroll
        self._qscroll.chain = True
        self._qscroll.idle = P["surface"]
        self._qacc = acc
        self._fill_quotes()
        form = ctk.CTkFrame(f, fg_color="transparent")
        form.pack(fill="x", padx=16, pady=(8, 14))
        ch = entry(form, "cap.", width=64)
        ch.insert(0, str(it["seen"]))
        ch.pack(side="left", padx=(0, 6))
        kind = menu(form, ["Citação", "Nota"], None, 96, fg=P["surface2"], height=36)
        kind.pack(side="left", padx=(0, 6))
        txt = entry(form, "Escreva o trecho ou a anotação...")
        txt.pack(side="left", fill="x", expand=True, padx=(0, 6))
        txt.bind("<Return>", lambda e: self.add_quote(ch, kind, txt), add="+")
        accent_button(form, "Adicionar", lambda: self.add_quote(ch, kind, txt), width=92).pack(side="left")

    def _fill_quotes(self):
        it, acc, host = self.it, self._qacc, self._qhost
        for w in host.winfo_children():
            w.destroy()
        self.wl = [lb for lb in self.wl if getattr(lb, "_wo", 0) != 140 and lb.winfo_exists()]
        self._qcount.configure(text=f"{len(it['quotes'])}")
        for q in sorted(it["quotes"], key=lambda q: (q.get("ch", 0), q.get("ts", 0))):
            row = ctk.CTkFrame(host, fg_color="transparent")
            row.pack(fill="x", pady=5)
            ctk.CTkFrame(row, width=3, height=24, fg_color=acc, corner_radius=0).pack(side="left", fill="y",
                                                                                  padx=(0, 10))
            body = ctk.CTkFrame(row, fg_color="transparent")
            body.pack(side="left", fill="x", expand=True)
            text = f"“{q['text']}”" if q.get("kind") == "citação" else q["text"]
            self.wrapped(body, off=140, text=text, text_color=P["text"],
                         font=ctk.CTkFont(size=13, slant="italic" if q.get("kind") == "citação" else "roman")).pack(
                anchor="w")
            ctk.CTkLabel(body, text=f"cap. {q.get('ch', 0)} · {q.get('kind', 'nota')}", text_color=P["muted"],
                         font=ctk.CTkFont(size=11)).pack(anchor="w")
            ghost_button(row, "", lambda q=q: self.del_quote(q), image=icon("close", 12), width=30, height=28,
                         ).pack(side="right", anchor="n")
            ghost_button(row, "", lambda q=q: self.fav_quote(q),
                         image=icon("star", 14, GOLD_HEX if q.get("fav") else P["muted"]), width=30,
                         height=28).pack(side="right", anchor="n")
        self._qfit()

    def _qfit(self):
        """Ajusta a altura da lista de citações ao conteúdo, até um máximo (depois disso, rola)."""
        sc = self._qscroll
        try:
            sc.update_idletasks()
            h = sc.winfo_reqheight()
            sc._region_h = max(1, h)
            sc.canvas.configure(height=min(h, px(300)), scrollregion=(0, 0, max(1, sc.winfo_width()), h))
            sc.canvas.yview_moveto(0 if h <= px(300) else sc.canvas.yview()[0])
        except tk.TclError:
            pass

    def add_quote(self, ch, kind, txt):
        text = txt.get().strip()
        if not text:
            return
        raw = ch.get().strip()
        self.it["quotes"].append({"ch": int(raw) if raw.isdigit() else self.it["seen"], "text": text,
                                  "kind": kind.get().lower(), "ts": time.time()})
        self.it["updated"] = time.time()
        self.app.commit(self.it["id"])
        txt.delete(0, "end")
        self._fill_quotes()
        try:
            self._qscroll.canvas.yview_moveto(1)        # mostra a citação recém-adicionada
        except tk.TclError:
            pass

    def _swap(self, attr, build):
        """Troca um painel sem deixar buraco: o novo é montado fora da tela, entra no lugar e só então o antigo sai."""
        old = getattr(self, attr)
        new = ctk.CTkFrame(old.master, fg_color="transparent")
        build(new)
        new.pack(fill="x", after=old)
        old.destroy()
        setattr(self, attr, new)

    def _refresh_hist(self):
        self._hl = len(self.it.get("history", []))
        return
        try:
            self._hl = len(self.it.get("history", []))
            self._swap("hist_host", lambda h: self.history_panel(h, self._acc))
        except Exception:
            self.render()

    def del_quote(self, q):
        if q in self.it["quotes"]:
            self.it["quotes"].remove(q)
            self.app.commit(self.it["id"])
            self._fill_quotes()

    # ---- histórico da obra (diário) ----
    def _hist_row(self, tl, e):
        base, col = EVENT_STYLE.get(e["kind"], (e["kind"], P["muted"]))
        txt = e.get("text", "")
        main = txt if e["kind"] == "note" else (base + (f" {txt}" if txt else ""))
        row = ctk.CTkFrame(tl, fg_color="transparent")
        ctk.CTkLabel(row, text="", image=icon("dot", 12, col), width=18).pack(side="left", anchor="n", pady=(4, 0))
        t = ctk.CTkFrame(row, fg_color="transparent")
        t.pack(side="left", fill="x", expand=True, padx=(6, 0))
        self.wrapped(t, text=main, text_color=P["text"]).pack(anchor="w")
        ctk.CTkLabel(t, text=datetime.fromtimestamp(e["ts"]).strftime("%d/%m/%Y · %H:%M"), text_color=P["muted"],
                     font=ctk.CTkFont(size=11)).pack(anchor="w")
        return row

    def history_panel(self, rc, acc):
        it = self.it
        ev = sorted(it.get("history", []), key=lambda e: -e["ts"])
        f, head = panel(rc, "Histórico")
        f.pack(fill="x", pady=(14, 0))
        count = ctk.CTkLabel(head, text=f"{len(ev)} registros", text_color=P["muted"], font=ctk.CTkFont(size=12))
        count.pack(side="right")
        form = ctk.CTkFrame(f, fg_color="transparent")
        form.pack(fill="x", padx=16, pady=(0, 8))
        ent = entry(form, "Escreva no diário desta leitura...")
        ent.pack(side="left", fill="x", expand=True, padx=(0, 6))
        ent.bind("<Return>", lambda e: self.add_diary(ent), add="+")
        accent_button(form, "Registrar", lambda: self.add_diary(ent), width=92).pack(side="left")
        hp = self._hp = {"f": f, "count": count, "tl": None, "empty": None, "more": None, "n": len(ev)}
        if not ev:
            hp["empty"] = self.wrapped(f, text="Nada registrado ainda. Início, pausas, notas e releituras aparecem aqui.",
                                       text_color=P["muted"])
            hp["empty"].pack(anchor="w", padx=16, pady=(0, 14))
        else:
            hp["tl"] = ctk.CTkFrame(f, fg_color="transparent")
            hp["tl"].pack(fill="x", padx=16, pady=(0, 6))
            for e in (ev if self.hist_all else ev[:8]):
                self._hist_row(hp["tl"], e).pack(fill="x", pady=3)
            if len(ev) > 8 and not self.hist_all:
                hp["more"] = ghost_button(f, f"Mostrar todos ({len(ev)})", self.show_all_hist, height=30)
                hp["more"].pack(anchor="w", padx=16, pady=(0, 14))
            else:
                hp["more"] = ctk.CTkFrame(f, width=1, height=8, fg_color="transparent")
                hp["more"].pack()

    def _hist_sync(self):
        """O painel de histórico não é mais mostrado; os registros continuam sendo guardados."""
        self._hl = len(self.it.get("history", []))
        return

    def _hist_sync_old(self):
        hp = getattr(self, "_hp", None)
        ev = sorted(self.it.get("history", []), key=lambda e: -e["ts"])
        try:
            n_new = len(ev) - hp["n"]
            if hp is None or n_new < 0 or not hp["f"].winfo_exists():
                return self._refresh_hist()
            hp["count"].configure(text=f"{len(ev)} registros")
            if n_new == 0:
                return
            if hp["tl"] is None:
                if hp["empty"] is not None:
                    hp["empty"].destroy()
                    hp["empty"] = None
                hp["tl"] = ctk.CTkFrame(hp["f"], fg_color="transparent")
                hp["tl"].pack(fill="x", padx=16, pady=(0, 6))
                hp["more"] = ctk.CTkFrame(hp["f"], width=1, height=8, fg_color="transparent")
                hp["more"].pack()
            tl = hp["tl"]
            for e in reversed(ev[:n_new]):
                kids = tl.winfo_children()
                row = self._hist_row(tl, e)
                if kids:
                    row.pack(fill="x", pady=3, before=kids[0])
                else:
                    row.pack(fill="x", pady=3)
            if not self.hist_all:
                kids = tl.winfo_children()
                for w in kids[8:]:
                    w.destroy()
                if len(ev) > 8 and not isinstance(hp["more"], ctk.CTkButton):
                    if hp["more"] is not None:
                        hp["more"].destroy()
                    hp["more"] = ghost_button(hp["f"], f"Mostrar todos ({len(ev)})", self.show_all_hist, height=30)
                    hp["more"].pack(anchor="w", padx=16, pady=(0, 14))
                elif isinstance(hp["more"], ctk.CTkButton):
                    hp["more"].configure(text=f"Mostrar todos ({len(ev)})")
            hp["n"] = len(ev)
            self._hl = len(ev)
        except Exception:
            self._refresh_hist()

    def show_all_hist(self):
        self.hist_all = True
        self.render()

    def add_diary(self, ent):
        text = ent.get().strip()
        if text:
            add_event(self.it, "note", text)
            self.it["updated"] = time.time()
            self.app.commit(self.it["id"])
            ent.delete(0, "end")
            self._hist_sync()

    def show_vols(self):
        n = len(self.it["vol_owned"])
        self.vol_lbl.configure(text=f"{n} de {self.it['vol_total']} volumes")

    def toggle_vol(self, n, b):
        owned = set(self.it["vol_owned"])
        if n in owned:
            owned.discard(n)
        else:
            owned.add(n)
        self.it["vol_owned"] = sorted(owned)
        on = n in owned
        b.configure(fg_color=self.app.item_color(self.it) if on else P["surface2"],
                    text_color="white" if on else P["muted"])
        self.show_vols()
        self.app.commit(self.it["id"])

    def _sig(self):
        return ()          # tudo que antes pedia refazer a tela agora se atualiza no lugar

    def _sync_top(self, sig):
        """Atualiza no lugar o que muda com o progresso/status; refaz a tela só se algo apareceu ou sumiu."""
        it = self.it
        if sig != self._sig() or self.status_btn is None:
            return self.render()
        try:
            sc = P["status"][it["status"]]
            self.status_btn.configure(text="●  " + STATUS[it["status"]] + "   ▾", fg_color=mix(sc, P["bg"], .8),
                                      hover_color=mix(sc, P["bg"], .65), text_color=sc,
                                      border_color=mix(sc, P["bg"], .55))
            self.cap_lbl.configure(text=self.cap_text())
            self._update_ong()
            self._update_sd()
            self._update_info()
            if self.pbar is not None and it["total"]:
                self.pbar.set(min(1, it["seen"] / it["total"]))
            if len(it.get("history", [])) != self._hl:       # novo registro: refaz só o painel do histórico
                self._hist_sync()
        except Exception:
            self.render()

    def plus(self):
        sig = self._sig()
        if self.app.add_progress(self.it, 1) is False:
            return
        self._sync_top(sig)

    def set_crit(self, key, v):
        it = self.it
        it.setdefault("crit", {})[key] = v
        it["updated"] = time.time()
        self.app.commit(it["id"])

    def set_rating(self, v):
        it = self.it
        if v != it["rating"]:
            it["rating"] = v
            if v:
                add_event(it, "rate", fmt_rating(v))
            it["updated"] = time.time()
            self.app.commit(it["id"])
            self._hl = len(it.get("history", []))
            if v:
                self._hist_sync()

    def toggle_ongoing(self):
        it = self.it
        it["ongoing"] = not it.get("ongoing")
        if it["ongoing"] and it["status"] == "completo":
            it["status"] = "lendo"          # saem capítulos novos: volta a ser uma leitura em andamento
        add_event(it, "ongoing", "ativado" if it["ongoing"] else "desativado")
        it["updated"] = time.time()
        sig = self._sig()
        self.app.commit(it["id"])
        try:
            on = bool(it["ongoing"])
            self._style_btn(self.ong_btn, "Em lançamento", "check" if on else "clock", self._acc, on)
        except Exception:
            return self.render()
        self._sync_top(sig)

    def share_card(self):
        it = self.it
        safe = "".join(c if c.isalnum() else "_" for c in it["title"])[:40] or "obra"
        p = filedialog.asksaveasfilename(parent=self.app, defaultextension=".png", initialfile=f"cartao_{safe}.png",
                                         filetypes=[("Imagem PNG", "*.png")])
        if not p:
            return
        try:
            make_work_card(self.app, it, p)
        except Exception as e:
            return messagebox.showerror("Erro", f"Não consegui gerar o cartão:\n{e}", parent=self.app)
        self.app.bump("share")
        self.app.toast("Cartão salvo! Agora é só postar.")

    def fav_quote(self, q):
        on = not q.get("fav")
        for o in self.it["quotes"]:
            o.pop("fav", None)
        if on:
            q["fav"] = True
        self.it["updated"] = time.time()
        self.app.commit(self.it["id"])
        self._fill_quotes()

    def fav(self):
        it = self.it
        it["favorite"] = not it["favorite"]
        it["updated"] = time.time()
        self.app.commit(it["id"])
        try:
            self._style_btn(self.fav_btn, "Favorito" if it["favorite"] else "Favoritar",
                            "heart_fill" if it["favorite"] else "heart", PINK, it["favorite"])
        except Exception:
            self.render()

    def add_list(self):
        name = (ctk.CTkInputDialog(text="Nome da lista:", title="Adicionar à lista").get_input() or "").strip()
        if name and name not in self.it["lists"]:
            self.it["lists"].append(name)
            self.it["updated"] = time.time()
            self.app.commit(self.it["id"])
            self.render()

    def sync_timer(self):
        t = self.app.timer
        running = bool(t and t["id"] == self.it["id"])
        try:
            self.timer_btn.configure(text="Parar e salvar" if running else "Iniciar leitura")
            self.total_lbl.configure(text=f"Total nesta leitura: {fmt_minutes(self.it['minutes'])}")
            if not running:
                self.timer_lbl.configure(text="00:00:00")
        except Exception:
            pass

    def toggle_timer(self):
        """Liga/desliga o cronômetro mexendo só no botão e nos textos (sem refazer a tela)."""
        t = self.app.timer
        if t and t["id"] == self.it["id"]:
            self.app.stop_timer()
        else:
            self.app.start_timer(self.it)
        t = self.app.timer
        running = bool(t and t["id"] == self.it["id"])
        try:
            self.timer_btn.configure(text="Parar e salvar" if running else "Iniciar leitura")
            self.total_lbl.configure(text=f"Total nesta leitura: {fmt_minutes(self.it['minutes'])}")
            if not running:
                self.timer_lbl.configure(text="00:00:00")
        except Exception:
            self.render()

    def status_menu(self):
        """Troca rápida de status: menu logo abaixo do botão de status."""
        m = tk.Menu(self, tearoff=0, bg=P["surface"], fg=P["text"], activebackground=P["surface2"],
                    activeforeground=P["text"], bd=0, relief="flat", font=("TkDefaultFont", fpt(11)))
        for key, label in STATUS.items():
            mark = "✓  " if key == self.it["status"] else "      "
            m.add_command(label=f"{mark}{label}", foreground=P["status"][key], command=lambda k=key: self.set_status(k))
        b = self.status_btn
        try:
            m.tk_popup(b.winfo_rootx(), b.winfo_rooty() + b.winfo_height() + 4)
        finally:
            m.grab_release()

    def set_status(self, new):
        it = self.it
        old = it["status"]
        if new == old:
            return
        today = date.today().strftime("%d/%m/%Y")
        ev = status_event(old, new)
        sig = self._sig()
        it["status"] = new
        if new == "lendo":
            it["started"] = it["started"] or today
        if new == "completo":
            it["finished"] = it["finished"] or today
            if it["total"]:
                it["seen"] = it["total"]
        if ev:
            add_event(it, ev)
        it["updated"] = time.time()
        self.app.commit(it["id"])
        self.app.toast(f"Status: {STATUS[new]}")
        self._sync_top(sig)

    def tick(self):
        if not self.winfo_exists():
            return
        t = self.app.timer
        if t and t["id"] == self.it["id"] and self.timer_lbl is not None:
            e = int(time.time() - t["start"])
            self.timer_lbl.configure(text=f"{e // 3600:02d}:{e % 3600 // 60:02d}:{e % 60:02d}")
        self.after(1000, self.tick)


class BadgesPage(ImgPage):
    MAXW = 980
    FILTERS = ["Todas", "Conquistadas", "Em progresso", "Secretas"]

    def __init__(self, app):
        self.filter, self.cat = "Todas", "Todas"
        self.st = badge_status(app)
        super().__init__(app, "Conquistas", back=True)

    # ---- dados: conquistas com etapas viram um cartão só ----
    def _entries(self):
        st = self.st
        fam = {}
        for b in st:
            if not b["secret"] and b["key"] in FAMILY:
                fam.setdefault(b["key"], []).append(b)
        ents, seen = [], set()
        for b in st:
            k = b["key"]
            if not b["secret"] and k in fam and len(fam[k]) > 1:
                if k in seen:
                    continue
                seen.add(k)
                steps = sorted(fam[k], key=lambda x: x["need"])
                got = [x for x in steps if x["earned"]]
                nxt = next((x for x in steps if not x["earned"]), None)
                cur = got[-1] if got else None
                shown = nxt if nxt else steps[-1]
                pct = min(1, shown["have"] / shown["need"])
                ents.append(dict(kind="fam", id=k, steps=steps, cur=cur, nxt=nxt, cat=b["cat"], secret=False,
                                 any=bool(got), done=nxt is None, pct=pct, title=FAMILY[k]))
            else:
                ents.append(dict(kind="one", b=b, id=b["id"], cur=b if b["earned"] else None, cat=b["cat"],
                                 secret=b["secret"], any=b["earned"], done=b["earned"],
                                 pct=1 if b["earned"] else min(1, b["have"] / b["need"])))
        return ents

    def _lists(self):
        rank = {"ouro": 0, "prata": 1, "bronze": 2}
        out = []
        for e in self._entries():
            if self.cat != "Todas" and e["cat"] != self.cat:
                continue
            f = self.filter
            if f == "Conquistadas" and not e["any"]:
                continue
            if f == "Em progresso" and (e["done"] or (e["secret"] and not e["any"])):
                continue
            if f == "Secretas" and not e["secret"]:
                continue
            out.append(e)

        def key(e):
            locked = e["secret"] and not e["any"]
            grp = 2 if locked else (0 if e["done"] else 1)
            tier = rank[(e["cur"] or (e["b"] if e["kind"] == "one" else e["steps"][0]))["tier"]]
            return (grp, tier if grp == 0 else 0, -e["pct"])
        return sorted(out, key=key)

    def _summary(self, w):
        st = self.st
        vis = [b for b in st if not b["secret"] or b["earned"]]
        got = sum(1 for b in vis if b["earned"])
        hidden = len(st) - len(vis)

        def draw(hov):
            img, d = panel_img(w, 112)
            T(d, 20, 16, f"{got} de {len(vis)} conquistadas", 20, P["text"], True)
            if hidden:
                T(d, w - 20, 24, f"{hidden} secretas por descobrir", 12, P["muted"], anchor="rm")
            bw = w - 40
            d.rounded_rectangle([20 * K, 52 * K, (20 + bw) * K, 60 * K], radius=4 * K, fill=P["surface2"])
            if got:
                d.rounded_rectangle([20 * K, 52 * K, (20 + bw * got / max(1, len(vis))) * K, 60 * K], radius=4 * K,
                                    fill=P["accent"])
            x = 20
            for tier in ("bronze", "prata", "ouro"):
                tv = [b for b in vis if b["tier"] == tier]
                tg = sum(1 for b in tv if b["earned"])
                bi = badge_pil("star", tier, True, 26 * K)
                img.paste(bi, (int(x * K), int(72 * K)), bi)
                T(d, x + 34, 85, f"{tg}/{len(tv)} {tier}", 13, P["text"], True, "lm")
                x += 34 + TW(d, f"{tg}/{len(tv)} {tier}", 13, True) + 26
            T(d, w - 20, 85, "Clique numa conquistada para fixar no perfil (até 3)", 12, P["muted"], anchor="rm")
            return img
        return Blk(f"sum-{got}-{w}-{len(self.app.profile.get('showcase', []))}", 0, 0, w, 112, draw)

    def _chips(self, w, names, cur, setter, tag):
        tmp = ImageDraw.Draw(Image.new("RGB", (4, 4)))
        boxes, x = [], 0
        for n in names:
            bw = TW(tmp, n, 13, True) + 30
            boxes.append((x, 0, x + bw, 34, n))
            x += bw + 8

        def draw(hov):
            img = Image.new("RGBA", (w * K, 34 * K), (0, 0, 0, 0))
            for i, (x0, y0, x1, y1, n) in enumerate(boxes):
                on = n == cur
                fill = P["accent"] if on else (P["surface2"] if hov == f"f{i}" else P["surface"])
                draw_btn(img, (x0, y0, x1, y1), n, fill, "#ffffff" if on else P["text"], size=13, radius=17)
            return img
        regs = [(x0, y0, x1, y1, f"f{i}") for i, (x0, y0, x1, y1, n) in enumerate(boxes)]

        def act(name):
            setter(names[int(name[1:])])
            self.view.rebuild()
        return Blk(f"{tag}-{cur}-{w}", 0, 0, w, 34, draw, regs, act)

    def _pin(self, bid):
        pr = self.app.profile
        sh = [i for i in pr.get("showcase", [])]
        if bid in sh:
            sh.remove(bid)
            msg = "Conquista removida do perfil"
        else:
            sh.append(bid)
            sh = sh[-3:]
            msg = "Conquista fixada no perfil"
        pr["showcase"] = sh
        save_profile(pr)
        self.app.toast(msg)
        self.view.rebuild()

    def _card(self, e, w, h):
        app = self.app
        secret = e["secret"] and not e["any"]
        pinned = set(app.profile.get("showcase", []))

        def draw(hov):
            img, d = panel_img(w, h)
            if hov in ("pin", "m0") and e["cur"]:
                d.rounded_rectangle([0, 0, w * K - 1, h * K - 1], radius=14 * K, outline=P["accent"], width=2 * K)
            x = 100
            if e["kind"] == "fam":
                cur, nxt, steps = e["cur"], e["nxt"], e["steps"]
                med = cur or steps[0]
                shown = nxt or steps[-1]
                pr_ = None if cur and not nxt else min(1, shown["have"] / shown["need"])
                bi = badge_pil(med["icon"], med["tier"], bool(cur), 68 * K, None if cur else pr_)
                title = e["title"]
                desc = (f"Próxima etapa: {nxt['title']} — {nxt['desc']}" if nxt else "Todas as etapas concluídas!")
                tier_col = TIER_COLOR[shown["tier"]]
                frac = 1 if not nxt else min(1, nxt["have"] / nxt["need"])
                tag = (f"{int(min(shown['have'], shown['need']))}/{int(shown['need'])}  •  "
                       f"etapa {sum(1 for t in steps if t['earned'])}/{len(steps)}")
                for n, t in enumerate(reversed(steps)):
                    mb = badge_pil(t["icon"], t["tier"], t["earned"], 22 * K)
                    img.paste(mb, (int((w - 16 - (n + 1) * 26) * K), int(12 * K)), mb)
                tw_max = w - x - 18 - len(steps) * 26
                ref = cur
            else:
                b = e["b"]
                pr_ = None if b["earned"] else min(1, b["have"] / b["need"])
                bi = badge_pil("lock" if secret else b["icon"], b["tier"], b["earned"], 68 * K, None if secret else pr_)
                title = "Conquista secreta" if secret else b["title"]
                desc = "Continue lendo para descobrir…" if secret else b["desc"]
                tier_col = TIER_COLOR[b["tier"]]
                frac = min(1, b["have"] / b["need"])
                tag = f"{int(min(b['have'], b['need']))}/{int(b['need'])}  •  {b['tier']}" + ("  •  secreta" if b["secret"] else "")
                tw_max = w - x - 18
                ref = b if b["earned"] else None
                if not secret:
                    rar = badge_rarity(b)
                    rw = TW(d, rar, 10, True) + 14
                    d.rounded_rectangle([(w - 16 - rw) * K, 14 * K, (w - 16) * K, 30 * K], radius=8 * K,
                                        fill=mix(RARITY[rar], P["surface"], .78))
                    T(d, w - 16 - rw / 2, 22, rar, 10, RARITY[rar], True, "mm")
                    tw_max = w - x - 18 - rw - 8
            img.paste(bi, (int(16 * K), int((h - 68) / 2 * K)), bi)
            T(d, x, 14, title, 15, P["text"] if e["any"] else P["muted"], True)
            for n, line in enumerate(wrap_l(desc, 12, w - x - 18, maxlines=2)):
                T(d, x, 38 + n * 16, line, 12, P["muted"])
            if not secret:
                d.rounded_rectangle([x * K, 76 * K, (w - 18) * K, 82 * K], radius=3 * K, fill=P["surface2"])
                if frac > 0:
                    d.rounded_rectangle([x * K, 76 * K, (x + (w - 18 - x) * frac) * K, 82 * K], radius=3 * K,
                                        fill=tier_col)
                T(d, x, 90, tag, 11, P["muted"])
                if ref:
                    when = fmt_badge_date(ref.get("date", ""))
                    if when:
                        T(d, w - 18, 90, f"conquistada em {when}", 11, P["muted"], anchor="ra")
            if ref and ref["id"] in pinned:
                lab = "no perfil"
                pw_ = TW(d, lab, 10, True) + 22
                d.rounded_rectangle([(w - 16 - pw_) * K, (h - 48) * K, (w - 16) * K, (h - 32) * K], radius=8 * K,
                                    fill=mix(P["accent"], P["surface"], .75))
                T(d, w - 16 - pw_ / 2, h - 40, lab, 10, P["accent"], True, "mm")
            return img
        return draw

    def layout(self, avail):
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        out, y = [], 8
        pinned = tuple(self.app.profile.get("showcase", []))
        for blk, hh in ((self._summary(W), 112),
                        (self._chips(W, self.FILTERS, self.filter, lambda v: setattr(self, "filter", v), "fs"), 34),
                        (self._chips(W, ["Todas"] + CATS, self.cat, lambda v: setattr(self, "cat", v), "ct"), 34)):
            blk.x, blk.y = pad, y
            out.append(blk)
            y += hh + 12
        y += 4
        n = 2 if W >= 640 else 1
        gap, h = 14, 106
        cw = (W - gap * (n - 1)) // n
        lst = self._lists()
        for k, e in enumerate(lst):
            r, c = divmod(k, n)
            ref = e["cur"]
            regs = [(0, 0, cw, h, "pin")] if ref else []
            act = (lambda nm, ref=ref: self._pin(ref["id"])) if ref else None
            blk = Blk(f"b-{self.filter}-{self.cat}-{e['id']}-{cw}-{pinned}", pad + c * (cw + gap),
                      y + r * (h + gap), cw, h, self._card(e, cw, h), regs, act)
            if e["kind"] == "fam":
                med = e["cur"] or e["steps"][0]
                nx = e["nxt"] or e["steps"][-1]
                spec = (med["icon"], med["tier"], bool(e["cur"]),
                        None if (e["cur"] and not e["nxt"]) or e["cur"] else min(1, nx["have"] / nx["need"]))
            else:
                b_ = e["b"]
                spec = ("lock" if (e["secret"] and not e["any"]) else b_["icon"], b_["tier"], b_["earned"],
                        None if (b_["earned"] or e["secret"]) else min(1, b_["have"] / b_["need"]))
            blk.medals = [dict(name="m0", cx=16 + 34, cy=h / 2, size=68, spec=spec)]
            blk.regs = [(16, (h - 68) / 2, 84, (h + 68) / 2, "m0")] + blk.regs
            out.append(blk)
        y += -(-len(lst) // n) * (h + gap)
        if not lst:
            def empty(hov, w=W):
                img = Image.new("RGBA", (w * K, 30 * K), (0, 0, 0, 0))
                T(ImageDraw.Draw(img), 4, 4, "Nenhuma conquista nesta categoria ainda.", 14, P["muted"])
                return img
            out.append(Blk("empty", pad, y, W, 30, empty))
        return out


class YearReviewPage(Page):
    MAXW = 900

    def __init__(self, app, year=None):
        super().__init__(app, "Retrospectiva", back=True)
        self.review_year = year or date.today().year
        years = sorted({y for i in app.items for y in (year_of(i["finished"]), year_of(i["started"])) if y}
                       | {date.today().year}, reverse=True)
        top = ctk.CTkFrame(self.col, fg_color="transparent")
        top.pack(fill="x", pady=(0, 6))
        self.ymenu = menu(top, [str(y) for y in years], self.set_year, 110, height=34)
        self.ymenu.set(str(self.review_year))
        self.ymenu.pack(side="left")
        self.body = ctk.CTkFrame(self.col, fg_color="transparent")
        self.body.pack(fill="x")
        self.render()

    def set_year(self, v):
        self.review_year = int(v)
        self.render()

    def render(self):
        for w in self.body.winfo_children():
            w.destroy()
        app, y = self.app, self.review_year
        items, act, pre = app.items, app.activity, str(self.review_year)
        done = [i for i in items if i["status"] == "completo" and year_of(i["finished"]) == y]
        chapters, mins = sum_activity(act, pre, "ch"), sum_activity(act, pre, "min")
        rated = [i["rating"] for i in done if i["rating"]]

        hero = ctk.CTkFrame(self.body, fg_color=P["accent"], corner_radius=18)
        hero.pack(fill="x", pady=(4, 12))
        ctk.CTkLabel(hero, text=f"Seu {y} em leituras", text_color="white",
                     font=ctk.CTkFont(size=26, weight="bold")).pack(anchor="w", padx=22, pady=(18, 4))
        g = ctk.CTkFrame(hero, fg_color="transparent")
        g.pack(fill="x", padx=14, pady=(0, 18))
        nums = [(len(done), "completas"), (chapters, "capítulos lidos"), (fmt_minutes(mins), "de leitura"),
                (f"{sum(rated) / len(rated):.1f}".replace(".", ",") if rated else "–", "nota média")]
        for k, (v, lab) in enumerate(nums):
            c = ctk.CTkFrame(g, fg_color="transparent")
            c.grid(row=0, column=k, padx=8, sticky="w")
            ctk.CTkLabel(c, text=str(v), text_color="white", font=ctk.CTkFont(size=30, weight="bold")).pack(anchor="w")
            ctk.CTkLabel(c, text=lab, text_color="white", font=ctk.CTkFont(size=12)).pack(anchor="w")
            g.grid_columnconfigure(k, weight=1)

        if not done and not chapters:
            ctk.CTkLabel(self.body, text=f"Nada registrado em {y} ainda. Complete leituras e use o +1 capítulo "
                         "ou o cronômetro para alimentar a retrospectiva.", text_color=P["muted"],
                         wraplength=520, justify="left").pack(anchor="w", pady=20)
            return

        genres, types = Counter(t for i in done for t in i["tags"]), Counter(i["type"] for i in done)
        months = Counter()
        for k, v in act.items():
            if k.startswith(pre):
                months[int(k[5:7])] += v.get("ch", 0)
        best = max(months.items(), key=lambda kv: kv[1]) if months and max(months.values()) > 0 else None
        longest = streaks({k: v for k, v in act.items() if k.startswith(pre)})[1]
        f, _ = panel(self.body, "Em destaque")
        f.pack(fill="x", pady=(0, 12))
        for lab, val in (("Gênero mais lido", genres.most_common(1)[0][0] if genres else "–"),
                         ("Tipo mais lido", types.most_common(1)[0][0] if types else "–"),
                         ("Mês mais ativo", f"{MESES_LONGOS[best[0] - 1]} ({best[1]} capítulos)" if best else "–"),
                         ("Maior sequência", f"{longest} dias" if longest else "–")):
            r = ctk.CTkFrame(f, fg_color="transparent")
            r.pack(fill="x", padx=16, pady=3)
            ctk.CTkLabel(r, text=lab, text_color=P["muted"], width=150, anchor="w").pack(side="left")
            ctk.CTkLabel(r, text=val, text_color=P["text"], font=ctk.CTkFont(size=14, weight="bold")).pack(side="left")
        ctk.CTkFrame(f, width=1, height=10, fg_color="transparent").pack()

        top = sorted(done, key=lambda i: (-i["rating"], -i["seen"]))[:5]
        if top:
            f, _ = panel(self.body, "Melhores leituras do ano")
            f.pack(fill="x")
            row = ctk.CTkFrame(f, fg_color="transparent")
            row.pack(fill="x", padx=10, pady=(0, 14))
            for n, it in enumerate(top):
                app.tile(row, it, 130, bg=P["surface"]).grid(row=0, column=n, padx=6, sticky="n")


class TierPage(Page):
    """Tier list num único canvas: as capas são itens que se movem (sem destruir/recriar widgets),
    então arrastar não deixa rastro e nada pisca ao soltar."""
    MAXW = 1400
    TW, TH, GAP, LBL = 64, 90, 6, 76

    def __init__(self, app):
        super().__init__(app, "Tier list", back=True)
        self.tiers = app.profile.setdefault("tiers", {})
        for t in TIERS:
            self.tiers.setdefault(t, [])
        self.drag, self.query = None, ""
        self.zones, self.sig, self.thumbs, self.ph, self.bg_img, self.slots = {}, None, {}, {}, {}, {}
        top = ctk.CTkFrame(self.col, fg_color="transparent")
        top.pack(fill="x", pady=(0, 10))
        accent_button(top, " Gerar imagem", self.make_image, image=icon("share", 16, "#ffffff"), compound="left",
                      width=150).pack(side="right")
        ghost_button(top, "Limpar tudo", self.clear_all, width=110).pack(side="right", padx=(0, 8))
        ctk.CTkLabel(top, text="Arraste as capas para as linhas. Clique numa capa para abrir.",
                     text_color=P["muted"]).pack(side="left")
        self.cv = tk.Canvas(self.col, bg=P["bg"], highlightthickness=0, bd=0, height=px(700))
        self.cv.pack(fill="x")
        self.cv.bind("<Configure>", lambda e: self._soon())
        self.cv.bind("<ButtonPress-1>", self._press)
        self.cv.bind("<B1-Motion>", self._motion)
        self.cv.bind("<ButtonRelease-1>", self._release)
        self.cv.bind("<Motion>", self._hover)
        self._job = None
        self.q_entry = entry(self.cv, "Filtrar por nome...", width=200)
        self.q_entry.bind("<KeyRelease>", lambda e: self._set_query(self.q_entry.get()), add="+")
        self._qwin = None
        self.after(60, self.relayout)

    # ---- geometria ----
    def _soon(self):
        if self._job:
            try:
                self.after_cancel(self._job)
            except Exception:
                pass
        self._job = self.after(60, self.relayout)

    def _by_id(self):
        return {i["id"]: i for i in self.app.items}

    def _slots(self, n, x0, y0, avail):
        per = max(1, int((avail + self.GAP) // (self.TW + self.GAP)))
        return per, [(x0 + (k % per) * (self.TW + self.GAP), y0 + (k // per) * (self.TH + self.GAP)) for k in range(n)]

    def _free(self, by_id):
        used = {x for t in TIERS for x in self.tiers[t]}
        q = self.query.lower()
        return [i for i in self.app.items if i["id"] not in used and q in i["title"].lower()][:80]

    def relayout(self):
        self._job = None
        if not self.winfo_exists():
            return
        W = int(lw(self.cv.winfo_width()))
        if W < 300:
            return
        by_id = self._by_id()
        for t in TIERS:
            self.tiers[t] = [x for x in self.tiers[t] if x in by_id]
        x_in = self.LBL + 22
        avail = W - x_in - 16
        zones, slots, y = {}, {}, 0
        for t in TIERS:
            ids = self.tiers[t]
            per, pos = self._slots(len(ids), x_in, y + 12, avail)
            lines = max(1, -(-len(ids) // per))
            h = max(112, 24 + lines * (self.TH + self.GAP) - self.GAP)
            zones[t] = (0, y, W, y + h)
            for k, i_ in enumerate(ids):
                slots[i_] = pos[k]
            y += h + 10
        free = self._free(by_id)
        y += 6
        per, pos = self._slots(len(free), 18, y + 56, W - 36)
        lines = max(1, -(-len(free) // per))
        hp = 56 + 12 + lines * (self.TH + self.GAP)
        zones["pool"] = (0, y, W, y + hp)
        for k, it in enumerate(free):
            slots[it["id"]] = pos[k]
        total = y + hp + 8
        sig = (W, tuple((k, v[3] - v[1]) for k, v in zones.items()), P["accent"], P["surface"])
        self.zones = zones
        cv = self.cv
        if sig != self.sig:                                   # só redesenha os fundos se a geometria mudou
            self.sig = sig
            cv.delete("bg")
            cv.delete("ui")
            self.bg_img = {}
            for key, (x0, y0, x1, y1) in zones.items():
                h = y1 - y0
                n_, h_ = self._bg_pil(key, W, h, False), self._bg_pil(key, W, h, True)
                self.bg_img[key] = (n_, h_)
                cv.create_image(0, px(y0), image=n_, anchor="nw", tags=("bg", f"bg-{key}"))
            ty = zones["pool"][1]
            cv.create_rectangle(px(18), px(ty + 16), px(21), px(ty + 40), fill=P["accent"], width=0, tags="ui")
            cv.create_text(px(32), px(ty + 28), text="Sem classificação", fill=P["text"], anchor="w",
                           font=ctk.CTkFont(size=15, weight="bold"), tags="ui")
            if self._qwin is None:
                self._qwin = cv.create_window(px(W - 18 - 200), px(ty + 10), window=self.q_entry, anchor="nw")
            else:
                cv.coords(self._qwin, px(W - 18 - 200), px(ty + 10))
            cv.tag_lower("bg")
        cv.configure(height=px(total))
        # capas: cria as que faltam, remove as que saíram, reposiciona todas
        for i_ in [i for i in self.thumbs if i not in slots]:
            cv.delete(self.thumbs.pop(i_))
        for i_, (x, yy) in slots.items():
            if self.drag and self.drag.get("moved") and self.drag["id"] == i_:
                continue
            if i_ not in self.thumbs:
                self.thumbs[i_] = cv.create_image(px(x), px(yy), image=self._photo(by_id[i_]), anchor="nw",
                                                  tags=("thumb", f"id:{i_}"))
            else:
                cv.coords(self.thumbs[i_], px(x), px(yy))
        self.slots = slots
        self._hot(None)

    def _bg_pil(self, key, W, h, hot):
        k = K
        im = Image.new("RGBA", (W * k, h * k), (0, 0, 0, 0))
        d = ImageDraw.Draw(im)
        d.rounded_rectangle([1, 1, W * k - 2, h * k - 2], radius=14 * k, fill=P["surface"],
                            outline=P["accent"] if hot else P["border"], width=(3 if hot else 2) * k)
        if key in TIERS:
            d.rounded_rectangle([10 * k, 10 * k, (10 + self.LBL) * k, (h - 10) * k], radius=10 * k,
                                fill=TIER_COLORS[key])
            T(d, 10 + self.LBL / 2, h / 2, key, 34, "#1a1206", True, "mm")
        return ImageTk.PhotoImage(im.resize((px(W), px(h)), Image.LANCZOS))

    def _photo(self, it):
        ph = self.ph.get(it["id"])
        if ph is None:
            img = self.app.cover_pil(it, self.TW, self.TH).resize((px(self.TW), px(self.TH)), Image.LANCZOS)
            ph = self.ph[it["id"]] = ImageTk.PhotoImage(img)
            while len(self.ph) > 240:
                self.ph.pop(next(iter(self.ph)))
        return ph

    def _hot(self, key):
        for k, (n_, h_) in self.bg_img.items():
            try:
                self.cv.itemconfigure(f"bg-{k}", image=h_ if k == key else n_)
            except tk.TclError:
                pass

    def _set_query(self, text):
        self.query = text.strip()
        self.relayout()

    # ---- arrastar e soltar ----
    def _hit_thumb(self, e):
        x, y = self.cv.canvasx(e.x), self.cv.canvasy(e.y)
        for item in reversed(self.cv.find_overlapping(x, y, x, y)):
            for tg in self.cv.gettags(item):
                if tg.startswith("id:"):
                    return item, tg[3:]
        return None, None

    def _hover(self, e):
        if self.drag:
            return
        item, _ = self._hit_thumb(e)
        self.cv.configure(cursor="fleur" if item else "")

    def _press(self, e):
        item, i_ = self._hit_thumb(e)
        if not item:
            return
        x, y = self.cv.coords(item)
        self.drag = {"id": i_, "item": item, "dx": e.x - x, "dy": e.y - y, "x0": e.x, "y0": e.y, "moved": False}

    def _motion(self, e):
        d = self.drag
        if not d:
            return
        if not d["moved"]:
            if abs(e.x - d["x0"]) + abs(e.y - d["y0"]) < 6:
                return
            d["moved"] = True
            self.cv.tag_raise(d["item"])
        self.cv.coords(d["item"], e.x - d["dx"], e.y - d["dy"])
        self._hot(self._zone_at(lw(e.x), lw(e.y)))
        self._autoscroll(e)

    def _autoscroll(self, e):
        try:
            sc = self.scroll.canvas
            top = sc.winfo_rooty()
            bot = top + sc.winfo_height()
            yr = e.y_root
            step = -3 if yr < top + px(60) else 3 if yr > bot - px(60) else 0
            if step and self.drag:
                sc.yview_scroll(step, "units")
                # a capa acompanha o cursor mesmo com a página rolando
                self.after(30, lambda: self._follow())
        except Exception:
            pass

    def _follow(self):
        d = self.drag
        if not d or not d["moved"]:
            return
        try:
            px_, py_ = self.cv.winfo_pointerx() - self.cv.winfo_rootx(), self.cv.winfo_pointery() - self.cv.winfo_rooty()
            self.cv.coords(d["item"], px_ - d["dx"], py_ - d["dy"])
            self._hot(self._zone_at(lw(px_), lw(py_)))
        except tk.TclError:
            pass

    def _zone_at(self, x, y):
        for key, (x0, y0, x1, y1) in self.zones.items():
            if x0 <= x <= x1 and y0 <= y <= y1:
                return key
        return None

    def _release(self, e):
        d, self.drag = self.drag, None
        if not d:
            return
        it = self._by_id().get(d["id"])
        if not d["moved"]:
            if it:
                self.app.open_detail(it)
            return
        key = self._zone_at(lw(e.x), lw(e.y))
        if it is None or key is None:
            return self.relayout()
        for t in TIERS:
            if it["id"] in self.tiers[t]:
                self.tiers[t].remove(it["id"])
        if key in TIERS:
            cx, cy = lw(e.x - d["dx"]) + self.TW / 2, lw(e.y - d["dy"]) + self.TH / 2
            idx = 0
            for o in self.tiers[key]:
                ox, oy = self.slots.get(o, (0, 0))
                ocy = oy + self.TH / 2
                if ocy < cy - self.TH / 2 or (abs(ocy - cy) <= self.TH / 2 and ox + self.TW / 2 < cx):
                    idx += 1
            self.tiers[key].insert(min(idx, len(self.tiers[key])), it["id"])
        save_profile(self.app.profile)
        self.relayout()

    def clear_all(self):
        if messagebox.askyesno("Limpar tier list", "Tirar todas as capas das linhas?", parent=self.app):
            for t in TIERS:
                self.tiers[t] = []
            save_profile(self.app.profile)
            self.relayout()

    def make_image(self):
        p = filedialog.asksaveasfilename(parent=self.app, defaultextension=".png", initialfile="minha_tier_list.png",
                                         filetypes=[("Imagem PNG", "*.png")])
        if not p:
            return
        try:
            make_tier_image(self.app, p)
        except Exception as e:
            return messagebox.showerror("Erro", f"Não consegui gerar a imagem:\n{e}", parent=self.app)
        self.app.toast("Imagem da tier list salva!")


class ListsPage(ImgPage):
    MAXW = 1800
    _title, _note, _tiles = ProfilePage._title, ProfilePage._note, ProfilePage._tiles

    def __init__(self, app):
        super().__init__(app, None)
        self.names = sorted({n for i in app.items for n in i["lists"]}, key=str.lower)
        self.members = {n: [i for i in app.items if n in i["lists"]] for n in self.names}

    def layout(self, avail):
        app = self.app
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        out, y = [], 8

        nobras = len({i["id"] for i in app.items if i["lists"]})
        sub = f"{len(self.names)} lista{'s' if len(self.names) != 1 else ''}  •  {nobras} obra{'s' if nobras != 1 else ''}"
        _bt = [("Tier list", "go", True)]
        _regs = head_banner(self, W, "list", "Listas", sub, _bt)[1]
        out.append(Blk(f"lists-head-{W}-{len(self.names)}-{nobras}-{P['accent']}", pad, y, W, BANNER_H,
                       lambda hov: head_banner(self, W, "list", "Listas", sub, _bt, hov)[0],
                       [(x0, y0, x1, y1, "go") for x0, y0, x1, y1, _n in _regs], lambda n: app.open_sub(TierPage)))
        y += BANNER_H + 8
        if not self.names:
            msg = ("Você ainda não criou listas. Abra uma leitura e use “+ Lista”, ou preencha o campo "
                   "“Listas” ao editar.")
            lines = wrap_l(msg, 14, 480)

            def note_draw(hov):
                img = Image.new("RGBA", (500 * K, (len(lines) * 20 + 4) * K), (0, 0, 0, 0))
                d = ImageDraw.Draw(img)
                for n, line in enumerate(lines):
                    T(d, 0, 2 + n * 20, line, 14, P["muted"])
                return img
            out.append(Blk("empty", pad + 10, y + 30, 500, len(lines) * 20 + 4, note_draw))
            return out
        cols = max(2, W // 172)
        tw = max(90, min(190, (W // cols - 22) // 10 * 10))
        for name in self.names:
            members = self.members[name]
            y += 16
            out.append(self._title("t-" + name, f"{name}  ·  {len(members)}", pad, y))

            def btn_draw(hov):
                img = Image.new("RGBA", (200 * K, 28 * K), (0, 0, 0, 0))
                flat_h = mix(P["surface2"], P["accent"], .38)
                draw_btn(img, (0, 0, 90, 28), "Renomear", flat_h if hov == "ren" else P["surface2"], P["text"],
                         size=12, radius=8)
                draw_btn(img, (98, 0, 198, 28), "Excluir lista", flat_h if hov == "del" else P["surface2"],
                         P["text"], size=12, radius=8)
                return img
            out.append(Blk("b-" + name, pad + W - 200, y, 200, 28, btn_draw,
                           [(0, 0, 90, 28, "ren"), (98, 0, 198, 28, "del")],
                           lambda n_, name=name: self.rename(name) if n_ == "ren" else self.delete(name)))
            y += 28 + 8
            y = self._tiles("l-" + name, members, "", pad, y, cols, tw, out, rows_max=None)
        return out

    def rename(self, old):
        new = (ctk.CTkInputDialog(text="Novo nome da lista:", title="Renomear lista").get_input() or "").strip()
        if not new or new == old:
            return
        for i in self.app.items:
            i["lists"] = [new if n == old else n for n in i["lists"]]
            i["lists"] = list(dict.fromkeys(i["lists"]))
        save_items(self.app.items)
        self.app.nav("lists")

    def delete(self, name):
        if messagebox.askyesno("Excluir lista", f"Excluir a lista “{name}”? As leituras continuam na biblioteca.",
                               parent=self.app):
            for i in self.app.items:
                i["lists"] = [n for n in i["lists"] if n != name]
            save_items(self.app.items)
            self.app.nav("lists")


def theme_preview(th, w=104, h=58, k=3):
    """Mini janela do tema (barra lateral, cartões e botão de destaque): mostra como ele é de verdade."""
    W, H = w * k, h * k
    im = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    r = 9 * k
    d.rounded_rectangle([0, 0, W - 1, H - 1], radius=r, fill=th["bg"], outline=th["border"], width=k)
    side = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    sd = ImageDraw.Draw(side)
    sd.rounded_rectangle([0, 0, 27 * k, H - 1], radius=r, fill=th["side"])
    sd.rectangle([14 * k, 0, 27 * k, H - 1], fill=th["side"])
    im.alpha_composite(side)
    d = ImageDraw.Draw(im)
    d.rounded_rectangle([5 * k, 6 * k, 22 * k, 12 * k], radius=3 * k, fill=th["accent"])
    for n in range(3):
        d.rounded_rectangle([6 * k, (18 + n * 8) * k, 22 * k, (22 + n * 8) * k], radius=2 * k,
                            fill=th["surface2"] if n else th["muted"])
    d.rounded_rectangle([33 * k, 7 * k, 98 * k, 13 * k], radius=3 * k, fill=th["text"])
    d.rounded_rectangle([33 * k, 19 * k, 63 * k, 38 * k], radius=4 * k, fill=th["surface"], outline=th["border"], width=k)
    d.rounded_rectangle([68 * k, 19 * k, 98 * k, 38 * k], radius=4 * k, fill=th["surface"], outline=th["border"], width=k)
    d.rounded_rectangle([33 * k, 43 * k, 58 * k, 51 * k], radius=4 * k, fill=th["accent"])
    d.rounded_rectangle([63 * k, 44 * k, 98 * k, 50 * k], radius=3 * k, fill=th["surface2"])
    return im.resize((w * 2, h * 2), Image.LANCZOS)


# ---------- configurações ----------
class SettingsPage(Page):
    MAXW = 640

    def __init__(self, app):
        super().__init__(app, "Configurações")
        f = self.card("Aparência")
        grid = ctk.CTkFrame(f, fg_color="transparent")
        grid.pack(anchor="w", padx=16, pady=(0, 6))
        for k, (name, th) in enumerate(THEMES.items()):
            on = name == S["theme"]
            ctk.CTkButton(grid, text=name, width=124, height=92, corner_radius=12,
                          fg_color=mix(P["accent"], P["surface"], .86) if on else P["surface2"],
                          hover_color=mix(P["accent"], P["surface"], .78), text_color=P["text"],
                          border_width=2 if on else 0, border_color=P["accent"],
                          image=ctk.CTkImage(theme_preview(th), size=(104, 58)), compound="top",
                          font=ctk.CTkFont(size=12, weight="bold" if on else "normal"),
                          command=lambda n=name: self.set_theme(n)).grid(
                row=k // 4, column=k % 4, padx=(0, 8), pady=(0, 8))
        ctk.CTkLabel(f, text="Cor de destaque", text_color=P["muted"]).pack(anchor="w", padx=16, pady=(12, 4))
        sw = ctk.CTkFrame(f, fg_color="transparent")
        sw.pack(anchor="w", padx=16, pady=(0, 14))
        for c in ACCENTS:
            ctk.CTkButton(sw, text="", width=30, height=30, corner_radius=15, fg_color=c, hover_color=c,
                          border_width=3 if c == S["accent"] else 0, border_color=P["text"],
                          command=lambda c=c: self.set_accent(c)).pack(side="left", padx=(0, 8))
        flat_button(sw, "Outra...", self.pick_color, width=70, height=30).pack(side="left")

        f = self.card("Interface")
        ctk.CTkLabel(f, text="Tamanho dos elementos na tela", text_color=P["muted"]).pack(anchor="w", padx=16)
        m = menu(f, list(UI_SCALES), self.set_scale, 160, fg=P["surface2"], height=34)
        m.set(S.get("ui_scale", "Automático"))
        m.pack(anchor="w", padx=16, pady=(4, 6))
        self.note(f, "“Automático” escolhe o tamanho ideal para a resolução do seu monitor.", (0, 4))
        self.start_max = tk.BooleanVar(value=bool(S.get("start_max")))
        check(f, "Abrir o programa maximizado", self.start_max, self.save_max).pack(
            anchor="w", padx=16, pady=(4, 6))
        self.opts = {}
        for key, text in (("anim", "Animações suaves"), ("splash", "Tela de abertura ao iniciar"),
                          ("preview", "Prévia ao passar o mouse nas capas"),
                          ("sounds", "Sons suaves ao completar uma obra ou ganhar uma conquista")):
            self.opts[key] = tk.BooleanVar(value=bool(S.get(key, True)))
            check(f, text, self.opts[key], lambda k=key: self.save_opt(k)).pack(anchor="w", padx=16, pady=(0, 6))
        ctk.CTkFrame(f, width=1, height=6, fg_color="transparent").pack()

        f = self.card("Seus dados")
        self.folder_lbl = ctk.CTkLabel(f, text=S["data_dir"], text_color=P["muted"], wraplength=420,
                                       justify="left")
        self.folder_lbl.pack(anchor="w", padx=16)
        flat_button(f, "Mudar pasta de salvamento...", self.change_folder).pack(anchor="w", padx=16, pady=(8, 0))
        self.note(f, "Dica: escolha uma pasta do Google Drive, Dropbox ou OneDrive para usar a lista em "
                     "mais de um computador.", (4, 12))
        row = ctk.CTkFrame(f, fg_color="transparent")
        row.pack(anchor="w", padx=16, pady=(0, 6))
        flat_button(row, "Exportar backup...", self.export).pack(side="left", padx=(0, 8))
        flat_button(row, "Importar backup...", self.import_).pack(side="left")
        self.note(f, "Backup automático: toda vez que você fecha o app, ele guarda uma cópia em “backups” "
                     "dentro da pasta de dados (as últimas 7). O backup inclui lista, capas, perfil e histórico.", (4, 14))

        f = self.card("Leitura parada")
        r = ctk.CTkFrame(f, fg_color="transparent")
        r.pack(anchor="w", padx=16, pady=(0, 6))
        ctk.CTkLabel(r, text="Avisar após", text_color=P["muted"]).pack(side="left")
        self.stall_entry = entry(r, width=60)
        self.stall_entry.insert(0, str(S.get("stall_days", 30)))
        self.stall_entry.pack(side="left", padx=8)
        ctk.CTkLabel(r, text="dias sem avançar", text_color=P["muted"]).pack(side="left", padx=(0, 10))
        accent_button(r, "Salvar", self.save_stall, width=70).pack(side="left")
        self.note(f, "Leituras “Lendo” sem progresso aparecem com um aviso e na seção “Retomar leitura” "
                     "do perfil.", (0, 14))

        f = self.card("Etiquetas")
        self.label_host = ctk.CTkFrame(f, fg_color="transparent")
        self.label_host.pack(fill="x", padx=16, pady=(0, 12))
        self.fill_labels()

        f = self.card("Importar e exportar (CSV)")
        row = ctk.CTkFrame(f, fg_color="transparent")
        row.pack(anchor="w", padx=16, pady=(0, 6))
        flat_button(row, "Exportar CSV...", self.export_csv_dialog).pack(side="left", padx=(0, 8))
        flat_button(row, "Importar CSV...", self.import_csv_dialog).pack(side="left")
        self.note(f, "O CSV abre no Excel. Ao importar, o app entende colunas em português ou inglês "
                     "(título, status, nota...) e não repete leituras que já existem.", (4, 14))

        f = self.card("Atalhos do teclado")
        keys = [("Ctrl+N", "Nova leitura"), ("Ctrl+F", "Buscar na biblioteca"), ("Ctrl+M", "Mini janela"),
                ("Ctrl+V", "Colar print (obra ou Galeria)"), ("Esc", "Voltar")]
        keys += [(f"Ctrl+{i}", label) for i, (_k, label, _ic) in enumerate(NAV, 1)]
        keys += [("← →", "Print anterior / próximo (visualizador)"), ("Del", "Excluir o print aberto"),
                 ("Roda", "Zoom no print (visualizador)"), ("2 cliques", "Ajustar o print à tela")]
        g = ctk.CTkFrame(f, fg_color="transparent")
        g.pack(fill="x", padx=16, pady=(0, 14))
        for n, (k_, txt) in enumerate(keys):
            r, c = divmod(n, 2)
            cell = ctk.CTkFrame(g, fg_color="transparent")
            cell.grid(row=r, column=c, sticky="w", padx=(0, 18), pady=3)
            ctk.CTkLabel(cell, text=k_, width=max(64, 22 + 8 * len(k_)), height=26, corner_radius=8, fg_color=P["surface2"],
                         text_color=P["text"], font=ctk.CTkFont(size=12, weight="bold")).pack(side="left")
            ctk.CTkLabel(cell, text=txt, text_color=P["muted"], font=ctk.CTkFont(size=13)).pack(side="left", padx=10)
        g.grid_columnconfigure((0, 1), weight=1)

    @staticmethod
    def note(parent, text, pady):
        ctk.CTkLabel(parent, text=text, text_color=P["muted"], font=ctk.CTkFont(size=11),
                     wraplength=420, justify="left").pack(anchor="w", padx=16, pady=pady)

    def fill_labels(self):
        for w in self.label_host.winfo_children():
            w.destroy()
        labels = self.app.profile.get("labels", {})
        if not labels:
            ctk.CTkLabel(self.label_host, text="Nenhuma etiqueta ainda. Crie na edição de uma leitura "
                         "(campo “Etiquetas coloridas”).", text_color=P["muted"], wraplength=420,
                         justify="left").pack(anchor="w")
            return
        for name, col in sorted(labels.items()):
            n = sum(1 for i in self.app.items if name in i["labels"])
            row = ctk.CTkFrame(self.label_host, fg_color="transparent")
            row.pack(fill="x", pady=3)
            ctk.CTkButton(row, text="", image=icon("dot", 16, col), width=34, height=30, corner_radius=15,
                          fg_color=mix(col, P["surface"], .72), hover_color=mix(col, P["surface"], .5),
                          command=lambda nm=name: self.pick_label_color(nm)).pack(side="left")
            ctk.CTkLabel(row, text=name, text_color=P["text"], font=ctk.CTkFont(size=13, weight="bold")).pack(
                side="left", padx=10)
            ctk.CTkLabel(row, text=f"{n} leituras", text_color=P["muted"], font=ctk.CTkFont(size=11)).pack(side="left")
            ghost_button(row, "", lambda nm=name: self.delete_label(nm), image=icon("close", 12), width=30,
                         height=28).pack(side="right")

    def pick_label_color(self, name):
        """Janelinha com 40 cores + 'Outra cor...' (qualquer cor) para a etiqueta."""
        d = self.app.profile.setdefault("labels", {})
        cur = d.get(name)
        app = self.app
        top = tk.Toplevel(app)
        top.overrideredirect(True)
        top.configure(bg=P["border"])
        top.attributes("-topmost", True)
        box = tk.Frame(top, bg=P["surface"], padx=px(12), pady=px(10))
        box.pack(padx=1, pady=1)
        tk.Label(box, text=f"Cor de “{name}”", bg=P["surface"], fg=P["text"],
                 font=("TkDefaultFont", fpt(11), "bold")).grid(row=0, column=0, columnspan=8, sticky="w",
                                                              pady=(0, px(8)))

        def apply(c):
            top.destroy()
            d[name] = c
            save_profile(app.profile)
            app.images.clear()
            self.fill_labels()

        def other():
            top.destroy()
            c = colorchooser.askcolor(color=cur or "#a78bfa", parent=app, title=f"Cor de “{name}”")[1]
            if c:
                apply(c)
        sz = px(28)
        for n, col in enumerate(LABEL_COLORS):
            cv = tk.Canvas(box, width=sz, height=sz, bg=P["surface"], highlightthickness=0, bd=0, cursor="hand2")
            cv.grid(row=1 + n // 8, column=n % 8, padx=px(2), pady=px(2))
            m = px(3)
            cv.create_oval(m, m, sz - m, sz - m, fill=col, outline="")
            if col == cur:
                cv.create_oval(1, 1, sz - 2, sz - 2, outline=P["text"], width=2)
            cv.bind("<Button-1>", lambda e, c=col: apply(c))
            cv.bind("<Enter>", lambda e, cv=cv: cv.configure(bg=P["surface2"]))
            cv.bind("<Leave>", lambda e, cv=cv: cv.configure(bg=P["surface"]))
        rows = 1 + len(LABEL_COLORS) // 8
        b_ = tk.Label(box, text="Outra cor...", bg=P["surface2"], fg=P["text"], cursor="hand2",
                      font=("TkDefaultFont", fpt(11)), pady=px(5))
        b_.grid(row=rows + 1, column=0, columnspan=8, sticky="ew", pady=(px(8), 0))
        b_.bind("<Button-1>", lambda e: other())
        top.update_idletasks()
        x = min(app.winfo_pointerx(), app.winfo_screenwidth() - top.winfo_reqwidth() - 10)
        y = min(app.winfo_pointery(), app.winfo_screenheight() - top.winfo_reqheight() - 50)
        top.geometry(f"+{x}+{y}")
        top.bind("<Escape>", lambda e: top.destroy())
        top.bind("<FocusOut>", lambda e: top.after(120, lambda: top.destroy() if top.winfo_exists() and
                                                    not str(top.focus_get()).startswith(str(top)) else None))
        top.focus_force()

    def delete_label(self, name):
        if not messagebox.askyesno("Excluir etiqueta", f"Excluir a etiqueta “{name}”? Ela some de todas as leituras.",
                                   parent=self.app):
            return
        self.app.profile.get("labels", {}).pop(name, None)
        for i in self.app.items:
            i["labels"] = [n for n in i["labels"] if n != name]
        save_profile(self.app.profile)
        save_items(self.app.items)
        self.app.images.clear()
        self.fill_labels()

    def set_scale(self, label):
        S["ui_scale"] = label
        save_settings()
        UI["ws"] = UI_SCALES.get(label) or auto_ws(self.app, UI["dpi"])
        try:
            ctk.set_widget_scaling(UI["ws"])
        except Exception:
            pass
        _icon_cache.clear()
        self.app.images.clear()
        app = self.app
        app.rebuild()
        app.nav("settings")

    def save_opt(self, key):
        S[key] = bool(self.opts[key].get())
        save_settings()

    def save_max(self):
        S["start_max"] = bool(self.start_max.get())
        save_settings()

    def save_stall(self):
        try:
            S["stall_days"] = max(1, int(self.stall_entry.get()))
        except ValueError:
            return
        save_settings()
        touch()
        self.app.toast("Configuração salva")

    def export_csv_dialog(self):
        p = filedialog.asksaveasfilename(parent=self.app, defaultextension=".csv",
                                         initialfile=f"leitura_foda_{date.today():%Y-%m-%d}.csv",
                                         filetypes=[("CSV", "*.csv")])
        if p:
            export_csv(self.app.items, p)
            self.app.toast("CSV exportado")

    def import_csv_dialog(self):
        p = filedialog.askopenfilename(parent=self.app, filetypes=[("CSV", "*.csv *.txt")])
        if not p:
            return
        try:
            new = import_csv(p)
        except (OSError, csv.Error, ValueError):
            return messagebox.showerror("Erro", "Não consegui ler esse arquivo CSV.", parent=self.app)
        have = {i["title"].lower() for i in self.app.items}
        new = [i for i in new if i["title"].lower() not in have]
        if not new:
            return self.app.toast("Nenhuma leitura nova nesse arquivo", "warn")
        if not messagebox.askyesno("Importar CSV", f"Adicionar {len(new)} leituras à sua lista?", parent=self.app):
            return
        self.app.items.extend(new)
        save_items(self.app.items)
        self.app.images.clear()
        self.app.toast(f"{len(new)} leituras adicionadas")

    def reload(self):
        app = self.app
        apply_palette()
        app.rebuild()
        app.nav("settings")

    def set_theme(self, label):
        S["theme"] = label
        S["accent"] = THEMES[label]["accent"]
        save_settings()
        self.after(120, self.reload)       # deixa o clique terminar antes de recriar a tela

    def set_accent(self, c):
        S["accent"] = c
        save_settings()
        self.after(120, self.reload)

    def pick_color(self):
        c = colorchooser.askcolor(color=S["accent"], parent=self.app)[1]
        if c:
            self.set_accent(c)

    def change_folder(self):
        new = filedialog.askdirectory(parent=self.app, title="Escolha a pasta de salvamento")
        if not new or Path(new) == data_dir():
            return
        new = Path(new)
        if (new / "data.json").exists():
            if not messagebox.askyesno("Pasta com lista", "Já existe uma lista nessa pasta. Usar essa lista?\n"
                                       "(A lista atual continua na pasta antiga.)", parent=self.app):
                return
        else:
            save_items(self.app.items)
            save_profile(self.app.profile)
            save_activity(self.app.activity)
            new.mkdir(parents=True, exist_ok=True)
            for f, n in ((data_file(), "data.json"), (profile_file(), "profile.json"),
                         (activity_file(), "activity.json")):
                if f.exists():
                    shutil.copy2(f, new / n)
            for d, n in ((covers_dir(), "covers"), (profile_dir(), "profile"), (shots_dir(), "shots")):
                if d.exists():
                    shutil.copytree(d, new / n, dirs_exist_ok=True)
        S["data_dir"] = str(new)
        save_settings()
        self.app.items = load_items()
        self.app.profile = load_profile()
        self.app.activity = load_activity()
        touch()
        self.app.images.clear()
        self.app.refresh_user()
        self.folder_lbl.configure(text=S["data_dir"])

    def export(self):
        p = filedialog.asksaveasfilename(parent=self.app, defaultextension=".zip",
                                         initialfile=f"leitura_foda_backup_{date.today():%Y-%m-%d}.zip",
                                         filetypes=[("Backup", "*.zip")])
        if p:
            save_items(self.app.items)
            save_profile(self.app.profile)
            make_backup(p)
            self.app.toast("Backup salvo")

    def import_(self):
        p = filedialog.askopenfilename(parent=self.app, filetypes=[("Backup", "*.zip")])
        if not p:
            return
        try:
            with zipfile.ZipFile(p) as z:
                items = json.loads(z.read("data.json").decode("utf-8"))
                if not isinstance(items, list):
                    raise ValueError
                if not messagebox.askyesno("Importar backup", "Isso substitui a lista atual pela do backup. "
                                           "Uma cópia da lista atual será guardada antes. Continuar?",
                                           parent=self.app):
                    return
                save_items(self.app.items)
                save_profile(self.app.profile)
                (data_dir() / "backups").mkdir(exist_ok=True)
                make_backup(data_dir() / "backups" / f"antes_de_importar_{int(time.time())}.zip")
                for n in z.namelist():
                    if n.endswith("/"):
                        continue
                    if n.startswith("covers/"):
                        dst = covers_dir() / Path(n).name
                    elif n.startswith("profile/"):
                        dst = profile_dir() / Path(n).name
                    elif n.startswith("shots/"):
                        dst = shots_dir() / Path(n).name
                    elif n == "profile.json":
                        dst = profile_file()
                    elif n == "activity.json":
                        dst = activity_file()
                    else:
                        continue
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    dst.write_bytes(z.read(n))
                data_file().write_text(json.dumps(items, ensure_ascii=False, indent=2), encoding="utf-8")
        except (OSError, KeyError, ValueError, zipfile.BadZipFile):
            return messagebox.showerror("Erro", "Esse arquivo não parece um backup do Leitura Foda.",
                                        parent=self.app)
        self.app.items = load_items()
        self.app.profile = load_profile()
        self.app.activity = load_activity()
        touch()
        self.app.images.clear()
        self.app.refresh_user()
        self.app.toast("Backup importado")


# ---------- desenho em imagem única (rolagem sem rastros) ----------
K_IMG = 2          # as imagens são geradas com o dobro do tamanho (nítidas em qualquer escala)


def wrap_px(d, text, font, maxw, maxlines):
    words, lines, cur = str(text).split(), [], ""
    for w in words:
        t = (cur + " " + w).strip()
        if cur and d.textlength(t, font=font) > maxw:
            lines.append(cur)
            cur = w
        else:
            cur = t
    if cur:
        lines.append(cur)
    if len(lines) > maxlines:
        lines = lines[:maxlines]
        lines[-1] = lines[-1] + "…"
    return [_fit_text(d, l, font, maxw) for l in lines] or [""]


def _stars_on(img, x, y, rating, size, empty):
    for i in range(5):
        r = rating - i
        st = star_pil(size, 1 if r >= 1 else (.5 if r >= .5 else 0), empty)
        img.paste(st, (int(x + i * (size + size * .12)), int(y)), st)


def tile_height(tw):
    return int(tw * 1.4) + 10 + 36


def tile_pil(app, it, tw, chips, hot, bg):
    """Capa + título + moldura em UMA imagem só (um widget por obra, sem camadas para borrar na rolagem)."""
    k = K_IMG
    th = int(tw * 1.4)
    W, H = tw + 10, tile_height(tw)
    img = Image.new("RGBA", (W * k, H * k), bg)
    d = ImageDraw.Draw(img)
    cv = app.cover_pil(it, tw, th, chips)
    img.paste(cv, (5 * k, 5 * k), cv)
    font = get_font(12 * k)
    for n, line in enumerate(wrap_px(d, it["title"], font, (tw - 4) * k, 2)):
        d.text((6 * k, (5 + th + 4 + n * 16) * k), line, font=font, fill=P["text"])
    d.rounded_rectangle([0, 0, W * k - 1, H * k - 1], radius=10 * k, outline=hot, width=2 * k)
    return img


def card_title_pil(it, w, cbg, dry=False):
    k = K_IMG
    font = get_font(15 * k, True)
    tmp = ImageDraw.Draw(Image.new("RGB", (4, 4)))
    lines = wrap_px(tmp, it["title"], font, w * k, 3)
    H = max(30, len(lines) * 20 + 4)
    if dry:
        return None, H
    img = Image.new("RGB", (w * k, H * k), cbg)
    d = ImageDraw.Draw(img)
    for n, line in enumerate(lines):
        d.text((0, (2 + n * 20) * k), line, font=font, fill=P["text"])
    return img, H


def card_info_pil(app, it, w, cbg, col, dry=False):
    """Autor, situação, tags, etiquetas, barra de progresso e estrelas do cartão numa imagem só."""
    k = K_IMG
    f12, f11, f10 = get_font(12 * k), get_font(11 * k), get_font(10 * k, True)
    tmp = ImageDraw.Draw(Image.new("RGB", (4, 4)))
    rows, post = [], []                         # (altura, função de desenho); post = estrelas
    meta = [x for x in (it["author"], str(it["year"])) if x]
    if it["rereads"]:
        meta.append(f"relida {it['rereads']}x")
    if meta:
        txt = "  •  ".join(meta)
        rows.append((18, lambda d, y: d.text((0, y * k), _fit_text(d, txt, f12, w * k), font=f12, fill=P["muted"])))
    cap = cap_text(it)

    def status_line(d, y):
        sc = P["status"][it["status"]]
        d.ellipse([0, (y + 5) * k, 8 * k, (y + 13) * k], fill=sc)
        d.text((14 * k, y * k), STATUS[it["status"]], font=f12, fill=sc)
        tw_ = d.textlength(cap, font=f12)
        d.text((w * k - tw_, y * k), cap, font=f12, fill=P["muted"])
    rows.append((20, status_line))
    sd = stalled_days(it)
    if sd:
        rows.append((16, lambda d, y: d.text((0, y * k), f"parada há {sd} dias", font=f11, fill=P["status"]["pausado"])))
    if it["tags"]:
        t = " · ".join(it["tags"][:3])
        rows.append((16, lambda d, y: d.text((0, y * k), _fit_text(d, t, f11, w * k), font=f11, fill=P["muted"])))
    if it["labels"]:
        def labels(d, y):
            x = 0
            for n in it["labels"][:3]:
                lc = label_color(app, n)
                tw_ = d.textlength(n, font=f10)
                bw = tw_ + 14 * k
                if x + bw > w * k:
                    break
                d.rounded_rectangle([x, (y + 4) * k, x + bw, (y + 24) * k], radius=8 * k, fill=mix(lc, cbg, .72))
                d.text((x + 7 * k, (y + 14) * k), n, font=f10, fill=lc, anchor="lm")
                x += bw + 4 * k
        rows.append((28, labels))
    if it["total"]:
        def bar(d, y):
            d.rounded_rectangle([0, (y + 8) * k, w * k, (y + 13) * k], radius=3 * k, fill=P["surface2"])
            fw = int(w * k * min(1, it["seen"] / it["total"]))
            if fw > 0:
                d.rounded_rectangle([0, (y + 8) * k, max(fw, 6 * k), (y + 13) * k], radius=3 * k, fill=col)
        rows.append((18, bar))
    if it["rating"]:
        rows.append((28, lambda d, y: post.append((y + 8) * k)))
    H = sum(h for h, _ in rows) + 2
    if dry:
        return None, H
    img = Image.new("RGBA", (w * k, H * k), cbg)
    d = ImageDraw.Draw(img)
    y = 0
    for h, fn in rows:
        fn(d, y)
        y += h
    for sy in post:
        _stars_on(img, 0, sy, it["rating"], 18 * k, P["empty"])
    return img, H


def row_meta_pil(it, bg, compact):
    """Situação + capítulo + estrelas da linha da lista numa imagem só."""
    k = K_IMG
    f = get_font(13 * k)
    sw = 0 if compact else 96
    stw = 0 if (compact or not it["rating"]) else 5 * 18 + 10
    W, H = sw + 104 + stw, 32
    img = Image.new("RGBA", (W * k, H * k), bg)
    d = ImageDraw.Draw(img)
    if not compact:
        sc = P["status"][it["status"]]
        d.ellipse([0, 12 * k, 8 * k, 20 * k], fill=sc)
        d.text((14 * k, 16 * k), STATUS[it["status"]], font=f, fill=sc, anchor="lm")
    d.text((sw * k, 16 * k), _fit_text(d, cap_text(it), f, 98 * k), font=f, fill=P["muted"], anchor="lm")
    if stw:
        _stars_on(img, (sw + 104) * k, 7 * k, it["rating"], 16 * k, P["empty"])
    return img, W, H


def tile_chips(it, typechip=False):
    chips = [("bl", cap_text(it), "dark")]
    if typechip:
        chips.append(("tl", it["type"], type_color(it["type"])))
    if it["rating"]:
        chips.append(("br", f"{it['rating']:g}".replace(".", ","), "gold"))
    sd = stalled_days(it)
    if sd:
        chips.append(("tr" if typechip else "tl", f"parada {sd}d", "warn"))
    return tuple(chips)


def card_layout(it, w):
    """Altura e áreas clicáveis do cartão (sem desenhar nada): a grade precisa disso para posicionar tudo."""
    cover_w = w - 20
    cover_h = int(cover_w * COVER_RATIO)
    wrap = w - 28
    _, th_ = card_title_pil(it, wrap - 40, "#000000", dry=True)
    _, ih = card_info_pil(None, it, wrap, "#000000", "#000000", dry=True)
    y = 10 + cover_h + 8
    reg = {"heart": (w - 14 - 30, y, w - 14, y + 30)}
    y += th_ + ih
    has_url, lendo = bool(it["url"]), it["status"] == "lendo"
    if has_url or lendo:
        y += 10
        x1 = w - 14
        if has_url and lendo:
            reg["plus"] = (x1 - 44, y, x1, y + 28)
            reg["cont"] = (14, y, x1 - 44 - 6, y + 28)
        elif has_url:
            reg["cont"] = (14, y, x1, y + 28)
        else:
            reg["plus"] = (14, y, 14 + 44, y + 28)
        y += 28
    return {"h": y + 16, "reg": reg, "cover_w": cover_w, "cover_h": cover_h, "ty": 10 + cover_h + 8,
            "th": th_, "wrap": wrap}


def _btn(img, box, text, fill, fg, k, play=False):
    d = ImageDraw.Draw(img)
    x0, y0, x1, y1 = [v * k for v in box]
    d.rounded_rectangle([x0, y0, x1, y1], radius=8 * k, fill=fill)
    f = get_font(13 * k, True)
    cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
    if play:
        tw_ = d.textlength(text, font=f)
        tri = 9 * k
        sx = cx - (tw_ + tri + 6 * k) / 2
        d.polygon([(sx, cy - tri / 2), (sx, cy + tri / 2), (sx + tri * .85, cy)], fill=fg)
        d.text((sx + tri + 6 * k, cy), text, font=f, fill=fg, anchor="lm")
    else:
        d.text((cx, cy), text, font=f, fill=fg, anchor="mm")


_HEART_CACHE = {}


def _heart(img, box, on, hot, k):
    d = ImageDraw.Draw(img)
    x0, y0, x1, y1 = [v * k for v in box]
    base = mix(P["surface2"], PINK, .2) if on else P["surface2"]
    d.ellipse([x0, y0, x1, y1], fill=mix(P["surface2"], PINK, .38) if hot else base)
    ckey = (on, k, P["muted"])
    ic = _HEART_CACHE.get(ckey)
    if ic is None:
        ic = _HEART_CACHE[ckey] = icon_pil("heart_fill" if on else "heart", 16, PINK if on else P["muted"]).resize(
            (16 * k, 16 * k), Image.LANCZOS)
    img.paste(ic, (int((x0 + x1) / 2 - 8 * k), int((y0 + y1) / 2 - 8 * k)), ic)


def _action_btns(img, it, reg, hover, k):
    if "cont" in reg:
        _btn(img, reg["cont"], "Continuar", P["accent_hover"] if hover == "cont" else P["accent"], "#ffffff", k, play=True)
    if "plus" in reg:
        _btn(img, reg["plus"], "+1", mix(P["surface2"], P["accent"], .38) if hover == "plus" else P["surface2"],
             P["text"], k)


def card_compose(app, it, w, lay, hover):
    """Cartão da biblioteca inteiro (capa, texto, coração e botões) desenhado numa imagem só."""
    k = K_IMG
    H = lay["h"]
    col = app.item_color(it)
    cbg, edge = mix(col, P["surface"], .93), mix(col, P["border"], .8)
    img = Image.new("RGBA", (w * k, H * k), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    on = hover is not None
    d.rounded_rectangle([0, 0, w * k - 1, H * k - 1], radius=16 * k, fill=cbg,
                        outline=col if on else edge, width=(2 if on else 1) * k)
    cv = app.cover_pil(it, lay["cover_w"], lay["cover_h"], (("tl", it["type"], type_color(it["type"])),))
    img.paste(cv, (10 * k, 10 * k), cv)
    tpil, _ = card_title_pil(it, lay["wrap"] - 40, cbg)
    img.paste(tpil, (14 * k, lay["ty"] * k))
    ipil, _ = card_info_pil(app, it, lay["wrap"], cbg, col)
    img.paste(ipil, (14 * k, (lay["ty"] + lay["th"]) * k))
    _heart(img, lay["reg"]["heart"], bool(it["favorite"]), hover == "heart", k)
    _action_btns(img, it, lay["reg"], hover, k)
    return img


def row_layout(it, W, compact):
    H = 72
    right = W - 12
    reg = {"heart": (right - 30, (H - 30) / 2, right, (H + 30) / 2)}
    right -= 36
    if it["url"]:
        reg["cont"] = (right - 108, (H - 28) / 2, right, (H + 28) / 2)
        right -= 112
    if it["status"] == "lendo":
        reg["plus"] = (right - 44, (H - 28) / 2, right, (H + 28) / 2)
        right -= 48
    return {"h": H, "reg": reg, "right": right}


def row_compose(app, it, W, lay, compact, hover):
    k = K_IMG
    H = lay["h"]
    img = Image.new("RGBA", (W * k, H * k), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    on = hover is not None
    d.rounded_rectangle([0, 0, W * k - 1, H * k - 1], radius=12 * k, fill=P["surface"],
                        outline=P["accent"] if on else P["border"], width=(2 if on else 1) * k)
    cv = app.cover_pil(it, 40, 56)
    img.paste(cv, (10 * k, 8 * k), cv)
    mpil, mw, mh = row_meta_pil(it, P["surface"], compact)
    right = lay["right"]
    img.paste(mpil, ((right - mw) * k, int((H - mh) / 2 * k)))
    mid_w = max(40, right - mw - 12 - 60)
    d = ImageDraw.Draw(img)
    ft, fs_ = get_font(15 * k, True), get_font(12 * k)
    d.text((60 * k, 13 * k), _fit_text(d, it["title"], ft, mid_w * k), font=ft, fill=P["text"])
    parts = [it["type"]] + ([STATUS[it["status"]]] if compact else []) + [
        it["author"], ", ".join(it["tags"][:3])] + ([f"parada há {stalled_days(it)} dias"] if stalled_days(it) else [])
    d.ellipse([60 * k, 43 * k, 68 * k, 51 * k], fill=type_color(it["type"]))
    d.text((74 * k, 38 * k), _fit_text(d, "  •  ".join(x for x in parts if x), fs_, (mid_w - 14) * k),
           font=fs_, fill=P["muted"])
    _heart(img, lay["reg"]["heart"], bool(it["favorite"]), hover == "heart", k)
    _action_btns(img, it, lay["reg"], hover, k)
    return img


class VGrid:
    """Biblioteca desenhada direto no canvas: só as obras visíveis existem (rolagem sem rastros, 100 ou 1000 obras)."""
    GAP_BUF = 1.2

    def __init__(self, app, sf):
        self.app, self.sf, self.cv = app, sf, sf.canvas
        self.on, self.items, self.cells, self.rows = False, [], [], []
        self.live, self.refs, self.photos, self._lay = {}, {}, OrderedDict(), {}
        self.hov, self.view, self.compact = (None, None), "Grade", False
        self._job = self._rz = self._pv = None
        self.cv.bind("<Motion>", self._motion, add="+")
        self.cv.bind("<Leave>", self._leave, add="+")
        self.cv.bind("<Button-1>", self._click, add="+")

    # ---- ligar/desligar ----
    def show(self, items, view, compact, restore=None):
        self.clear_items()
        self.items, self.view, self.compact = items, view, compact
        self.photos.clear()
        self._lay = {}
        self.on = True
        self.sf.virtual = self
        try:
            self.cv.itemconfigure(self.sf._win, state="hidden")
        except tk.TclError:
            pass
        self.place()
        if restore is not None:
            try:
                self.cv.yview_moveto(restore)
            except tk.TclError:
                pass
        self.sync()

    def hide(self):
        self.clear_items()
        if self.on:
            self.on = False
            self.sf.virtual = None
            try:
                self.cv.itemconfigure(self.sf._win, state="normal")
                self.cv.configure(cursor="")
            except tk.TclError:
                pass
            self.sf.reflow()

    def clear_items(self):
        for i in list(self.live):
            try:
                self.cv.delete(self.live[i])
            except tk.TclError:
                pass
        self.live.clear()
        self.refs.clear()
        self.hov = (None, None)
        preview_hide()
        if self._job:
            try:
                self.app.after_cancel(self._job)
            except Exception:
                pass
            self._job = None

    # ---- posições ----
    def _size(self, i, avail):
        it = self.items[i]
        app = self.app
        if self.view == "Lista":
            W = int(avail) - 16
            lay = row_layout(it, W, self.compact)
            return W, lay["h"], lay
        if self.view == "Pôster":
            return app.card_w + 10, tile_height(app.card_w), {"reg": {}}
        key = (it["id"], app.card_w)
        if key not in self._lay:
            self._lay[key] = card_layout(it, app.card_w)
        lay = self._lay[key]
        return app.card_w, lay["h"], lay

    def place(self):
        k = scale_k()
        cw = self.cv.winfo_width()
        avail = max(200, lw(cw))
        lista = self.view == "Lista"
        cols = 1 if lista else max(1, self.app.cols)
        cell_w = avail / cols
        gap = 8 if lista else 16
        y = gap / 2
        self.cells, self.rows = [], []
        n = len(self.items)
        for r0 in range(0, n, cols):
            grp = list(range(r0, min(n, r0 + cols)))
            sizes = [self._size(i, avail) for i in grp]
            hmax = max(h for _, h, _ in sizes)
            for c, (w, h, lay) in enumerate(sizes):
                self.cells.append((c * cell_w + (cell_w - w) / 2, y, w, h, lay))
            self.rows.append((y, y + hmax, r0, grp[-1]))
            y += hmax + gap
        treal = int(y * k) + 1
        self.sf._region_h = treal
        self.cv.configure(scrollregion=(0, 0, max(1, cw), treal))

    def resized(self):
        if self._rz:
            try:
                self.app.after_cancel(self._rz)
            except Exception:
                pass
        self._rz = self.app.after(60, self._do_resize)

    def _do_resize(self):
        self._rz = None
        if not self.on:
            return
        try:
            frac = self.cv.yview()[0]
        except tk.TclError:
            frac = 0
        self.clear_items()
        self.place()
        try:
            self.cv.yview_moveto(frac)
        except tk.TclError:
            pass
        self.sync()

    # ---- desenhar só o que aparece ----
    def _photo(self, i, kind):
        it = self.items[i]
        x, y, w, h, lay = self.cells[i]
        key = (it["id"], self.view, w, kind)
        ph = self.photos.get(key)
        if ph is not None:
            self.photos.move_to_end(key)
            return ph
        app = self.app
        if self.view == "Lista":
            img = row_compose(app, it, w, lay, self.compact, kind)
        elif self.view == "Pôster":
            hot = app.item_color(it) if kind else P["bg"]
            img = tile_pil(app, it, app.card_w, tile_chips(it, True), hot, P["bg"])
        else:
            img = card_compose(app, it, w, lay, kind)
        k = scale_k()
        size = (max(1, int(round(w * k))), max(1, int(round(h * k))))
        if img.size != size:
            img = img.resize(size, Image.BICUBIC)
        ph = ImageTk.PhotoImage(img)
        self.photos[key] = ph
        while len(self.photos) > 90:
            self.photos.popitem(last=False)
        return ph

    def sync(self):
        if not self.on or not self.rows:
            return
        k = scale_k()
        try:
            top = self.cv.canvasy(0) / k
            H = self.cv.winfo_height() / k
        except tk.TclError:
            return
        lo, hi = top - H * self.GAP_BUF, top + H * (1 + self.GAP_BUF)
        need = []
        for y0, y1, a, b in self.rows:
            if y1 < lo:
                continue
            if y0 > hi:
                break
            need.extend(range(a, b + 1))
        want = set(need)
        for i in [i for i in self.live if i not in want]:
            try:
                self.cv.delete(self.live.pop(i))
            except tk.TclError:
                pass
            self.refs.pop(i, None)
        mid = top + H / 2
        need.sort(key=lambda i: abs(self.cells[i][1] + self.cells[i][3] / 2 - mid))
        budget, later = 6, False
        for i in need:
            if i in self.live:
                continue
            if budget <= 0:
                later = True
                break
            ph = self._photo(i, None)
            x, y = self.cells[i][0], self.cells[i][1]
            self.live[i] = self.cv.create_image(int(x * k), int(y * k), image=ph, anchor="nw")
            self.refs[i] = ph
            budget -= 1
        if later and self._job is None:
            self._job = self.app.after(6, self._more)

    def _more(self):
        self._job = None
        self.sync()

    # ---- mouse ----
    def _hit(self, e):
        k = scale_k()
        x, y = self.cv.canvasx(e.x) / k, self.cv.canvasy(e.y) / k
        for i in self.live:
            cx, cy, w, h, lay = self.cells[i]
            if cx <= x < cx + w and cy <= y < cy + h:
                rx, ry = x - cx, y - cy
                for name, (a, b, c, d) in lay.get("reg", {}).items():
                    if a <= rx < c and b <= ry < d:
                        return i, name
                return i, "card"
        return None, None

    def _set(self, i, kind):
        if i in self.live:
            ph = self._photo(i, kind)
            self.refs[i] = ph
            self.cv.itemconfigure(self.live[i], image=ph)

    def _hover(self, i, kind):
        old = self.hov
        if (i, kind) == old:
            return
        self.hov = (i, kind)
        if old[0] is not None and old[0] != i:
            self._set(old[0], None)
        if i is not None:
            self._set(i, kind)
        try:
            self.cv.configure(cursor="hand2" if i is not None else "")
        except tk.TclError:
            pass
        if i != old[0]:
            preview_hide()
            if i is not None and S.get("preview", True) and preview_has_content(self.items[i]):
                PV["root"] = self.app
                it = self.items[i]
                PV["job"] = self.app.after(650, lambda: preview_show(self.app, it))

    def _motion(self, e):
        if self.on and not scrolling():
            self._hover(*self._hit(e))

    def _leave(self, e):
        if self.on:
            self._hover(None, None)

    def _click(self, e):
        if not self.on:
            return
        i, kind = self._hit(e)
        if i is None:
            return
        preview_hide()
        it, app = self.items[i], self.app
        if kind == "heart":
            app.toggle_fav(it)
        elif kind == "cont":
            open_url(it["url"])
        elif kind == "plus":
            app.plus_one(it)
        else:
            app.open_detail(it)


class NoFab:
    """O antigo botão flutuante saiu: 'Nova leitura' agora fica no menu lateral."""

    def show(self): pass
    def hide(self): pass
    def reposition(self): pass



# ---------- mini janela ----------
class MiniWindow(tk.Toplevel):
    """Janelinha flutuante: capa, cronômetro e +1, tudo desenhado numa imagem só."""
    W, H = 344, 136
    KEY = "#010203"

    def __init__(self, app, it=None):
        super().__init__(app)
        self.app = app
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        self.transp = True
        try:
            self.attributes("-transparentcolor", self.KEY)
        except tk.TclError:
            self.transp = False
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        pw, ph = px(self.W), px(self.H)
        pos = S.get("mini_pos")
        x, y = (pos if pos and 0 <= pos[0] < sw - 60 and 0 <= pos[1] < sh - 60 else (sw - pw - 40, sh - ph - 90))
        self.geometry(f"{pw}x{ph}+{x}+{y}")
        bg = self.KEY if self.transp else P["bg"]
        self.configure(bg=bg)
        self.cv = tk.Canvas(self, width=pw, height=ph, bg=bg, highlightthickness=0, bd=0)
        self.cv.pack()
        self.item = self.cv.create_image(0, 0, anchor="nw")
        self.hov, self.flash, self._press, self._drag, self._ph = None, 0, None, None, None
        self.cv.bind("<Motion>", self._motion)
        self.cv.bind("<Leave>", lambda e: self._set_hov(None))
        self.cv.bind("<ButtonPress-1>", self._down)
        self.cv.bind("<B1-Motion>", self._move)
        self.cv.bind("<ButtonRelease-1>", self._up)
        self.idx, self.list = 0, []
        self.pick(prefer=(it or {}).get("id") or (app.timer or {}).get("id"), extra=it)
        self.tick()

    # ---- dados ----
    def pick(self, prefer=None, extra=None):
        its = [i for i in self.app.items if i["status"] == "lendo"]
        its.sort(key=lambda i: -i["updated"])
        if extra is not None and all(i["id"] != extra["id"] for i in its):
            its.insert(0, extra)
        self.list = its
        self.idx = next((n for n, i in enumerate(its) if i["id"] == prefer), min(self.idx, max(0, len(its) - 1)))
        self.redraw()

    def set_item(self, it):
        self.pick(prefer=it["id"], extra=it)

    def cur(self):
        return self.list[self.idx] if self.list else None

    def cycle(self, d):
        if self.list:
            self.idx = (self.idx + d) % len(self.list)
            self.redraw()

    # ---- desenho ----
    def _regions(self):
        W = self.W
        return [(W - 100, 8, W - 76, 32, "prev"), (W - 74, 8, W - 50, 32, "next"), (W - 48, 8, W - 26, 32, "big"),
                (W - 24, 8, W - 4, 32, "close"), (96, 34, W - 14, 58, "title"),
                (192, 88, 236, 128, "play"), (242, 90, W - 14, 126, "plus")]

    def _frame(self):
        app, it, W, H = self.app, self.cur(), self.W, self.H
        img = Image.new("RGBA", (W * K, H * K), (0, 0, 0, 0))
        col = app.item_color(it) if it else P["accent"]
        m = Image.new("L", img.size, 0)
        ImageDraw.Draw(m).rounded_rectangle([0, 0, W * K - 1, H * K - 1], radius=20 * K, fill=255)
        base = Image.new("RGBA", img.size, P["surface"])
        tint = Image.new("RGBA", img.size, (0, 0, 0, 0))
        td = ImageDraw.Draw(tint)
        for x in range(0, W * K, 2):
            a = int(70 * max(0, 1 - x / (W * K * .85)) ** 1.5)
            td.line([(x, 0), (x, H * K)], fill=hex_rgba(col, a), width=2)
        base.alpha_composite(tint)
        img.paste(base, (0, 0), m)
        d = ImageDraw.Draw(img)
        d.rounded_rectangle([0, 0, W * K - 1, H * K - 1], radius=20 * K, outline=mix(col, P["surface"], .55), width=K)
        if not it:
            T(d, W / 2, H / 2 - 8, "Nenhuma leitura em andamento", 14, P["muted"], True, "mm")
            T(d, W / 2, H / 2 + 14, "Coloque uma obra em “Lendo”", 12, P["muted"], False, "mm")
        else:
            cov = app.cover_pil(it, 64, 92)
            sh = Image.new("RGBA", img.size, (0, 0, 0, 0))
            ImageDraw.Draw(sh).rounded_rectangle([14 * K, 26 * K, 78 * K, 124 * K], radius=12 * K, fill=(0, 0, 0, 110))
            img.alpha_composite(sh.filter(ImageFilter.GaussianBlur(5 * K)))
            img.paste(cov, (14 * K, 22 * K), cov)
            d = ImageDraw.Draw(img)
            ttl = it["title"]
            while TW(d, ttl, 15, True) > W - 96 - 14 and len(ttl) > 4:
                ttl = ttl[:-2]
            if ttl != it["title"]:
                ttl = ttl.rstrip() + "…"
            T(d, 96, 20, "LENDO AGORA" if it["status"] == "lendo" else STATUS[it["status"]].upper(), 10,
              mix(col, "#ffffff", .35), True, "lm")
            T(d, 96, 36, ttl, 15, P["text"] if self.hov != "title" else mix(col, "#ffffff", .5), True)
            total = it["total"] or 0
            T(d, 96, 62, f"cap. {it['seen']}" + (f"/{total}" if total else ""), 12, P["muted"], False, "lm")
            if total:
                T(d, W - 14, 62, f"{int(min(1, it['seen'] / total) * 100)}%", 12, P["muted"], False, "rm")
            d.rounded_rectangle([96 * K, 72 * K, (W - 14) * K, 77 * K], radius=3 * K, fill=P["surface2"])
            if total and it["seen"]:
                fw = (W - 14 - 96) * min(1, it["seen"] / total)
                d.rounded_rectangle([96 * K, 72 * K, (96 + max(fw, 6)) * K, 77 * K], radius=3 * K, fill=col)
            t_ = app.timer
            run = bool(t_ and t_["id"] == it["id"])
            e = int(time.time() - t_["start"]) if run else 0
            T(d, 96, 108, f"{e // 3600:02d}:{e % 3600 // 60:02d}:{e % 60:02d}", 19, P["text"] if run else P["muted"],
              True, "lm")
            on = self.hov == "play"
            d.ellipse([198 * K, 90 * K, 232 * K, 124 * K], fill=col if run or on else P["surface2"])
            if run:
                d.rounded_rectangle([208 * K, 100 * K, 222 * K, 114 * K], radius=3 * K, fill="#ffffff")
            else:
                d.polygon([(210 * K, 100 * K), (210 * K, 114 * K), (223 * K, 107 * K)], fill="#ffffff" if on else P["text"])
            on = self.hov == "plus"
            ok = self.flash > time.time()
            d.rounded_rectangle([242 * K, 92 * K, (W - 14) * K, 122 * K], radius=15 * K,
                                fill="#2fbf71" if ok else (P["accent_hover"] if on else P["accent"]))
            cx_ = (242 + W - 14) / 2
            if ok:                      # o ✓ não existe na fonte do canvas: desenha o visto com linhas
                tw_ = TW(d, "feito", 14, True)
                x0_ = cx_ - (14 + 7 + tw_) / 2
                d.line([((x0_ + 1) * K, 107 * K), ((x0_ + 5) * K, 111 * K), ((x0_ + 13) * K, 102 * K)],
                       fill="#ffffff", width=int(2.2 * K), joint="curve")
                T(d, x0_ + 21, 107, "feito", 14, "#ffffff", True, "lm")
            else:
                T(d, cx_, 107, "+1 cap", 14, "#ffffff", True, "mm")
        for name, x0, ch in (("prev", W - 100, "‹"), ("next", W - 74, "›"), ("big", W - 48, "⤢"), ("close", W - 24, "✕")):
            if self.hov == name:
                d.ellipse([(x0 - 1) * K, 8 * K, (x0 + 23) * K, 32 * K], fill=P["surface2"])
            fg = P["text"] if self.hov == name else P["muted"]
            cx, cy, wl = x0 + 11, 20, int(1.8 * K)
            if name == "big":      # dois cantos opostos, como "expandir"
                d.line([((cx + 1) * K, (cy - 5) * K), ((cx + 5) * K, (cy - 5) * K), ((cx + 5) * K, (cy - 1) * K)], fill=fg, width=wl)
                d.line([((cx - 1) * K, (cy + 5) * K), ((cx - 5) * K, (cy + 5) * K), ((cx - 5) * K, (cy + 1) * K)], fill=fg, width=wl)
                d.line([((cx + 5) * K, (cy - 5) * K), ((cx + 1) * K, (cy - 1) * K)], fill=fg, width=wl)
                d.line([((cx - 5) * K, (cy + 5) * K), ((cx - 1) * K, (cy + 1) * K)], fill=fg, width=wl)
            elif name == "close":
                d.line([((cx - 4) * K, (cy - 4) * K), ((cx + 4) * K, (cy + 4) * K)], fill=fg, width=wl)
                d.line([((cx - 4) * K, (cy + 4) * K), ((cx + 4) * K, (cy - 4) * K)], fill=fg, width=wl)
            else:
                sg = -1 if name == "prev" else 1
                d.line([((cx - 2 * sg) * K, (cy - 5) * K), ((cx + 2 * sg) * K, cy * K), ((cx - 2 * sg) * K, (cy + 5) * K)],
                       fill=fg, width=wl, joint="curve")
        if self.transp:
            bg = Image.new("RGBA", img.size, self.KEY)
            bg.alpha_composite(img)
            img = bg
        return img.convert("RGB").resize((px(W), px(H)), Image.LANCZOS)

    def redraw(self):
        try:
            self._ph = ImageTk.PhotoImage(self._frame())
            self.cv.itemconfigure(self.item, image=self._ph)
        except tk.TclError:
            pass

    def tick(self):
        try:
            if not self.winfo_exists():
                return
        except Exception:
            return
        if self._drag is None:
            self.redraw()
        self.after(500, self.tick)

    # ---- mouse ----
    def _region(self, e):
        k = scale_k()
        x, y = e.x / k, e.y / k
        for x0, y0, x1, y1, n in self._regions():
            if x0 <= x < x1 and y0 <= y < y1:
                if n in ("play", "plus", "title") and not self.cur():
                    continue
                return n
        return None

    def _set_hov(self, n):
        if n != self.hov:
            self.hov = n
            try:
                self.cv.configure(cursor="hand2" if n else "")
            except tk.TclError:
                pass
            self.redraw()

    def _motion(self, e):
        if self._drag is None:
            self._set_hov(self._region(e))

    def _down(self, e):
        self._press = self._region(e)
        self._drag = None
        if self._press is None:
            self._drag = (e.x_root - self.winfo_x(), e.y_root - self.winfo_y())

    def _move(self, e):
        if self._drag:
            self.geometry(f"+{e.x_root - self._drag[0]}+{e.y_root - self._drag[1]}")

    def _up(self, e):
        if self._drag:
            S["mini_pos"] = [self.winfo_x(), self.winfo_y()]
            save_settings()
            self._drag = None
            return
        n = self._press
        self._press = None
        if n and n == self._region(e):
            self.act(n)

    def act(self, n):
        it, app = self.cur(), self.app
        if n == "close":
            self.close()
        elif n == "big":
            self.expand()
        elif n == "prev":
            self.cycle(-1)
        elif n == "next":
            self.cycle(1)
        elif n == "title":
            self.choose()
        elif n == "play" and it:
            t = app.timer
            if t and t["id"] == it["id"]:
                app.stop_timer()
            else:
                app.start_timer(it)
            self.redraw()
            app.sync_detail(it)
        elif n == "plus" and it:
            if app.add_progress(it, 1) is not False:
                self.flash = time.time() + .8
                self.redraw()
                self.after(850, self.redraw)
                app.sync_detail(it)

    def choose(self):
        m = tk.Menu(self, tearoff=0, bg=P["surface"], fg=P["text"], activebackground=P["surface2"],
                    activeforeground=P["text"], bd=0, relief="flat", font=("TkDefaultFont", fpt(11)))
        for n, i in enumerate(self.list):
            t = i["title"] if len(i["title"]) < 38 else i["title"][:36] + "…"
            m.add_command(label=("✓  " if n == self.idx else "      ") + t, command=lambda i=i: self.set_item(i))
        try:
            m.tk_popup(self.winfo_rootx() + 96, self.winfo_rooty() + px(58))
        finally:
            m.grab_release()

    def expand(self):
        it = self.cur()
        self.close(save=False)          # o cronômetro continua rodando na página da obra
        self.app.deiconify()
        self.app.lift()
        if it:
            self.app.open_detail(it)

    def close(self, save=True):
        """Fecha a mini janela; se o cronômetro estiver rodando, para e salva o tempo lido."""
        app = self.app
        app.mini = None
        saved = None
        if save and app.timer:
            tid = app.timer["id"]
            mins = app.stop_timer()
            saved = next((i for i in app.items if i["id"] == tid), None)
            if mins:
                app.toast(f"Tempo salvo: {mins} min")
        try:
            self.destroy()
        except tk.TclError:
            pass
        if saved is not None:
            app.sync_detail(saved)


# ---------- app ----------
NAV = [("home", "Início", "home"), ("profile", "Perfil", "user"), ("library", "Biblioteca", "library"), ("lists", "Listas", "list"), ("collection", "Coleção", "gem"), ("gallery", "Galeria", "image"),
       ("stats", "Estatísticas", "chart"), ("settings", "Configurações", "gear")]


class App(ctk.CTk):
    def __init__(self):
        super().__init__(fg_color=P["bg"])
        self.title("Leitura Foda")
        self._t0 = time.time()
        self._init_window()
        self.withdraw()
        splash = show_splash(self) if S.get("splash", True) else None
        splash_step(splash, 0.2)
        self.items = load_items()
        self.profile = load_profile()
        self.activity = load_activity()
        splash_step(splash, 0.4)
        self.timer = None
        self.images = {}
        self._pilc = OrderedDict()            # capas prontas (limitado, as mais antigas saem)
        self.cache = {}                       # nome da tela -> (tela pronta, versão dos dados)
        self._lib_ver, self._lib_dirty, self._user_ver = -1, True, -1
        self.page, self.cur, self.back = None, "home", None
        self.stack, self.sub = [], None
        self.lib_shown, self._side_state = False, None
        self.cols, self.card_w = 0, MIN_CARD
        self._after, self._pos = None, 0
        self._render_id, self._soon, self._toast = 0, None, None
        self.v_type = tk.StringVar(value="Todos os tipos")
        self.v_tag, self.v_sort = tk.StringVar(value="Todos os gêneros"), tk.StringVar(value=SORTS[0])
        self.v_tab, self.v_view = tk.StringVar(value="Todos"), tk.StringVar(value=S["view"])
        self.v_fav = tk.BooleanVar(value=False)
        self.v_list, self.v_stall = tk.StringVar(value="Todas as listas"), tk.BooleanVar(value=False)
        self.v_label = tk.StringVar(value="Todas as etiquetas")
        self.bind("<Configure>", self._on_resize)
        self.bind("<Escape>", lambda e: self.go_back() if self.back else None)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        for k in ("n", "N"):
            self.bind(f"<Control-{k}>", lambda e: self.open_new())
        for k in ("f", "F"):
            self.bind(f"<Control-{k}>", lambda e: self.focus_search())
        for k in ("m", "M"):
            self.bind(f"<Control-{k}>", lambda e: self.open_mini_side())
        self.mini = None
        self.bind("<Control-v>", self._ctrl_v, add="+")
        self.bind("<Control-V>", self._ctrl_v, add="+")
        for i, (key, _l, _i) in enumerate(NAV, 1):
            self.bind(f"<Control-Key-{i}>", lambda e, k=key: self.nav(k))
        self.after(300, self._set_icon)
        self._bind_wheel()
        splash_step(splash, 0.55)
        self.build()
        splash_step(splash, 0.8)
        self.nav("home")
        self.after(1500, lambda: self.check_badges(True))
        splash_step(splash, 1.0)
        self._finish_splash(splash)

    # --- estrutura geral ---
    def build(self):
        for w in self.winfo_children():
            w.destroy()
        self.page, self.lib_shown, self._side_state = None, False, None
        self.cache, self._lib_dirty = {}, True
        self.configure(fg_color=P["side"])
        self.build_side()
        self.main = ctk.CTkFrame(self, fg_color=P["bg"], corner_radius=0)
        self.main.pack(side="left", fill="both", expand=True, padx=(px(SIDE_OPEN), 0))
        self.side.lift()
        self.build_lib()
        self.fab = NoFab()
        self.after(30, self.apply_sidebar)

    def rebuild(self):
        self.build()

    # --- menu lateral ---
    def build_side(self):
        self.side = ctk.CTkFrame(self, fg_color=P["side"], corner_radius=0, width=SIDE_OPEN)
        self.side.place(x=0, y=0, relheight=1)      # flutua sobre a página: animar a largura não refaz o conteúdo
        self.side.pack_propagate(False)
        brand = ctk.CTkFrame(self.side, fg_color="transparent")
        brand.pack(fill="x", padx=18, pady=(24, 18))
        ctk.CTkFrame(brand, width=3, height=24, fg_color=P["accent"], corner_radius=0).pack(side="left", padx=(0, 10))
        self.brand_logo = ctk.CTkLabel(brand, text="", image=self._brand_logo(), width=30, height=30)
        self.brand_lbl = ctk.CTkLabel(brand, text="LEITURA FODA", text_color=P["text"],
                                      font=ctk.CTkFont(size=15, weight="bold"))
        self.brand_lbl.pack(side="left")
        self.add_btn = ctk.CTkButton(self.side, text="+  Nova leitura", height=42, corner_radius=21,
                                     fg_color=P["accent"], hover_color=P["accent_hover"], text_color="white",
                                     font=ctk.CTkFont(size=14, weight="bold"), command=self.open_new)
        self.add_btn.pack(fill="x", padx=14, pady=(0, 14))
        Tip(self.add_btn, lambda: "Nova leitura  (Ctrl+N)" if self._side_state else "")
        self.nav_btns = {}
        for key, label, ic in NAV:
            row = ctk.CTkFrame(self.side, fg_color="transparent")
            row.pack(fill="x", padx=8, pady=2)
            if key == NAV[0][0]:
                self.nav_first = row
            mark = ctk.CTkFrame(row, width=3, height=24, fg_color="transparent", corner_radius=0)
            mark.pack(side="left", padx=(0, 4))
            btn = ctk.CTkButton(row, text=label, image=icon(ic, 20), compound="left", anchor="w", height=42,
                                corner_radius=10, fg_color="transparent", hover_color=P["surface2"],
                                text_color=P["muted"], font=ctk.CTkFont(size=15),
                                command=lambda k=key: self.nav(k))
            btn.pack(side="left", fill="x", expand=True)
            self.nav_btns[key] = (mark, btn, label, ic)
            Tip(btn, lambda l=label: l if self._side_state else "")

        ub = ctk.CTkFrame(self.side, fg_color="transparent")
        ub.pack(side="bottom", fill="x", padx=12, pady=(4, 16))
        self.u_av = ctk.CTkLabel(ub, text="", cursor="hand2")
        self.u_av.pack(side="left")
        self.u_txt = ctk.CTkFrame(ub, fg_color="transparent")
        self.u_name = ctk.CTkLabel(self.u_txt, text="", text_color=P["text"], anchor="w",
                                   font=ctk.CTkFont(size=14, weight="bold"))
        self.u_name.pack(anchor="w")
        self.u_handle = ctk.CTkLabel(self.u_txt, text="", text_color=P["muted"], anchor="w",
                                     font=ctk.CTkFont(size=12))
        self.u_handle.pack(anchor="w")
        for w in (ub, self.u_av, self.u_txt, self.u_name, self.u_handle):
            w.bind("<Button-1>", lambda e: self.nav("profile"))
        self.collapse_btn = ctk.CTkButton(self.side, text="Recolher menu", image=icon("collapse", 20),
                                          compound="left", anchor="w", height=40, corner_radius=10,
                                          fg_color="transparent", hover_color=P["surface2"],
                                          text_color=P["muted"], font=ctk.CTkFont(size=14),
                                          command=self.toggle_side)
        self.collapse_btn.pack(side="bottom", fill="x", padx=12, pady=(0, 8))
        self.mini_btn = ctk.CTkButton(self.side, text="Mini janela", image=icon("clock", 20), compound="left",
                                      anchor="w", height=40, corner_radius=10, fg_color="transparent",
                                      hover_color=P["surface2"], text_color=P["muted"], font=ctk.CTkFont(size=14),
                                      command=self.open_mini_side)
        self.mini_btn.pack(side="bottom", fill="x", padx=12, pady=(0, 2))
        Tip(self.mini_btn, lambda: "Mini janela  (Ctrl+M)" if self._side_state else "")
        Tip(self.collapse_btn, lambda: "Expandir menu" if self._side_state else "")
        self._user_ver = -1                       # menu novo (ex.: troca de tema): preenche nome e foto de novo
        self.refresh_user()

    def refresh_user(self):
        if not hasattr(self, "u_av") or not self.u_av.winfo_exists():
            return
        if self._user_ver == DATA["v"]:
            return                                # nada mudou desde a última vez
        self._user_ver = DATA["v"]
        pr = self.profile
        av = profile_dir() / pr["avatar"] if pr.get("avatar") else None
        lv = level_info(xp_breakdown(self)[1])
        self.u_av.configure(image=avatar_img(av, pr["name"], 40, P["side"], lv["color"]))
        self.u_name.configure(text=pr["name"])
        self.u_handle.configure(text=f"Nível {lv['level']}  ·  {pr['handle']}")

    def want_collapsed(self):
        w = lw(self.winfo_width())
        return bool(S.get("collapsed")) or 120 < w < 900

    def _brand_logo(self):
        got = getattr(self, "_logo_img", None)
        if got is None:
            try:
                lg = Image.open(resource_path("icone.ico")).convert("RGBA").resize((64, 64), Image.LANCZOS)
                got = ctk.CTkImage(lg, size=(30, 30))
            except Exception:
                got = icon("book", 24, P["accent"])
            self._logo_img = got
        return got

    def _side_content(self, c):
        """Troca textos/ícones do menu entre aberto e recolhido (a largura é animada à parte)."""
        if c:
            self.brand_lbl.pack_forget()
            self.brand_logo.pack(side="left", padx=(2, 0))
        else:
            self.brand_logo.pack_forget()
            self.brand_lbl.pack(side="left")
        self.add_btn.configure(text="" if c else "+  Nova leitura", image=icon("plus", 20, "#ffffff") if c else None,
                               width=42 if c else 140, font=ctk.CTkFont(size=14, weight="bold"))
        if c:
            self.add_btn.pack(fill="none", padx=0, pady=(0, 14), before=self.nav_first)
        else:
            self.add_btn.pack(fill="x", padx=14, pady=(0, 14), before=self.nav_first)
        for mark, btn, label, ic in self.nav_btns.values():
            btn.configure(text="" if c else label, anchor="center" if c else "w")
        self.mini_btn.configure(text="" if c else "Mini janela", anchor="center" if c else "w")
        self.collapse_btn.configure(text="" if c else "Recolher menu", image=icon("expand" if c else "collapse", 20),
                                    anchor="center" if c else "w")
        if c:
            self.u_txt.pack_forget()
        else:
            self.u_txt.pack(side="left", padx=10)

    def _main_pad(self, w):
        try:
            tk.Frame.pack_configure(self.main, padx=(px(w), 0))
        except Exception:
            pass

    def apply_sidebar(self):
        c = self.want_collapsed()
        if c == self._side_state:
            return
        first = self._side_state is None
        self._side_state = c
        target = SIDE_CLOSED if c else SIDE_OPEN
        job = getattr(self, "_side_job", None)
        if job:
            try:
                self.after_cancel(job)
            except Exception:
                pass
            self._side_job = None
        start = getattr(self, "_side_w", None)
        if first or start is None or not S.get("anim", True) or abs(start - target) < 2:
            self._side_w = target
            self.side.configure(width=target)
            self._main_pad(target)
            self._side_content(c)
            return
        self._main_pad(SIDE_OPEN if c else SIDE_CLOSED)     # a página só se ajusta uma vez, no fim
        if c:
            self._side_content(True)               # recolhendo: some o texto já, a barra encolhe depois
        t0 = time.time()
        dur = 0.2

        def step():
            t = min(1.0, (time.time() - t0) / dur)
            e = t * t * (3 - 2 * t)                # suaviza começo e fim
            w = start + (target - start) * e
            self._side_w = w
            self.side.configure(width=int(round(w)))
            if not c and t >= .45 and self.add_btn.cget("text") == "":
                self._side_content(False)          # expandindo: o texto volta quando já há espaço
            if t < 1:
                self._side_job = self.after(15, step)
            else:
                self._side_job = None
                self._side_w = target
                if self._side_state == c:
                    self._side_content(c)
                    self._main_pad(target)
        step()

    def open_mini_side(self):
        """Botão do menu: se você está na página de uma obra, a mini janela abre nela (igual ao botão da página)."""
        pg = self.page
        self.open_mini(getattr(pg, "it", None) if isinstance(pg, DetailPage) else None)

    # ---- prints (galeria) ----
    def _shots_target(self, it=None):
        if it is not None:
            return it
        pg = self.page
        if isinstance(pg, DetailPage):
            return pg.it
        if isinstance(pg, GalleryPage) and pg.obra is not None:
            return pg.obra
        return None

    def pick_item(self, cb):
        its = sorted(self.items, key=lambda i: (i["status"] != "lendo", -(i.get("updated") or 0)))[:30]
        if not its:
            return self.toast("Adicione uma leitura primeiro.", "warn")
        m = tk.Menu(self, tearoff=0, bg=P["surface"], fg=P["text"], activebackground=P["surface2"],
                    activeforeground=P["text"], bd=0, relief="flat", font=("TkDefaultFont", fpt(11)))
        m.add_command(label="Em qual obra?", state="disabled")
        for i in its:
            t = i["title"] if len(i["title"]) < 42 else i["title"][:40] + "…"
            m.add_command(label=t, command=lambda i=i: cb(i))
        try:
            m.tk_popup(self.winfo_pointerx(), self.winfo_pointery())
        finally:
            m.grab_release()

    def add_shot_files(self, it=None):
        it = self._shots_target(it)
        if it is None:
            return self.pick_item(self.add_shot_files)
        paths = filedialog.askopenfilenames(parent=self, title=f"Prints de {it['title']}",
                                            filetypes=[("Imagens", "*.png *.jpg *.jpeg *.webp *.bmp *.gif"),
                                                       ("Todos os arquivos", "*.*")])
        n = 0
        for p_ in paths:
            try:
                im = Image.open(p_)
                im.load()
                add_shot(self, it, im)
                n += 1
            except (OSError, ValueError):
                pass
        if paths and not n:
            self.toast("Não consegui abrir essa imagem.", "err")
        self._shots_done(it, n)

    def paste_shots(self, it=None, quiet=False):
        imgs = clipboard_images()
        if not imgs:
            if not quiet:
                self.toast("Não há imagem na área de transferência.", "warn")
            return False
        it = self._shots_target(it)
        if it is None:
            self.pick_item(lambda i: self._add_imgs(i, imgs))
            return True
        self._add_imgs(it, imgs)
        return True

    def _add_imgs(self, it, imgs):
        n = 0
        for im in imgs:
            try:
                add_shot(self, it, im)
                n += 1
            except (OSError, ValueError):
                pass
        self._shots_done(it, n)

    def _shots_done(self, it, n):
        if not n:
            return
        self.toast(f"{n} print{'s' if n > 1 else ''} salvo{'s' if n > 1 else ''} em “{it['title']}”")
        pg = self.page
        try:
            if isinstance(pg, DetailPage) and pg.it is it:
                pg._fill_shots()
            elif isinstance(pg, GalleryPage):
                pg.view.rebuild()
        except Exception:
            pass

    def _ctrl_v(self, e):
        if isinstance(self.page, (DetailPage, GalleryPage)):
            self.paste_shots(quiet=True)

    def sync_detail(self, it):
        """A mini janela mexeu numa obra: atualiza no lugar a página dela, se estiver aberta."""
        pg = self.page
        if isinstance(pg, DetailPage) and pg.it is not None and pg.it["id"] == it["id"]:
            try:
                pg._sync_top(())
                pg.sync_timer()
            except Exception:
                pass

    def bump(self, key):
        """Conta um uso (mini janela, compartilhar...) no perfil, para as conquistas."""
        u = self.profile.setdefault("usage", {})
        u[key] = u.get(key, 0) + 1
        save_profile(self.profile)
        touch()

    def open_mini(self, it=None):
        """Abre a mini janela (na obra pedida, se for o caso); se já estiver aberta, só troca a obra."""
        self.bump("mini")
        if getattr(self, "mini", None):
            try:
                if it is not None:
                    self.mini.set_item(it)
                self.mini.lift()
                return
            except Exception:
                self.mini = None
        if it is None and not any(i["status"] == "lendo" for i in self.items):
            return self.toast("Coloque uma leitura em “Lendo” para usar a mini janela.", "warn")
        self.mini = MiniWindow(self, it)
        self.iconify()

    def toggle_side(self):
        S["collapsed"] = not S.get("collapsed", False)
        save_settings()
        self.apply_sidebar()

    def update_sidebar(self):
        pill = mix(P["accent"], P["side"], .84)
        for key, (mark, btn, label, ic) in self.nav_btns.items():
            on = key == self.cur
            mark.configure(fg_color=P["accent"] if on else "transparent")
            btn.configure(fg_color=pill if on else "transparent", hover_color=pill if on else P["surface2"],
                          text_color=P["text"] if on else P["muted"],
                          image=icon(ic, 20, P["accent"] if on else P["muted"]),
                          font=ctk.CTkFont(size=15, weight="bold" if on else "normal"))

    # --- navegação (tudo na mesma janela) ---
    def _active_canvas(self):
        return self.scroll._parent_canvas

    def _leave(self):
        self._render_id += 1                      # cancela cartões ainda sendo montados
        preview_hide()
        if self.page is not None:
            if any(self.page is p for p, _v in self.cache.values()):
                self.page.pack_forget()           # tela guardada: só esconde (volta na hora)
            else:
                self.page.destroy()
            self.page = None
        elif self.lib_shown:
            try:
                self._pos = self._active_canvas().yview()[0]
            except Exception:
                self._pos = 0
            self.lib.pack_forget()
            self.lib_shown = False

    def nav(self, name):
        self._leave()
        self.cur, self.back = name, None
        self.stack, self.sub = [], None
        self.update_sidebar()                     # o item do menu muda no mesmo instante do clique
        if name == "library":
            self.show_library()
        else:
            self.show_cached(name)
        self.refresh_user()
        self.fab_toggle()

    def show_library(self):
        self.lib.pack(fill="both", expand=True)
        self.lib_shown = True
        self.update_idletasks()
        self.layout()
        if self._lib_dirty or self._lib_ver != DATA["v"] or self.grid_params() != (self.cols, self.card_w):
            self.refresh(restore=self._pos)       # só redesenha se algo mudou

    def show_cached(self, name):
        """Perfil, Listas, Estatísticas e Configurações ficam prontos na memória: voltar a elas é instantâneo."""
        cls = {"home": HomePage, "profile": ProfilePage, "lists": ListsPage, "collection": CollectionPage, "gallery": GalleryPage, "stats": StatsPage, "settings": SettingsPage}[name]
        ent = self.cache.get(name)
        if ent is not None and ent[1] == DATA["v"] and ent[0].winfo_exists():
            self.page = ent[0]
            self.page.pack(fill="both", expand=True)
            if name == "home":
                self.page.reshuffle()
            return
        veil = self._veil_show()
        if ent is not None:
            try:
                ent[0].destroy()
            except Exception:
                pass
        self.page = cls(self)
        self.cache[name] = (self.page, DATA["v"])
        self.page.pack(fill="both", expand=True)
        self._veil_hide(veil)

    def _veil_show(self):
        """Tela de carregamento roxa: aparece no mesmo instante do clique, antes da tela nova ser montada."""
        if not S.get("anim", True):
            return None
        try:
            v = tk.Frame(self.main, bg=P["bg"], bd=0, highlightthickness=0)
            v.place(x=0, y=0, relwidth=1, relheight=1)
            v.lift()
            bar = tk.Frame(v, bg=P["accent"], height=px(3))
            bar.place(x=0, y=0, relwidth=0.18)
            size = px(64)
            cv = tk.Canvas(v, width=size + px(10), height=size + px(10), bg=P["bg"], highlightthickness=0, bd=0)
            cv.place(relx=0.5, rely=0.46, anchor="center")
            m = px(5)
            cv.create_oval(m, m, size + m, size + m, outline=P["surface2"], width=px(5))
            cv.create_arc(m, m, size + m, size + m, start=70, extent=110, style="arc", outline=P["accent"],
                          width=px(5))
            tk.Label(v, text="Carregando…", bg=P["bg"], fg=P["muted"], font=("TkDefaultFont", fpt(11))).place(
                relx=0.5, rely=0.46, y=size // 2 + px(30), anchor="center")
            v._bar, v._t0 = bar, time.time()
            self.update_idletasks()               # desenha agora, antes de começar a montar a tela
            return v
        except Exception:
            return None

    def _veil_hide(self, v):
        if v is None:
            return
        try:
            v.lift()
            if time.time() - v._t0 < 0.09:        # montou rápido: nem precisa de animação
                v.destroy()
                return
            bar = v._bar

            def step(k=1):
                try:
                    if not v.winfo_exists():
                        return
                    if k <= 3:
                        bar.place_configure(relwidth=0.18 + 0.82 * k / 3)
                    elif k <= 7:
                        f = (k - 3) / 4
                        v.place_configure(rely=f, relheight=1 - f)
                    else:
                        v.destroy()
                        return
                    v.after(14, lambda: step(k + 1))
                except tk.TclError:
                    pass

            step()
        except Exception:
            try:
                v.destroy()
            except Exception:
                pass

    def open_sub(self, cls, *args):
        if self.back is None:
            self.back, self.stack = self.cur, []
        elif self.sub is not None:
            self.stack.append(self.sub)
        self.sub = (cls, args)
        self._leave()
        self._show_sub(cls, args)
        self.fab_toggle()

    def _show_sub(self, cls, args):
        veil = self._veil_show()
        self.page = cls(self, *args)
        self.page.pack(fill="both", expand=True)
        self._veil_hide(veil)

    def go_back(self):
        if self.stack:
            self.sub = self.stack.pop()
            self._leave()
            self._show_sub(self.sub[0], self.sub[1])
            self.fab_toggle()
        else:
            self.go_home()

    def go_home(self):
        self.nav(self.back or "home")

    def fab_toggle(self):
        if self.cur in ("library", "profile") and self.back is None:
            self.fab.show()
        else:
            self.fab.hide()

    def _reveal(self, widget):
        """Transição suave: uma cortina da cor do fundo que sobe, revelando a tela nova."""
        if not S.get("anim", True):
            return
        try:
            cover = tk.Frame(widget, bg=P["bg"], bd=0, highlightthickness=0)
            cover.place(x=0, y=0, relwidth=1, relheight=1)
            cover.lift()

            def step(k=1):
                try:
                    if not cover.winfo_exists():
                        return
                    if k >= 6:
                        cover.destroy()
                        return
                    f = k / 6
                    cover.place_configure(rely=f, relheight=1 - f)
                    cover.after(16, lambda: step(k + 1))
                except tk.TclError:
                    pass

            cover.after(8, step)
        except Exception:
            pass

    def open_new(self):
        self.open_sub(EditPage)

    def open_edit(self, it):
        self.open_sub(EditPage, it)

    def on_close(self):
        try:
            if self.mini:
                self.mini.destroy()
        except Exception:
            pass
        self._save_window()
        try:
            if self.timer:
                self.stop_timer()
            if self.items:
                save_items(self.items)
                save_activity(self.activity)
                d = data_dir() / "backups"
                d.mkdir(exist_ok=True)
                make_backup(d / f"auto_{date.today():%Y-%m-%d}.zip")
                for old in sorted(d.glob("auto_*.zip"))[:-7]:
                    old.unlink()
        except OSError:
            pass
        self.destroy()

    def _set_icon(self):
        try:
            p = resource_path("icone.ico")
            if p.exists():
                self.iconbitmap(str(p))
        except Exception:
            pass

    def focus_search(self):
        self.nav("library")
        self.after(80, lambda: self.search_entry.focus_set())

    def open_detail(self, it):
        self.open_sub(DetailPage, it)

    def share_image(self):
        p = filedialog.asksaveasfilename(parent=self, defaultextension=".png",
                                         initialfile="meu_perfil_leitura_foda.png",
                                         filetypes=[("Imagem PNG", "*.png")])
        if not p:
            return
        try:
            make_share_image(self, p)
        except Exception as e:
            return messagebox.showerror("Erro", f"Não consegui gerar a imagem:\n{e}", parent=self)
        self.bump("share")
        self.toast("Imagem salva! Agora é só compartilhar.")

    def add_progress(self, it, n=1):
        """+1 capítulo. Em obras 'em lançamento' o total acompanha (saiu capítulo novo) e nunca fecha sozinha;
        nas demais, ao chegar no último capítulo a leitura vira Completo."""
        ongoing = bool(it.get("ongoing"))
        if it["total"] and it["seen"] >= it["total"] and not ongoing:
            self.toast("Já está no último capítulo. Ative “Em lançamento” se saem capítulos novos.", "warn")
            return False
        today = date.today().strftime("%d/%m/%Y")
        it["seen"] += n
        if ongoing and it["total"] and it["seen"] > it["total"]:
            it["total"] = it["seen"]
        it["updated"] = it["progressed"] = time.time()
        if it["status"] in ("planejo", "pausado", "largado") or (it["status"] == "completo" and ongoing):
            ev = status_event(it["status"], "lendo")
            it["status"] = "lendo"
            it["started"] = it["started"] or today
            if ev:
                add_event(it, ev)
        if it["total"] and it["seen"] >= it["total"] and not ongoing:
            it["seen"], it["status"] = it["total"], "completo"
            it["finished"] = it["finished"] or today
            add_event(it, "done")
        log_activity(self.activity, ch=n)
        save_activity(self.activity)
        self.commit(it["id"])
        return True

    def start_timer(self, it):
        if self.timer:
            self.stop_timer()
        self.timer = {"id": it["id"], "start": time.time()}

    def stop_timer(self):
        t, self.timer = self.timer, None
        if not t:
            return 0
        secs = time.time() - t["start"]
        mins = round(secs / 60) if secs >= 30 else 0
        mins = max(mins, 1) if secs >= 30 else 0
        it = next((i for i in self.items if i["id"] == t["id"]), None)
        if it and mins:
            it["minutes"] = it.get("minutes", 0) + mins
            it["updated"] = it["progressed"] = time.time()
            log_activity(self.activity, minutes=mins)
            save_activity(self.activity)
            self.commit(it["id"])
        return mins

    # --- janela, rolagem e avisos ---
    def _init_window(self):
        """Ajusta a janela ao monitor: escala do Windows, tamanho da interface e posição."""
        UI["dpi"] = detect_dpi(self)
        ws = UI_SCALES.get(S.get("ui_scale", "Automático"))
        UI["ws"] = ws if ws else auto_ws(self, UI["dpi"])
        try:
            ctk.set_widget_scaling(UI["ws"])
        except Exception:
            UI["ws"] = 1.0
        sw, sh, dpi = self.winfo_screenwidth(), self.winfo_screenheight(), UI["dpi"]
        win = S.get("win") or {}
        maxw, maxh = int(sw * 0.96 / dpi), int(sh * 0.90 / dpi)
        w = max(min(420, maxw), min(int(win.get("w", 1280)), maxw))
        h = max(min(520, maxh), min(int(win.get("h", 820)), maxh))
        self.minsize(min(420, maxw), min(520, maxh))
        self.geometry(f"{w}x{h}")
        x, y = win.get("x"), win.get("y")
        pw, ph = int(w * dpi), int(h * dpi)
        if not (isinstance(x, int) and isinstance(y, int) and -pw // 2 < x < sw - 120 and 0 <= y < sh - 120):
            x, y = max(0, (sw - pw) // 2), max(0, (sh - ph) // 2 - 20)
        try:
            tk.Wm.geometry(self, f"+{x}+{y}")
        except Exception:
            pass
        self._want_max = bool(win.get("zoomed") or S.get("start_max"))

    def _finish_splash(self, sp):
        """Mostra a janela principal (depois de, no mínimo, ~1 s de tela de abertura)."""
        def show():
            try:
                if sp is not None:
                    sp.destroy()
            except Exception:
                pass
            try:
                self.deiconify()
                self.lift()
                if self._want_max:
                    self._maximize()
            except Exception:
                pass

        if sp is None:
            show()
            return
        wait = max(120, int(1300 - (time.time() - self._t0) * 1000))
        self.after(wait, lambda: self._fade_splash(sp, show))

    def _fade_splash(self, sp, done, k=0):
        try:
            if k >= 6:
                done()
                return
            sp.attributes("-alpha", 1 - k / 6)
            self.after(25, lambda: self._fade_splash(sp, done, k + 1))
        except Exception:
            done()

    def _maximize(self):
        try:
            self.state("zoomed")
        except Exception:
            try:
                self.attributes("-zoomed", True)
            except Exception:
                pass

    def _save_window(self):
        try:
            zoomed = self.state() == "zoomed"
            win = dict(S.get("win") or {})
            if not zoomed:
                win.update(w=int(self.winfo_width() / UI["dpi"]), h=int(self.winfo_height() / UI["dpi"]),
                           x=int(self.winfo_x()), y=int(self.winfo_y()))
            win["zoomed"] = zoomed
            S["win"] = win
            save_settings()
        except Exception:
            pass

    def _bind_wheel(self):
        self.bind_all("<MouseWheel>", self._on_wheel, add="+")
        self.bind_all("<Button-4>", lambda e: self._on_wheel(e, 1), add="+")
        self.bind_all("<Button-5>", lambda e: self._on_wheel(e, -1), add="+")

    def _on_wheel(self, e, step=None):
        """Rola a área sob o mouse (a mais interna). Shift + roda rola as prateleiras para o lado."""
        preview_hide()
        try:
            w = self.winfo_containing(e.x_root, e.y_root)
        except (KeyError, tk.TclError):
            return
        v_owner = h_owner = None
        while w is not None:
            if isinstance(w, tk.Text):       # caixas de texto rolam sozinhas
                return
            if v_owner is None:
                v_owner = getattr(w, "_scroll_owner", None)
            if h_owner is None:
                h_owner = getattr(w, "_hscroll_owner", None)
            w = getattr(w, "master", None)
        state = getattr(e, "state", 0)
        shift = bool(state & 0x1) if isinstance(state, int) else False
        if h_owner is not None and (shift or v_owner is None):
            h_owner.wheel(e, step)
        elif v_owner is not None:
            v_owner.wheel(e, step)

    def refresh_soon(self, ms=220):
        if self._soon:
            try:
                self.after_cancel(self._soon)
            except Exception:
                pass
        self._soon = self.after(ms, self.refresh)

    def toast(self, msg, kind="ok", ms=2600):
        """Aviso discreto no rodapé (some sozinho), no lugar de janelinhas de 'OK'."""
        col = {"ok": P["accent"], "err": DANGER, "warn": P["status"]["pausado"]}.get(kind, P["accent"])
        self._drop_toast()
        t = ctk.CTkLabel(self.main, text=f"   {msg}   ", fg_color=col, text_color="white", corner_radius=12,
                         height=40, font=ctk.CTkFont(size=13, weight="bold"))
        t.place(relx=0.5, rely=1.0, y=-26, anchor="s")
        t.lift()
        self._toast = t
        self.after(ms, lambda t=t: self._drop_toast(t))

    def _drop_toast(self, which=None):
        t = self._toast
        if t is None or (which is not None and which is not t):
            return
        self._toast = None
        try:
            t.destroy()
        except Exception:
            pass

    # --- biblioteca ---
    def build_lib(self):
        self.lib = ctk.CTkFrame(self.main, fg_color="transparent")
        self.head = ctk.CTkFrame(self.lib, fg_color="transparent")
        self.head.pack(fill="x", padx=28, pady=(24, 4))
        self.head.grid_columnconfigure(1, weight=1)
        self.h_title = section(self.head, "Biblioteca", 28)
        self.h_stats = ctk.CTkLabel(self.head, text="", text_color=P["muted"])

        self.tool = ctk.CTkFrame(self.lib, fg_color="transparent")
        self.tool.pack(fill="x", padx=28, pady=(8, 4))
        self.tool1 = ctk.CTkFrame(self.tool, fg_color="transparent")       # linha 1: busca + tipo
        self.tool1.pack(fill="x")
        self.tool2 = ctk.CTkFrame(self.tool, fg_color="transparent")       # linha 2: filtros e ordem
        self.tool2.pack(fill="x", pady=(4, 0))
        sbox = ctk.CTkFrame(self.tool1, fg_color=P["surface"], corner_radius=10, border_width=1,
                            border_color=P["border"], width=300, height=40)
        sbox.pack_propagate(False)                   # tamanho fixo: nada de dentro vaza pela borda arredondada
        ctk.CTkLabel(sbox, text="", image=icon("search", 16), width=28).pack(side="left", padx=(8, 0))
        self.search_entry = ctk.CTkEntry(sbox, placeholder_text="Buscar por nome...", fg_color="transparent",
                                         border_width=0, height=34, width=240, text_color=P["text"])
        self.search_entry.pack(side="left", fill="x", expand=True, padx=(0, 10), pady=2)
        self.search_entry.bind("<KeyRelease>", lambda e: self.refresh_soon(), add="+")
        tmenu = self.build_type_filter(self.tool1)
        self.tag_menu = menu(self.tool2, ["Todos os gêneros"], lambda _: self.refresh(), 170,
                             variable=self.v_tag, height=38)
        self.list_menu = menu(self.tool2, ["Todas as listas"], lambda _: self.refresh(), 170,
                              variable=self.v_list, height=38)
        self.label_menu = menu(self.tool2, ["Todas as etiquetas"], lambda _: self.refresh(), 180,
                               variable=self.v_label, height=38)
        smenu = menu(self.tool2, SORTS, lambda _: self.refresh(), 190, variable=self.v_sort, height=38)
        fav = toggle_chip(self.tool2, " Favoritos", self.v_fav, self.refresh, ic="heart", width=120)
        stall = toggle_chip(self.tool2, " Paradas", self.v_stall, self.refresh, ic="clock", width=120)
        self.tool_rows = [[sbox, tmenu], [self.tag_menu, self.list_menu, self.label_menu, smenu, fav, stall]]

        self.row2 = ctk.CTkFrame(self.lib, fg_color="transparent")
        self.row2.pack(fill="x", padx=28, pady=(2, 10))
        self.row2.grid_columnconfigure(0, weight=1)
        labels = ["Todos"] + list(STATUS.values())
        self.tab_seg = segmented(self.row2, labels, self.set_tab)
        self.tab_menu = menu(self.row2, labels, self.set_tab, 150, height=34)
        self.view_seg = segmented(self.row2, VIEWS, self.set_view)
        self.tab_seg.set(self.v_tab.get())
        self.tab_menu.set(self.v_tab.get())
        self.view_seg.set(self.v_view.get())
        self.view_seg.grid(row=0, column=1, sticky="e", padx=(8, 0))

        self.scroll = new_scroll(self.lib)
        self.scroll.pack(fill="both", expand=True, padx=18, pady=(0, 0))
        self.vg = VGrid(self, self.scroll) if isinstance(self.scroll, ScrollFrame) else None
        self.images.clear()
        self._pilc.clear()

    def layout(self):
        """Reorganiza o cabeçalho, os filtros e as abas conforme a largura disponível."""
        if not self.lib_shown:
            return
        wp = self.main.winfo_width()
        w = lw(wp)
        if w < 200:
            w, wp = 1000, px(1000)
        self.h_title.grid_forget()
        self.h_stats.grid_forget()
        self.h_title.grid(row=0, column=0, sticky="w")
        if w >= 700:
            self.h_stats.grid(row=0, column=1, sticky="e")
        else:
            self.h_stats.grid(row=1, column=0, columnspan=2, sticky="w")
        self.update_idletasks()
        for row_ in self.tool_rows:
            reflow(row_, wp - px(60), 10)
        if w >= 900:
            self.tab_menu.grid_forget()
            self.tab_seg.grid(row=0, column=0, sticky="w")
        else:
            self.tab_seg.grid_forget()
            self.tab_menu.grid(row=0, column=0, sticky="w")

    def build_type_filter(self, parent):
        """Filtro por tipo com uma bolinha da cor de cada tipo (clicar de novo limpa)."""
        f = ctk.CTkFrame(parent, fg_color=P["surface"], corner_radius=10, border_width=1, border_color=P["border"])
        self.type_btns = {}
        for t in ["Todos"] + TYPES:
            col = P["accent"] if t == "Todos" else type_color(t)
            b = ctk.CTkButton(f, text=t, width=max(54, 16 + 8 * len(t)), height=30, corner_radius=8,
                              image=icon("dot", 12, col), compound="left", fg_color="transparent",
                              hover_color=P["surface2"], text_color=P["muted"], font=ctk.CTkFont(size=12),
                              command=lambda t=t: self.set_type(t))
            b.pack(side="left", padx=3, pady=3)
            self.type_btns[t] = b
        self.paint_types()
        return f

    def set_type(self, t):
        self.v_type.set("Todos os tipos" if (t == "Todos" or self.v_type.get() == t) else t)
        self.paint_types()
        self.refresh()

    def paint_types(self):
        cur = self.v_type.get()
        for t, b in self.type_btns.items():
            on = (cur == "Todos os tipos" and t == "Todos") or cur == t
            col = P["accent"] if t == "Todos" else type_color(t)
            b.configure(fg_color=mix(col, P["surface"], .62) if on else "transparent",
                        text_color=P["text"] if on else P["muted"])

    def set_tab(self, v):
        self.v_tab.set(v)
        self.tab_seg.set(v)
        self.tab_menu.set(v)
        self.refresh()

    def set_view(self, v):
        self.v_view.set(v)
        S["view"] = v
        save_settings()
        self.refresh()

    # --- estado ---
    def check_badges(self, quiet=False):
        """Descobre conquistas novas, guarda a data e mostra o aviso (as que já eram suas entram sem festa)."""
        self._cb_job = None
        try:
            st = badge_status(self)
        except Exception:
            return
        pr = self.profile
        known = set(pr.get("badge_known", []))
        dates = pr.setdefault("badge_dates", {})
        new, changed = [], False
        for b in st:
            if b["id"] not in known:
                known.add(b["id"])
                changed = True
                if b["earned"] and b["id"] not in dates:
                    dates[b["id"]] = ""
            elif b["earned"] and b["id"] not in dates:
                dates[b["id"]] = date.today().isoformat()
                changed = True
                new.append(b)
        ck = pr.get("cards_known")
        done_now = [i for i in self.items if i["status"] == "completo"]
        if ck is None:
            pr["cards_known"] = [i["id"] for i in done_now]
            changed = True
        else:
            fresh = [i for i in done_now if i["id"] not in set(ck)]
            if fresh:
                pr["cards_known"] = sorted(set(ck) | {i["id"] for i in fresh}, key=str)
                changed = True
                if not quiet:
                    self._card_q = getattr(self, "_card_q", []) + fresh
                    if getattr(self, "_card_w", None) is None:
                        self._card_next()
        if changed:
            pr["badge_known"] = sorted(known)
            save_profile(pr)
        if new and not quiet:
            self._badge_q = getattr(self, "_badge_q", []) + new
            if getattr(self, "_badge_w", None) is None:
                self._badge_next()

    def _card_next(self):
        q = getattr(self, "_card_q", [])
        if not q:
            self._card_w = None
            return
        it = q.pop(0)
        rar = card_rarity(it)
        nums = card_numbers(self.items)
        front = card_pil(self, it, nums[it["id"]], len(self.items), 0)
        CWd, CHd = 180, 250
        back = card_back(CWd, CHd)
        f = ctk.CTkFrame(self, fg_color=P["surface"], corner_radius=16, border_width=2, border_color=CARD_RAR[rar][0])
        ctk.CTkLabel(f, text="NOVA CARTA", text_color=CARD_RAR[rar][0], font=ctk.CTkFont(size=11, weight="bold")).pack(
            pady=(10, 0))
        lab = ctk.CTkLabel(f, text="", width=CWd + 20, height=CHd + 6)
        lab.pack(padx=12, pady=(4, 12))
        self._card_w = f

        def frame(sc, img):
            w = max(2, int(CWd * sc))
            lab.configure(image=ctk.CTkImage(img.resize((w * 2, CHd * 2), Image.LANCZOS), size=(w, CHd)))

        def flip(n=0):
            try:
                if not f.winfo_exists():
                    return
            except Exception:
                return
            steps = 7
            if n <= steps:
                frame(abs(1 - n / steps) if False else 1 - n / steps, back)
            elif n <= 2 * steps:
                frame((n - steps) / steps, front)
            if n < 2 * steps:
                self.after(34, lambda: flip(n + 1))
            else:
                self.after(4200, leave)

        def leave(n=0):
            try:
                if not f.winfo_exists():
                    return
                if n >= 8:
                    f.destroy()
                    self._card_w = None
                    return self.after(200, self._card_next)
                f.place(relx=1.0, x=-20 + int(380 * (n / 8) ** 2), y=140, anchor="ne")
                self.after(16, lambda: leave(n + 1))
            except Exception:
                self._card_w = None

        f.place(relx=1.0, x=-20, y=140, anchor="ne")
        f.lift()
        frame(1, back)
        self.after(350, flip)

    def _badge_next(self):
        q = getattr(self, "_badge_q", [])
        if not q:
            self._badge_w = None
            return
        b = q.pop(0)
        play_sound("badge")
        rar = badge_rarity(b)
        f = ctk.CTkFrame(self, fg_color=P["surface"], corner_radius=16, border_width=2,
                         border_color=TIER_COLOR[b["tier"]])
        ctk.CTkLabel(f, text="", image=badge_img(b["icon"], b["tier"], True, 64)).pack(side="left", padx=(14, 6), pady=12)
        t = ctk.CTkFrame(f, fg_color="transparent")
        t.pack(side="left", padx=(4, 18), pady=12)
        ctk.CTkLabel(t, text="CONQUISTA DESBLOQUEADA", text_color=P["accent"], anchor="w",
                     font=ctk.CTkFont(size=10, weight="bold")).pack(anchor="w")
        ctk.CTkLabel(t, text=b["title"], text_color=P["text"], anchor="w",
                     font=ctk.CTkFont(size=17, weight="bold")).pack(anchor="w")
        ctk.CTkLabel(t, text=f"{rar}  •  {b['desc']}", text_color=RARITY[rar], anchor="w", wraplength=300,
                     justify="left", font=ctk.CTkFont(size=12)).pack(anchor="w")
        ctk.CTkLabel(t, text=f"Novo título: {b['ptitle']}", text_color=P["muted"], anchor="w",
                     font=ctk.CTkFont(size=12)).pack(anchor="w")
        self._badge_w = f
        steps = 10

        def slide(n=0):
            try:
                if not f.winfo_exists():
                    return
                x = int(380 * (1 - n / steps) ** 2)
                f.place(relx=1.0, x=-20 + x, y=22, anchor="ne")
                f.lift()
                if n < steps:
                    self.after(16, lambda: slide(n + 1))
                else:
                    self.after(4800, leave)
            except Exception:
                pass

        def leave(n=0):
            try:
                if not f.winfo_exists():
                    return
                f.place(relx=1.0, x=-20 + int(380 * (n / steps) ** 2), y=22, anchor="ne")
                if n < steps:
                    self.after(16, lambda: leave(n + 1))
                else:
                    f.destroy()
                    self._badge_w = None
                    self._badge_next()
            except Exception:
                self._badge_w = None
        slide()

    def commit(self, item_id):
        save_items(self.items)
        if getattr(self, "_cb_job", None) is None:
            self._cb_job = self.after(500, self.check_badges)
        for k in [k for k in self.images if k[0] == item_id]:
            del self.images[k]
        for k in [k for k in self._pilc if k[0] == item_id]:
            del self._pilc[k]
        if self.cur == "library" and self.page is None:    # atualiza já, mantendo a rolagem
            try:
                pos = self.scroll._parent_canvas.yview()[0]
            except Exception:
                pos = 0
            self.refresh(restore=pos)

    def _restore(self, pos):
        try:
            self.scroll._parent_canvas.yview_moveto(pos)
        except Exception:
            pass

    def grid_params(self):
        try:
            cwid = self.scroll.canvas.winfo_width()      # a largura real da área (o frame interno fica velho quando a grade é virtual)
        except Exception:
            cwid = self.scroll.winfo_width()
        avail = max(200, int(lw(cwid)) - 12)
        view = self.v_view.get()
        if view == "Lista":
            return 1, avail
        if view == "Prateleiras":
            return 1, 150
        lo, hi = (MIN_POSTER, MAX_POSTER) if view == "Pôster" else (MIN_CARD, MAX_CARD)
        cols = max(1, avail // (lo + 16))
        cw = min(hi, avail // cols - 16)
        return cols, max(150, cw // 2 * 2)       # quase sem arredondar: as capas ocupam a linha toda

    def _on_resize(self, e):
        if e.widget is self:
            if getattr(self, "fab", None) is not None:
                self.fab.reposition()
            if self._after:
                self.after_cancel(self._after)
            self._after = self.after(120, self._relayout)

    def _relayout(self, again=True):
        self.apply_sidebar()
        if self.cur == "library" and self.page is None and self.lib_shown:
            self.update_idletasks()                 # ao maximizar/restaurar a janela a largura ainda estava velha
            self.layout()
            if self.grid_params() != (self.cols, self.card_w):
                self.refresh()
            if again:                               # confere de novo quando o Windows termina de redimensionar
                self.after(260, lambda: self._relayout(False))

    def filtered(self):
        q = self.search_entry.get().strip().lower()
        tab, tf, tg = self.v_tab.get(), self.v_type.get(), self.v_tag.get()
        out = [i for i in self.items
               if q in i["title"].lower()
               and (tab == "Todos" or STATUS[i["status"]] == tab)
               and (tf == "Todos os tipos" or i["type"] == tf)
               and (tg == "Todos os gêneros" or tg in i["tags"])
               and (not self.v_fav.get() or i["favorite"])
               and (self.v_list.get() == "Todas as listas" or self.v_list.get() in i["lists"])
               and (self.v_label.get() == "Todas as etiquetas" or self.v_label.get() in i["labels"])
               and (not self.v_stall.get() or stalled_days(i))]
        keys = {"Nome (A–Z)": lambda i: i["title"].lower(),
                "Maior nota": lambda i: -i["rating"],
                "Mais capítulos lidos": lambda i: -i["seen"],
                "Última atualização": lambda i: -i["updated"],
                "Data de início": lambda i: -(parse_date(i["started"]) or date.min).toordinal()}
        out.sort(key=keys.get(self.v_sort.get(), lambda i: -i["created"]))
        out.sort(key=lambda i: not i["favorite"])   # favoritos no topo
        return out

    def _load_cover(self, it):
        path = covers_dir() / (it.get("cover") or "")
        try:
            return Image.open(path).convert("RGB") if it.get("cover") and path.exists() else placeholder(it["title"])
        except OSError:
            return placeholder(it["title"])

    def item_color(self, it):
        """Cor dominante da capa (guardada junto das imagens; some quando a obra é editada)."""
        key = (it["id"], "dom")
        if key not in self.images:
            self.images[key] = dominant_color(self._load_cover(it))
        return self.images[key]

    def hero_image(self, it, w):
        key = (it["id"], "hero", w)
        if key not in self.images:
            k = ss()
            img = hero_pil(self._load_cover(it), int(w * k), int(HERO_H * k), self.item_color(it), P["bg"])
            self.images[key] = ctk.CTkImage(img, size=(w, HERO_H))
        return self.images[key]

    def cover_pil(self, it, w, h, chips=()):
        """Capa já recortada e com etiquetas (guardada: não refaz o trabalho a cada tela)."""
        key = (it["id"], "pil", w, h, chips)
        got = self._pilc.get(key)
        if got is None:
            img = self._load_cover(it)
            if (it["id"], "dom") not in self.images:
                self.images[(it["id"], "dom")] = dominant_color(img)
            img = ImageOps.fit(img.convert("RGB"), (w * K_IMG, h * K_IMG))
            if chips:
                img = overlay_chips(img, chips)
            got = self._pilc[key] = rounded(img, min(w, h) * 0.16 * K_IMG)
            while len(self._pilc) > 160:
                self._pilc.popitem(last=False)
        else:
            self._pilc.move_to_end(key)
        return got

    def cover(self, it, w, h, chips=()):
        key = (it["id"], w, h, chips)
        if key not in self.images:
            self.images[key] = ctk.CTkImage(self.cover_pil(it, w, h, chips), size=(w, h))
        return self.images[key]

    def refresh(self, restore=None):
        if not (self.cur == "library" and self.page is None and self.lib_shown and self.scroll.winfo_exists()):
            self._lib_dirty = True                # está escondida: refaz quando for aberta
            return
        self._soon = None
        shelf_x = {}
        for t, sh in getattr(self, "_shelves", []):
            try:
                shelf_x[t] = sh.canvas.xview()[0]
            except Exception:
                pass
        self._shelves = []
        if self.vg is not None:
            self.vg.hide()
        for w in self.scroll.winfo_children():
            w.destroy()
        tags = sorted({t for i in self.items for t in i["tags"]}, key=str.lower)
        self.tag_menu.configure(values=["Todos os gêneros"] + tags)
        if self.v_tag.get() not in tags:
            self.v_tag.set("Todos os gêneros")
        lists = sorted({n for i in self.items for n in i["lists"]}, key=str.lower)
        self.list_menu.configure(values=["Todas as listas"] + lists)
        if self.v_list.get() not in lists:
            self.v_list.set("Todas as listas")
        labs = sorted({n for i in self.items for n in i["labels"]}, key=str.lower)
        self.label_menu.configure(values=["Todas as etiquetas"] + labs)
        if self.v_label.get() not in labs:
            self.v_label.set("Todas as etiquetas")
        rated = [i["rating"] for i in self.items if i["rating"]]
        done = sum(1 for i in self.items if i["status"] == "completo")
        avg = f"{sum(rated) / len(rated):.1f}".replace(".", ",") if rated else "–"
        self.h_stats.configure(text=f"{len(self.items)} leituras  •  {done} completas  •  nota média {avg}")

        self.update_idletasks()
        old_w = self.card_w
        self.cols, self.card_w = self.grid_params()
        if old_w != self.card_w:               # só as imagens redimensionadas saem; as cores das capas ficam
            for key in [k for k in self.images if not (len(k) == 2 and k[1] == "dom")]:
                del self.images[key]
            self._pilc.clear()
        for c in range(40):
            self.scroll.grid_columnconfigure(c, weight=0)
        shown = self.filtered()
        self._render_id += 1
        self._lib_ver, self._lib_dirty = DATA["v"], False
        if not shown:
            if self.items:
                f = empty_state(self.scroll, "book", "Nada encontrado", "Tente limpar a busca ou os filtros.")
            else:
                f = empty_state(self.scroll, "library", "Sua biblioteca está vazia",
                                "Adicione sua primeira leitura para começar.",
                                lambda p: accent_button(p, "+  Adicionar leitura", self.open_new))
            f.grid(row=0, column=0, pady=70, padx=20)
            self.scroll.grid_columnconfigure(0, weight=1)
            return
        view = self.v_view.get()
        if view == "Prateleiras":
            self.scroll.grid_columnconfigure(0, weight=1)
            self.render_shelves(shown)
            self.update_idletasks()
            for t, sh in self._shelves:
                if t in shelf_x:
                    sh.canvas.xview_moveto(shelf_x[t])
            if restore is not None:
                self._restore(restore)
            return
        lista = view == "Lista"
        for c in range(1 if lista else self.cols):
            self.scroll.grid_columnconfigure(c, weight=1)   # a sobra de espaço divide entre as colunas
        compact = lista and lw(self.scroll.winfo_width()) < 640
        if self.vg is not None:
            self.vg.show(shown, view, compact, restore)
            return
        self._render_chunk(self._render_id, shown, 0, view, compact, restore)

    def shelves_for(self, shown):
        by_prog = sorted([i for i in shown if i["status"] == "lendo"], key=lambda i: -i["progressed"])
        done = sorted([i for i in shown if i["status"] == "completo"], key=lambda i: -i["updated"])
        return [("Continuar lendo", by_prog),
                ("Em lançamento", [i for i in shown if i.get("ongoing")]),
                ("Retomar leitura", [i for i in shown if stalled_days(i)]),
                ("Mais bem avaliadas", sorted([i for i in shown if i["rating"]], key=lambda i: -i["rating"])),
                ("Favoritas", [i for i in shown if i["favorite"]]),
                ("Quero ler", [i for i in shown if i["status"] == "planejo"]),
                ("Completas recentemente", done)]

    def render_shelves(self, shown):
        """Faixas horizontais (estilo Netflix): cada uma rola para o lado."""
        tw = 150
        rows = [(t, l[:30]) for t, l in self.shelves_for(shown) if l]
        if not rows:
            empty_state(self.scroll, "library", "Nenhuma prateleira ainda",
                        "Leituras em andamento, favoritas e bem avaliadas aparecem aqui.").grid(
                row=0, column=0, pady=60)
            return
        for r, (title, its) in enumerate(rows):
            head = ctk.CTkFrame(self.scroll, fg_color="transparent")
            head.grid(row=2 * r, column=0, sticky="ew", padx=8, pady=(14, 4))
            section(head, title, 16).pack(side="left")
            ctk.CTkLabel(head, text=str(len(its)), text_color=P["muted"]).pack(side="left", padx=10)
            shelf = HShelf(self.scroll, tile_height(tw) + 8)
            self._shelves.append((title, shelf))
            ghost_button(head, "", lambda sh=shelf: sh.scroll_by(px(420)), image=icon("forward", 14), width=34,
                         height=30).pack(side="right")
            ghost_button(head, "", lambda sh=shelf: sh.scroll_by(-px(420)), image=icon("back", 14), width=34,
                         height=30).pack(side="right", padx=(0, 6))
            shelf.grid(row=2 * r + 1, column=0, sticky="ew", padx=8)
            for it in its:
                self.tile(shelf.inner, it, tw).pack(side="left", padx=(0, 10), anchor="n")

    BATCH = 16

    def _render_chunk(self, rid, shown, start, view, compact, restore):
        """Desenha as leituras em lotes, para a tela não travar com listas grandes."""
        if rid != self._render_id or not self.scroll.winfo_exists():
            return
        for n in range(start, min(start + self.BATCH, len(shown))):
            it = shown[n]
            if view == "Lista":
                self.make_row(it, compact).grid(row=n, column=0, padx=8, pady=4, sticky="ew")
            elif view == "Pôster":
                self.tile(self.scroll, it, self.card_w, typechip=True).grid(
                    row=n // self.cols, column=n % self.cols, padx=8, pady=8, sticky="n")
            else:
                self.make_card(it).grid(row=n // self.cols, column=n % self.cols, padx=8, pady=8, sticky="n")
        nxt = start + self.BATCH
        if nxt < len(shown):
            self.update_idletasks()
            self.after(5, lambda: self._render_chunk(rid, shown, nxt, view, compact, restore))
        elif restore is not None:
            self.update_idletasks()
            self._restore(restore)

    # ações dos itens
    def toggle_fav(self, it):
        it["favorite"] = not it["favorite"]
        self.commit(it["id"])

    def plus_one(self, it):
        self.add_progress(it, 1)

    def bind_click(self, w, cb, skip):
        if w in skip:
            return
        w.bind("<Button-1>", cb, add="+")
        for c in w.winfo_children():
            self.bind_click(c, cb, skip)

    def action_buttons(self, parent, it, skip, height=28):
        out = []
        if it["url"]:
            out.append(accent_button(parent, "▶ Continuar", lambda: open_url(it["url"]), height=height))
        if it["status"] == "lendo":
            out.append(flat_button(parent, "+1", lambda: self.plus_one(it), height=height, width=44))
        skip.update(out)
        return out

    def heart(self, parent, it, skip, size=30):
        on = bool(it["favorite"])
        b = ctk.CTkButton(parent, text="", image=icon("heart_fill" if on else "heart", 16, PINK if on else P["muted"]),
                          width=size, height=size, corner_radius=size // 2,
                          fg_color=mix(P["surface2"], PINK, .2) if on else P["surface2"],
                          hover_color=mix(P["surface2"], PINK, .38), command=lambda: self.toggle_fav(it))
        skip.add(b)
        return b

    def tile(self, parent, it, tw, bg=None, typechip=False):
        """Obra inteira (capa, etiquetas, título e borda) desenhada numa única imagem: um widget só."""
        bg = bg or P["bg"]
        chips = tile_chips(it, typechip)
        hot = self.item_color(it)
        size = (tw + 10, tile_height(tw))

        def img(on):
            key = (it["id"], "tile", tw, bg, typechip, on)
            if key not in self.images:
                self.images[key] = ctk.CTkImage(tile_pil(self, it, tw, chips, hot if on else bg, bg), size=size)
            return self.images[key]

        lab = ctk.CTkLabel(parent, text="", image=img(False), fg_color="transparent", cursor="hand2")
        state = {"on": False}

        def enter(e):
            if not state["on"] and not scrolling():
                state["on"] = True
                lab.configure(image=img(True))

        def leave(e):
            if state["on"]:
                state["on"] = False
                lab.configure(image=img(False))

        lab.bind("<Enter>", enter, add="+")
        lab.bind("<Leave>", leave, add="+")
        lab.bind("<Button-1>", lambda _e, it=it: self.open_detail(it), add="+")
        attach_preview(self, lab, it)
        return lab

    def make_card(self, it):
        skip = set()
        cw_ = self.card_w
        cover_w = cw_ - 20
        cover_h = int(cover_w * COVER_RATIO)
        wrap = cw_ - 28
        col = self.item_color(it)
        cbg, edge = mix(col, P["surface"], .93), mix(col, P["border"], .8)
        card = ctk.CTkFrame(self.scroll, width=cw_, fg_color=cbg, corner_radius=16,
                            border_width=1, border_color=edge)
        ctk.CTkLabel(card, text="", image=self.cover(it, cover_w, cover_h, (("tl", it["type"], type_color(it["type"])),))).pack(
            padx=10, pady=(10, 8))
        trow = ctk.CTkFrame(card, fg_color="transparent")
        trow.pack(fill="x", padx=14)
        self.heart(trow, it, skip, 30).pack(side="right", padx=(8, 0), anchor="n")
        tkey = (it["id"], "ctitle", cw_, cbg)
        if tkey not in self.images:
            pil, th_ = card_title_pil(it, wrap - 40, cbg)
            self.images[tkey] = ctk.CTkImage(pil, size=(wrap - 40, th_))
        ctk.CTkLabel(trow, text="", image=self.images[tkey], anchor="w").pack(side="left", fill="x", expand=True)
        ikey = (it["id"], "cinfo", cw_, cbg)
        if ikey not in self.images:
            pil, ih = card_info_pil(self, it, wrap, cbg, col)
            self.images[ikey] = ctk.CTkImage(pil, size=(wrap, ih))
        ctk.CTkLabel(card, text="", image=self.images[ikey], anchor="w").pack(fill="x", padx=14)
        if it["url"] or it["status"] == "lendo":
            fr = ctk.CTkFrame(card, fg_color="transparent")
            fr.pack(fill="x", padx=14, pady=(10, 0))
            for b in self.action_buttons(fr, it, skip):
                b.pack(side="left", expand=b.cget("text") != "+1", fill="x", padx=(0, 6))
        ctk.CTkFrame(card, width=1, height=12, fg_color="transparent").pack()
        self.bind_click(card, lambda _e, it=it: self.open_detail(it), skip)
        hover_card(card, normal=edge, hot=col)
        attach_preview(self, card, it)
        return card

    def make_row(self, it, compact=False):
        skip = set()
        row = ctk.CTkFrame(self.scroll, fg_color=P["surface"], corner_radius=12, border_width=1,
                           border_color=P["border"])
        ctk.CTkLabel(row, text="", image=self.cover(it, 40, 56)).pack(side="left", padx=10, pady=8)
        h = self.heart(row, it, skip, 30)
        h.pack(side="right", padx=(6, 12))
        for b in self.action_buttons(row, it, skip):
            b.pack(side="right", padx=4)
        mkey = (it["id"], "rmeta", compact, P["surface"])
        if mkey not in self.images:
            pil, mw, mh = row_meta_pil(it, P["surface"], compact)
            self.images[mkey] = ctk.CTkImage(pil, size=(mw, mh))
        ctk.CTkLabel(row, text="", image=self.images[mkey]).pack(side="right", padx=(0, 6))
        mid = ctk.CTkFrame(row, fg_color="transparent")
        mid.pack(side="left", fill="x", expand=True)
        ctk.CTkLabel(mid, text=it["title"], text_color=P["text"], anchor="w",
                     font=ctk.CTkFont(size=15, weight="bold")).pack(fill="x")
        parts = [it["type"]] + ([STATUS[it["status"]]] if compact else []) + [
            it["author"], ", ".join(it["tags"][:3])] + (
            [f"parada há {stalled_days(it)} dias"] if stalled_days(it) else [])
        ctk.CTkLabel(mid, text="●  " + "  •  ".join(x for x in parts if x), text_color=P["muted"], anchor="w",
                     font=ctk.CTkFont(size=12)).pack(fill="x")
        self.bind_click(row, lambda _e, it=it: self.open_detail(it), skip)
        hover_card(row)
        attach_preview(self, row, it)
        return row


if __name__ == "__main__":
    S.update(load_settings())
    apply_palette()
    App().mainloop()
