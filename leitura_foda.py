import colorsys
import csv
import io
import json
import math
import re
import shutil
import sys
import time
import functools
import unicodedata
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
MIN_CARD, MAX_CARD = 170, 260
MIN_POSTER, MAX_POSTER = 190, 300
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
LABEL_COLORS = ["#f87171", "#fb923c", "#fbbf24", "#4ade80", "#2dd4bf", "#60a5fa", "#a78bfa", "#f472b6"]


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
             stall_days=30)
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


DEFAULTS = dict(url="", author="", year="", tags=[], favorite=False, notes="", started="",
                finished="", rereads=0, rating=0.0, seen=0, total=0, cover=None,
                crit=dict(story=0.0, art=0.0, chars=0.0), lists=[], vol_total=0, vol_owned=[],
                minutes=0, progressed=0, ongoing=False, quotes=[], history=[], labels=[])


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


def add_event(it, kind, text=""):
    it.setdefault("history", []).append({"ts": time.time(), "kind": kind, "text": text})
    del it["history"][:-500]


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
    for d, pre in ((covers_dir(), "covers"), (profile_dir(), "profile")):
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
DETAIL_HERO = 110


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


def backdrop_pil(img, W, H, color, bg, x0, x1, hh):
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
        side.putpixel((0, y), int(255 * min(1.0, 0.08 + 0.92 * t ** 0.9)))
        c = (y - 0.30 * hh) / (0.70 * hh)
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
    elif name in ("library", "book"):
        box(.12, .18, .34, .84)
        box(.40, .18, .62, .84)
        line([(.69, .26), (.87, .2), (.98, .76), (.80, .82)], close=True)
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
    """Imagem do perfil para postar (1080x1440): banner, avatar, números, gêneros e favoritos."""
    W, H = 1080, 1440
    pal, accent = DARK, S["accent"]
    bg, pr, items = pal["bg"], app.profile, app.items
    img = Image.new("RGB", (W, H), bg)
    bp = profile_dir() / pr["banner"] if pr.get("banner") else None
    img.paste(banner_pil(bp, W, 400, bg, accent), (0, 0))
    try:        # brilho suave na cor de destaque
        glow = Image.radial_gradient("L").resize((1200, 1200), Image.BICUBIC)
        glow = glow.point(lambda v: int(max(0.0, 1 - v / 175.0) ** 1.6 * 255 * 0.28))   # zera antes da borda
        gm = Image.new("L", (W, H), 0)
        gm.paste(glow, (W - 780, -470))
        img = Image.composite(Image.new("RGB", (W, H), accent), img, gm)
    except Exception:
        pass
    show = showcase_badges(app)
    if show:
        bs, gp = 96, 16
        pw_ = len(show) * bs + (len(show) - 1) * gp + 40
        ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ImageDraw.Draw(ov).rounded_rectangle([W - 48 - pw_, 40, W - 48, 40 + bs + 40], radius=30, fill=(11, 11, 18, 175))
        img = Image.alpha_composite(img.convert("RGBA"), ov).convert("RGB")
        for n_, b in enumerate(show):
            bi = badge_pil(b["icon"], b["tier"], True, bs * 2).resize((bs, bs), Image.LANCZOS)
            img.paste(bi, (W - 48 - pw_ + 20 + n_ * (bs + gp), 60), bi)
    d = ImageDraw.Draw(img)

    def T(xy, text, size, fill, bold=False, anchor="la"):
        font = get_font(size, bold)
        try:
            d.text(xy, text, font=font, fill=fill, anchor=anchor)
        except (TypeError, ValueError):
            d.text(xy, text, font=font, fill=fill)

    # avatar redondo
    AV = 250
    ap = profile_dir() / pr["avatar"] if pr.get("avatar") else None
    am = Image.new("L", (AV * 4, AV * 4), 0)
    ImageDraw.Draw(am).ellipse([0, 0, AV * 4 - 1, AV * 4 - 1], fill=255)
    lv = level_info(xp_breakdown(app)[1])
    img.paste(avatar_pil(ap, pr["name"], AV, bg, lv["color"]), (64, 290), am.resize((AV, AV), Image.LANCZOS))

    X = 64 + AV + 40
    maxw = W - X - 64
    T((X, 336), _fit_text(d, pr["name"], get_font(72, True), maxw), 72, pal["text"], True)
    handle = _fit_text(d, pr["handle"], get_font(36), maxw)
    T((X, 426), handle, 36, accent)
    lab_lv = f"Nível {lv['level']} · {lv['title']}"
    cfont = get_font(26, True)
    cx0 = X + d.textlength(handle, font=get_font(36)) + 24
    lwid = d.textlength(lab_lv, font=cfont)
    if cx0 + lwid + 36 >= W - 64:                    # título longo: mostra só "Nível N"
        lab_lv = f"Nível {lv['level']}"
        lwid = d.textlength(lab_lv, font=cfont)
    if cx0 + lwid + 36 < W - 64:
        d.rounded_rectangle([cx0, 428, cx0 + lwid + 36, 470], radius=21, fill=mix(lv["color"], bg, .78),
                            outline=lv["color"], width=2)
        T((cx0 + 18, 434), lab_lv, 26, lv["color"], True)
    bio = (pr.get("bio") or "").strip()
    if bio and not bio.startswith("Clique em"):
        for k, line in enumerate(_wrap(d, bio, get_font(30), maxw, 3)):
            T((X, 486 + k * 42), line, 30, pal["muted"])

    # números
    rated = [i["rating"] for i in items if i["rating"]]
    stats = [(str(len(items)), "leituras"), (str(sum(1 for i in items if i["status"] == "completo")), "completas"),
             (f"{sum(rated) / len(rated):.1f}".replace(".", ",") if rated else "–", "nota média"),
             (fmt_minutes(sum_activity(app.activity, "", "min")), "de leitura")]
    gap = 18
    tw = (W - 128 - 3 * gap) // 4
    for k, (val, lab) in enumerate(stats):
        x = 64 + k * (tw + gap)
        d.rounded_rectangle([x, 640, x + tw, 780], radius=26, fill=pal["surface"], outline=pal["border"], width=2)
        size = 56
        while size > 28 and d.textlength(val, font=get_font(size, True)) > tw - 28:
            size -= 4
        T((x + tw / 2, 698), val, size, pal["text"], True, "mm")
        T((x + tw / 2, 746), lab, 26, pal["muted"], False, "mm")

    # gêneros mais lidos
    y = 812
    top = [t for t, _ in Counter(t for i in items for t in i["tags"]).most_common(3)]
    if top:
        cx = 64
        T((cx, y + 8), "Gêneros", 28, pal["muted"])
        cx += d.textlength("Gêneros", font=get_font(28)) + 22
        cf = get_font(28, True)
        for t in top:
            label = _fit_text(d, t, cf, 230)
            lw_ = d.textlength(label, font=cf)
            d.rounded_rectangle([cx, y, cx + lw_ + 44, y + 50], radius=25, fill=mix(accent, bg, .78),
                                outline=mix(accent, bg, .4), width=2)
            T((cx + 22, y + 9), label, 28, accent, True)
            cx += lw_ + 44 + 14
        y += 74
    else:
        y += 10

    # favoritos
    ranked = sorted(items, key=lambda i: (-i["rating"], -i["seen"]))
    favs = [i for i in ranked if i["favorite"]]
    title = "Leituras favoritas" if favs else "Destaques"
    favs = (favs + [i for i in ranked if not i["favorite"]])[:5]
    ty = y + 34
    d.rectangle([64, ty, 70, ty + 48], fill=accent)
    T((90, ty - 4), title, 46, pal["text"], True)
    CW, CH = 176, 244
    cgap = (W - 128 - 5 * CW) // 4
    cy = ty + 82
    rmask = Image.new("L", (CW * 4, CH * 4), 0)
    ImageDraw.Draw(rmask).rounded_rectangle([0, 0, CW * 4 - 1, CH * 4 - 1], radius=84, fill=255)
    rmask = rmask.resize((CW, CH), Image.LANCZOS)
    if not favs:
        for k in range(5):
            x = 64 + k * (CW + cgap)
            d.rounded_rectangle([x, cy, x + CW, cy + CH], radius=21, fill=pal["surface"], outline=pal["border"], width=2)
        T((W / 2, cy + CH + 36), "Adicione e favorite leituras para elas aparecerem aqui", 28, pal["muted"], False, "mm")
    for k, it in enumerate(favs):
        x = 64 + k * (CW + cgap)
        try:
            cp = covers_dir() / it["cover"] if it.get("cover") else None
            cov = Image.open(cp).convert("RGB") if cp and cp.exists() else placeholder(it["title"])
        except OSError:
            cov = placeholder(it["title"])
        cov = ImageOps.fit(cov.convert("RGB"), (CW * 2, CH * 2))
        if it["rating"]:
            cov = overlay_chips(cov, [("bl", f"{it['rating']:g}".replace(".", ","), "gold")])
        img.paste(cov.convert("RGB").resize((CW, CH), Image.LANCZOS), (x, cy), rmask)
        T((x, cy + CH + 12), _fit_text(d, it["title"], get_font(24), CW), 24, pal["muted"])

    # rodapé
    d.line([(64, 1318), (W - 64, 1318)], fill=pal["border"], width=2)
    logo = logo_pil(60, accent)
    img.paste(logo, (64, 1342), logo)
    T((64 + 60 + 20, 1350), "Leitura Foda", 42, pal["text"], True)
    T((W - 64, 1356), str(date.today().year), 34, pal["muted"], False, "ra")
    img.save(path, "PNG")


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
    e = ctk.CTkEntry(parent, placeholder_text=ph, fg_color=P["surface2"], border_width=1,
                     border_color=P["surface2"], height=36, corner_radius=10, text_color=P["text"], **kw)
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
            self.bar.configure(button_color=P["surface2"] if need else P["bg"],
                               button_hover_color=P["accent"] if need else P["bg"])

    def _on_inner(self, e):
        if self.virtual is not None:
            return
        self._region_h = max(1, e.height)
        self.canvas.configure(scrollregion=(0, 0, max(e.width, self.canvas.winfo_width()), e.height))

    def _on_canvas(self, e):
        if self.win_w:
            ww = min(e.width, px(self.win_w))
            self.canvas.coords(self._win, (e.width - ww) // 2, 0)
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

    def __init__(self, master, height):
        super().__init__(master, fg_color="transparent")
        self.canvas = tk.Canvas(self, height=px(height), bg=P["bg"], highlightthickness=0, bd=0)
        self.canvas.pack(fill="x")
        self.inner = tk.Frame(self.canvas, bg=P["bg"], bd=0, highlightthickness=0)
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
]

LEGENDARY = {"seq100", "hora500", "completa100", "estante250", "cap10000", "saga500", "coruja20", "semfronteiras",
             "mes300", "voltaporcima"}
RARITY = {"Comum": "#9296c0", "Rara": "#4dd0e1", "Épica": "#b86bff", "Lendária": "#ffc233"}
CATS = ["Leitura", "Tempo", "Sequências", "Coleção", "Avaliação", "Datas"]
KEY_CAT = {"done": "Leitura", "done_year": "Leitura", "big_done": "Leitura", "huge_done": "Leitura",
           "chapters": "Leitura", "max_day": "Leitura", "best_month": "Leitura", "week_done": "Leitura",
           "done_same_day": "Leitura", "done_fast": "Leitura", "n_reading": "Leitura", "types": "Leitura",
           "tags": "Leitura", "rereads": "Leitura", "hours": "Tempo", "morning": "Tempo", "night": "Tempo",
           "longest": "Sequências", "comeback": "Sequências", "n_items": "Coleção", "owned": "Coleção",
           "lists": "Coleção", "rated": "Avaliação", "rated5": "Avaliação", "quotes": "Avaliação",
           "favs": "Avaliação", "newyear": "Datas", "christmas": "Datas", "terror_oct": "Datas",
           "yearend": "Datas", "sunday": "Datas", "friday13": "Datas"}
FAMILY = {"chapters": "Capítulos lidos", "hours": "Horas de leitura", "done": "Leituras completas",
          "longest": "Dias seguidos", "best_month": "Capítulos no mês", "rated": "Notas dadas",
          "favs": "Favoritas", "owned": "Volumes", "n_items": "Tamanho da lista", "quotes": "Citações",
          "rereads": "Releituras"}


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
    out = []
    for secret, lst in ((False, BADGES), (True, SECRET_BADGES)):
        for bid, title, desc, ic, tier, key, need in lst:
            need = need if need is not None else max(1, S["goal"])
            have = ctx[key]
            out.append(dict(id=bid, title=title, desc=desc, icon=ic, tier=tier, have=have, need=need,
                            earned=have >= need, secret=secret, key=key, cat=KEY_CAT.get(key, "Leitura"),
                            date=dates.get(bid, "")))
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
    w = int((24 + min(n, 240) / 8) * k)
    h = int((150 + (sum(ord(c) for c in it["title"]) % 6) * 10) * k)
    return w, h


def text_on(color):
    r, g, b = (int(color.lstrip("#")[i:i + 2], 16) for i in (0, 2, 4))
    return "#14120a" if 0.299 * r + 0.587 * g + 0.114 * b > 150 else "#ffffff"


def shelf_label(title, w, k):
    """Lombada fina: só a primeira palavra (ou sigla); o nome completo vai no tooltip."""
    if w >= 40 * k:
        return title
    words = [x for x in re.split(r"\s+", title.strip()) if x]
    if not words:
        return title
    first = words[0]
    if len(first) <= 3 and len(words) > 1:
        return "".join(x[0] for x in words[:3]).upper()
    return first


def shelf_pil(entries, width, k, pull=None):
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
    rows = rows[:4]
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
            d.rounded_rectangle([x, top, x + w, base], radius=int(4 * k), fill=col)
            band = mix(col, "#000000", .28)
            d.rectangle([x, top + int(10 * k), x + w, top + int(14 * k)], fill=band)
            d.rectangle([x, base - int(14 * k), x + w, base - int(10 * k)], fill=band)
            font = get_font(max(10, int(min(w * 0.46, 15 * k))), True)
            txt = _fit_text(d, shelf_label(it["title"], w, k), font, h - int(46 * k))
            try:
                l, t_, rr, bb = d.textbbox((0, 0), txt, font=font)
                tw_, th_ = rr - l + 4, bb - t_ + 6
            except Exception:
                tw_, th_ = 60, 16
            tim = Image.new("RGBA", (max(1, tw_), max(1, th_)), (0, 0, 0, 0))
            ImageDraw.Draw(tim).text((2, 2), txt, font=font, fill=text_on(col))
            tim = tim.rotate(270, expand=True)
            img.paste(tim, (x + (w - tim.size[0]) // 2, top + int(18 * k)), tim)
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
    """Citação favorita (estrela); senão a citação mais recente; senão a anotação mais recente."""
    qs = it.get("quotes") or []
    if not qs:
        return None
    for pool in ([q for q in qs if q.get("fav")], [q for q in qs if q.get("kind") == "citação"], qs):
        if pool:
            return max(pool, key=lambda q: q.get("ts", 0))
    return None


def make_work_card(app, it, path):
    """Imagem 1080x1440 de uma leitura só (capa, nota, situação e citação) para postar."""
    W, H = 1080, 1440
    acc = app.item_color(it)
    bg = DARK["bg"]
    cov = app._load_cover(it).convert("RGB")
    back = ImageOps.fit(cov, (W, H)).filter(ImageFilter.GaussianBlur(46))
    back = Image.blend(back, Image.new("RGB", (W, H), bg), .62)
    fade = Image.new("L", (1, H))
    for y in range(H):
        fade.putpixel((0, y), int(255 * max(0, min(1, (y - H * .45) / (H * .55))) ** 1.2))
    img = Image.composite(Image.new("RGB", (W, H), bg), back, fade.resize((W, H))).convert("RGBA")
    d = ImageDraw.Draw(img)

    def T(xy, text, size, fill, bold=False, anchor="la"):
        font = get_font(size, bold)
        try:
            d.text(xy, text, font=font, fill=fill, anchor=anchor)
        except (TypeError, ValueError):
            d.text(xy, text, font=font, fill=fill)

    cw, ch = 360, 504
    cx0, cy0 = (W - cw) // 2, 70
    sh = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ImageDraw.Draw(sh).rounded_rectangle([cx0 - 6, cy0 + 24, cx0 + cw + 6, cy0 + ch + 34], radius=40, fill=(0, 0, 0, 170))
    img = Image.alpha_composite(img, sh.filter(ImageFilter.GaussianBlur(30)))
    cover = rounded(ImageOps.fit(cov, (cw, ch)), 36)
    img.paste(cover, (cx0, cy0), cover)
    d = ImageDraw.Draw(img)
    y = cy0 + ch + 44
    font = get_font(62, True)
    for line in wrap_px(d, it["title"], font, W - 160, 2):
        T((W / 2, y), line, 62, "#ffffff", True, "ma")
        y += 74
    meta = "  •  ".join(x for x in (it["type"], it["author"], str(it["year"]) if it["year"] else "") if x)
    T((W / 2, y + 2), _fit_text(d, meta, get_font(30), W - 160), 30, "#b9bdd6", False, "ma")
    y += 66
    r = it["rating"] or 0
    if r:
        sz, gap = 58, 14
        x0 = (W - (5 * sz + 4 * gap)) / 2
        for i in range(5):
            f = 1 if r >= i + 1 else (.5 if r >= i + .5 else 0)
            st = star_pil(sz, f, (255, 255, 255, 55))
            img.paste(st, (int(x0 + i * (sz + gap)), int(y)), st)
        d = ImageDraw.Draw(img)
        y += sz + 12
        T((W / 2, y), f"{r:g}".replace(".", ",") + " / 5", 32, GOLD_HEX, True, "ma")
        y += 52
    else:
        y += 6
    stt = STATUS[it["status"]]
    cap = f"cap. {it['seen']}" + (f" de {it['total']}" if it["total"] and not it.get("ongoing") else "")
    chip = f"{stt}  ·  {cap}"
    fnt = get_font(30, True)
    tw_ = d.textlength(chip, font=fnt)
    d.rounded_rectangle([W / 2 - tw_ / 2 - 28, y, W / 2 + tw_ / 2 + 28, y + 56], radius=28,
                        fill=mix(P["status"][it["status"]], bg, .72))
    T((W / 2, y + 28), chip, 30, P["status"][it["status"]], True, "mm")
    y += 84
    q = best_quote(it)
    if q:
        txt = q["text"].strip()
        qf = get_font(36)
        lines = wrap_px(d, txt, qf, W - 260, 3)
        bh = len(lines) * 50 + 110
        by = min(y, H - 150 - bh)
        panel_ = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ImageDraw.Draw(panel_).rounded_rectangle([70, by, W - 70, by + bh], radius=34, fill=(12, 12, 20, 190),
                                                 outline=acc, width=2)
        img = Image.alpha_composite(img, panel_)
        d = ImageDraw.Draw(img)
        T((100, by - 6), "“", 100, acc, True)
        for n, line in enumerate(lines):
            T((130, by + 62 + n * 50), line, 36, "#ffffff")
        T((W - 104, by + bh - 40), f"cap. {q.get('ch', 0)}", 26, "#9aa0c0", False, "ra")
    # rodapé
    lg = logo_pil(64, S["accent"])
    img.paste(lg, (70, H - 110), lg)
    d = ImageDraw.Draw(img)
    T((150, H - 100), "Leitura Foda", 36, S["accent"], True)
    T((W - 70, H - 96), app.profile.get("handle", ""), 30, "#9aa0c0", False, "ra")
    img.convert("RGB").save(path, "PNG")


# ---------- base das páginas (ficam dentro da janela principal) ----------
class Page(ctk.CTkFrame):
    MAXW = 720

    def __init__(self, app, title=None, back=False):
        super().__init__(app.main, fg_color="transparent")
        self.app = app
        if title or back:
            top = ctk.CTkFrame(self, fg_color="transparent")
            top.pack(fill="x", padx=22, pady=(18, 6))
            if back:
                ghost_button(top, " Voltar", app.go_back, image=icon("back", 16), compound="left", width=96,
                             height=34).pack(side="left", padx=(0, 14))
            if title:
                section(top, title, 26).pack(side="left")
        self.footer = ctk.CTkFrame(self, fg_color="transparent", height=1)   # sem height ocupava 200 px vazios
        self.footer.pack(side="bottom", fill="x", padx=20, pady=(0, 14))
        self.scroll = new_scroll(self)
        self.scroll.pack(fill="both", expand=True, padx=8, pady=(0, 8))
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
                for x0, y0, x1, y1, name in b.regs:
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
            elif b is not None and b.item is not None and name and S.get("preview", True) \
                    and preview_has_content(b.item):
                PV["root"] = self.app
                PV["job"] = self.app.after(650, lambda it=b.item: preview_show(self.app, it))

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


def profile_header(app, w, hov, pr, lv):
    BH, g = HBH, _hdr_geom(app, w, pr, lv)
    AV, ix, y0, bio = g["AV"], g["ix"], g["y0"], g["bio"]
    bg = P["bg"]
    items = app.items

    def path(key):
        n = pr.get(key)
        return profile_dir() / n if n else None

    img = Image.new("RGBA", (w * K, BH * K), bg)
    img.paste(banner_pil(path("banner"), w * K, BH * K, bg, P["accent"], fade=(0.62, 0.38)), (0, 0))
    shade_ = Image.new("RGBA", img.size, (0, 0, 0, 0))                  # escurece a metade de baixo p/ o texto
    sd = ImageDraw.Draw(shade_)
    for yy in range(int(BH * K * .38), BH * K):
        t = (yy - BH * K * .38) / (BH * K * .62)
        sd.line([(0, yy), (w * K, yy)], fill=(8, 8, 14, int(150 * min(1, t * 1.2))))
    img.alpha_composite(shade_)
    # avatar
    av = avatar_pil(path("avatar"), pr["name"], AV * K, bg, lv["color"])
    am = Image.new("L", (AV * K * 4, AV * K * 4), 0)
    ImageDraw.Draw(am).ellipse([0, 0, AV * K * 4 - 1, AV * K * 4 - 1], fill=255)
    img.paste(av, (26 * K, (BH - AV - 22) * K), am.resize((AV * K, AV * K), Image.LANCZOS))
    d = ImageDraw.Draw(img)
    # linha 1: nome + título do nível
    T(d, ix, y0, pr["name"], 32, "#ffffff", True)
    nw = TW(d, pr["name"], 32, True)
    chip = f" {lv['title']} "
    cw_ = TW(d, chip, 12, True) + 8
    cx0 = ix + nw + 14
    d.rounded_rectangle([cx0 * K, (y0 + 10) * K, (cx0 + cw_) * K, (y0 + 32) * K], radius=6 * K,
                        fill=mix(lv["color"], "#000000", .55), outline=mix(lv["color"], "#000000", .15), width=K)
    T(d, cx0 + cw_ / 2, y0 + 21, chip, 12, mix(lv["color"], "#ffffff", .25), True, "mm")
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
    return img


class ImgPage(Page):
    """Página cujo conteúdo é uma lista de imagens (blocos) desenhadas direto no canvas."""

    def __init__(self, app, title=None, back=False):
        super().__init__(app, title, back=back)
        self.view = BlockView(app, self.scroll, self.layout)
        self.after(40, self.view.rebuild)


class ProfilePage(ImgPage):
    MAXW = 1500

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
        for n, it in enumerate(items[:lim]):
            r, c = divmod(n, cols)
            hot = app.item_color(it)

            def draw(hov, it=it, hot=hot):
                return tile_pil(app, it, tw, tile_chips(it, False), hot if hov else P["bg"], P["bg"])
            out.append(Blk(f"{key}-{it['id']}-{tw}", x + c * (tw + 22) + 6, y + r * (th + 12) + 6, tw + 10, th, draw,
                           [(0, 0, tw + 10, th, "go")], lambda n_, it=it: app.open_detail(it), item=it))
        rows = -(-min(len(items), lim) // cols)
        return y + rows * (th + 12) + 12

    def layout(self, avail):
        app, items = self.app, self.app.items
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        two = W >= 1000
        LW = W - 18 - 330 if two else W
        out, y = [], 8
        pr, lv = self.pr, self.lv

        def hdr_draw(hov):
            return profile_header(app, LW, hov, pr, lv)
        BH = HBH
        bx0 = LW - 16 - 3 * 42 - 2 * 8
        g = _hdr_geom(app, LW, pr, lv)
        hb = Blk("hdr-" + str(len(g["medals"])), pad, y, LW, BH, hdr_draw,
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
            y += 28 + 10
            y = self._tiles(key, lst, empty, pad, y, cols, tw, out)
        if len(items) >= 3:
            y += 18
            out.append(self._title("t-shelf", "Minha estante", pad, y))
            y += 28 + 10
            ranked = sorted(items, key=lambda i: (not i["favorite"], -i["rating"], i["title"].lower()))
            if self._shelf[0] != LW or self._shelf[1] is None:
                img, hits = shelf_pil([(i, app.item_color(i)) for i in ranked[:60]], int(LW * K), K)
                self._shelf = (LW, img, hits)
            _, simg, hits = self._shelf
            sh = -(-simg.size[1] // K)
            regs = [(a / K, b / K, c / K, e_ / K, f"it{n}") for n, (a, b, c, e_, _it) in enumerate(hits)]

            ents = [(i, app.item_color(i)) for i in ranked[:60]]

            def sdraw(hov, simg=simg, ents=ents, hits=hits):
                if hov:
                    try:
                        pid = hits[int(hov[2:])][4]["id"]
                        return shelf_pil(ents, int(LW * K), K, pull=pid)[0].convert("RGBA")
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
            rx, ry, rw = pad + LW + 18, 8, 330
        else:
            rx, ry, rw = pad, y + 10, W
        for name in ("year", "ratings", "genres", "badges"):
            sp = self.specs[name]
            h = sp.nat(rw)
            out.append(sp.block(name, rx, ry, rw, h))
            ry += h + 14
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
        flat_button(r, "Remover", lambda: self.clear("banner"), width=80).pack(side="left")
        label("Foto de perfil")
        self.avatar_prev = ctk.CTkLabel(body, text="")
        self.avatar_prev.pack(padx=18, anchor="w")
        r = ctk.CTkFrame(body, fg_color="transparent")
        r.pack(fill="x", padx=18, pady=6)
        flat_button(r, "Escolher foto", lambda: self.pick("avatar")).pack(side="left", padx=(0, 8))
        flat_button(r, "Remover", lambda: self.clear("avatar"), width=80).pack(side="left")
        label("Nome")
        self.name = entry(body)
        self.name.pack(fill="x", padx=18)
        label("Usuário")
        self.handle = entry(body)
        self.handle.pack(fill="x", padx=18)
        label("Sobre você")
        self.bio = ctk.CTkTextbox(body, height=90, fg_color=P["surface2"], text_color=P["text"])
        self.bio.pack(fill="x", padx=18, pady=(0, 18))
        self.name.insert(0, self.pr["name"])
        self.handle.insert(0, self.pr["handle"])
        self.bio.insert("1.0", self.pr["bio"])
        self.previews()

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

    def pick(self, key):
        p = filedialog.askopenfilename(parent=self.app, filetypes=[("Imagens", "*.png *.jpg *.jpeg *.webp *.bmp *.gif")])
        if p:
            self.new[key], self.remove[key] = p, False
            self.previews()

    def clear(self, key):
        self.new[key], self.remove[key] = None, True
        self.previews()

    def save(self):
        pr = self.pr
        pr["name"] = self.name.get().strip() or "Leitor"
        pr["handle"] = self.handle.get().strip() or "@leitor"
        pr["bio"] = self.bio.get("1.0", "end").strip()
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
            H = int(1000 * k)
            img = backdrop_pil(self.app._load_cover(self.it), cw, H, self.app.item_color(self.it), P["bg"],
                               x0, x0 + colw, int(DETAIL_HERO * k))
            self._bd_ph = ImageTk.PhotoImage(img)
            cv = sc.canvas
            if self._bd_item is None:
                self._bd_item = cv.create_image(0, 0, image=self._bd_ph, anchor="nw")
            else:
                cv.itemconfigure(self._bd_item, image=self._bd_ph)
            cv.tag_lower(self._bd_item)
            hero = img.crop((x0, 0, x0 + colw, int(DETAIL_HERO * k)))
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
                lb.configure(wraplength=self._wrap)
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

    def wrapped(self, parent, **kw):
        lb = ctk.CTkLabel(parent, wraplength=self._wrap, justify="left", anchor="w", **kw)
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
        action_btn(self.left, "Favorito" if it["favorite"] else "Favoritar",
                   "heart_fill" if it["favorite"] else "heart", self.fav, hot=PINK, on=it["favorite"]).pack(
            fill="x", pady=3)
        action_btn(self.left, "Em lançamento", "check" if ongoing else "clock", self.toggle_ongoing,
                   on=ongoing, hot=acc).pack(fill="x", pady=3)
        action_btn(self.left, "Editar", "edit", lambda: app.open_sub(EditPage, it)).pack(fill="x", pady=3)
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
        if ongoing:
            tag = "em lançamento"
            if it["total"]:
                tag += " · em dia" if it["seen"] >= it["total"] else f" · {it['total']} lançados"
            ctk.CTkLabel(row, text=f"  {tag}  ", fg_color=P["surface2"], text_color=P["accent"], corner_radius=8,
                         height=24, font=ctk.CTkFont(size=12, weight="bold")).pack(side="left", padx=(0, 10))
        sd = stalled_days(it)
        if sd:
            ctk.CTkLabel(row, text=f"parada há {sd} dias", text_color=P["status"]["pausado"]).pack(side="left")
        if it["total"]:
            pb = ctk.CTkProgressBar(rc, height=8, fg_color=P["surface2"], progress_color=acc)
            pb.pack(fill="x", pady=(8, 0))
            self.pbar = pb
            animate_bar(pb, min(1, it["seen"] / it["total"]))
        if it["rating"]:
            r = ctk.CTkFrame(rc, fg_color="transparent")
            r.pack(anchor="w", pady=(12, 0))
            StarRating(r, P["bg"], it["rating"], size=30, interactive=False).pack(side="left")
            ctk.CTkLabel(r, text=fmt_rating(it["rating"]), text_color=GOLD_HEX).pack(side="left", padx=10)
        crit = it.get("crit") or {}
        if any(crit.get(k) for k in ("story", "art", "chars")):
            r = ctk.CTkFrame(rc, fg_color="transparent")
            r.pack(anchor="w", pady=(10, 0))
            for key, lab in (("story", "História"), ("art", "Arte"), ("chars", "Personagens")):
                c = ctk.CTkFrame(r, fg_color="transparent")
                c.pack(side="left", padx=(0, 18))
                ctk.CTkLabel(c, text=lab, text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(anchor="w")
                StarRating(c, P["bg"], crit.get(key, 0.0), size=18, interactive=False).pack(anchor="w")
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
        self.info_lbl = None
        if self.info_text():
            self.info_lbl = ctk.CTkLabel(rc, text=self.info_text(), text_color=P["muted"])
            self.info_lbl.pack(anchor="w", pady=(8, 0))

        # cronômetro
        f, _ = panel(rc, "Cronômetro de leitura")
        f.pack(fill="x", pady=(16, 0))
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
        self.hist_host = ctk.CTkFrame(rc, fg_color="transparent")
        self.hist_host.pack(fill="x")
        self._hl, self._acc = len(it.get("history", [])), acc
        self.history_panel(self.hist_host, acc)

    # ---- citações e anotações por capítulo ----
    def quotes_panel(self, rc, acc):
        it = self.it
        f, head = panel(rc, "Citações e anotações")
        f.pack(fill="x", pady=(14, 0))
        ctk.CTkLabel(head, text=f"{len(it['quotes'])}", text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(
            side="right")
        host = ctk.CTkFrame(f, fg_color="transparent")
        host.pack(fill="x", padx=16)
        for q in sorted(it["quotes"], key=lambda q: (q.get("ch", 0), q.get("ts", 0))):
            row = ctk.CTkFrame(host, fg_color="transparent")
            row.pack(fill="x", pady=5)
            ctk.CTkFrame(row, width=3, height=24, fg_color=acc, corner_radius=0).pack(side="left", fill="y",
                                                                                  padx=(0, 10))
            body = ctk.CTkFrame(row, fg_color="transparent")
            body.pack(side="left", fill="x", expand=True)
            text = f"“{q['text']}”" if q.get("kind") == "citação" else q["text"]
            self.wrapped(body, text=text, text_color=P["text"],
                         font=ctk.CTkFont(size=13, slant="italic" if q.get("kind") == "citação" else "roman")).pack(
                anchor="w")
            ctk.CTkLabel(body, text=f"cap. {q.get('ch', 0)} · {q.get('kind', 'nota')}", text_color=P["muted"],
                         font=ctk.CTkFont(size=11)).pack(anchor="w")
            ghost_button(row, "", lambda q=q: self.del_quote(q), image=icon("close", 12), width=30, height=28,
                         ).pack(side="right", anchor="n")
            ghost_button(row, "", lambda q=q: self.fav_quote(q),
                         image=icon("star", 14, GOLD_HEX if q.get("fav") else P["muted"]), width=30,
                         height=28).pack(side="right", anchor="n")
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

    def add_quote(self, ch, kind, txt):
        text = txt.get().strip()
        if not text:
            return
        raw = ch.get().strip()
        self.it["quotes"].append({"ch": int(raw) if raw.isdigit() else self.it["seen"], "text": text,
                                  "kind": kind.get().lower(), "ts": time.time()})
        self.it["updated"] = time.time()
        self.app.commit(self.it["id"])
        self.render()

    def del_quote(self, q):
        if q in self.it["quotes"]:
            self.it["quotes"].remove(q)
            self.app.commit(self.it["id"])
            self.render()

    # ---- histórico da obra (diário) ----
    def history_panel(self, rc, acc):
        it = self.it
        ev = sorted(it.get("history", []), key=lambda e: -e["ts"])
        f, head = panel(rc, "Histórico")
        f.pack(fill="x", pady=(14, 0))
        ctk.CTkLabel(head, text=f"{len(ev)} registros", text_color=P["muted"], font=ctk.CTkFont(size=12)).pack(
            side="right")
        form = ctk.CTkFrame(f, fg_color="transparent")
        form.pack(fill="x", padx=16, pady=(0, 8))
        ent = entry(form, "Escreva no diário desta leitura...")
        ent.pack(side="left", fill="x", expand=True, padx=(0, 6))
        ent.bind("<Return>", lambda e: self.add_diary(ent), add="+")
        accent_button(form, "Registrar", lambda: self.add_diary(ent), width=92).pack(side="left")
        if not ev:
            self.wrapped(f, text="Nada registrado ainda. Início, pausas, notas e releituras aparecem aqui.",
                         text_color=P["muted"]).pack(anchor="w", padx=16, pady=(0, 14))
            return
        tl = ctk.CTkFrame(f, fg_color="transparent")
        tl.pack(fill="x", padx=16, pady=(0, 6))
        for e in (ev if self.hist_all else ev[:8]):
            base, col = EVENT_STYLE.get(e["kind"], (e["kind"], P["muted"]))
            txt = e.get("text", "")
            main = txt if e["kind"] == "note" else (base + (f" {txt}" if txt else ""))
            row = ctk.CTkFrame(tl, fg_color="transparent")
            row.pack(fill="x", pady=3)
            ctk.CTkLabel(row, text="", image=icon("dot", 12, col), width=18).pack(side="left", anchor="n", pady=(4, 0))
            t = ctk.CTkFrame(row, fg_color="transparent")
            t.pack(side="left", fill="x", expand=True, padx=(6, 0))
            self.wrapped(t, text=main, text_color=P["text"]).pack(anchor="w")
            ctk.CTkLabel(t, text=datetime.fromtimestamp(e["ts"]).strftime("%d/%m/%Y · %H:%M"), text_color=P["muted"],
                         font=ctk.CTkFont(size=11)).pack(anchor="w")
        if len(ev) > 8 and not self.hist_all:
            ghost_button(f, f"Mostrar todos ({len(ev)})", self.show_all_hist, height=30).pack(
                anchor="w", padx=16, pady=(0, 14))
        else:
            ctk.CTkFrame(f, width=1, height=8, fg_color="transparent").pack()

    def show_all_hist(self):
        self.hist_all = True
        self.render()

    def add_diary(self, ent):
        text = ent.get().strip()
        if text:
            add_event(self.it, "note", text)
            self.it["updated"] = time.time()
            self.app.commit(self.it["id"])
            self.render()

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
        it = self.it
        return (bool(stalled_days(it)), bool(self.info_text()))

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
            if self.info_lbl is not None:
                self.info_lbl.configure(text=self.info_text())
            if self.pbar is not None and it["total"]:
                self.pbar.set(min(1, it["seen"] / it["total"]))
            if len(it.get("history", [])) != self._hl:       # novo registro: refaz só o painel do histórico
                for w in self.hist_host.winfo_children():
                    w.destroy()
                self._hl = len(it.get("history", []))
                self.history_panel(self.hist_host, self._acc)
        except Exception:
            self.render()

    def plus(self):
        sig = self._sig()
        if self.app.add_progress(self.it, 1) is False:
            return
        self._sync_top(sig)

    def toggle_ongoing(self):
        it = self.it
        it["ongoing"] = not it.get("ongoing")
        if it["ongoing"] and it["status"] == "completo":
            it["status"] = "lendo"          # saem capítulos novos: volta a ser uma leitura em andamento
        add_event(it, "ongoing", "ativado" if it["ongoing"] else "desativado")
        it["updated"] = time.time()
        self.app.commit(it["id"])
        self.render()

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
        self.app.toast("Cartão salvo! Agora é só postar.")

    def fav_quote(self, q):
        on = not q.get("fav")
        for o in self.it["quotes"]:
            o.pop("fav", None)
        if on:
            q["fav"] = True
        self.it["updated"] = time.time()
        self.app.commit(self.it["id"])
        self.render()

    def fav(self):
        self.it["favorite"] = not self.it["favorite"]
        self.it["updated"] = time.time()
        self.app.commit(self.it["id"])
        self.render()

    def add_list(self):
        name = (ctk.CTkInputDialog(text="Nome da lista:", title="Adicionar à lista").get_input() or "").strip()
        if name and name not in self.it["lists"]:
            self.it["lists"].append(name)
            self.it["updated"] = time.time()
            self.app.commit(self.it["id"])
            self.render()

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
    MAXW = 1100

    def __init__(self, app):
        super().__init__(app, "Tier list", back=True)
        self.tiers = app.profile.setdefault("tiers", {})
        for t in TIERS:
            self.tiers.setdefault(t, [])
        self.zones, self.thumbs, self.drag = {}, {}, None
        top = ctk.CTkFrame(self.col, fg_color="transparent")
        top.pack(fill="x", pady=(0, 10))
        accent_button(top, " Gerar imagem", self.make_image, image=icon("share", 16, "#ffffff"), compound="left",
                      width=150).pack(side="right")
        ghost_button(top, "Limpar tudo", self.clear_all, width=110).pack(side="right", padx=(0, 8))
        ctk.CTkLabel(top, text="Arraste as capas para as linhas. Clique numa capa para abrir.",
                     text_color=P["muted"]).pack(side="left")
        self.rows_host = ctk.CTkFrame(self.col, fg_color="transparent")
        self.rows_host.pack(fill="x")
        self.pool_host = ctk.CTkFrame(self.col, fg_color="transparent")
        self.pool_host.pack(fill="x", pady=(14, 0))
        self.query = ""
        self.render()

    def thumb(self, parent, it):
        lab = ctk.CTkLabel(parent, text="", image=self.app.cover(it, 64, 90), cursor="fleur")
        lab.bind("<ButtonPress-1>", lambda e, it=it: self.drag_start(e, it))
        lab.bind("<B1-Motion>", self.drag_move)
        lab.bind("<ButtonRelease-1>", self.drag_end)
        return lab

    def render(self):
        by_id = {i["id"]: i for i in self.app.items}
        for host in (self.rows_host, self.pool_host):
            for w in host.winfo_children():
                w.destroy()
        self.zones, self.thumbs = {}, {}
        used = set()
        for t in TIERS:
            ids = [x for x in self.tiers[t] if x in by_id]
            self.tiers[t] = ids
            used.update(ids)
            row = ctk.CTkFrame(self.rows_host, fg_color=P["surface"], corner_radius=14, border_width=2,
                               border_color=P["border"])
            row.pack(fill="x", pady=5)
            ctk.CTkLabel(row, text=t, fg_color=TIER_COLORS[t], text_color="#1a1206", corner_radius=10, width=70,
                         font=ctk.CTkFont(size=30, weight="bold")).pack(side="left", fill="y", padx=8, pady=8)
            zone = ctk.CTkFrame(row, fg_color="transparent", height=104)
            zone.pack(side="left", fill="both", expand=True, padx=(0, 8), pady=6)
            ths = [self.thumb(zone, by_id[x]) for x in ids]
            zone.bind("<Configure>", lambda e, ws=ths: reflow(ws, e.width, 6))
            self.zones[t], self.thumbs[t] = row, ths
        pool = ctk.CTkFrame(self.pool_host, fg_color=P["surface"], corner_radius=14, border_width=2,
                            border_color=P["border"])
        pool.pack(fill="x")
        head = ctk.CTkFrame(pool, fg_color="transparent")
        head.pack(fill="x", padx=14, pady=(12, 6))
        section(head, "Sem classificação", 15).pack(side="left")
        q = entry(head, "Filtrar por nome...", width=200)
        q.pack(side="right")
        q.insert(0, self.query)
        q.bind("<KeyRelease>", lambda e, q=q: self.set_query(q.get()), add="+")
        free = [i for i in self.app.items if i["id"] not in used and self.query.lower() in i["title"].lower()]
        pz = ctk.CTkFrame(pool, fg_color="transparent", height=104)
        pz.pack(fill="x", padx=14, pady=(0, 12))
        ths = [self.thumb(pz, it) for it in free[:80]]
        pz.bind("<Configure>", lambda e, ws=ths: reflow(ws, e.width, 6))
        self.zones["pool"], self.thumbs["pool"] = pool, ths

    def set_query(self, text):
        self.query = text.strip()
        self.render()

    # ---- arrastar e soltar ----
    def drag_start(self, e, it):
        self.drag = {"it": it, "ghost": None}

    def drag_move(self, e):
        d = self.drag
        if not d:
            return
        if d["ghost"] is None:
            d["ghost"] = ctk.CTkLabel(self, text="", image=self.app.cover(d["it"], 64, 90))
        gx, gy = e.x_root - self.winfo_rootx(), e.y_root - self.winfo_rooty()
        d["ghost"].place(x=lw(gx) - 32, y=lw(gy) - 45)
        d["ghost"].lift()
        self.highlight(self.hit(e.x_root, e.y_root))

    def drag_end(self, e):
        d, self.drag = self.drag, None
        if not d:
            return
        moved = d["ghost"] is not None
        if moved:
            d["ghost"].destroy()
        key = self.hit(e.x_root, e.y_root)
        self.highlight(None)
        if not moved:
            self.app.open_detail(d["it"])
        elif key is not None:
            self.move(d["it"], key, e.x_root)

    def hit(self, xr, yr):
        for key, z in self.zones.items():
            x0, y0 = z.winfo_rootx(), z.winfo_rooty()
            if x0 <= xr <= x0 + z.winfo_width() and y0 <= yr <= y0 + z.winfo_height():
                return key
        return None

    def highlight(self, key):
        for k, z in self.zones.items():
            z.configure(border_color=P["accent"] if k == key else P["border"])

    def move(self, it, key, xr):
        for t in TIERS:
            if it["id"] in self.tiers[t]:
                self.tiers[t].remove(it["id"])
        if key in TIERS:
            idx = sum(1 for th in self.thumbs.get(key, []) if th.winfo_rootx() + th.winfo_width() / 2 < xr)
            self.tiers[key].insert(min(idx, len(self.tiers[key])), it["id"])
        save_profile(self.app.profile)
        self.render()

    def clear_all(self):
        if messagebox.askyesno("Limpar tier list", "Tirar todas as capas das linhas?", parent=self.app):
            for t in TIERS:
                self.tiers[t] = []
            save_profile(self.app.profile)
            self.render()

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
    MAXW = 1500
    _title, _note, _tiles = ProfilePage._title, ProfilePage._note, ProfilePage._tiles

    def __init__(self, app):
        super().__init__(app, "Listas")
        self.names = sorted({n for i in app.items for n in i["lists"]}, key=str.lower)
        self.members = {n: [i for i in app.items if n in i["lists"]] for n in self.names}

    def layout(self, avail):
        app = self.app
        pad = max(14, int((avail - self.MAXW) // 2)) + 8
        W = int(avail - 2 * pad)
        out, y = [], 8

        def tier_draw(hov):
            img = Image.new("RGBA", (130 * K, 36 * K), (0, 0, 0, 0))
            draw_btn(img, (0, 0, 130, 36), "Tier list", P["accent_hover"] if hov else P["accent"], "#ffffff",
                     ("star", "#ffffff"))
            return img
        out.append(Blk("tier", pad + W - 130, y, 130, 36, tier_draw, [(0, 0, 130, 36, "go")],
                       lambda n: app.open_sub(TierPage)))
        y += 44
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
            ctk.CTkButton(grid, text=name, width=118, height=58, corner_radius=12, fg_color=th["bg"],
                          hover_color=th["surface2"], text_color=th["text"], border_width=3 if on else 1,
                          border_color=th["accent"] if on else th["border"],
                          font=ctk.CTkFont(size=13, weight="bold" if on else "normal"),
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
                          ("preview", "Prévia ao passar o mouse nas capas")):
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
        self.note(f, "Ctrl+N nova leitura  •  Ctrl+F buscar na biblioteca  •  Ctrl+1 a 5 trocar de tela  •  "
                     "Esc voltar", (0, 14))

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
                          command=lambda nm=name: self.cycle_label(nm)).pack(side="left")
            ctk.CTkLabel(row, text=name, text_color=P["text"], font=ctk.CTkFont(size=13, weight="bold")).pack(
                side="left", padx=10)
            ctk.CTkLabel(row, text=f"{n} leituras", text_color=P["muted"], font=ctk.CTkFont(size=11)).pack(side="left")
            ghost_button(row, "", lambda nm=name: self.delete_label(nm), image=icon("close", 12), width=30,
                         height=28).pack(side="right")

    def cycle_label(self, name):
        d = self.app.profile.setdefault("labels", {})
        cur = d.get(name)
        nxt = LABEL_COLORS[(LABEL_COLORS.index(cur) + 1) % len(LABEL_COLORS)] if cur in LABEL_COLORS else LABEL_COLORS[0]
        d[name] = nxt
        save_profile(self.app.profile)
        self.fill_labels()

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
        self.reload()

    def set_accent(self, c):
        S["accent"] = c
        save_settings()
        self.reload()

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
            for d, n in ((covers_dir(), "covers"), (profile_dir(), "profile")):
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


# ---------- app ----------
NAV = [("profile", "Perfil", "user"), ("library", "Biblioteca", "library"), ("lists", "Listas", "list"),
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
        self.page, self.cur, self.back = None, "profile", None
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
        for i, (key, _l, _i) in enumerate(NAV, 1):
            self.bind(f"<Control-Key-{i}>", lambda e, k=key: self.nav(k))
        self.after(300, self._set_icon)
        self._bind_wheel()
        splash_step(splash, 0.55)
        self.build()
        splash_step(splash, 0.8)
        self.nav("profile")
        self.after(1500, lambda: self.check_badges(True))
        splash_step(splash, 1.0)
        self._finish_splash(splash)

    # --- estrutura geral ---
    def build(self):
        for w in self.winfo_children():
            w.destroy()
        self.page, self.lib_shown, self._side_state = None, False, None
        self.cache, self._lib_dirty = {}, True
        self.configure(fg_color=P["bg"])
        self.build_side()
        self.main = ctk.CTkFrame(self, fg_color=P["bg"], corner_radius=0)
        self.main.pack(side="left", fill="both", expand=True)
        self.build_lib()
        self.fab = NoFab()
        self.after(30, self.apply_sidebar)

    def rebuild(self):
        self.build()

    # --- menu lateral ---
    def build_side(self):
        self.side = ctk.CTkFrame(self, fg_color=P["side"], corner_radius=0, width=SIDE_OPEN)
        self.side.pack(side="left", fill="y")
        self.side.pack_propagate(False)
        brand = ctk.CTkFrame(self.side, fg_color="transparent")
        brand.pack(fill="x", padx=18, pady=(24, 18))
        ctk.CTkFrame(brand, width=3, height=24, fg_color=P["accent"], corner_radius=0).pack(side="left", padx=(0, 10))
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
        Tip(self.collapse_btn, lambda: "Expandir menu" if self._side_state else "")
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

    def apply_sidebar(self):
        c = self.want_collapsed()
        if c == self._side_state:
            return
        self._side_state = c
        self.side.configure(width=SIDE_CLOSED if c else SIDE_OPEN)
        self.brand_lbl.configure(text="LF" if c else "LEITURA FODA")
        self.add_btn.configure(text="+" if c else "+  Nova leitura",
                               font=ctk.CTkFont(size=24 if c else 14, weight="bold"))
        for mark, btn, label, ic in self.nav_btns.values():
            btn.configure(text="" if c else label, anchor="center" if c else "w")
        self.collapse_btn.configure(text="" if c else "Recolher menu", image=icon("expand" if c else "collapse", 20),
                                    anchor="center" if c else "w")
        if c:
            self.u_txt.pack_forget()
        else:
            self.u_txt.pack(side="left", padx=10)

    def toggle_side(self):
        S["collapsed"] = not S.get("collapsed", False)
        save_settings()
        self._side_state = None
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
        cls = {"profile": ProfilePage, "lists": ListsPage, "stats": StatsPage, "settings": SettingsPage}[name]
        ent = self.cache.get(name)
        if ent is not None and ent[1] == DATA["v"] and ent[0].winfo_exists():
            self.page = ent[0]
            self.page.pack(fill="both", expand=True)
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
        self.nav(self.back or "profile")

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
        self.tool.pack(fill="x", padx=28, pady=6)
        sbox = ctk.CTkFrame(self.tool, fg_color=P["surface"], corner_radius=10, border_width=1,
                            border_color=P["border"])
        ctk.CTkLabel(sbox, text="", image=icon("search", 16), width=28).pack(side="left", padx=(8, 0))
        self.search_entry = ctk.CTkEntry(sbox, placeholder_text="Buscar por nome...", fg_color="transparent",
                                         border_width=0, height=36, width=190, text_color=P["text"])
        self.search_entry.pack(side="left", padx=(0, 6), pady=1)
        self.search_entry.bind("<KeyRelease>", lambda e: self.refresh_soon(), add="+")
        tmenu = self.build_type_filter(self.tool)
        self.tag_menu = menu(self.tool, ["Todos os gêneros"], lambda _: self.refresh(), 150,
                             variable=self.v_tag, height=38)
        smenu = menu(self.tool, SORTS, lambda _: self.refresh(), 170, variable=self.v_sort, height=38)
        fav = toggle_chip(self.tool, " Favoritos", self.v_fav, self.refresh, ic="heart")
        self.list_menu = menu(self.tool, ["Todas as listas"], lambda _: self.refresh(), 150,
                              variable=self.v_list, height=38)
        stall = toggle_chip(self.tool, " Paradas", self.v_stall, self.refresh, ic="clock")
        self.label_menu = menu(self.tool, ["Todas as etiquetas"], lambda _: self.refresh(), 160,
                               variable=self.v_label, height=38)
        self.tool_widgets = [sbox, tmenu, self.tag_menu, self.list_menu, self.label_menu, smenu, fav, stall]

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
        self.scroll.pack(fill="both", expand=True, padx=18, pady=(0, 14))
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
        reflow(self.tool_widgets, wp - px(60))
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
        if changed:
            pr["badge_known"] = sorted(known)
            save_profile(pr)
        if new and not quiet:
            self._badge_q = getattr(self, "_badge_q", []) + new
            if getattr(self, "_badge_w", None) is None:
                self._badge_next()

    def _badge_next(self):
        q = getattr(self, "_badge_q", [])
        if not q:
            self._badge_w = None
            return
        b = q.pop(0)
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
        avail = max(200, int(lw(self.scroll.winfo_width())) - 12)
        view = self.v_view.get()
        if view == "Lista":
            return 1, avail
        if view == "Prateleiras":
            return 1, 150
        lo, hi = (MIN_POSTER, MAX_POSTER) if view == "Pôster" else (MIN_CARD, MAX_CARD)
        cols = max(1, avail // (lo + 16))
        cw = min(hi, avail // cols - 16)
        return cols, max(150, cw // 10 * 10)

    def _on_resize(self, e):
        if e.widget is self:
            if getattr(self, "fab", None) is not None:
                self.fab.reposition()
            if self._after:
                self.after_cancel(self._after)
            self._after = self.after(120, self._relayout)

    def _relayout(self):
        self.apply_sidebar()
        if self.cur == "library" and self.page is None and self.lib_shown:
            self.layout()
            if self.grid_params() != (self.cols, self.card_w):
                self.refresh()

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
