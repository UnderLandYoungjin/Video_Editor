"""
VideoTextEditor V2

[영상]
- 영상 드래그&드롭 / 열기
- 다른 영상 파일의 원하는 구간만 잘라서 현재 위치에 삽입 또는 맨 뒤에 추가
- 현재 위치에서 자르기(분할), 구간 삭제, 구간 순서 이동, 구간 범위 수정

[그리기]
- 글자 (프리셋, 시스템/외부 폰트, 외곽선, 그림자, 배경 박스)
- 사각형 / 원 / 화살표 : 미리보기 화면에서 드래그로 그리기
- 모자이크 영역 (개인정보·QR 가리기)
- 항목별 표시 구간, 페이드 인/아웃, 레이어 순서

[기타]
- 타임라인 확대/축소 (Ctrl+휠), 단축키 이동
- 실행 취소 / 다시 실행
- 프로젝트 저장 / 불러오기 (.vte.json)
- 원본 소리 볼륨, 배경음악 추가
- 현재 화면 PNG 저장 (글자·도형·모자이크 포함)
- MP4 내보내기 (화질, 해상도, 시작/끝 페이드)

Python 3.12.3 / PySide6 / Pillow / imageio-ffmpeg (ffmpeg 별도 설치 불필요)
"""
import copy
import io
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
import zlib
from dataclasses import asdict, dataclass, field, fields, replace
from functools import lru_cache

import imageio_ffmpeg
from PIL import Image, ImageDraw, ImageFilter, ImageFont
from PySide6.QtCore import QPointF, QRectF, QSizeF, Qt, QThread, QTimer, QUrl, Signal
from PySide6.QtGui import (QBrush, QColor, QFont, QFontMetrics, QImage, QKeySequence,
                           QPainter, QPen, QPixmap, QShortcut)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtMultimediaWidgets import QGraphicsVideoItem, QVideoWidget
from PySide6.QtWidgets import (QApplication, QButtonGroup, QCheckBox, QColorDialog, QComboBox,
                               QCompleter, QDialog, QDialogButtonBox, QDoubleSpinBox,
                               QFileDialog, QFrame, QGraphicsItem, QGraphicsPixmapItem,
                               QGraphicsRectItem, QGraphicsScene, QGraphicsSimpleTextItem,
                               QGraphicsView, QGridLayout, QGroupBox, QHBoxLayout, QLabel,
                               QLineEdit, QListWidget, QListWidgetItem, QMainWindow, QMessageBox,
                               QPlainTextEdit, QProgressBar, QPushButton, QScrollArea, QSlider,
                               QSpinBox, QStackedWidget, QToolButton, QVBoxLayout, QWidget)

APP_TITLE = "VideoTextEditor V2"
FFMPEG = imageio_ffmpeg.get_ffmpeg_exe()
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
VIDEO_FILTER = "영상 파일 (*.mp4 *.mov *.avi *.mkv *.wmv *.m4v *.webm *.flv *.ts *.mts);;모든 파일 (*.*)"
AUDIO_FILTER = "오디오/영상 파일 (*.mp3 *.wav *.m4a *.aac *.flac *.ogg *.mp4 *.mov *.mkv);;모든 파일 (*.*)"
PROJECT_FILTER = "VideoTextEditor 프로젝트 (*.vte.json *.json)"

KIND_LABEL = {"text": "글자", "rect": "사각형", "ellipse": "원", "arrow": "화살표", "mosaic": "모자이크"}
KIND_COLOR = {"text": QColor(70, 125, 215), "rect": QColor(215, 70, 70), "ellipse": QColor(150, 90, 210),
              "arrow": QColor(225, 130, 30), "mosaic": QColor(110, 110, 120)}
TOOLS = [("select", "🖱 선택/이동 (V)"), ("text", "T 글자 (T)"), ("rect", "▭ 사각형 (R)"),
         ("ellipse", "◯ 원 (E)"), ("arrow", "➚ 화살표 (A)"), ("mosaic", "▦ 모자이크 (M)")]


# ─────────────────────────────────────────────────────────────
# 시간 유틸
# ─────────────────────────────────────────────────────────────
def fmt_time(sec: float) -> str:
    ms = int(round(max(0.0, sec) * 1000))
    h, rem = divmod(ms, 3_600_000)
    m, rem = divmod(rem, 60_000)
    s, ms = divmod(rem, 1000)
    if h:
        return f"{h}:{m:02d}:{s:02d}.{ms:03d}"
    return f"{m:02d}:{s:02d}.{ms:03d}"


def fmt_short(sec: float, step: float = 1.0) -> str:
    if step < 1:
        m, s = divmod(sec, 60)
        return f"{int(m)}:{s:04.1f}"
    sec = int(round(sec))
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def parse_time(text: str) -> float:
    """'83.5', '1:23.5', '0:01:23' 형식 모두 허용"""
    text = text.strip().replace("：", ":")
    if not text:
        raise ValueError("empty")
    parts = text.split(":")
    if len(parts) > 3:
        raise ValueError("format")
    total = 0.0
    for p in parts:
        total = total * 60 + float(p)
    return total


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


# ─────────────────────────────────────────────────────────────
# 미디어 정보 (ffmpeg -i 출력 파싱)
# ─────────────────────────────────────────────────────────────
@dataclass
class MediaInfo:
    path: str
    width: int
    height: int
    duration: float
    fps: float
    has_video: bool
    has_audio: bool


_probe_cache: dict[str, MediaInfo] = {}


def probe_media(path: str) -> MediaInfo:
    key = os.path.abspath(path)
    if key in _probe_cache:
        return _probe_cache[key]
    r = subprocess.run([FFMPEG, "-hide_banner", "-i", path],
                       capture_output=True, creationflags=NO_WINDOW)
    err = r.stderr.decode("utf-8", errors="ignore")
    if "Duration:" not in err and "Stream #" not in err:
        raise RuntimeError("미디어 파일을 읽을 수 없습니다.")

    duration = 0.0
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", err)
    if m:
        duration = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))

    lines = err.splitlines()
    vline = next((ln for ln in lines if "Stream #" in ln and "Video:" in ln
                  and "attached pic" not in ln), None)
    w = h = 0
    fps = 30.0
    if vline:
        m = re.search(r",\s*(\d{2,5})x(\d{2,5})", vline)
        if m:
            w, h = int(m.group(1)), int(m.group(2))
        m = re.search(r"([\d.]+)\s*fps", vline) or re.search(r"([\d.]+)\s*tbr", vline)
        if m:
            try:
                fps = float(m.group(1)) or 30.0
            except ValueError:
                pass
        if fps > 120:
            fps = 30.0
        rot = 0
        m = re.search(r"rotation of\s*(-?[\d.]+)\s*degrees", err) or re.search(r"rotate\s*:\s*(-?\d+)", err)
        if m:
            rot = int(round(float(m.group(1))))
        if abs(rot) % 180 == 90:
            w, h = h, w
    has_audio = any("Stream #" in ln and "Audio:" in ln for ln in lines)
    info = MediaInfo(path, w, h, duration, fps, bool(vline and w and h), has_audio)
    _probe_cache[key] = info
    return info


def probe_video(path: str) -> MediaInfo:
    info = probe_media(path)
    if not info.has_video:
        raise RuntimeError("영상 스트림을 찾을 수 없습니다.\n지원되지 않는 파일일 수 있습니다.")
    if info.duration <= 0:
        raise RuntimeError("영상 길이를 읽을 수 없습니다.")
    return info


def grab_frame(path: str, src_t: float) -> Image.Image | None:
    r = subprocess.run([FFMPEG, "-hide_banner", "-loglevel", "error", "-ss", f"{max(0, src_t):.3f}",
                        "-i", path, "-frames:v", "1", "-f", "image2pipe", "-vcodec", "png", "-"],
                       capture_output=True, creationflags=NO_WINDOW)
    if not r.stdout:
        return None
    try:
        return Image.open(io.BytesIO(r.stdout)).convert("RGB")
    except Exception:
        return None


# ─────────────────────────────────────────────────────────────
# 폰트
# ─────────────────────────────────────────────────────────────
KOREAN_HINTS = ("malgun", "맑은", "nanum", "나눔", "gmarket", "bm", "pretendard", "noto sans kr",
                "notosanskr", "noto serif kr", "notosanscjk", "gulim", "batang", "dotum", "gungsuh",
                "jalnan", "s-core", "spoqa", "kopub", "binggrae", "black han", "do hyeon", "jua",
                "sunflower", "gothic a1", "cafe24", "applesdgothic", "applemyungjo", "hancom", "함초롬")


def _font_dirs() -> list[str]:
    dirs = []
    if os.name == "nt":
        dirs.append(os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts"))
        la = os.environ.get("LOCALAPPDATA")
        if la:
            dirs.append(os.path.join(la, "Microsoft", "Windows", "Fonts"))
    elif sys.platform == "darwin":
        dirs += ["/System/Library/Fonts", "/Library/Fonts", os.path.expanduser("~/Library/Fonts")]
    else:
        dirs += ["/usr/share/fonts", "/usr/local/share/fonts",
                 os.path.expanduser("~/.fonts"), os.path.expanduser("~/.local/share/fonts")]
    return [d for d in dirs if os.path.isdir(d)]


def font_display_name(path: str) -> str:
    try:
        fam, style = ImageFont.truetype(path, 12).getname()
        fam = fam or os.path.basename(path)
        if style and style.lower() not in ("regular", "normal"):
            return f"{fam} {style}"
        return fam
    except Exception:
        return ""


def scan_fonts() -> list[tuple[str, str]]:
    found: dict[str, str] = {}
    for d in _font_dirs():
        for root, _, files in os.walk(d):
            for fn in files:
                if not fn.lower().endswith((".ttf", ".otf", ".ttc")):
                    continue
                p = os.path.join(root, fn)
                name = font_display_name(p)
                if name and name not in found:
                    found[name] = p

    def sort_key(n):
        low = (n + " " + os.path.basename(found[n])).lower()
        return (0 if any(k in low for k in KOREAN_HINTS) else 1, n.lower())

    return [(n, found[n]) for n in sorted(found, key=sort_key)]


def pick_default_font(fonts: list[tuple[str, str]]) -> str:
    wanted = ("malgunbd.ttf", "malgun.ttf", "nanumgothicbold.ttf", "nanumgothic.ttf",
              "applesdgothicneo.ttc", "notosanscjk-bold.ttc", "notosanscjk-regular.ttc")
    by_file = {os.path.basename(p).lower(): p for _, p in fonts}
    for w in wanted:
        if w in by_file:
            return by_file[w]
    return fonts[0][1] if fonts else ""


@lru_cache(maxsize=64)
def load_font(path: str, size: int):
    try:
        if path:
            return ImageFont.truetype(path, size)
    except Exception:
        pass
    try:
        return ImageFont.load_default(size)
    except TypeError:
        return ImageFont.load_default()


# ─────────────────────────────────────────────────────────────
# 데이터 모델
# ─────────────────────────────────────────────────────────────
@dataclass
class Clip:
    path: str
    src_in: float
    src_out: float
    id: str = field(default_factory=lambda: uuid.uuid4().hex)

    @property
    def duration(self) -> float:
        return max(0.0, self.src_out - self.src_in)


@dataclass
class OverlayItem:
    kind: str = "text"            # text / rect / ellipse / arrow / mosaic
    start: float = 0.0            # 타임라인 기준 시간(초)
    end: float = 3.0
    fade_in: float = 0.0
    fade_out: float = 0.0
    # 글자
    text: str = "텍스트를 입력하세요"
    font_path: str = ""
    font_size: int = 72
    color: tuple = (255, 255, 255, 255)
    stroke_color: tuple = (0, 0, 0, 255)
    stroke_width: int = 6
    shadow: bool = True
    shadow_color: tuple = (0, 0, 0, 170)
    box: bool = False
    box_color: tuple = (0, 0, 0, 160)
    line_spacing: int = 10
    x: float = 0.5                # 글자 중심 (화면 비율 0~1)
    y: float = 0.85
    # 도형 / 모자이크 (화면 비율 좌표)
    x1: float = 0.35
    y1: float = 0.35
    x2: float = 0.65
    y2: float = 0.65
    line_color: tuple = (255, 50, 50, 255)
    line_width: int = 6
    fill: bool = False
    fill_color: tuple = (255, 50, 50, 60)
    radius: int = 0
    mosaic_size: int = 20
    id: str = field(default_factory=lambda: uuid.uuid4().hex)


_ITEM_FIELDS = {f.name for f in fields(OverlayItem)}
_CLIP_FIELDS = {f.name for f in fields(Clip)}


def item_from_dict(d: dict) -> OverlayItem:
    kw = {k: (tuple(v) if isinstance(v, list) else v) for k, v in d.items() if k in _ITEM_FIELDS}
    return OverlayItem(**kw)


def clip_from_dict(d: dict) -> Clip:
    return Clip(**{k: v for k, v in d.items() if k in _CLIP_FIELDS})


def normalize_rect(it: OverlayItem):
    it.x1, it.x2 = sorted((it.x1, it.x2))
    it.y1, it.y2 = sorted((it.y1, it.y2))


def rect_px(it: OverlayItem, w: int, h: int):
    l, r = sorted((it.x1 * w, it.x2 * w))
    t, b = sorted((it.y1 * h, it.y2 * h))
    return l, t, r, b


def item_name(it: OverlayItem) -> str:
    if it.kind == "text":
        first = (it.text.strip().splitlines() or ["(빈 글자)"])[0]
        return first[:18] + ("…" if len(first) > 18 else "")
    return KIND_LABEL.get(it.kind, it.kind)


PRESETS = {
    "기본 · 흰 글자 + 검정 외곽선": dict(color=(255, 255, 255, 255), stroke_color=(0, 0, 0, 255),
                                 stroke_ratio=0.08, shadow=True, shadow_color=(0, 0, 0, 170), box=False),
    "유튜브 · 노랑 강조": dict(color=(255, 222, 0, 255), stroke_color=(0, 0, 0, 255),
                          stroke_ratio=0.11, shadow=True, shadow_color=(0, 0, 0, 200), box=False),
    "자막 · 반투명 검정 박스": dict(color=(255, 255, 255, 255), stroke_color=(0, 0, 0, 255),
                              stroke_ratio=0.0, shadow=False, box=True, box_color=(0, 0, 0, 160)),
    "깔끔 · 흰 박스 + 검정 글자": dict(color=(25, 25, 25, 255), stroke_color=(0, 0, 0, 255),
                                stroke_ratio=0.0, shadow=False, box=True, box_color=(255, 255, 255, 230)),
    "핑크 팝": dict(color=(255, 92, 170, 255), stroke_color=(255, 255, 255, 255),
                  stroke_ratio=0.10, shadow=True, shadow_color=(90, 0, 50, 190), box=False),
    "네온 민트": dict(color=(190, 255, 240, 255), stroke_color=(0, 190, 160, 255),
                  stroke_ratio=0.05, shadow=True, shadow_color=(0, 255, 210, 230), box=False),
    "빈티지 · 크림 + 갈색": dict(color=(255, 240, 205, 255), stroke_color=(90, 50, 20, 255),
                           stroke_ratio=0.07, shadow=True, shadow_color=(40, 20, 5, 160), box=False),
    "레드 경고": dict(color=(255, 255, 255, 255), stroke_color=(200, 20, 30, 255),
                  stroke_ratio=0.10, shadow=True, shadow_color=(0, 0, 0, 180), box=False),
    "설명 라벨 · 파랑 박스": dict(color=(255, 255, 255, 255), stroke_color=(0, 0, 0, 255),
                            stroke_ratio=0.0, shadow=False, box=True, box_color=(30, 90, 200, 220)),
}


def apply_preset(item: OverlayItem, name: str):
    for k, v in PRESETS[name].items():
        if k == "stroke_ratio":
            item.stroke_width = int(round(item.font_size * v))
        else:
            setattr(item, k, v)


# ─────────────────────────────────────────────────────────────
# 렌더링 (미리보기와 내보내기가 같은 이미지를 사용)
# ─────────────────────────────────────────────────────────────
def _composite(base: Image.Image, layer: Image.Image, x: float, y: float):
    x, y = int(round(x)), int(round(y))
    if x < 0:
        if -x >= layer.width:
            return
        layer = layer.crop((-x, 0, layer.width, layer.height))
        x = 0
    if y < 0:
        if -y >= layer.height:
            return
        layer = layer.crop((0, -y, layer.width, layer.height))
        y = 0
    cw, ch = min(layer.width, base.width - x), min(layer.height, base.height - y)
    if cw <= 0 or ch <= 0:
        return
    if (cw, ch) != layer.size:
        layer = layer.crop((0, 0, cw, ch))
    base.alpha_composite(layer, dest=(x, y))


def _render_text(canvas: Image.Image, it: OverlayItem, w: int, h: int, s: float):
    cx, cy = it.x * w, it.y * h
    empty_bbox = (cx - 30, cy - 15, cx + 30, cy + 15)
    text = it.text.rstrip()
    if not text.strip():
        return empty_bbox
    size = max(4, int(round(it.font_size * s)))
    font = load_font(it.font_path, size)
    sw = max(0, int(round(it.stroke_width * s)))
    sp = int(round(it.line_spacing * s))

    measure = ImageDraw.Draw(Image.new("RGBA", (1, 1)))
    l, t, r, b = measure.multiline_textbbox((0, 0), text, font=font, spacing=sp,
                                            align="center", stroke_width=sw)
    tw, th = int(math.ceil(r - l)), int(math.ceil(b - t))
    if tw <= 0 or th <= 0:
        return empty_bbox
    left, top = cx - tw / 2, cy - th / 2
    bbox = [left, top, left + tw, top + th]

    if it.box:
        padx = int(size * 0.4) + sw
        pady = int(size * 0.25) + sw
        bw, bh = tw + padx * 2, th + pady * 2
        layer = Image.new("RGBA", (bw, bh), (0, 0, 0, 0))
        ImageDraw.Draw(layer).rounded_rectangle((0, 0, bw - 1, bh - 1), radius=int(min(bh / 2, size * 0.3)),
                                                fill=tuple(it.box_color))
        _composite(canvas, layer, left - padx, top - pady)
        bbox = [left - padx, top - pady, left - padx + bw, top - pady + bh]

    if it.shadow:
        off = max(2, int(size * 0.06))
        blur = max(1.5, size * 0.05)
        m = int(blur * 3) + 4
        sc = tuple(it.shadow_color)
        layer = Image.new("RGBA", (tw + m * 2, th + m * 2), sc[:3] + (0,))
        ImageDraw.Draw(layer).multiline_text((m - l, m - t), text, font=font, fill=sc, spacing=sp,
                                             align="center", stroke_width=sw, stroke_fill=sc)
        layer = layer.filter(ImageFilter.GaussianBlur(blur))
        _composite(canvas, layer, left - m + off, top - m + off)

    pad = 4
    layer = Image.new("RGBA", (tw + pad * 2, th + pad * 2), (0, 0, 0, 0))
    ImageDraw.Draw(layer).multiline_text((pad - l, pad - t), text, font=font, fill=tuple(it.color),
                                         spacing=sp, align="center", stroke_width=sw,
                                         stroke_fill=tuple(it.stroke_color))
    _composite(canvas, layer, left - pad, top - pad)
    return tuple(bbox)


def _render_shape(canvas: Image.Image, it: OverlayItem, w: int, h: int, s: float, preview: bool):
    d = ImageDraw.Draw(canvas)
    lw = max(1, int(round(it.line_width * s)))
    lc, fc = tuple(it.line_color), tuple(it.fill_color)

    if it.kind == "arrow":
        p1 = (it.x1 * w, it.y1 * h)
        p2 = (it.x2 * w, it.y2 * h)
        dx, dy = p2[0] - p1[0], p2[1] - p1[1]
        length = math.hypot(dx, dy)
        if length < 1:
            return (p1[0] - 5, p1[1] - 5, p1[0] + 5, p1[1] + 5)
        ux, uy = dx / length, dy / length
        head = min(max(lw * 3.5, 14 * s), length)
        half = head * 0.55
        bx, by = p2[0] - ux * head, p2[1] - uy * head
        px, py = -uy, ux
        tri = [p2, (bx + px * half, by + py * half), (bx - px * half, by - py * half)]
        end = (p2[0] - ux * head * 0.8, p2[1] - uy * head * 0.8)
        if length > head:
            d.line([p1, end], fill=lc, width=lw)
            r = lw / 2
            d.ellipse((p1[0] - r, p1[1] - r, p1[0] + r, p1[1] + r), fill=lc)
        d.polygon(tri, fill=lc)
        xs = [p1[0]] + [p[0] for p in tri]
        ys = [p1[1]] + [p[1] for p in tri]
        return (min(xs) - lw, min(ys) - lw, max(xs) + lw, max(ys) + lw)

    l, t, r, b = rect_px(it, w, h)
    r, b = max(r, l + 2), max(b, t + 2)
    box = (l, t, r, b)

    if it.kind == "mosaic":
        if preview:
            rw, rh = max(2, int(r - l)), max(2, int(b - t))
            layer = Image.new("RGBA", (rw, rh), (40, 40, 40, 120))
            ld = ImageDraw.Draw(layer)
            for i in range(-rh, rw, 14):
                ld.line([(i, rh), (i + rh, 0)], fill=(255, 255, 255, 80), width=2)
            ld.rectangle((0, 0, rw - 1, rh - 1), outline=(255, 255, 255, 220), width=2)
            try:
                ld.text((6, 4), "모자이크", font=load_font(_DEFAULT_FONT[0], 16), fill=(255, 255, 255, 230))
            except Exception:
                pass
            _composite(canvas, layer, l, t)
        return box

    if it.kind == "rect":
        rad = int(round(it.radius * s))
        if rad > 0:
            if it.fill:
                d.rounded_rectangle(box, radius=rad, fill=fc)
            d.rounded_rectangle(box, radius=rad, outline=lc, width=lw)
        else:
            if it.fill:
                d.rectangle(box, fill=fc)
            d.rectangle(box, outline=lc, width=lw)
    elif it.kind == "ellipse":
        if it.fill:
            d.ellipse(box, fill=fc)
        d.ellipse(box, outline=lc, width=lw)
    return box


_DEFAULT_FONT = [""]


def render_overlay(it: OverlayItem, w: int, h: int, scale: float = 1.0, preview: bool = True):
    """(RGBA 전체 프레임 이미지, 선택 영역 bbox) 반환"""
    canvas = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    if it.kind == "text":
        bbox = _render_text(canvas, it, w, h, scale)
    else:
        bbox = _render_shape(canvas, it, w, h, scale, preview)
    return canvas, bbox


def apply_mosaic_pil(img: Image.Image, it: OverlayItem, w: int, h: int, scale: float = 1.0):
    l, t, r, b = rect_px(it, w, h)
    l, t = int(clamp(l, 0, w)), int(clamp(t, 0, h))
    r, b = int(clamp(r, 0, w)), int(clamp(b, 0, h))
    if r - l < 2 or b - t < 2:
        return
    bs = max(2, int(round(it.mosaic_size * scale)))
    region = img.crop((l, t, r, b))
    small = region.resize((max(1, (r - l) // bs), max(1, (b - t) // bs)), Image.Resampling.BILINEAR)
    img.paste(small.resize((r - l, b - t), Image.Resampling.NEAREST), (l, t))


def pil_to_qpixmap(img: Image.Image) -> QPixmap:
    data = img.tobytes("raw", "RGBA")
    qimg = QImage(data, img.width, img.height, img.width * 4, QImage.Format.Format_RGBA8888).copy()
    return QPixmap.fromImage(qimg)


# ─────────────────────────────────────────────────────────────
# 내보내기 스레드
# ─────────────────────────────────────────────────────────────
class ExportWorker(QThread):
    progress = Signal(int)
    done = Signal(bool, str)

    def __init__(self, cmd: list[str], duration: float, tmpdir: str, out_path: str):
        super().__init__()
        self.cmd, self.duration, self.tmpdir, self.out_path = cmd, duration, tmpdir, out_path
        self._proc = None
        self._cancel = False

    def run(self):
        ok, msg = False, ""
        try:
            self._proc = subprocess.Popen(self.cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                          stdin=subprocess.DEVNULL, creationflags=NO_WINDOW)
            for raw in self._proc.stdout:
                line = raw.decode("utf-8", "ignore").strip()
                if line.startswith(("out_time_us=", "out_time_ms=")):
                    v = line.split("=", 1)[1]
                    if v.isdigit() and self.duration > 0:
                        self.progress.emit(min(99, int(int(v) / 1e6 / self.duration * 100)))
            self._proc.wait()
            err = self._proc.stderr.read().decode("utf-8", "ignore").strip()
            if self._cancel:
                msg = "내보내기가 취소되었습니다."
                try:
                    if os.path.exists(self.out_path):
                        os.remove(self.out_path)
                except OSError:
                    pass
            elif self._proc.returncode == 0:
                ok, msg = True, self.out_path
            else:
                msg = err[-2000:] or f"ffmpeg 오류 (code {self._proc.returncode})"
        except Exception as e:
            msg = str(e)
        finally:
            shutil.rmtree(self.tmpdir, ignore_errors=True)
        if ok:
            self.progress.emit(100)
        self.done.emit(ok, msg)

    def cancel(self):
        self._cancel = True
        if self._proc and self._proc.poll() is None:
            self._proc.terminate()


# ─────────────────────────────────────────────────────────────
# 미리보기 뷰
# ─────────────────────────────────────────────────────────────
class PreviewView(QGraphicsView):
    fileDropped = Signal(str)
    pressed = Signal(QPointF)
    moved = Signal(QPointF)
    released = Signal(QPointF)

    def __init__(self, scene):
        super().__init__(scene)
        self.setAcceptDrops(True)
        self.viewport().setAcceptDrops(True)
        self.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setBackgroundBrush(QColor(18, 18, 20))
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setMinimumSize(480, 270)
        self._dragging = False

    def fit(self):
        self.fitInView(self.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def resizeEvent(self, e):
        super().resizeEvent(e)
        self.fit()

    def showEvent(self, e):
        super().showEvent(e)
        self.fit()

    def wheelEvent(self, e):
        e.ignore()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._dragging = True
            self.pressed.emit(self.mapToScene(e.position().toPoint()))
            e.accept()
            return
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._dragging:
            self.moved.emit(self.mapToScene(e.position().toPoint()))
            e.accept()
            return
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        if self._dragging and e.button() == Qt.MouseButton.LeftButton:
            self._dragging = False
            self.released.emit(self.mapToScene(e.position().toPoint()))
            e.accept()
            return
        super().mouseReleaseEvent(e)

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
        else:
            e.ignore()

    def dragMoveEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
        else:
            e.ignore()

    def dropEvent(self, e):
        for url in e.mimeData().urls():
            p = url.toLocalFile()
            if p:
                self.fileDropped.emit(p)
                break
        e.acceptProposedAction()


# ─────────────────────────────────────────────────────────────
# 타임라인 (영상 구간 트랙 + 오버레이 트랙, Ctrl+휠 확대)
# ─────────────────────────────────────────────────────────────
class TimelineWidget(QWidget):
    seekRequested = Signal(float)
    itemSelected = Signal(str)
    M = 12
    RULER = 22
    CLIP_Y = 26
    CLIP_H = 28
    OV_Y = 62
    ROW_H = 18
    GAP = 3

    def __init__(self):
        super().__init__()
        self.setMinimumHeight(150)
        self.total = 0.0
        self.position = 0.0
        self.clips: list[tuple] = []          # (offset, duration, label, path)
        self.items: list[OverlayItem] = []
        self.selected_id = None
        self.zoom = 1.0
        self.view_start = 0.0
        self._rects = []
        self._scrub = False
        self.setToolTip("클릭/드래그: 이동 · Ctrl+휠: 확대/축소 · 휠: 좌우 스크롤")

    def visible_dur(self):
        return self.total / self.zoom if self.total > 0 else 0.0

    def _clamp_view(self):
        self.view_start = clamp(self.view_start, 0.0, max(0.0, self.total - self.visible_dur()))

    def set_data(self, total, clips, items, selected_id):
        self.total = max(0.0, total)
        self.clips = clips
        self.items = list(items)
        self.selected_id = selected_id
        self._clamp_view()
        self.update()

    def set_position(self, t, follow=False):
        self.position = t
        if follow and self.zoom > 1:
            vd = self.visible_dur()
            if t < self.view_start or t > self.view_start + vd:
                self.view_start = t - vd * 0.1
                self._clamp_view()
        self.update()

    def _x(self, t):
        vd = self.visible_dur()
        if vd <= 0:
            return self.M
        return self.M + (self.width() - 2 * self.M) * (t - self.view_start) / vd

    def _t(self, x):
        vd = self.visible_dur()
        if vd <= 0:
            return 0.0
        r = (x - self.M) / max(1, self.width() - 2 * self.M)
        return clamp(self.view_start + r * vd, 0.0, self.total)

    def wheelEvent(self, e):
        if self.total <= 0:
            return
        dy = e.angleDelta().y()
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            anchor = self._t(e.position().x())
            rel = (e.position().x() - self.M) / max(1, self.width() - 2 * self.M)
            self.zoom = clamp(self.zoom * (1.25 if dy > 0 else 0.8), 1.0, 300.0)
            self.view_start = anchor - rel * self.visible_dur()
        else:
            self.view_start -= (dy / 120) * self.visible_dur() * 0.1
        self._clamp_view()
        self.update()
        e.accept()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.fillRect(self.rect(), QColor(32, 33, 38))
        if self.total <= 0:
            p.setPen(QColor(150, 150, 150))
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "영상을 불러오면 타임라인이 표시됩니다")
            return
        vd = self.visible_dur()
        usable = self.width() - 2 * self.M

        # 눈금
        step = 3600.0
        for s in (0.1, 0.2, 0.5, 1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 900, 1800, 3600):
            if vd / s <= usable / 70:
                step = s
                break
        f = p.font()
        f.setPointSize(8)
        p.setFont(f)
        p.setPen(QColor(120, 120, 130))
        t = math.floor(self.view_start / step) * step
        while t <= self.view_start + vd + 1e-6:
            x = self._x(t)
            if x >= self.M - 1:
                p.drawLine(QPointF(x, self.RULER - 7), QPointF(x, self.RULER))
                p.drawText(QPointF(x + 3, 13), fmt_short(t, step))
            t += step
        p.drawLine(QPointF(self.M, self.RULER), QPointF(self.width() - self.M, self.RULER))

        # 영상 구간 트랙
        f.setPointSize(9)
        p.setFont(f)
        fm = QFontMetrics(f)
        n = len(self.clips)
        for i, (off, dur, label, path) in enumerate(self.clips):
            x1, x2 = self._x(off), self._x(off + dur)
            if x2 < 0 or x1 > self.width():
                continue
            rect = QRectF(x1 + 1, self.CLIP_Y, max(2.0, x2 - x1 - 2), self.CLIP_H)
            hue = zlib.crc32(os.path.basename(path).encode("utf-8")) % 360
            cur = off <= self.position < off + dur or (i == n - 1 and self.position >= off + dur)
            p.setBrush(QColor.fromHsv(hue, 110, 150))
            p.setPen(QPen(QColor(255, 255, 255), 2) if cur else QPen(QColor(20, 20, 20), 1))
            p.drawRoundedRect(rect, 4, 4)
            p.setPen(QColor(255, 255, 255))
            p.drawText(rect.adjusted(6, 0, -4, 0), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                       fm.elidedText(f"🎞 {label}  ({fmt_short(dur, 0.5 if dur < 60 else 1)})",
                                     Qt.TextElideMode.ElideRight, int(max(0, rect.width() - 10))))

        # 오버레이 트랙
        n_rows = max(1, (self.height() - self.OV_Y - 4) // (self.ROW_H + self.GAP))
        row_ends: list[float] = []
        self._rects = []
        f.setPointSize(8)
        p.setFont(f)
        fm = QFontMetrics(f)
        for it in sorted(self.items, key=lambda i: i.start):
            row = next((i for i, end in enumerate(row_ends) if end <= it.start), None)
            if row is None:
                row = len(row_ends)
                row_ends.append(it.end)
            else:
                row_ends[row] = it.end
            row = min(row, n_rows - 1)
            x1 = self._x(it.start)
            x2 = max(x1 + 4, self._x(it.end))
            rect = QRectF(x1, self.OV_Y + row * (self.ROW_H + self.GAP), x2 - x1, self.ROW_H)
            sel = it.id == self.selected_id
            p.setBrush(QColor(255, 175, 40) if sel else KIND_COLOR.get(it.kind, QColor(90, 90, 90)))
            p.setPen(QPen(QColor(255, 255, 255), 1.5) if sel else Qt.PenStyle.NoPen)
            p.drawRoundedRect(rect, 3, 3)
            p.setPen(QColor(20, 20, 20) if sel else QColor(255, 255, 255))
            label = f"{KIND_LABEL.get(it.kind, '')}: {item_name(it)}" if it.kind == "text" else item_name(it)
            p.drawText(rect.adjusted(4, 0, -2, 0), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                       fm.elidedText(label, Qt.TextElideMode.ElideRight, int(max(0, rect.width() - 6))))
            self._rects.append((rect, it.id))

        # 재생 위치
        x = self._x(self.position)
        p.setPen(QPen(QColor(255, 60, 60), 2))
        p.drawLine(QPointF(x, 0), QPointF(x, self.height()))
        p.setBrush(QColor(255, 60, 60))
        p.drawPolygon([QPointF(x - 6, 0), QPointF(x + 6, 0), QPointF(x, 8)])

        if self.zoom > 1.01:
            p.setPen(QColor(200, 200, 120))
            p.drawText(QRectF(0, 0, self.width() - 6, 14), Qt.AlignmentFlag.AlignRight, f"확대 x{self.zoom:.1f}")

    def mousePressEvent(self, e):
        if self.total <= 0:
            return
        pos = e.position()
        for rect, iid in reversed(self._rects):
            if rect.contains(pos):
                self.itemSelected.emit(iid)
                break
        self._scrub = True
        self.seekRequested.emit(self._t(pos.x()))

    def mouseMoveEvent(self, e):
        if self._scrub:
            self.seekRequested.emit(self._t(e.position().x()))

    def mouseReleaseEvent(self, e):
        self._scrub = False


# ─────────────────────────────────────────────────────────────
# 다른 영상의 구간 선택 대화상자
# ─────────────────────────────────────────────────────────────
class TrimDialog(QDialog):
    def __init__(self, parent, info: MediaInfo, src_in: float = 0.0, src_out: float | None = None,
                 title: str = "넣을 영상 구간 선택"):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.resize(960, 680)
        self.info = info
        self.duration = info.duration
        self._first = True

        v = QVBoxLayout(self)
        v.addWidget(QLabel(f"<b>{os.path.basename(info.path)}</b> · {info.width}×{info.height} · "
                           f"{fmt_time(info.duration)}<br>재생하면서 넣을 부분의 시작/끝을 지정하세요."))
        self.video = QVideoWidget()
        self.video.setMinimumHeight(380)
        v.addWidget(self.video, 1)

        self.player = QMediaPlayer(self)
        self.audio = QAudioOutput(self)
        self.audio.setVolume(0.8)
        self.player.setAudioOutput(self.audio)
        self.player.setVideoOutput(self.video)

        self.slider = QSlider(Qt.Orientation.Horizontal)
        self.slider.setRange(0, int(self.duration * 1000))
        v.addWidget(self.slider)

        row = QHBoxLayout()
        self.btn_play = QPushButton("▶ 재생")
        self.btn_b1 = QPushButton("◀ 1초")
        self.btn_f1 = QPushButton("1초 ▶")
        self.lbl_time = QLabel("00:00.000")
        self.lbl_time.setStyleSheet("font-family:Consolas,monospace; font-size:14px; padding:0 8px;")
        for w in (self.btn_b1, self.btn_play, self.btn_f1, self.lbl_time):
            row.addWidget(w)
        row.addStretch(1)
        v.addLayout(row)

        g = QGridLayout()
        g.addWidget(QLabel("시작"), 0, 0)
        self.sp_in = self._spin()
        g.addWidget(self.sp_in, 0, 1)
        self.btn_in = QPushButton("[ 현재 위치를 시작으로")
        g.addWidget(self.btn_in, 0, 2)
        g.addWidget(QLabel("끝"), 1, 0)
        self.sp_out = self._spin()
        g.addWidget(self.sp_out, 1, 1)
        self.btn_out = QPushButton("] 현재 위치를 끝으로")
        g.addWidget(self.btn_out, 1, 2)
        self.lbl_len = QLabel()
        self.lbl_len.setStyleSheet("color:#2d6cdf; font-weight:bold;")
        g.addWidget(self.lbl_len, 0, 3, 2, 1)
        g.setColumnStretch(3, 1)
        v.addLayout(g)

        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        bb.button(QDialogButtonBox.StandardButton.Ok).setText("이 구간 넣기")
        bb.button(QDialogButtonBox.StandardButton.Cancel).setText("취소")
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        v.addWidget(bb)

        self.sp_in.setValue(src_in)
        self.sp_out.setValue(self.duration if src_out is None else src_out)
        self._update_len()

        self.player.positionChanged.connect(self._on_pos)
        self.player.mediaStatusChanged.connect(self._on_status)
        self.player.playbackStateChanged.connect(
            lambda _s: self.btn_play.setText("⏸ 일시정지" if self._playing() else "▶ 재생"))
        self.slider.sliderMoved.connect(lambda ms: self.player.setPosition(ms))
        self.slider.actionTriggered.connect(lambda _a: self.player.setPosition(self.slider.sliderPosition()))
        self.btn_play.clicked.connect(self.toggle)
        self.btn_b1.clicked.connect(lambda: self.player.setPosition(max(0, self.player.position() - 1000)))
        self.btn_f1.clicked.connect(lambda: self.player.setPosition(
            min(int(self.duration * 1000), self.player.position() + 1000)))
        self.btn_in.clicked.connect(lambda: self.sp_in.setValue(self.player.position() / 1000))
        self.btn_out.clicked.connect(lambda: self.sp_out.setValue(self.player.position() / 1000))
        self.sp_in.valueChanged.connect(self._update_len)
        self.sp_out.valueChanged.connect(self._update_len)
        QShortcut(QKeySequence(Qt.Key.Key_Space), self, activated=self.toggle)
        QShortcut(QKeySequence("["), self, activated=self.btn_in.click)
        QShortcut(QKeySequence("]"), self, activated=self.btn_out.click)

        self.player.setSource(QUrl.fromLocalFile(info.path))

    def _spin(self):
        s = QDoubleSpinBox()
        s.setDecimals(3)
        s.setSingleStep(0.1)
        s.setRange(0, max(0.001, self.duration))
        s.setSuffix(" 초")
        return s

    def _playing(self):
        return self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState

    def toggle(self):
        self.player.pause() if self._playing() else self.player.play()

    def _on_status(self, st):
        if st == QMediaPlayer.MediaStatus.LoadedMedia and self._first:
            self._first = False
            self.player.pause()
            self.player.setPosition(int(self.sp_in.value() * 1000))

    def _on_pos(self, ms):
        if not self.slider.isSliderDown():
            self.slider.blockSignals(True)
            self.slider.setValue(ms)
            self.slider.blockSignals(False)
        self.lbl_time.setText(f"{fmt_time(ms / 1000)} / {fmt_time(self.duration)}")

    def _update_len(self, *_):
        a, b = self.sp_in.value(), self.sp_out.value()
        self.lbl_len.setText(f"선택 구간: {fmt_time(a)} ~ {fmt_time(b)}   (길이 {max(0, b - a):.3f}초)")

    def values(self):
        return round(self.sp_in.value(), 3), round(self.sp_out.value(), 3)

    def accept(self):
        a, b = self.values()
        if b - a < 0.1:
            QMessageBox.warning(self, APP_TITLE, "끝 시간은 시작 시간보다 0.1초 이상 뒤여야 합니다.")
            return
        self.player.stop()
        super().accept()

    def reject(self):
        self.player.stop()
        super().reject()


# ─────────────────────────────────────────────────────────────
# 메인 윈도우
# ─────────────────────────────────────────────────────────────
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_TITLE)
        self.resize(1500, 920)
        self.setAcceptDrops(True)

        # 프로젝트 상태
        self.clips: list[Clip] = []
        self.items: list[OverlayItem] = []
        self.selected_id: str | None = None
        self.proj_w, self.proj_h, self.proj_fps = 1280, 720, 30.0
        self.bgm_path = ""
        self.bgm_volume = 0.3
        self.orig_volume = 1.0
        self.project_path = ""

        # 재생 상태
        self._t = 0.0
        self._cur_k = 0
        self._loaded_path: str | None = None
        self._pending: tuple | None = None
        self._want_play = False
        self._seek_guard = 0.0

        # 편집 상태
        self.tool = "select"
        self._drag: dict | None = None
        self._loading = False
        self.undo_stack: list = []
        self.redo_stack: list = []
        self._undo_key = None
        self._undo_time = 0.0
        self.overlay_gi: dict[str, QGraphicsPixmapItem] = {}
        self.overlay_bbox: dict[str, tuple] = {}
        self.export_worker: ExportWorker | None = None

        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            self.fonts = scan_fonts()
        finally:
            QApplication.restoreOverrideCursor()
        self.default_font = pick_default_font(self.fonts)
        _DEFAULT_FONT[0] = self.default_font

        # 플레이어
        self.player = QMediaPlayer(self)
        self.audio = QAudioOutput(self)
        self.player.setAudioOutput(self.audio)
        self.bgm_player = QMediaPlayer(self)
        self.bgm_audio = QAudioOutput(self)
        self.bgm_player.setAudioOutput(self.bgm_audio)
        try:
            self.bgm_player.setLoops(-1)
        except Exception:
            pass
        self.bgm_duration = 0.0

        # 미리보기 장면
        self.scene = QGraphicsScene(self)
        self.scene.setSceneRect(0, 0, 1280, 720)
        self.video_item = QGraphicsVideoItem()
        self.video_item.setSize(QSizeF(1280, 720))
        self.scene.addItem(self.video_item)
        self.player.setVideoOutput(self.video_item)
        self.placeholder = QGraphicsSimpleTextItem("🎬  영상 파일을 여기로 드래그하세요\n\n      (또는 [영상 열기] 버튼)")
        self.placeholder.setFont(QFont("Malgun Gothic", 30))
        self.placeholder.setBrush(QBrush(QColor(160, 160, 170)))
        br = self.placeholder.boundingRect()
        self.placeholder.setPos((1280 - br.width()) / 2, (720 - br.height()) / 2)
        self.scene.addItem(self.placeholder)

        pen = QPen(QColor(0, 200, 255), 1.5, Qt.PenStyle.DashLine)
        pen.setCosmetic(True)
        self.sel_rect = QGraphicsRectItem()
        self.sel_rect.setPen(pen)
        self.sel_rect.setZValue(5000)
        self.sel_rect.setVisible(False)
        self.scene.addItem(self.sel_rect)
        self.handles = []
        hpen = QPen(QColor(0, 150, 255), 1.5)
        hpen.setCosmetic(True)
        for _ in range(4):
            hnd = QGraphicsRectItem(-5, -5, 10, 10)
            hnd.setFlag(QGraphicsItem.GraphicsItemFlag.ItemIgnoresTransformations, True)
            hnd.setBrush(QBrush(QColor(255, 255, 255)))
            hnd.setPen(hpen)
            hnd.setZValue(5001)
            hnd.setVisible(False)
            self.scene.addItem(hnd)
            self.handles.append(hnd)

        self._refresh_timer = QTimer(self)
        self._refresh_timer.setSingleShot(True)
        self._refresh_timer.setInterval(25)
        self._refresh_timer.timeout.connect(self._refresh_selected_overlay)
        self._play_timer = QTimer(self)
        self._play_timer.setInterval(30)
        self._play_timer.timeout.connect(self._poll_position)

        self._build_ui()
        self._connect_signals()
        self._make_shortcuts()
        self._apply_volumes()
        self._load_item_to_editor(None)
        self._update_all()
        self.statusBar().showMessage(f"폰트 {len(self.fonts)}개 로드됨 · ffmpeg 준비 완료")

    # ════════════════════════════════════════════════════════
    # UI 구성
    # ════════════════════════════════════════════════════════
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        root = QHBoxLayout(central)
        root.setContentsMargins(8, 8, 8, 8)

        left = QVBoxLayout()
        top = QHBoxLayout()
        self.btn_new = QPushButton("📄 새로 만들기")
        self.btn_open = QPushButton("📂 영상 열기")
        self.btn_proj_open = QPushButton("📁 프로젝트 열기")
        self.btn_proj_save = QPushButton("💾 프로젝트 저장")
        self.btn_undo = QPushButton("↶ 실행취소")
        self.btn_redo = QPushButton("↷ 다시실행")
        self.btn_snap = QPushButton("📷 현재 화면 저장")
        for b in (self.btn_new, self.btn_open, self.btn_proj_open, self.btn_proj_save,
                  self.btn_undo, self.btn_redo, self.btn_snap):
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            top.addWidget(b)
        top.addStretch(1)
        left.addLayout(top)
        self.lbl_info = QLabel("영상을 드래그하거나 [영상 열기]를 누르세요.")
        self.lbl_info.setStyleSheet("color:#555;")
        left.addWidget(self.lbl_info)

        tools = QHBoxLayout()
        self.tool_group = QButtonGroup(self)
        self.tool_group.setExclusive(True)
        self.tool_btns = {}
        for i, (name, label) in enumerate(TOOLS):
            b = QToolButton()
            b.setText(label)
            b.setCheckable(True)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.setMinimumHeight(30)
            b.setStyleSheet("QToolButton{padding:3px 10px;} QToolButton:checked{background:#2d6cdf;color:white;"
                            "border-radius:4px;}")
            self.tool_group.addButton(b, i)
            self.tool_btns[name] = b
            tools.addWidget(b)
        self.tool_btns["select"].setChecked(True)
        self.lbl_tool_tip = QLabel()
        self.lbl_tool_tip.setStyleSheet("color:#2d6cdf;")
        tools.addWidget(self.lbl_tool_tip, 1)
        left.addLayout(tools)

        self.view = PreviewView(self.scene)
        left.addWidget(self.view, 1)
        self.timeline = TimelineWidget()
        left.addWidget(self.timeline)

        ctrl = QHBoxLayout()
        self.btn_home = QPushButton("⏮")
        self.btn_back5 = QPushButton("⏪ 5초")
        self.btn_back1 = QPushButton("◀ 1초")
        self.btn_prevf = QPushButton("◁ 프레임")
        self.btn_play = QPushButton("▶ 재생")
        self.btn_nextf = QPushButton("프레임 ▷")
        self.btn_fwd1 = QPushButton("1초 ▶")
        self.btn_fwd5 = QPushButton("5초 ⏩")
        self.btn_endk = QPushButton("⏭")
        self.ctrl_btns = (self.btn_home, self.btn_back5, self.btn_back1, self.btn_prevf, self.btn_play,
                          self.btn_nextf, self.btn_fwd1, self.btn_fwd5, self.btn_endk)
        for b in self.ctrl_btns:
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            ctrl.addWidget(b)
        self.btn_play.setMinimumWidth(90)
        self.lbl_time = QLabel("00:00.000 / 00:00.000")
        self.lbl_time.setStyleSheet("font-family:Consolas,monospace; font-size:14px; padding:0 8px;")
        ctrl.addWidget(self.lbl_time)
        self.ed_jump = QLineEdit()
        self.ed_jump.setPlaceholderText("시간 이동 (예: 1:23.5)")
        self.ed_jump.setFixedWidth(150)
        self.btn_jump = QPushButton("이동")
        self.btn_jump.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        ctrl.addWidget(self.ed_jump)
        ctrl.addWidget(self.btn_jump)
        ctrl.addStretch(1)
        ctrl.addWidget(QLabel("🔊"))
        self.sl_master = QSlider(Qt.Orientation.Horizontal)
        self.sl_master.setRange(0, 100)
        self.sl_master.setValue(80)
        self.sl_master.setFixedWidth(90)
        self.sl_master.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.sl_master.setToolTip("미리보기 듣기 볼륨 (내보내기에는 영향 없음)")
        ctrl.addWidget(self.sl_master)
        left.addLayout(ctrl)

        hint = QLabel("Space 재생 · ←/→ 1초 · Shift+←/→ 5초 · ,/. 프레임 · Home/End · S 자르기 · "
                      "[ / ] 선택 항목 시작/끝 · Del 항목 삭제 · Ctrl+D 복제 · Ctrl+Z/Y 실행취소/다시 · "
                      "Ctrl+S 저장 · Ctrl+E 내보내기 · V/T/R/E/A/M 도구")
        hint.setWordWrap(True)
        hint.setStyleSheet("color:#777; font-size:11px;")
        left.addWidget(hint)
        root.addLayout(left, 1)

        # ── 오른쪽 패널
        panel = QWidget()
        pv = QVBoxLayout(panel)
        pv.setContentsMargins(4, 0, 4, 0)

        gb_clip = QGroupBox("영상 구간 편집")
        cg = QGridLayout(gb_clip)
        self.lbl_clip = QLabel("-")
        self.lbl_clip.setWordWrap(True)
        self.lbl_clip.setStyleSheet("color:#333;")
        cg.addWidget(self.lbl_clip, 0, 0, 1, 2)
        self.btn_insert_clip = QPushButton("➕ 다른 영상 삽입 (현재 위치)")
        self.btn_append_clip = QPushButton("➕ 맨 뒤에 영상 추가")
        self.btn_split = QPushButton("✂ 현재 위치에서 자르기 (S)")
        self.btn_del_clip = QPushButton("🗑 현재 구간 삭제")
        self.btn_clip_left = QPushButton("◀ 구간 앞으로")
        self.btn_clip_right = QPushButton("구간 뒤로 ▶")
        self.btn_trim_clip = QPushButton("✏ 현재 구간 범위 수정")
        cg.addWidget(self.btn_insert_clip, 1, 0, 1, 2)
        cg.addWidget(self.btn_append_clip, 2, 0, 1, 2)
        cg.addWidget(self.btn_split, 3, 0)
        cg.addWidget(self.btn_del_clip, 3, 1)
        cg.addWidget(self.btn_clip_left, 4, 0)
        cg.addWidget(self.btn_clip_right, 4, 1)
        cg.addWidget(self.btn_trim_clip, 5, 0, 1, 2)
        pv.addWidget(gb_clip)

        gb_list = QGroupBox("글자 · 도형 목록 (아래쪽이 위에 그려짐)")
        lv = QVBoxLayout(gb_list)
        self.list_items = QListWidget()
        self.list_items.setMinimumHeight(130)
        lv.addWidget(self.list_items)
        row = QHBoxLayout()
        self.btn_add = QPushButton("➕ 글자")
        self.btn_dup = QPushButton("복제")
        self.btn_del = QPushButton("삭제")
        self.btn_up = QPushButton("▲")
        self.btn_down = QPushButton("▼")
        self.btn_up.setToolTip("뒤로 (아래 레이어)")
        self.btn_down.setToolTip("앞으로 (위 레이어)")
        for b, s in ((self.btn_add, 2), (self.btn_dup, 1), (self.btn_del, 1), (self.btn_up, 1), (self.btn_down, 1)):
            row.addWidget(b, s)
        lv.addLayout(row)
        pv.addWidget(gb_list)

        self.gb_edit = QGroupBox("선택 항목 편집")
        ev = QVBoxLayout(self.gb_edit)
        cg2 = QGridLayout()
        cg2.addWidget(QLabel("시작"), 0, 0)
        self.sp_start = self._time_spin()
        cg2.addWidget(self.sp_start, 0, 1)
        self.btn_set_start = QPushButton("[ 현재 위치")
        cg2.addWidget(self.btn_set_start, 0, 2)
        cg2.addWidget(QLabel("끝"), 1, 0)
        self.sp_end = self._time_spin()
        cg2.addWidget(self.sp_end, 1, 1)
        self.btn_set_end = QPushButton("] 현재 위치")
        cg2.addWidget(self.btn_set_end, 1, 2)
        cg2.addWidget(QLabel("페이드"), 2, 0)
        fr = QHBoxLayout()
        self.sp_fin = self._fade_spin("인 ")
        self.sp_fout = self._fade_spin("아웃 ")
        fr.addWidget(self.sp_fin)
        fr.addWidget(self.sp_fout)
        cg2.addLayout(fr, 2, 1, 1, 2)
        self.btn_goto_start = QPushButton("▶ 이 항목 시작 지점으로 이동")
        cg2.addWidget(self.btn_goto_start, 3, 0, 1, 3)
        ev.addLayout(cg2)

        self.stack = QStackedWidget()
        self.stack.addWidget(self._build_text_page())
        self.stack.addWidget(self._build_shape_page())
        self.stack.addWidget(self._build_mosaic_page())
        ev.addWidget(self.stack)
        pv.addWidget(self.gb_edit)

        gb_audio = QGroupBox("소리")
        ag = QGridLayout(gb_audio)
        ag.addWidget(QLabel("원본 소리"), 0, 0)
        self.sl_orig = QSlider(Qt.Orientation.Horizontal)
        self.sl_orig.setRange(0, 200)
        self.sl_orig.setValue(100)
        ag.addWidget(self.sl_orig, 0, 1)
        self.lbl_orig = QLabel("100%")
        ag.addWidget(self.lbl_orig, 0, 2)
        self.btn_bgm = QPushButton("🎵 배경음악 선택")
        self.btn_bgm_clear = QPushButton("제거")
        ag.addWidget(self.btn_bgm, 1, 0, 1, 2)
        ag.addWidget(self.btn_bgm_clear, 1, 2)
        self.lbl_bgm = QLabel("배경음악 없음")
        self.lbl_bgm.setStyleSheet("color:#666;")
        ag.addWidget(self.lbl_bgm, 2, 0, 1, 3)
        ag.addWidget(QLabel("배경음악"), 3, 0)
        self.sl_bgm = QSlider(Qt.Orientation.Horizontal)
        self.sl_bgm.setRange(0, 200)
        self.sl_bgm.setValue(30)
        ag.addWidget(self.sl_bgm, 3, 1)
        self.lbl_bgm_vol = QLabel("30%")
        ag.addWidget(self.lbl_bgm_vol, 3, 2)
        pv.addWidget(gb_audio)

        gb_exp = QGroupBox("내보내기")
        eg = QGridLayout(gb_exp)
        eg.addWidget(QLabel("화질"), 0, 0)
        self.cb_quality = QComboBox()
        self.cb_quality.addItem("고화질 (권장)", 18)
        self.cb_quality.addItem("표준", 23)
        self.cb_quality.addItem("용량 작게", 28)
        eg.addWidget(self.cb_quality, 0, 1)
        eg.addWidget(QLabel("해상도"), 1, 0)
        self.cb_res = QComboBox()
        self.cb_res.addItem("원본 (첫 영상 기준)", 0)
        self.cb_res.addItem("1080p", 1080)
        self.cb_res.addItem("720p", 720)
        self.cb_res.addItem("480p", 480)
        eg.addWidget(self.cb_res, 1, 1)
        self.chk_fade_all = QCheckBox("영상 시작/끝 페이드 (0.5초)")
        eg.addWidget(self.chk_fade_all, 2, 0, 1, 2)
        self.btn_export = QPushButton("🎬 MP4로 내보내기")
        self.btn_export.setMinimumHeight(42)
        self.btn_export.setStyleSheet("QPushButton{background:#2d6cdf;color:white;font-weight:bold;"
                                      "font-size:14px;border-radius:6px;}"
                                      "QPushButton:disabled{background:#9db5e6;}")
        eg.addWidget(self.btn_export, 3, 0, 1, 2)
        self.progress = QProgressBar()
        self.progress.setRange(0, 100)
        eg.addWidget(self.progress, 4, 0, 1, 2)
        pv.addWidget(gb_exp)
        pv.addStretch(1)

        scroll = QScrollArea()
        scroll.setWidget(panel)
        scroll.setWidgetResizable(True)
        scroll.setFixedWidth(420)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        root.addWidget(scroll)

        self.color_btns = {"color": self.btn_color, "stroke_color": self.btn_stroke_color,
                           "shadow_color": self.btn_shadow_color, "box_color": self.btn_box_color,
                           "line_color": self.btn_line_color, "fill_color": self.btn_fill_color}

    def _build_text_page(self):
        w = QWidget()
        g = QGridLayout(w)
        g.setContentsMargins(0, 4, 0, 0)
        r = 0
        g.addWidget(QLabel("내용"), r, 0, Qt.AlignmentFlag.AlignTop)
        self.ed_text = QPlainTextEdit()
        self.ed_text.setFixedHeight(64)
        g.addWidget(self.ed_text, r, 1, 1, 3)
        r += 1
        g.addWidget(QLabel("프리셋"), r, 0)
        self.cb_preset = QComboBox()
        self.cb_preset.addItems(list(PRESETS.keys()))
        g.addWidget(self.cb_preset, r, 1, 1, 2)
        self.btn_preset = QPushButton("적용")
        g.addWidget(self.btn_preset, r, 3)
        r += 1
        g.addWidget(QLabel("폰트"), r, 0)
        self.cb_font = QComboBox()
        self.cb_font.setEditable(True)
        self.cb_font.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        for name, path in self.fonts:
            self.cb_font.addItem(name, path)
        comp = self.cb_font.completer()
        comp.setFilterMode(Qt.MatchFlag.MatchContains)
        comp.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        g.addWidget(self.cb_font, r, 1, 1, 3)
        r += 1
        self.btn_add_font = QPushButton("폰트 파일 추가… (ttf/otf)")
        g.addWidget(self.btn_add_font, r, 1, 1, 3)
        r += 1
        g.addWidget(QLabel("크기"), r, 0)
        self.sp_size = QSpinBox()
        self.sp_size.setRange(8, 600)
        g.addWidget(self.sp_size, r, 1)
        g.addWidget(QLabel("줄간격"), r, 2)
        self.sp_spacing = QSpinBox()
        self.sp_spacing.setRange(-50, 300)
        g.addWidget(self.sp_spacing, r, 3)
        r += 1
        g.addWidget(QLabel("글자색"), r, 0)
        self.btn_color = QPushButton()
        g.addWidget(self.btn_color, r, 1)
        g.addWidget(QLabel("외곽선"), r, 2)
        self.btn_stroke_color = QPushButton()
        g.addWidget(self.btn_stroke_color, r, 3)
        r += 1
        g.addWidget(QLabel("외곽선 두께"), r, 0)
        self.sp_stroke = QSpinBox()
        self.sp_stroke.setRange(0, 80)
        g.addWidget(self.sp_stroke, r, 1)
        r += 1
        self.chk_shadow = QCheckBox("그림자")
        g.addWidget(self.chk_shadow, r, 0, 1, 2)
        self.btn_shadow_color = QPushButton()
        g.addWidget(self.btn_shadow_color, r, 2, 1, 2)
        r += 1
        self.chk_box = QCheckBox("배경 박스")
        g.addWidget(self.chk_box, r, 0, 1, 2)
        self.btn_box_color = QPushButton()
        g.addWidget(self.btn_box_color, r, 2, 1, 2)
        r += 1
        g.addWidget(QLabel("위치 X %"), r, 0)
        self.sp_x = self._pct_spin()
        g.addWidget(self.sp_x, r, 1)
        g.addWidget(QLabel("Y %"), r, 2)
        self.sp_y = self._pct_spin()
        g.addWidget(self.sp_y, r, 3)
        r += 1
        pos_row = QHBoxLayout()
        self.btn_pos_top = QPushButton("상단")
        self.btn_pos_mid = QPushButton("가운데")
        self.btn_pos_bot = QPushButton("하단")
        for b in (self.btn_pos_top, self.btn_pos_mid, self.btn_pos_bot):
            pos_row.addWidget(b)
        g.addLayout(pos_row, r, 1, 1, 3)
        r += 1
        tip = QLabel("💡 [선택/이동] 도구로 미리보기의 글자를 드래그하면 위치가 바뀝니다.")
        tip.setWordWrap(True)
        tip.setStyleSheet("color:#2d6cdf;")
        g.addWidget(tip, r, 0, 1, 4)
        return w

    def _build_shape_page(self):
        w = QWidget()
        g = QGridLayout(w)
        g.setContentsMargins(0, 4, 0, 0)
        g.addWidget(QLabel("선 색"), 0, 0)
        self.btn_line_color = QPushButton()
        g.addWidget(self.btn_line_color, 0, 1)
        g.addWidget(QLabel("선 두께"), 0, 2)
        self.sp_line_width = QSpinBox()
        self.sp_line_width.setRange(1, 80)
        g.addWidget(self.sp_line_width, 0, 3)
        self.chk_fill = QCheckBox("채우기")
        g.addWidget(self.chk_fill, 1, 0)
        self.btn_fill_color = QPushButton()
        g.addWidget(self.btn_fill_color, 1, 1)
        self.lbl_radius = QLabel("모서리")
        g.addWidget(self.lbl_radius, 1, 2)
        self.sp_radius = QSpinBox()
        self.sp_radius.setRange(0, 300)
        g.addWidget(self.sp_radius, 1, 3)
        tip = QLabel("💡 도형을 드래그하면 이동, 모서리의 흰 점을 드래그하면 크기 조절됩니다.\n"
                     "   채우기 색의 투명도를 낮추면 형광펜 강조처럼 쓸 수 있습니다.")
        tip.setWordWrap(True)
        tip.setStyleSheet("color:#2d6cdf;")
        g.addWidget(tip, 2, 0, 1, 4)
        return w

    def _build_mosaic_page(self):
        w = QWidget()
        g = QGridLayout(w)
        g.setContentsMargins(0, 4, 0, 0)
        g.addWidget(QLabel("블록 크기"), 0, 0)
        self.sp_mosaic = QSpinBox()
        self.sp_mosaic.setRange(4, 120)
        self.sp_mosaic.setSuffix(" px")
        g.addWidget(self.sp_mosaic, 0, 1)
        tip = QLabel("💡 미리보기에서는 빗금으로 표시되고, 내보낸 영상과 [현재 화면 저장]에는 "
                     "실제 모자이크가 적용됩니다.")
        tip.setWordWrap(True)
        tip.setStyleSheet("color:#2d6cdf;")
        g.addWidget(tip, 1, 0, 1, 2)
        g.setColumnStretch(1, 1)
        return w

    def _time_spin(self):
        s = QDoubleSpinBox()
        s.setDecimals(3)
        s.setSingleStep(0.1)
        s.setRange(0, 999999)
        s.setSuffix(" 초")
        return s

    def _fade_spin(self, prefix):
        s = QDoubleSpinBox()
        s.setDecimals(1)
        s.setSingleStep(0.1)
        s.setRange(0, 10)
        s.setPrefix(prefix)
        s.setSuffix(" 초")
        return s

    def _pct_spin(self):
        s = QDoubleSpinBox()
        s.setDecimals(1)
        s.setSingleStep(0.5)
        s.setRange(-50, 150)
        s.setSuffix(" %")
        return s

    def _connect_signals(self):
        self.btn_new.clicked.connect(self.new_project)
        self.btn_open.clicked.connect(self.open_dialog)
        self.btn_proj_open.clicked.connect(self.open_project_dialog)
        self.btn_proj_save.clicked.connect(self.save_project)
        self.btn_undo.clicked.connect(self.undo)
        self.btn_redo.clicked.connect(self.redo)
        self.btn_snap.clicked.connect(self.save_snapshot)
        self.tool_group.idClicked.connect(lambda i: self.set_tool(TOOLS[i][0]))

        self.view.fileDropped.connect(self.handle_new_file)
        self.view.pressed.connect(self._on_view_press)
        self.view.moved.connect(self._on_view_move)
        self.view.released.connect(self._on_view_release)

        self.player.positionChanged.connect(self._on_position)
        self.player.playbackStateChanged.connect(self._on_play_state)
        self.player.mediaStatusChanged.connect(self._on_media_status)
        self.player.errorOccurred.connect(lambda _e, s: self.statusBar().showMessage(f"재생 오류: {s}"))
        self.bgm_player.durationChanged.connect(lambda ms: setattr(self, "bgm_duration", ms / 1000))

        self.timeline.seekRequested.connect(lambda t: self.seek(t))
        self.timeline.itemSelected.connect(self.select_item)

        self.btn_play.clicked.connect(self.toggle_play)
        self.btn_home.clicked.connect(lambda: self.seek(0))
        self.btn_endk.clicked.connect(lambda: self.seek(self.total()))
        self.btn_back5.clicked.connect(lambda: self.step(-5))
        self.btn_back1.clicked.connect(lambda: self.step(-1))
        self.btn_fwd1.clicked.connect(lambda: self.step(1))
        self.btn_fwd5.clicked.connect(lambda: self.step(5))
        self.btn_prevf.clicked.connect(lambda: self.step_frame(-1))
        self.btn_nextf.clicked.connect(lambda: self.step_frame(1))
        self.btn_jump.clicked.connect(self.jump_to_input)
        self.ed_jump.returnPressed.connect(self.jump_to_input)
        self.sl_master.valueChanged.connect(self._apply_volumes)

        self.btn_insert_clip.clicked.connect(lambda: self.insert_from_dialog(at_end=False))
        self.btn_append_clip.clicked.connect(lambda: self.insert_from_dialog(at_end=True))
        self.btn_split.clicked.connect(self.split_clip)
        self.btn_del_clip.clicked.connect(self.delete_clip)
        self.btn_clip_left.clicked.connect(lambda: self.move_clip(-1))
        self.btn_clip_right.clicked.connect(lambda: self.move_clip(1))
        self.btn_trim_clip.clicked.connect(self.edit_clip_range)

        self.list_items.currentRowChanged.connect(self._on_list_row)
        self.list_items.itemDoubleClicked.connect(lambda _i: self.goto_selected_start())
        self.btn_add.clicked.connect(lambda: self.add_overlay("text"))
        self.btn_dup.clicked.connect(self.duplicate_item)
        self.btn_del.clicked.connect(self.delete_item)
        self.btn_up.clicked.connect(lambda: self.move_layer(-1))
        self.btn_down.clicked.connect(lambda: self.move_layer(1))

        self.ed_text.textChanged.connect(self._apply_editor_to_item)
        for sp in (self.sp_start, self.sp_end, self.sp_fin, self.sp_fout, self.sp_x, self.sp_y,
                   self.sp_size, self.sp_spacing, self.sp_stroke, self.sp_line_width, self.sp_radius,
                   self.sp_mosaic):
            sp.valueChanged.connect(self._apply_editor_to_item)
        for chk in (self.chk_shadow, self.chk_box, self.chk_fill):
            chk.toggled.connect(self._apply_editor_to_item)
        self.cb_font.currentIndexChanged.connect(self._apply_editor_to_item)

        self.btn_set_start.clicked.connect(self.set_start_here)
        self.btn_set_end.clicked.connect(self.set_end_here)
        self.btn_goto_start.clicked.connect(self.goto_selected_start)
        self.btn_preset.clicked.connect(self.apply_selected_preset)
        self.btn_add_font.clicked.connect(self.add_font_file)
        titles = {"color": "글자색", "stroke_color": "외곽선 색", "shadow_color": "그림자 색",
                  "box_color": "배경 박스 색", "line_color": "선 색", "fill_color": "채우기 색"}
        for attr, btn in self.color_btns.items():
            btn.clicked.connect(lambda _c=False, a=attr: self.pick_color(a, titles[a]))
        self.btn_pos_top.clicked.connect(lambda: self.set_text_y(0.12))
        self.btn_pos_mid.clicked.connect(lambda: self.set_text_y(0.5))
        self.btn_pos_bot.clicked.connect(lambda: self.set_text_y(0.85))

        self.sl_orig.valueChanged.connect(self._on_orig_volume)
        self.sl_bgm.valueChanged.connect(self._on_bgm_volume)
        self.btn_bgm.clicked.connect(self.choose_bgm)
        self.btn_bgm_clear.clicked.connect(self.clear_bgm)
        self.btn_export.clicked.connect(self.export_or_cancel)

    def _make_shortcuts(self):
        def sc(key, fn):
            QShortcut(QKeySequence(key), self, activated=fn)

        sc(Qt.Key.Key_Space, self.toggle_play)
        sc(Qt.Key.Key_Left, lambda: self.step(-1))
        sc(Qt.Key.Key_Right, lambda: self.step(1))
        sc("Shift+Left", lambda: self.step(-5))
        sc("Shift+Right", lambda: self.step(5))
        sc(",", lambda: self.step_frame(-1))
        sc(".", lambda: self.step_frame(1))
        sc(Qt.Key.Key_Home, lambda: self.seek(0))
        sc(Qt.Key.Key_End, lambda: self.seek(self.total()))
        sc("[", self.set_start_here)
        sc("]", self.set_end_here)
        sc("S", self.split_clip)
        sc(Qt.Key.Key_Delete, self.delete_item)
        sc("Ctrl+D", self.duplicate_item)
        sc("Ctrl+Z", self.undo)
        sc("Ctrl+Y", self.redo)
        sc("Ctrl+Shift+Z", self.redo)
        sc("Ctrl+S", self.save_project)
        sc("Ctrl+O", self.open_dialog)
        sc("Ctrl+E", self.export_or_cancel)
        sc("Ctrl+T", lambda: self.add_overlay("text"))
        sc(Qt.Key.Key_Escape, lambda: self.set_tool("select"))
        for key, name in (("V", "select"), ("T", "text"), ("R", "rect"), ("E", "ellipse"),
                          ("A", "arrow"), ("M", "mosaic")):
            sc(key, lambda n=name: self.set_tool(n))

    # ════════════════════════════════════════════════════════
    # 시퀀스(구간) 계산
    # ════════════════════════════════════════════════════════
    def total(self) -> float:
        return sum(c.duration for c in self.clips)

    def offsets(self) -> list[float]:
        offs, acc = [], 0.0
        for c in self.clips:
            offs.append(acc)
            acc += c.duration
        return offs

    def locate(self, t: float) -> tuple[int, float]:
        offs = self.offsets()
        for k, c in enumerate(self.clips):
            if t < offs[k] + c.duration - 1e-6:
                return k, c.src_in + max(0.0, t - offs[k])
        last = self.clips[-1]
        return len(self.clips) - 1, max(last.src_in, last.src_out - 0.001)

    def current_item(self) -> OverlayItem | None:
        return next((i for i in self.items if i.id == self.selected_id), None)

    # ════════════════════════════════════════════════════════
    # 재생 / 이동
    # ════════════════════════════════════════════════════════
    def seek(self, t: float, play: bool | None = None):
        if not self.clips:
            return
        t = clamp(t, 0.0, self.total())
        self._t = t
        if play is None:
            play = self._want_play
        self._want_play = play
        k, src = self.locate(t)
        self._cur_k = k
        clip = self.clips[k]
        ms = int(round(src * 1000))
        self._seek_guard = time.monotonic() + 0.25
        if self._loaded_path != clip.path:
            self._loaded_path = clip.path
            self._pending = (ms, play)
            self.player.setSource(QUrl.fromLocalFile(clip.path))
        else:
            if self.player.playbackState() == QMediaPlayer.PlaybackState.StoppedState:
                self.player.pause()
            self.player.setPosition(ms)
            playing = self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
            if play and not playing:
                self.player.play()
            elif not play and playing:
                self.player.pause()
        if play:
            self._play_timer.start()
        else:
            self._play_timer.stop()
        self._sync_bgm(play)
        self._update_time_ui()

    def _on_media_status(self, st):
        if st in (QMediaPlayer.MediaStatus.LoadedMedia, QMediaPlayer.MediaStatus.BufferedMedia) and self._pending:
            ms, play = self._pending
            self._pending = None
            self.player.pause()
            self.player.setPosition(ms)
            if play:
                self.player.play()
            self._seek_guard = time.monotonic() + 0.25
        elif st == QMediaPlayer.MediaStatus.EndOfMedia and self._want_play and not self._pending:
            self._advance_clip()
        elif st == QMediaPlayer.MediaStatus.InvalidMedia:
            self.statusBar().showMessage("이 영상은 미리보기 재생이 안 됩니다. (내보내기는 가능할 수 있음)", 6000)

    def _poll_position(self):
        if not self._pending:
            self._on_position(self.player.position())

    def _on_position(self, ms: int):
        if self._pending or not self.clips or self._cur_k >= len(self.clips):
            return
        clip = self.clips[self._cur_k]
        if clip.path != self._loaded_path:
            return
        src = ms / 1000
        if src < clip.src_in - 0.3 or src > clip.src_out + 0.3:
            return
        if self._want_play and time.monotonic() > self._seek_guard and src >= clip.src_out - 0.035:
            self._advance_clip()
            return
        offs = self.offsets()
        self._t = offs[self._cur_k] + clamp(src - clip.src_in, 0.0, clip.duration)
        self._update_time_ui()

    def _advance_clip(self):
        k = self._cur_k + 1
        if k < len(self.clips):
            self.seek(self.offsets()[k], play=True)
        else:
            self._want_play = False
            self.player.pause()
            self._play_timer.stop()
            self._sync_bgm(False)
            self._t = self.total()
            self._update_time_ui()

    def _on_play_state(self, _st):
        self.btn_play.setText("⏸ 일시정지" if self._want_play else "▶ 재생")
        self._update_overlay_visibility()

    def toggle_play(self):
        if not self.clips:
            return
        if self._want_play:
            self._want_play = False
            self.player.pause()
            self._play_timer.stop()
            self._sync_bgm(False)
            self.btn_play.setText("▶ 재생")
            self._update_overlay_visibility()
        else:
            t = 0.0 if self._t >= self.total() - 0.05 else self._t
            self.seek(t, play=True)
            self.btn_play.setText("⏸ 일시정지")

    def step(self, dt: float):
        self.seek(self._t + dt)

    def step_frame(self, n: int):
        if not self.clips:
            return
        self.seek(self._t + n / (self.proj_fps or 30), play=False)

    def jump_to_input(self):
        try:
            t = parse_time(self.ed_jump.text())
        except ValueError:
            self.statusBar().showMessage("시간 형식 예: 83.5 / 1:23.5 / 0:01:23", 4000)
            return
        self.seek(t)
        self.view.setFocus()

    def _sync_bgm(self, play: bool):
        if not self.bgm_path:
            return
        pos = (self._t % self.bgm_duration) if self.bgm_duration > 0 else self._t
        self.bgm_player.setPosition(int(pos * 1000))
        if play:
            self.bgm_player.play()
        else:
            self.bgm_player.pause()

    def _apply_volumes(self, *_):
        master = self.sl_master.value() / 100
        self.audio.setVolume(clamp(master * self.orig_volume, 0.0, 1.0))
        self.bgm_audio.setVolume(clamp(master * self.bgm_volume, 0.0, 1.0))

    def _on_orig_volume(self, v):
        self.orig_volume = v / 100
        self.lbl_orig.setText(f"{v}%")
        self._apply_volumes()

    def _on_bgm_volume(self, v):
        self.bgm_volume = v / 100
        self.lbl_bgm_vol.setText(f"{v}%")
        self._apply_volumes()

    # ════════════════════════════════════════════════════════
    # 화면 갱신
    # ════════════════════════════════════════════════════════
    def _update_time_ui(self):
        total = self.total()
        self.lbl_time.setText(f"{fmt_time(self._t)} / {fmt_time(total)}")
        self.timeline.set_position(self._t, follow=self._want_play)
        if self.clips:
            k, src = self.locate(self._t)
            c = self.clips[k]
            off = self.offsets()[k]
            self.lbl_clip.setText(f"현재 구간 <b>{k + 1}/{len(self.clips)}</b> · {os.path.basename(c.path)}<br>"
                                  f"타임라인 {fmt_time(off)} ~ {fmt_time(off + c.duration)} · "
                                  f"원본 {fmt_time(c.src_in)} ~ {fmt_time(c.src_out)}")
        else:
            self.lbl_clip.setText("영상이 없습니다.")
        self._update_overlay_visibility()

    def _refresh_timeline(self):
        offs = self.offsets()
        data = [(offs[k], c.duration, os.path.basename(c.path), c.path) for k, c in enumerate(self.clips)]
        self.timeline.set_data(self.total(), data, self.items, self.selected_id)

    def _update_all(self):
        has = bool(self.clips)
        for w in self.ctrl_btns + (self.btn_jump, self.ed_jump, self.btn_add, self.btn_export, self.btn_snap,
                                   self.btn_insert_clip, self.btn_append_clip, self.btn_split,
                                   self.btn_del_clip, self.btn_clip_left, self.btn_clip_right,
                                   self.btn_trim_clip, self.btn_proj_save):
            w.setEnabled(has)
        for b in self.tool_btns.values():
            b.setEnabled(has)
        self.btn_undo.setEnabled(bool(self.undo_stack))
        self.btn_redo.setEnabled(bool(self.redo_stack))
        self.placeholder.setVisible(not has)
        self.video_item.setVisible(has)
        if has:
            self.lbl_info.setText(f"구간 {len(self.clips)}개 · 총 {fmt_time(self.total())} · "
                                  f"{self.proj_w}×{self.proj_h} · {self.proj_fps:.2f}fps"
                                  + (f" · 📁 {os.path.basename(self.project_path)}" if self.project_path else ""))
        self._refresh_timeline()
        self._update_time_ui()

    def _refresh_selected_overlay(self):
        it = self.current_item()
        if it:
            self._refresh_overlay(it)

    def _refresh_overlay(self, it: OverlayItem):
        if not self.clips:
            return
        img, bbox = render_overlay(it, self.proj_w, self.proj_h, 1.0, preview=True)
        self.overlay_bbox[it.id] = bbox
        gi = self.overlay_gi.get(it.id)
        if gi is None:
            gi = QGraphicsPixmapItem()
            gi.setTransformationMode(Qt.TransformationMode.SmoothTransformation)
            self.scene.addItem(gi)
            self.overlay_gi[it.id] = gi
        gi.setPixmap(pil_to_qpixmap(img))
        gi.setPos(0, 0)
        self._update_z()
        self._update_overlay_visibility()

    def _rebuild_overlays(self):
        for gi in self.overlay_gi.values():
            self.scene.removeItem(gi)
        self.overlay_gi.clear()
        self.overlay_bbox.clear()
        for it in self.items:
            self._refresh_overlay(it)

    def _update_z(self):
        for i, it in enumerate(self.items):
            gi = self.overlay_gi.get(it.id)
            if gi:
                gi.setZValue(10 + i)

    def _item_alpha(self, it: OverlayItem, t: float) -> float:
        a = 1.0
        if it.fade_in > 0 and t < it.start + it.fade_in:
            a = min(a, (t - it.start) / it.fade_in)
        if it.fade_out > 0 and t > it.end - it.fade_out:
            a = min(a, (it.end - t) / it.fade_out)
        return clamp(a, 0.0, 1.0)

    def _update_overlay_visibility(self):
        t = self._t
        playing = self._want_play
        for it in self.items:
            gi = self.overlay_gi.get(it.id)
            if not gi:
                continue
            if it.start <= t <= it.end:
                gi.setVisible(True)
                gi.setOpacity(max(0.05, self._item_alpha(it, t)) if not (it.id == self.selected_id and not playing)
                              else max(0.35, self._item_alpha(it, t)))
            elif it.id == self.selected_id and not playing:
                gi.setVisible(True)      # 구간 밖이어도 편집 중인 항목은 흐리게 표시
                gi.setOpacity(0.35)
            else:
                gi.setVisible(False)
        self._update_selection_graphics()

    def _handle_points(self, it: OverlayItem):
        W, H = self.proj_w, self.proj_h
        if it.kind == "arrow":
            return [(it.x1 * W, it.y1 * H), (it.x2 * W, it.y2 * H)]
        if it.kind in ("rect", "ellipse", "mosaic"):
            l, t, r, b = rect_px(it, W, H)
            return [(l, t), (r, t), (r, b), (l, b)]
        return []

    def _update_selection_graphics(self):
        it = self.current_item()
        bbox = self.overlay_bbox.get(it.id) if it else None
        show = bool(it and bbox and not self._want_play and self.clips)
        self.sel_rect.setVisible(show)
        pts = self._handle_points(it) if show else []
        for i, h in enumerate(self.handles):
            if i < len(pts):
                h.setPos(*pts[i])
                h.setVisible(True)
            else:
                h.setVisible(False)
        if show:
            l, t, r, b = bbox
            self.sel_rect.setRect(QRectF(l - 4, t - 4, r - l + 8, b - t + 8))

    # ════════════════════════════════════════════════════════
    # 실행 취소
    # ════════════════════════════════════════════════════════
    def _snapshot(self):
        return copy.deepcopy((self.clips, self.items, self.selected_id, self._t))

    def push_undo(self, key=None):
        now = time.monotonic()
        if key is not None and key == self._undo_key and now - self._undo_time < 1.5:
            self._undo_time = now
            return
        self._undo_key, self._undo_time = key, now
        self.undo_stack.append(self._snapshot())
        if len(self.undo_stack) > 100:
            self.undo_stack.pop(0)
        self.redo_stack.clear()
        self.btn_undo.setEnabled(True)
        self.btn_redo.setEnabled(False)

    def _restore(self, snap):
        clips, items, sel, t = copy.deepcopy(snap)
        self.clips, self.items, self.selected_id = clips, items, sel
        self._undo_key = None
        self._rebuild_overlays()
        self._rebuild_list()
        self._load_item_to_editor(self.current_item())
        self._update_all()
        self.seek(min(t, self.total()), play=False)

    def undo(self):
        if not self.undo_stack or self.export_worker:
            return
        self.redo_stack.append(self._snapshot())
        self._restore(self.undo_stack.pop())
        self.statusBar().showMessage("실행 취소", 2000)

    def redo(self):
        if not self.redo_stack or self.export_worker:
            return
        self.undo_stack.append(self._snapshot())
        self._restore(self.redo_stack.pop())
        self.statusBar().showMessage("다시 실행", 2000)

    # ════════════════════════════════════════════════════════
    # 파일 열기 / 프로젝트
    # ════════════════════════════════════════════════════════
    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dropEvent(self, e):
        for url in e.mimeData().urls():
            if url.toLocalFile():
                self.handle_new_file(url.toLocalFile())
                break

    def open_dialog(self):
        path, _ = QFileDialog.getOpenFileName(self, "영상 열기", "", VIDEO_FILTER)
        if path:
            self.handle_new_file(path)

    def handle_new_file(self, path: str):
        if self.export_worker:
            QMessageBox.information(self, APP_TITLE, "내보내기 중에는 사용할 수 없습니다.")
            return
        if not os.path.isfile(path):
            return
        if path.lower().endswith(".json"):
            self.load_project(path)
            return
        if not self.clips:
            self.new_project_with(path)
            return
        box = QMessageBox(self)
        box.setWindowTitle(APP_TITLE)
        box.setText(f"<b>{os.path.basename(path)}</b><br><br>이 영상을 어떻게 사용할까요?")
        b_ins = box.addButton("현재 위치에 삽입", QMessageBox.ButtonRole.ActionRole)
        b_app = box.addButton("맨 뒤에 추가", QMessageBox.ButtonRole.ActionRole)
        b_new = box.addButton("새 프로젝트로 열기", QMessageBox.ButtonRole.ActionRole)
        box.addButton("취소", QMessageBox.ButtonRole.RejectRole)
        box.exec()
        c = box.clickedButton()
        if c == b_ins:
            self.insert_from_file(path, self._t)
        elif c == b_app:
            self.insert_from_file(path, self.total())
        elif c == b_new:
            self.new_project_with(path)

    def _reset_state(self):
        self._want_play = False
        self._play_timer.stop()
        self.player.stop()
        self._pending = None
        self._loaded_path = None
        for gi in self.overlay_gi.values():
            self.scene.removeItem(gi)
        self.overlay_gi.clear()
        self.overlay_bbox.clear()
        self.clips.clear()
        self.items.clear()
        self.selected_id = None
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.project_path = ""
        self._t = 0.0
        self._cur_k = 0

    def _set_project_size(self, w, h, fps):
        self.proj_w, self.proj_h, self.proj_fps = int(w), int(h), float(fps) or 30.0
        self.scene.setSceneRect(0, 0, self.proj_w, self.proj_h)
        self.video_item.setPos(0, 0)
        self.video_item.setSize(QSizeF(self.proj_w, self.proj_h))
        self.view.fit()

    def new_project(self):
        if self.export_worker:
            return
        if self.clips and QMessageBox.question(self, APP_TITLE, "현재 작업을 닫고 새로 시작할까요?\n"
                                               "(저장하지 않은 내용은 사라집니다)") != QMessageBox.StandardButton.Yes:
            return
        self._reset_state()
        self.clear_bgm()
        self._rebuild_list()
        self._load_item_to_editor(None)
        self.setWindowTitle(APP_TITLE)
        self.lbl_info.setText("영상을 드래그하거나 [영상 열기]를 누르세요.")
        self._update_all()

    def new_project_with(self, path: str):
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            info = probe_video(path)
        except Exception as e:
            QApplication.restoreOverrideCursor()
            QMessageBox.warning(self, APP_TITLE, f"영상을 열 수 없습니다.\n\n{e}")
            return
        QApplication.restoreOverrideCursor()
        self._reset_state()
        self._set_project_size(info.width, info.height, info.fps)
        self.clips = [Clip(path, 0.0, round(info.duration, 3))]
        self._rebuild_list()
        self._load_item_to_editor(None)
        self.setWindowTitle(f"{APP_TITLE} - {os.path.basename(path)}")
        self.progress.setValue(0)
        self._update_all()
        self.seek(0, play=False)

    def project_dict(self) -> dict:
        return {
            "app": "VideoTextEditor", "version": 2,
            "project": {"width": self.proj_w, "height": self.proj_h, "fps": self.proj_fps},
            "clips": [asdict(c) for c in self.clips],
            "items": [asdict(i) for i in self.items],
            "audio": {"orig_volume": self.orig_volume, "bgm_path": self.bgm_path, "bgm_volume": self.bgm_volume},
            "export": {"quality": self.cb_quality.currentIndex(), "resolution": self.cb_res.currentIndex(),
                       "fade_all": self.chk_fade_all.isChecked()},
        }

    def save_project(self):
        if not self.clips:
            return
        default = self.project_path or os.path.splitext(self.clips[0].path)[0] + ".vte.json"
        path, _ = QFileDialog.getSaveFileName(self, "프로젝트 저장", default, PROJECT_FILTER)
        if not path:
            return
        if not path.lower().endswith(".json"):
            path += ".vte.json"
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.project_dict(), f, ensure_ascii=False, indent=2)
        except OSError as e:
            QMessageBox.warning(self, APP_TITLE, f"저장 실패\n\n{e}")
            return
        self.project_path = path
        self._update_all()
        self.statusBar().showMessage(f"프로젝트 저장: {path}", 5000)

    def open_project_dialog(self):
        path, _ = QFileDialog.getOpenFileName(self, "프로젝트 열기", "", PROJECT_FILTER)
        if path:
            self.load_project(path)

    def load_project(self, path: str):
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            clips = [clip_from_dict(c) for c in data["clips"]]
            items = [item_from_dict(i) for i in data.get("items", [])]
        except Exception as e:
            QMessageBox.warning(self, APP_TITLE, f"프로젝트 파일을 읽을 수 없습니다.\n\n{e}")
            return
        missing = sorted({c.path for c in clips if not os.path.isfile(c.path)})
        if missing:
            QMessageBox.warning(self, APP_TITLE, "다음 영상 파일을 찾을 수 없습니다.\n\n" + "\n".join(missing))
            return
        if not clips:
            QMessageBox.warning(self, APP_TITLE, "프로젝트에 영상 구간이 없습니다.")
            return
        for p in {c.path for c in clips}:
            try:
                probe_video(p)
            except Exception as e:
                QMessageBox.warning(self, APP_TITLE, f"영상을 열 수 없습니다: {p}\n\n{e}")
                return
        self._reset_state()
        pr = data.get("project", {})
        first = probe_video(clips[0].path)
        self._set_project_size(pr.get("width", first.width), pr.get("height", first.height),
                               pr.get("fps", first.fps))
        self.clips, self.items = clips, items
        self.selected_id = items[0].id if items else None
        au = data.get("audio", {})
        self.sl_orig.setValue(int(round(au.get("orig_volume", 1.0) * 100)))
        self.sl_bgm.setValue(int(round(au.get("bgm_volume", 0.3) * 100)))
        bgm = au.get("bgm_path", "")
        if bgm and os.path.isfile(bgm):
            self.set_bgm(bgm)
        else:
            self.clear_bgm()
        ex = data.get("export", {})
        self.cb_quality.setCurrentIndex(ex.get("quality", 0))
        self.cb_res.setCurrentIndex(ex.get("resolution", 0))
        self.chk_fade_all.setChecked(ex.get("fade_all", False))
        self.project_path = path
        self._rebuild_overlays()
        self._rebuild_list()
        self._load_item_to_editor(self.current_item())
        self.setWindowTitle(f"{APP_TITLE} - {os.path.basename(path)}")
        self._update_all()
        self.seek(0, play=False)
        self.statusBar().showMessage(f"프로젝트 열기: {path}", 5000)

    # ════════════════════════════════════════════════════════
    # 영상 구간 편집
    # ════════════════════════════════════════════════════════
    def _pause_for_dialog(self):
        if self._want_play:
            self.toggle_play()

    def insert_from_dialog(self, at_end: bool):
        if not self.clips:
            return
        path, _ = QFileDialog.getOpenFileName(self, "넣을 영상 선택", os.path.dirname(self.clips[0].path),
                                              VIDEO_FILTER)
        if path:
            self.insert_from_file(path, self.total() if at_end else self._t)

    def insert_from_file(self, path: str, at: float):
        try:
            info = probe_video(path)
        except Exception as e:
            QMessageBox.warning(self, APP_TITLE, f"영상을 열 수 없습니다.\n\n{e}")
            return
        self._pause_for_dialog()
        dlg = TrimDialog(self, info)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        a, b = dlg.values()
        self.insert_clip(Clip(path, a, b), at)

    def insert_clip(self, new: Clip, at: float):
        self.push_undo()
        total = self.total()
        if at >= total - 0.05:
            idx, at = len(self.clips), total
        elif at <= 0.05:
            idx, at = 0, 0.0
        else:
            k, src = self.locate(at)
            off = self.offsets()[k]
            c = self.clips[k]
            if at - off < 0.05:
                idx, at = k, off
            elif off + c.duration - at < 0.05:
                idx, at = k + 1, off + c.duration
            else:
                right = Clip(c.path, round(src, 3), c.src_out)
                c.src_out = round(src, 3)
                self.clips.insert(k + 1, right)
                idx = k + 1
        self.clips.insert(idx, new)
        self._ripple_insert(at, new.duration)
        self._after_structure_change(at)
        self.statusBar().showMessage(f"영상 구간 삽입: {os.path.basename(new.path)} ({new.duration:.2f}초)", 5000)

    def split_clip(self):
        if not self.clips:
            return
        k, src = self.locate(self._t)
        c = self.clips[k]
        if src - c.src_in < 0.05 or c.src_out - src < 0.05:
            self.statusBar().showMessage("구간 경계에서는 자를 수 없습니다.", 3000)
            return
        self.push_undo()
        self.clips.insert(k + 1, Clip(c.path, round(src, 3), c.src_out))
        c.src_out = round(src, 3)
        self._after_structure_change(self._t)
        self.statusBar().showMessage("현재 위치에서 잘랐습니다. (구간 삭제/이동 가능)", 4000)

    def delete_clip(self):
        if not self.clips:
            return
        if len(self.clips) == 1:
            QMessageBox.information(self, APP_TITLE, "구간이 하나뿐이라 삭제할 수 없습니다.\n"
                                                     "먼저 [자르기]로 구간을 나눠주세요.")
            return
        k, _ = self.locate(self._t)
        off = self.offsets()[k]
        c = self.clips[k]
        if QMessageBox.question(self, APP_TITLE, f"현재 구간을 삭제할까요?\n\n{os.path.basename(c.path)}\n"
                                f"{fmt_time(off)} ~ {fmt_time(off + c.duration)} ({c.duration:.2f}초)\n\n"
                                "이 구간 안의 글자·도형도 함께 삭제됩니다.") != QMessageBox.StandardButton.Yes:
            return
        self.push_undo()
        self.clips.pop(k)
        self._ripple_delete(off, off + c.duration)
        self._after_structure_change(off)

    def move_clip(self, direction: int):
        if not self.clips:
            return
        k, _ = self.locate(self._t)
        j = k + direction
        if not (0 <= j < len(self.clips)):
            return
        self.push_undo()
        a = min(k, j)
        offs = self.offsets()
        a0 = offs[a]
        dA, dB = self.clips[a].duration, self.clips[a + 1].duration
        a1, b1 = a0 + dA, a0 + dA + dB
        for it in self.items:   # 구간 안의 항목은 구간과 함께 이동
            if it.start >= a0 - 1e-6 and it.end <= a1 + 1e-6:
                it.start += dB
                it.end += dB
            elif it.start >= a1 - 1e-6 and it.end <= b1 + 1e-6:
                it.start -= dA
                it.end -= dA
        self.clips[a], self.clips[a + 1] = self.clips[a + 1], self.clips[a]
        self._after_structure_change(self.offsets()[j])

    def edit_clip_range(self):
        if not self.clips:
            return
        k, _ = self.locate(self._t)
        c = self.clips[k]
        try:
            info = probe_video(c.path)
        except Exception as e:
            QMessageBox.warning(self, APP_TITLE, str(e))
            return
        self._pause_for_dialog()
        dlg = TrimDialog(self, info, c.src_in, c.src_out, title="현재 구간 범위 수정")
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        a, b = dlg.values()
        self.push_undo()
        off = self.offsets()[k]
        old_d, new_d = c.duration, b - a
        if new_d > old_d:
            self._ripple_insert(off + old_d, new_d - old_d)
        elif new_d < old_d:
            self._ripple_delete(off + new_d, off + old_d)
        c.src_in, c.src_out = a, b
        self._after_structure_change(off)

    def _ripple_insert(self, at: float, d: float):
        for it in self.items:
            if it.start >= at - 1e-6:
                it.start = round(it.start + d, 3)
                it.end = round(it.end + d, 3)

    def _ripple_delete(self, a: float, b: float):
        d = b - a
        keep = []
        for it in self.items:
            if it.end <= a + 1e-6:
                pass
            elif it.start >= b - 1e-6:
                it.start -= d
                it.end -= d
            elif it.start >= a - 1e-6 and it.end <= b + 1e-6:
                continue
            elif it.start < a and it.end > b:
                it.end -= d
            elif it.start < a:
                it.end = a
            else:
                it.start = a
                it.end -= d
            it.start, it.end = round(it.start, 3), round(it.end, 3)
            if it.end - it.start > 0.05:
                keep.append(it)
        removed = {i.id for i in self.items} - {i.id for i in keep}
        for iid in removed:
            gi = self.overlay_gi.pop(iid, None)
            if gi:
                self.scene.removeItem(gi)
        self.items = keep
        if self.selected_id in removed:
            self.selected_id = None

    def _after_structure_change(self, seek_t: float):
        total = self.total()
        for it in self.items:
            it.end = min(it.end, total)
            it.start = min(it.start, max(0.0, total - 0.1))
        self._rebuild_list()
        self._load_item_to_editor(self.current_item())
        self._update_all()
        self.seek(seek_t, play=False)

    # ════════════════════════════════════════════════════════
    # 글자 · 도형 관리
    # ════════════════════════════════════════════════════════
    def set_tool(self, name: str):
        if name != "select" and not self.clips:
            name = "select"
        self.tool = name
        self.tool_btns[name].setChecked(True)
        cursor = Qt.CursorShape.ArrowCursor if name == "select" else Qt.CursorShape.CrossCursor
        self.view.viewport().setCursor(cursor)
        tips = {"select": "항목을 클릭해 선택 · 드래그로 이동 · 흰 점으로 크기 조절",
                "text": "글자를 넣을 위치를 클릭하세요",
                "rect": "드래그해서 사각형을 그리세요", "ellipse": "드래그해서 원을 그리세요",
                "arrow": "시작점에서 끝점(화살촉)으로 드래그하세요",
                "mosaic": "가릴 영역을 드래그하세요"}
        self.lbl_tool_tip.setText("  💡 " + tips[name])

    def _item_label(self, it: OverlayItem) -> str:
        return f"[{KIND_LABEL.get(it.kind, it.kind)}] {fmt_time(it.start)} ~ {fmt_time(it.end)}   " \
               f"{item_name(it) if it.kind == 'text' else ''}"

    def _rebuild_list(self):
        self.list_items.blockSignals(True)
        self.list_items.clear()
        row = -1
        for i, it in enumerate(self.items):
            self.list_items.addItem(QListWidgetItem(self._item_label(it)))
            if it.id == self.selected_id:
                row = i
        self.list_items.setCurrentRow(row)
        self.list_items.blockSignals(False)
        self._refresh_timeline()

    def _update_list_row(self, it: OverlayItem):
        if it not in self.items:
            return
        li = self.list_items.item(self.items.index(it))
        if li:
            li.setText(self._item_label(it))
        self._refresh_timeline()

    def select_item(self, iid: str | None):
        self.selected_id = iid
        idx = next((i for i, it in enumerate(self.items) if it.id == iid), -1)
        self.list_items.blockSignals(True)
        self.list_items.setCurrentRow(idx)
        self.list_items.blockSignals(False)
        self._load_item_to_editor(self.current_item())
        self._refresh_timeline()
        self._update_overlay_visibility()

    def _on_list_row(self, row: int):
        self.select_item(self.items[row].id if 0 <= row < len(self.items) else None)

    def add_overlay(self, kind: str, at=None, rect=None):
        if not self.clips:
            QMessageBox.information(self, APP_TITLE, "먼저 영상을 불러와 주세요.")
            return None
        self.push_undo()
        total = self.total()
        start = self._t
        end = min(total, start + 3.0)
        if end - start < 0.5:
            start = max(0.0, end - 3.0)
        start, end = round(start, 3), round(end, 3)
        prev = next((i for i in reversed(self.items) if i.kind == kind), None)
        if prev:   # 같은 종류의 직전 스타일 이어받기
            it = replace(prev, id=uuid.uuid4().hex, start=start, end=end)
        else:
            it = OverlayItem(kind=kind, start=start, end=end, font_path=self.default_font,
                             font_size=max(24, int(self.proj_h * 0.07)),
                             line_width=max(3, int(self.proj_h * 0.006)))
            it.line_spacing = int(it.font_size * 0.15)
            it.mosaic_size = max(8, int(self.proj_h * 0.025))
            if kind == "text":
                apply_preset(it, self.cb_preset.currentText())
        if kind == "text":
            it.text = "텍스트를 입력하세요"
            if at:
                it.x, it.y = at
        elif rect:
            it.x1, it.y1, it.x2, it.y2 = rect
        elif kind == "arrow":
            it.x1, it.y1, it.x2, it.y2 = 0.35, 0.5, 0.6, 0.5
        else:
            it.x1, it.y1, it.x2, it.y2 = 0.35, 0.35, 0.65, 0.65
        self.items.append(it)
        self.selected_id = it.id
        self._refresh_overlay(it)
        self._rebuild_list()
        self._load_item_to_editor(it)
        self._update_overlay_visibility()
        if kind == "text":
            self.ed_text.setFocus()
            self.ed_text.selectAll()
        return it

    def duplicate_item(self):
        cur = self.current_item()
        if not cur or not self.clips:
            return
        self.push_undo()
        length = cur.end - cur.start
        total = self.total()
        start = cur.end if cur.end + 0.1 < total else cur.start
        it = replace(cur, id=uuid.uuid4().hex, start=round(start, 3), end=round(min(total, start + length), 3))
        if start == cur.start:   # 뒤에 공간이 없으면 살짝 옆에 복제
            it.x, it.y = it.x + 0.03, it.y + 0.03
            it.x1, it.y1, it.x2, it.y2 = it.x1 + 0.03, it.y1 + 0.03, it.x2 + 0.03, it.y2 + 0.03
        self.items.append(it)
        self.selected_id = it.id
        self._refresh_overlay(it)
        self._rebuild_list()
        self._load_item_to_editor(it)
        self.seek(it.start)

    def delete_item(self):
        cur = self.current_item()
        if not cur:
            return
        self.push_undo()
        gi = self.overlay_gi.pop(cur.id, None)
        if gi:
            self.scene.removeItem(gi)
        self.overlay_bbox.pop(cur.id, None)
        idx = self.items.index(cur)
        self.items.remove(cur)
        self.selected_id = self.items[min(idx, len(self.items) - 1)].id if self.items else None
        self._rebuild_list()
        self._load_item_to_editor(self.current_item())
        self._update_overlay_visibility()

    def move_layer(self, direction: int):
        cur = self.current_item()
        if not cur:
            return
        i = self.items.index(cur)
        j = i + direction
        if not (0 <= j < len(self.items)):
            return
        self.push_undo()
        self.items[i], self.items[j] = self.items[j], self.items[i]
        self._update_z()
        self._rebuild_list()

    # ── 편집 패널 ↔ 항목 ──────────────────────────────────
    def _set_color_btn(self, btn: QPushButton, rgba):
        r, g, b, a = rgba
        btn.setStyleSheet(f"QPushButton{{background-color:rgba({r},{g},{b},{a});"
                          f"border:1px solid #888;border-radius:4px;min-height:24px;}}")
        btn.setToolTip(f"RGBA({r}, {g}, {b}, {a})")

    def _load_item_to_editor(self, it: OverlayItem | None):
        self._loading = True
        try:
            on = it is not None
            self.gb_edit.setEnabled(on)
            for b in (self.btn_dup, self.btn_del, self.btn_up, self.btn_down):
                b.setEnabled(on)
            if not on:
                self.gb_edit.setTitle("선택 항목 편집")
                self.ed_text.setPlainText("")
                return
            self.gb_edit.setTitle(f"선택 항목 편집 — {KIND_LABEL.get(it.kind, it.kind)}")
            self.sp_start.setValue(it.start)
            self.sp_end.setValue(it.end)
            self.sp_fin.setValue(it.fade_in)
            self.sp_fout.setValue(it.fade_out)
            for attr, btn in self.color_btns.items():
                self._set_color_btn(btn, getattr(it, attr))
            if it.kind == "text":
                self.stack.setCurrentIndex(0)
                self.ed_text.setPlainText(it.text)
                idx = self.cb_font.findData(it.font_path)
                if idx < 0 and it.font_path:
                    self.cb_font.addItem(font_display_name(it.font_path) or os.path.basename(it.font_path),
                                         it.font_path)
                    idx = self.cb_font.count() - 1
                self.cb_font.setCurrentIndex(idx)
                self.sp_size.setValue(it.font_size)
                self.sp_spacing.setValue(it.line_spacing)
                self.sp_stroke.setValue(it.stroke_width)
                self.chk_shadow.setChecked(it.shadow)
                self.chk_box.setChecked(it.box)
                self.sp_x.setValue(it.x * 100)
                self.sp_y.setValue(it.y * 100)
            elif it.kind == "mosaic":
                self.stack.setCurrentIndex(2)
                self.sp_mosaic.setValue(it.mosaic_size)
            else:
                self.stack.setCurrentIndex(1)
                self.sp_line_width.setValue(it.line_width)
                self.chk_fill.setChecked(it.fill)
                self.sp_radius.setValue(it.radius)
                arrow = it.kind == "arrow"
                rect = it.kind == "rect"
                self.chk_fill.setEnabled(not arrow)
                self.btn_fill_color.setEnabled(not arrow)
                self.lbl_radius.setEnabled(rect)
                self.sp_radius.setEnabled(rect)
        finally:
            self._loading = False

    def _apply_editor_to_item(self, *_):
        if self._loading:
            return
        it = self.current_item()
        if not it:
            return
        self.push_undo(key=("edit", it.id))
        it.start = round(self.sp_start.value(), 3)
        it.end = round(self.sp_end.value(), 3)
        it.fade_in = round(self.sp_fin.value(), 2)
        it.fade_out = round(self.sp_fout.value(), 2)
        if it.kind == "text":
            it.text = self.ed_text.toPlainText()
            fp = self.cb_font.currentData()
            if fp:
                it.font_path = fp
            it.font_size = self.sp_size.value()
            it.line_spacing = self.sp_spacing.value()
            it.stroke_width = self.sp_stroke.value()
            it.shadow = self.chk_shadow.isChecked()
            it.box = self.chk_box.isChecked()
            it.x = self.sp_x.value() / 100
            it.y = self.sp_y.value() / 100
        elif it.kind == "mosaic":
            it.mosaic_size = self.sp_mosaic.value()
        else:
            it.line_width = self.sp_line_width.value()
            it.fill = self.chk_fill.isChecked()
            it.radius = self.sp_radius.value()
        self._update_list_row(it)
        self._refresh_timer.start()

    def set_start_here(self):
        it = self.current_item()
        if not it or not self.clips:
            return
        self.push_undo()
        it.start = round(self._t, 3)
        if it.end <= it.start:
            it.end = round(min(self.total(), it.start + 3.0), 3)
        self._load_item_to_editor(it)
        self._update_list_row(it)
        self._update_overlay_visibility()

    def set_end_here(self):
        it = self.current_item()
        if not it or not self.clips:
            return
        if self._t <= it.start:
            self.statusBar().showMessage("끝 시간은 시작 시간보다 뒤여야 합니다.", 4000)
            return
        self.push_undo()
        it.end = round(self._t, 3)
        self._load_item_to_editor(it)
        self._update_list_row(it)
        self._update_overlay_visibility()

    def goto_selected_start(self):
        it = self.current_item()
        if it:
            self.seek(it.start)

    def apply_selected_preset(self):
        it = self.current_item()
        if not it or it.kind != "text":
            return
        self.push_undo()
        apply_preset(it, self.cb_preset.currentText())
        self._load_item_to_editor(it)
        self._refresh_overlay(it)

    def add_font_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "폰트 파일 선택", "", "폰트 (*.ttf *.otf *.ttc)")
        if not path:
            return
        name = font_display_name(path)
        if not name:
            QMessageBox.warning(self, APP_TITLE, "폰트 파일을 읽을 수 없습니다.")
            return
        idx = self.cb_font.findData(path)
        if idx < 0:
            self.cb_font.insertItem(0, f"★ {name}", path)
            idx = 0
        self.cb_font.setCurrentIndex(idx)

    def pick_color(self, attr: str, title: str):
        it = self.current_item()
        if not it:
            return
        c = QColorDialog.getColor(QColor(*getattr(it, attr)), self, title,
                                  QColorDialog.ColorDialogOption.ShowAlphaChannel)
        if not c.isValid():
            return
        self.push_undo()
        setattr(it, attr, (c.red(), c.green(), c.blue(), c.alpha()))
        self._load_item_to_editor(it)
        self._refresh_overlay(it)

    def set_text_y(self, y: float):
        it = self.current_item()
        if not it or it.kind != "text":
            return
        self.push_undo()
        it.x, it.y = 0.5, y
        self._load_item_to_editor(it)
        self._refresh_overlay(it)

    # ── 미리보기 마우스 조작 ──────────────────────────────────
    def _hit_test(self, x: float, y: float) -> OverlayItem | None:
        tol = 6 / max(1e-6, self.view.transform().m11())
        t = self._t
        for it in reversed(self.items):
            if not (it.start <= t <= it.end or it.id == self.selected_id):
                continue
            if it.kind == "arrow":
                x1, y1 = it.x1 * self.proj_w, it.y1 * self.proj_h
                x2, y2 = it.x2 * self.proj_w, it.y2 * self.proj_h
                dx, dy = x2 - x1, y2 - y1
                L2 = dx * dx + dy * dy
                u = clamp(((x - x1) * dx + (y - y1) * dy) / L2, 0, 1) if L2 > 0 else 0
                dist = math.hypot(x - (x1 + u * dx), y - (y1 + u * dy))
                if dist <= tol + it.line_width * 2:
                    return it
                continue
            bbox = self.overlay_bbox.get(it.id)
            if bbox and bbox[0] - tol <= x <= bbox[2] + tol and bbox[1] - tol <= y <= bbox[3] + tol:
                return it
        return None

    def _on_view_press(self, pos: QPointF):
        if not self.clips:
            return
        if self._want_play:
            self.toggle_play()
        W, H = self.proj_w, self.proj_h
        x, y = pos.x(), pos.y()
        if self.tool == "select":
            it = self.current_item()
            if it and it.kind != "text":
                tol = 10 / max(1e-6, self.view.transform().m11())
                for i, (hx, hy) in enumerate(self._handle_points(it)):
                    if abs(x - hx) <= tol and abs(y - hy) <= tol:
                        self.push_undo()
                        if it.kind != "arrow":
                            normalize_rect(it)
                        self._drag = {"mode": "handle", "i": i}
                        return
            hit = self._hit_test(x, y)
            if hit:
                if hit.id != self.selected_id:
                    self.select_item(hit.id)
                self.push_undo()
                self._drag = {"mode": "move", "sx": x, "sy": y,
                              "orig": (hit.x, hit.y, hit.x1, hit.y1, hit.x2, hit.y2)}
            else:
                self.select_item(None)
        elif self.tool == "text":
            self.add_overlay("text", at=(clamp(x / W, 0, 1), clamp(y / H, 0, 1)))
            self.set_tool("select")
        else:
            rx, ry = clamp(x / W, 0, 1), clamp(y / H, 0, 1)
            if self.add_overlay(self.tool, rect=(rx, ry, rx, ry)):
                self._drag = {"mode": "draw"}

    def _on_view_move(self, pos: QPointF):
        if not self._drag:
            return
        it = self.current_item()
        if not it:
            return
        W, H = self.proj_w, self.proj_h
        rx, ry = clamp(pos.x() / W, 0, 1), clamp(pos.y() / H, 0, 1)
        mode = self._drag["mode"]
        if mode == "move":
            dx = (pos.x() - self._drag["sx"]) / W
            dy = (pos.y() - self._drag["sy"]) / H
            ox, oy, ox1, oy1, ox2, oy2 = self._drag["orig"]
            if it.kind == "text":
                it.x, it.y = clamp(ox + dx, 0, 1), clamp(oy + dy, 0, 1)
                self._loading = True
                self.sp_x.setValue(it.x * 100)
                self.sp_y.setValue(it.y * 100)
                self._loading = False
            else:
                it.x1, it.y1, it.x2, it.y2 = ox1 + dx, oy1 + dy, ox2 + dx, oy2 + dy
        elif mode == "handle":
            i = self._drag["i"]
            if it.kind == "arrow":
                if i == 0:
                    it.x1, it.y1 = rx, ry
                else:
                    it.x2, it.y2 = rx, ry
            else:
                if i in (0, 3):
                    it.x1 = rx
                else:
                    it.x2 = rx
                if i in (0, 1):
                    it.y1 = ry
                else:
                    it.y2 = ry
        elif mode == "draw":
            it.x2, it.y2 = rx, ry
        self._refresh_timer.start()

    def _on_view_release(self, _pos: QPointF):
        if not self._drag:
            return
        mode = self._drag["mode"]
        self._drag = None
        it = self.current_item()
        if not it:
            return
        if mode == "draw":
            W, H = self.proj_w, self.proj_h
            if abs(it.x2 - it.x1) * W < 6 and abs(it.y2 - it.y1) * H < 6:   # 클릭만 했으면 기본 크기
                if it.kind == "arrow":
                    it.x2, it.y2 = it.x1 + 0.15, it.y1
                else:
                    it.x1, it.y1 = it.x1 - 0.1, it.y1 - 0.08
                    it.x2, it.y2 = it.x1 + 0.2, it.y1 + 0.16
            self.set_tool("select")
        if it.kind not in ("text", "arrow"):
            normalize_rect(it)
        self._refresh_overlay(it)

    # ════════════════════════════════════════════════════════
    # 배경음악
    # ════════════════════════════════════════════════════════
    def choose_bgm(self):
        path, _ = QFileDialog.getOpenFileName(self, "배경음악 선택", "", AUDIO_FILTER)
        if path:
            self.set_bgm(path)

    def set_bgm(self, path: str):
        try:
            info = probe_media(path)
        except Exception as e:
            QMessageBox.warning(self, APP_TITLE, f"파일을 읽을 수 없습니다.\n\n{e}")
            return
        if not info.has_audio:
            QMessageBox.warning(self, APP_TITLE, "오디오가 없는 파일입니다.")
            return
        self.bgm_path = path
        self.bgm_duration = info.duration
        self.bgm_player.setSource(QUrl.fromLocalFile(path))
        self.lbl_bgm.setText(f"🎵 {os.path.basename(path)} ({fmt_time(info.duration)}) · 영상 길이에 맞춰 반복")
        self._sync_bgm(self._want_play)

    def clear_bgm(self):
        self.bgm_path = ""
        self.bgm_player.stop()
        self.bgm_player.setSource(QUrl())
        self.lbl_bgm.setText("배경음악 없음")

    # ════════════════════════════════════════════════════════
    # 현재 화면 저장
    # ════════════════════════════════════════════════════════
    def save_snapshot(self):
        if not self.clips:
            return
        k, src = self.locate(self._t)
        clip = self.clips[k]
        base = os.path.splitext(self.clips[0].path)[0]
        path, _ = QFileDialog.getSaveFileName(self, "현재 화면 저장",
                                              f"{base}_{fmt_time(self._t).replace(':', '-')}.png",
                                              "PNG 이미지 (*.png);;JPG 이미지 (*.jpg)")
        if not path:
            return
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            frame = grab_frame(clip.path, src)
            W, H = self.proj_w, self.proj_h
            canvas = Image.new("RGB", (W, H), (0, 0, 0))
            if frame:
                fr = frame.copy()
                fr.thumbnail((W, H), Image.Resampling.LANCZOS)
                if fr.width < W and fr.height < H:
                    ratio = min(W / frame.width, H / frame.height)
                    fr = frame.resize((max(1, int(frame.width * ratio)), max(1, int(frame.height * ratio))),
                                      Image.Resampling.LANCZOS)
                canvas.paste(fr, ((W - fr.width) // 2, (H - fr.height) // 2))
            canvas = canvas.convert("RGBA")
            for it in self.items:
                if not (it.start <= self._t <= it.end):
                    continue
                if it.kind == "mosaic":
                    apply_mosaic_pil(canvas, it, W, H)
                    continue
                img, _ = render_overlay(it, W, H, 1.0, preview=False)
                a = self._item_alpha(it, self._t)
                if a < 1:
                    img.putalpha(img.getchannel("A").point(lambda v, a=a: int(v * a)))
                canvas.alpha_composite(img)
            if path.lower().endswith((".jpg", ".jpeg")):
                canvas.convert("RGB").save(path, quality=95)
            else:
                canvas.save(path)
        finally:
            QApplication.restoreOverrideCursor()
        self.statusBar().showMessage(f"화면 저장: {path}", 5000)

    # ════════════════════════════════════════════════════════
    # 내보내기
    # ════════════════════════════════════════════════════════
    def export_or_cancel(self):
        if self.export_worker:
            self.export_worker.cancel()
            return
        self.export()

    def build_export_cmd(self, out: str, tmpdir: str):
        total = self.total()
        H0 = self.proj_h
        out_h = self.cb_res.currentData() or H0
        W2 = max(2, int(round(self.proj_w * out_h / H0 / 2)) * 2)
        H2 = max(2, int(round(out_h / 2)) * 2)
        s = H2 / H0
        fps = self.proj_fps or 30.0
        fps_s = f"{fps:.3f}".rstrip("0").rstrip(".")
        args, f = [], []
        n_in = 0

        # 1) 영상 구간 이어붙이기
        for k, c in enumerate(self.clips):
            d = c.duration
            info = probe_media(c.path)
            args += ["-ss", f"{c.src_in:.3f}", "-t", f"{d:.3f}", "-i", c.path]
            f.append(f"[{n_in}:v:0]trim=duration={d:.3f},setpts=PTS-STARTPTS,"
                     f"scale={W2}:{H2}:force_original_aspect_ratio=decrease,"
                     f"pad={W2}:{H2}:(ow-iw)/2:(oh-ih)/2:color=black,setsar=1,fps={fps_s},format=yuv420p[cv{k}]")
            if info.has_audio:
                f.append(f"[{n_in}:a:0]atrim=duration={d:.3f},asetpts=PTS-STARTPTS,aresample=48000,"
                         f"aformat=sample_fmts=fltp:channel_layouts=stereo,apad=whole_dur={d:.3f},"
                         f"atrim=duration={d:.3f}[ca{k}]")
            else:
                f.append(f"anullsrc=r=48000:cl=stereo,atrim=duration={d:.3f}[ca{k}]")
            n_in += 1
        n = len(self.clips)
        f.append("".join(f"[cv{k}][ca{k}]" for k in range(n)) + f"concat=n={n}:v=1:a=1[vcat][acat]")
        cur = "[vcat]"

        # 2) 글자 · 도형 · 모자이크
        for i, it in enumerate(self.items):
            st, en = max(0.0, it.start), min(total, it.end)
            if en - st <= 0.01:
                continue
            enable = f"enable='between(t,{st:.3f},{en:.3f})'"
            if it.kind == "mosaic":
                l, t, r, b = rect_px(it, W2, H2)
                l, t = int(clamp(l, 0, W2)) // 2 * 2, int(clamp(t, 0, H2)) // 2 * 2
                cw = (int(clamp(r, 0, W2)) - l) // 2 * 2
                ch = (int(clamp(b, 0, H2)) - t) // 2 * 2
                if cw < 4 or ch < 4:
                    continue
                bs = max(2, int(round(it.mosaic_size * s)))
                f.append(f"{cur}split[ma{i}][mb{i}];[mb{i}]crop={cw}:{ch}:{l}:{t},"
                         f"scale={max(1, cw // bs)}:{max(1, ch // bs)}:flags=area,"
                         f"scale={cw}:{ch}:flags=neighbor[mc{i}];[ma{i}][mc{i}]overlay={l}:{t}:{enable}[mo{i}]")
                cur = f"[mo{i}]"
                continue
            img, _ = render_overlay(it, W2, H2, s, preview=False)
            if img.getbbox() is None:
                continue
            p = os.path.join(tmpdir, f"ov_{i:03d}.png")
            img.save(p)
            if it.fade_in > 0 or it.fade_out > 0:
                args += ["-loop", "1", "-framerate", fps_s, "-t", f"{en + 0.2:.3f}", "-i", p]
                chain = "format=rgba"
                if it.fade_in > 0:
                    chain += f",fade=t=in:st={st:.3f}:d={it.fade_in:.3f}:alpha=1"
                if it.fade_out > 0:
                    chain += f",fade=t=out:st={max(st, en - it.fade_out):.3f}:d={it.fade_out:.3f}:alpha=1"
                f.append(f"[{n_in}:v]{chain}[ov{i}]")
                src = f"[ov{i}]"
            else:
                args += ["-i", p]
                src = f"[{n_in}:v]"
            n_in += 1
            f.append(f"{cur}{src}overlay=0:0:{enable}[vo{i}]")
            cur = f"[vo{i}]"

        fade = self.chk_fade_all.isChecked()
        fd = min(0.5, total / 4)
        if fade:
            f.append(f"{cur}fade=t=in:st=0:d={fd:.3f},fade=t=out:st={max(0.0, total - fd):.3f}:d={fd:.3f}[vfd]")
            cur = "[vfd]"
        f.append(f"{cur}format=yuv420p[vout]")

        # 3) 소리
        f.append(f"[acat]volume={self.orig_volume:.2f}[a0]")
        acur = "[a0]"
        if self.bgm_path and os.path.isfile(self.bgm_path):
            args += ["-stream_loop", "-1", "-i", self.bgm_path]
            f.append(f"[{n_in}:a:0]atrim=duration={total:.3f},asetpts=PTS-STARTPTS,aresample=48000,"
                     f"aformat=sample_fmts=fltp:channel_layouts=stereo,volume={self.bgm_volume:.2f}[bg]")
            f.append(f"{acur}[bg]amix=inputs=2:duration=first:dropout_transition=0:normalize=0[am]")
            acur = "[am]"
            n_in += 1
        if fade:
            f.append(f"{acur}afade=t=in:st=0:d={fd:.3f},afade=t=out:st={max(0.0, total - fd):.3f}:d={fd:.3f}[afd]")
            acur = "[afd]"
        f.append(f"{acur}anull[aout]")

        cmd = [FFMPEG, "-y", "-hide_banner", "-loglevel", "error"] + args + [
            "-filter_complex", ";".join(f), "-map", "[vout]", "-map", "[aout]",
            "-c:v", "libx264", "-preset", "medium", "-crf", str(self.cb_quality.currentData()),
            "-r", fps_s, "-c:a", "aac", "-b:a", "192k", "-movflags", "+faststart",
            "-progress", "pipe:1", "-nostats", out]
        return cmd, total

    def export(self):
        if not self.clips:
            return
        total = self.total()
        bad = [it for it in self.items if it.end <= it.start or it.start >= total]
        if bad:
            QMessageBox.warning(self, APP_TITLE, "시작/끝 시간이 잘못된 항목이 있습니다.\n\n" +
                                "\n".join(self._item_label(b) for b in bad[:5]))
            self.select_item(bad[0].id)
            return
        base = os.path.splitext(self.clips[0].path)[0]
        out, _ = QFileDialog.getSaveFileName(self, "저장 위치", base + "_edited.mp4", "MP4 영상 (*.mp4)")
        if not out:
            return
        if not out.lower().endswith(".mp4"):
            out += ".mp4"
        srcs = {os.path.abspath(c.path) for c in self.clips}
        if os.path.abspath(out) in srcs or (self.bgm_path and os.path.abspath(out) == os.path.abspath(self.bgm_path)):
            QMessageBox.warning(self, APP_TITLE, "원본 파일과 다른 이름으로 저장해 주세요.")
            return
        if self._want_play:
            self.toggle_play()
        tmpdir = tempfile.mkdtemp(prefix="vte_")
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            cmd, total = self.build_export_cmd(out, tmpdir)
        except Exception as e:
            QApplication.restoreOverrideCursor()
            shutil.rmtree(tmpdir, ignore_errors=True)
            QMessageBox.warning(self, APP_TITLE, f"내보내기 준비 실패\n\n{e}")
            return
        QApplication.restoreOverrideCursor()

        self.progress.setValue(0)
        self.btn_export.setText("⏹ 내보내기 취소")
        self.statusBar().showMessage("내보내는 중…")
        self.export_worker = ExportWorker(cmd, total, tmpdir, out)
        self.export_worker.progress.connect(self.progress.setValue)
        self.export_worker.done.connect(self._on_export_done)
        self.export_worker.start()

    def _on_export_done(self, ok: bool, msg: str):
        self.export_worker.wait()
        self.export_worker = None
        self.btn_export.setText("🎬 MP4로 내보내기")
        if ok:
            self.statusBar().showMessage(f"저장 완료: {msg}")
            box = QMessageBox(self)
            box.setWindowTitle(APP_TITLE)
            box.setText(f"저장이 완료되었습니다.\n\n{msg}")
            btn_folder = box.addButton("폴더 열기", QMessageBox.ButtonRole.ActionRole)
            box.addButton("확인", QMessageBox.ButtonRole.AcceptRole)
            box.exec()
            if box.clickedButton() == btn_folder:
                if os.name == "nt":
                    subprocess.Popen(["explorer", "/select,", os.path.normpath(msg)])
                elif sys.platform == "darwin":
                    subprocess.Popen(["open", os.path.dirname(msg)])
                else:
                    subprocess.Popen(["xdg-open", os.path.dirname(msg)])
        else:
            self.progress.setValue(0)
            self.statusBar().showMessage("내보내기 실패/취소")
            QMessageBox.warning(self, APP_TITLE, msg)

    def closeEvent(self, e):
        if self.export_worker:
            if QMessageBox.question(self, APP_TITLE, "내보내는 중입니다. 취소하고 종료할까요?") \
                    != QMessageBox.StandardButton.Yes:
                e.ignore()
                return
            self.export_worker.cancel()
            self.export_worker.wait(5000)
        self.player.stop()
        self.bgm_player.stop()
        super().closeEvent(e)


def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setFont(QFont("Malgun Gothic", 9))
    w = MainWindow()
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
