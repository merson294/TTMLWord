#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TTML Word Editor - word-level editor for Apple Music / Spicy Lyrics TTML files.
Пословный редактор TTML: тайминг каждого слова, караоке-просмотр, замедление звука.

Run / Запуск:    python ttml_word_editor.py [file.ttml] [--lang en|ru] [--theme cosmic|light|contrast|plain]
Optional / По желанию:
    pip install pygame    - audio playback / воспроизведение звука
    pip install numpy     - slow-down (0.25x-1.5x) / замедление

Themes: built-in Cosmos (default), Light, High contrast, System - or your own CSS
(Theme menu; see Help > CSS theme reference). Interface: Russian / English / your own language pack.
Settings live in a per-user folder (Help > Open settings folder); it is safe to delete it.
"""
import colorsys
import copy
import json
import math
import os
import random
import re
import shutil
import sys
import time
import traceback
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field

os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
try:
    import pygame
    HAVE_PYGAME = True
except Exception:  # pygame не обязателен
    pygame = None
    HAVE_PYGAME = False

import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog, ttk

# ----------------------------------------------------------------------------
# МОДЕЛЬ
# ----------------------------------------------------------------------------
TTML = "http://www.w3.org/ns/ttml"
TTM = "http://www.w3.org/ns/ttml#metadata"
ITUNES = "http://music.apple.com/lyric-ttml-internal"
TTS = "http://www.w3.org/ns/ttml#styling"
XMLNS = "http://www.w3.org/XML/1998/namespace"
ET.register_namespace("", TTML)
ET.register_namespace("ttm", TTM)
ET.register_namespace("itunes", ITUNES)
ET.register_namespace("tts", TTS)

A_LANG = f"{{{XMLNS}}}lang"
A_ID = f"{{{XMLNS}}}id"
A_TIMING = f"{{{ITUNES}}}timing"
A_PART = f"{{{ITUNES}}}song-part"
A_KEY = f"{{{ITUNES}}}key"
A_AGENT = f"{{{TTM}}}agent"
A_ROLE = f"{{{TTM}}}role"

MIN_DUR = 0.01
DEFAULT_WORD = 0.4
PARTS = ["", "Intro", "Verse", "Pre-Chorus", "Chorus", "Bridge", "Outro", "Instrumental"]


def q(tag, ns=TTML):
    return f"{{{ns}}}{tag}"


def parse_time(s):
    """'1:23.456' | '83.456' | '1:02:03.5' | '1234ms' | '5s' -> секунды"""
    s = (s or "").strip().replace(",", ".")
    if not s:
        raise ValueError("empty")
    if s.endswith("ms"):
        v = float(s[:-2]) / 1000.0
    else:
        if s.endswith("s"):
            s = s[:-1]
        parts = s.split(":")
        if len(parts) > 3:
            raise ValueError(s)
        v = 0.0
        for p in parts:
            v = v * 60 + float(p)
    if v < 0 or math.isnan(v) or math.isinf(v):
        raise ValueError(s)
    return v


def fmt_time(t):
    ms = int(round(max(0.0, t) * 1000))
    h, ms = divmod(ms, 3600000)
    m, ms = divmod(ms, 60000)
    s = ms / 1000.0
    if h:
        return f"{h}:{m:02d}:{s:06.3f}"
    if m:
        return f"{m}:{s:06.3f}"
    return f"{s:.3f}"


@dataclass
class Word:
    text: str
    begin: float
    end: float
    space: bool = True   # пробел после слова (False = слог внутри слова)
    bg: bool = False     # бэк-вокал


@dataclass
class Line:
    words: list = field(default_factory=list)
    agent: str = "v1"
    part: str = ""
    extras: list = field(default_factory=list)   # переводы/транслит (сырые XML-элементы)

    @property
    def begin(self):
        return min((w.begin for w in self.words), default=0.0)

    @property
    def end(self):
        return max((w.end for w in self.words), default=0.0)

    def text(self):
        out = []
        for i, w in enumerate(self.words):
            out.append(w.text)
            if w.space and i < len(self.words) - 1:
                out.append(" ")
        return "".join(out)


def make_words(text, t0, t1, bg=False):
    toks = text.split()
    n = len(toks)
    if n == 0:
        return []
    if t1 <= t0:
        t1 = t0 + DEFAULT_WORD * n
    d = (t1 - t0) / n
    return [Word(tok, t0 + i * d, t0 + (i + 1) * d, space=(i < n - 1), bg=bg)
            for i, tok in enumerate(toks)]


class Doc:
    def __init__(self):
        self.lines = []
        self.agents = [["v1", "person"]]
        self.lang = "ru"
        self.head = None          # исходный <head> (без агентов)
        self.tt_attrib = {}

    @classmethod
    def new(cls):
        return cls()

    # ---------- загрузка ----------
    @classmethod
    def load(cls, path):
        root = ET.parse(path).getroot()
        if root.tag != q("tt"):
            raise ValueError(tr("Это не TTML: корневой элемент не <tt>"))
        doc = cls()
        doc.lang = root.get(A_LANG, "ru")
        doc.tt_attrib = {k: v for k, v in root.attrib.items() if k not in (A_LANG, A_TIMING)}
        head = root.find(q("head"))
        doc.agents = []
        if head is not None:
            for a in head.iter(q("agent", TTM)):
                aid = a.get(A_ID)
                if aid:
                    doc.agents.append([aid, a.get("type", "person")])
            doc.head = copy.deepcopy(head)
            for parent in list(doc.head.iter()):
                for ch in list(parent):
                    if ch.tag == q("agent", TTM):
                        parent.remove(ch)
        body = root.find(q("body"))
        if body is not None:
            for child in body:
                if child.tag == q("div"):
                    part = child.get(A_PART, "")
                    for p in child.iter(q("p")):
                        ln = cls._parse_p(p, part)
                        if ln.words:
                            doc.lines.append(ln)
                elif child.tag == q("p"):
                    ln = cls._parse_p(child, "")
                    if ln.words:
                        doc.lines.append(ln)
        if not doc.agents:
            for ln in doc.lines:
                if ln.agent and not any(a[0] == ln.agent for a in doc.agents):
                    doc.agents.append([ln.agent, "person"])
        if not doc.agents:
            doc.agents = [["v1", "person"]]
        for ln in doc.lines:
            if not ln.agent:
                ln.agent = doc.agents[0][0]
        return doc

    @staticmethod
    def _parse_p(p, part):
        line = Line(agent=p.get(A_AGENT) or "", part=part or "")
        pb = parse_time(p.get("begin")) if p.get("begin") else 0.0
        pe = parse_time(p.get("end")) if p.get("end") else pb

        def span_word(sp, bg=False):
            raw = "".join(sp.itertext())
            text = raw.strip()
            b = parse_time(sp.get("begin")) if sp.get("begin") else pb
            e = parse_time(sp.get("end")) if sp.get("end") else max(pe, b)
            space = bool(sp.tail) or raw.endswith((" ", "\n", "\t"))
            return Word(text, b, max(e, b), space, bg)

        for child in p:
            if child.tag != q("span"):
                continue
            role = child.get(A_ROLE)
            if role == "x-bg":
                subs = [c for c in child if c.tag == q("span")]
                grp = [span_word(s, True) for s in subs] if subs else [span_word(child, True)]
                if grp:
                    grp[-1].space = bool(child.tail)
                    grp[0].text = grp[0].text.lstrip("(")
                    grp[-1].text = grp[-1].text.rstrip(")")
                    line.words.extend(w for w in grp if w.text)
            elif role in ("x-translation", "x-roman"):
                ex = copy.deepcopy(child)
                ex.tail = None
                line.extras.append(ex)
            else:
                w = span_word(child)
                if w.text:
                    line.words.append(w)
        if not line.words and p.text and p.text.strip():   # построчный TTML
            line.words = make_words(p.text.strip(), pb, pe)
        if line.words:
            line.words[-1].space = False
        return line

    # ---------- сохранение ----------
    def build(self):
        attrib = dict(self.tt_attrib)
        attrib[A_LANG] = self.lang or "ru"
        attrib[A_TIMING] = "Word"
        tt = ET.Element(q("tt"), attrib)
        head = copy.deepcopy(self.head) if self.head is not None else ET.Element(q("head"))
        meta = head.find(q("metadata"))
        if meta is None:
            meta = ET.Element(q("metadata"))
            head.insert(0, meta)
        agents = [list(a) for a in self.agents]
        for ln in self.lines:
            if ln.agent and not any(a[0] == ln.agent for a in agents):
                agents.append([ln.agent, "other" if ln.agent.startswith("v1000") else "person"])
        for i, (aid, typ) in enumerate(agents):
            meta.insert(i, ET.Element(q("agent", TTM), {"type": typ, A_ID: aid}))
        tt.append(head)

        lines = [ln for ln in self.lines if ln.words]
        total = max((ln.end for ln in lines), default=0.0)
        body = ET.SubElement(tt, q("body"), {"dur": fmt_time(total)})
        div = None
        cur_part = None
        div_lines = []
        divs = []
        for idx, ln in enumerate(lines, start=1):
            if div is None or ln.part != cur_part:
                attrs = {}
                div = ET.SubElement(body, q("div"), attrs)
                cur_part = ln.part
                div_lines = []
                divs.append((div, div_lines, ln.part))
            div_lines.append(ln)
            p = ET.SubElement(div, q("p"))
            self._fill_p(p, ln, idx)
        for d, dl, part in divs:
            d.set("begin", fmt_time(min(l.begin for l in dl)))
            d.set("end", fmt_time(max(l.end for l in dl)))
            if part:
                d.set(A_PART, part)
        _indent(tt)
        return tt

    @staticmethod
    def _fill_p(p, ln, idx):
        p.set("begin", fmt_time(ln.begin))
        p.set("end", fmt_time(ln.end))
        p.set(A_AGENT, ln.agent or "v1")
        p.set(A_KEY, f"L{idx}")
        ws = ln.words
        i = 0
        while i < len(ws):
            w = ws[i]
            last = i == len(ws) - 1
            if not w.bg:
                sp = ET.SubElement(p, q("span"), {"begin": fmt_time(w.begin), "end": fmt_time(w.end)})
                sp.text = w.text
                if w.space and not last:
                    sp.tail = " "
                i += 1
            else:
                j = i
                while j < len(ws) and ws[j].bg:
                    j += 1
                grp = ws[i:j]
                wrap = ET.SubElement(p, q("span"), {A_ROLE: "x-bg"})
                for k, g in enumerate(grp):
                    s = ET.SubElement(wrap, q("span"), {"begin": fmt_time(g.begin), "end": fmt_time(g.end)})
                    s.text = ("(" if k == 0 else "") + g.text + (")" if k == len(grp) - 1 else "")
                    if k < len(grp) - 1 and g.space:
                        s.tail = " "
                if grp[-1].space and j < len(ws):
                    wrap.tail = " "
                i = j
        for ex in ln.extras:
            p.append(copy.deepcopy(ex))

    def save(self, path):
        tt = self.build()
        ET.ElementTree(tt).write(path, encoding="utf-8", xml_declaration=True)


def _indent(el, level=0):
    """Отступы только вне <p> — внутри строки пробелы значимы."""
    kids = list(el)
    if el.tag == q("p") or el.tag.endswith("}text") or not kids:
        return
    el.text = "\n" + "  " * (level + 1)
    for k in kids:
        _indent(k, level + 1)
    for k in kids[:-1]:
        k.tail = "\n" + "  " * (level + 1)
    kids[-1].tail = "\n" + "  " * level


# ---------- LRC ----------
LRC_TS = re.compile(r"\[(\d+):(\d+(?:[.:]\d+)?)\]")
LRC_WORD = re.compile(r"<(\d+):(\d+(?:[.:]\d+)?)>")


def _lrc_t(m, s):
    return int(m) * 60 + float(s.replace(":", "."))


def parse_lrc(text):
    entries = []
    for raw in text.splitlines():
        stamps = list(LRC_TS.finditer(raw))
        if not stamps:
            continue
        body = raw[stamps[-1].end():].strip()
        for m in stamps:
            entries.append((_lrc_t(m.group(1), m.group(2)), body))
    entries.sort(key=lambda x: x[0])
    lines = []
    for i, (t, body) in enumerate(entries):
        if not body:
            continue
        n_tok = max(1, len(LRC_WORD.sub("", body).split()))
        nxt = entries[i + 1][0] if i + 1 < len(entries) else t + 0.6 * n_tok
        nxt = min(nxt, t + 0.7 * n_tok + 0.3)
        if LRC_WORD.search(body):
            parts = LRC_WORD.split(body)
            items = []
            for k in range(1, len(parts), 3):
                items.append((_lrc_t(parts[k], parts[k + 1]), parts[k + 2]))
            words = []
            for k, (t0, txt) in enumerate(items):
                if not txt.strip():
                    continue
                t1 = items[k + 1][0] if k + 1 < len(items) else nxt
                ws = make_words(txt, t0, max(t1, t0 + 0.05))
                if ws:
                    ws[-1].space = txt.endswith(" ")
                words.extend(ws)
            pre = parts[0].strip()
            if pre and words:
                words = make_words(pre, t, words[0].begin) + words
        else:
            words = make_words(body, t, nxt)
        if words:
            words[-1].space = False
            lines.append(Line(words=words))
    return lines


def to_lrc(doc, enhanced):
    def stamp(t, br):
        cs = int(round(t * 100))
        m, cs = divmod(cs, 6000)
        s = f"{m:02d}:{cs / 100:05.2f}"
        return f"[{s}]" if br == "[" else f"<{s}>"

    out = []
    for ln in doc.lines:
        if not ln.words:
            continue
        if enhanced:
            body = "".join(stamp(w.begin, "<") + w.text + (" " if w.space else "") for w in ln.words).rstrip()
        else:
            body = ln.text()
        out.append(stamp(ln.begin, "[") + body)
    return "\n".join(out) + "\n"



def time_stretch(arr, speed, keep_pitch=True):
    """Замедление/ускорение звука. arr: numpy int16 (n, ch); speed<1 — медленнее.
    keep_pitch=True — WSOLA (тон сохраняется), False — «как на магнитофоне»."""
    import numpy as np
    if arr.ndim == 1:
        arr = arr[:, None]
    n, ch = arr.shape
    x = arr.astype(np.float32)
    if not keep_pitch:
        out_n = max(1, int(n / speed))
        idx = np.linspace(0, n - 1, out_n)
        i0 = idx.astype(np.int64)
        i1 = np.minimum(i0 + 1, n - 1)
        fr = (idx - i0).astype(np.float32)[:, None]
        out = x[i0] * (1 - fr) + x[i1] * fr
        return np.clip(out, -32768, 32767).astype(np.int16)
    win, hs, tol, dec = 2048, 1024, 512, 8
    hann = (0.5 - 0.5 * np.cos(2 * np.pi * np.arange(win) / win)).astype(np.float32)[:, None]
    xp = np.concatenate([x, np.zeros((win + 2 * tol + 4 * dec, ch), np.float32)])
    mono = xp.mean(axis=1)
    m = mono[: len(mono) // dec * dec].reshape(-1, dec).mean(axis=1)
    wd = win // dec
    target = int(n / speed)
    out = np.zeros((target + 2 * win, ch), np.float32)
    out[:win] += xp[:win] * hann
    prev, k = 0, 1
    while True:
        out_pos = k * hs
        nominal = int(out_pos * speed)
        if nominal >= n or out_pos + win > out.shape[0]:
            break
        lo = max(0, nominal - tol)
        hi = nominal + tol
        r0 = (prev + hs) // dec
        ref = m[r0: r0 + wd]
        reg = m[lo // dec: hi // dec + wd]
        if len(ref) == wd and len(reg) >= wd:
            best = lo + int(np.argmax(np.correlate(reg, ref, mode="valid"))) * dec
        else:
            best = nominal
        out[out_pos: out_pos + win] += xp[best: best + win] * hann
        prev = best
        k += 1
    return np.clip(out[:target], -32768, 32767).astype(np.int16)


# ----------------------------------------------------------------------------
# GUI
# ----------------------------------------------------------------------------
TEXT_CLASSES = ("Entry", "TEntry", "TCombobox", "Text", "Spinbox", "TSpinbox")

# ---- космическая тема
BG0 = "#070a1a"      # глубокий космос
BG1 = "#0d1230"      # панели
BG2 = "#151b45"      # приподнятые элементы
BORDER = "#2a3170"
FG = "#dfe6ff"
FG_DIM = "#8a94c8"
ACC = "#4de1ff"      # неон-циан
ACC_D = "#1f6fd1"
MAG = "#c86bff"      # неон-маджента
GOLD = "#ffd166"
GREEN = "#5cf2a0"

C_BG = BG1
C_WORD = "#1b2358"
C_WORD_LINE = "#27357f"
C_WORD_BG = "#3a2470"
C_WORD_SEL = "#2b6bff"
C_WORD_NOW = "#12a56c"
C_PLAYHEAD = "#ff5d9e"
SEL_FG = "#ffffff"
SKY_A, SKY_B, STAR_DIM = "#070a1a", "#0f1538", "#2a3170"
NEB_COLS = ("#3a1a8a", "#0d4a8c", "#6a1f7a")
TREE_LINE, TREE_NOW, TREE_BGFG = "#141b48", "#0c5c3c", "#c9a0ff"
GRID, WORD_TEXT, WORD_TEXT_NOW = "#1a2152", "#eaf0ff", "#04241a"
WORD_BORDER, WORD_BORDER_BG, HOVER_COL = "#3a4590", "#6a4fb0", "#ffb84d"
MINI_A, MINI_B = "#3fa9d6", "#8e5bd6"
WORD_R, GLOSS = 6.0, True


def _rgb(h):
    h = h.lstrip("#")
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


def blend(a, b, f):
    """Смесь цветов a→b, f∈[0,1]."""
    f = 0.0 if f < 0 else (1.0 if f > 1 else f)
    ra, ga, ba = _rgb(a)
    rb, gb, bb = _rgb(b)
    return "#%02x%02x%02x" % (int(ra + (rb - ra) * f), int(ga + (gb - ga) * f), int(ba + (bb - ba) * f))


def rr_points(x0, y0, x1, y1, r):
    r = max(0.0, min(r, (x1 - x0) / 2.0, (y1 - y0) / 2.0))
    return [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1,
            x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]


def rrect(c, x0, y0, x1, y1, r, **kw):
    """Скруглённый прямоугольник на Canvas (сглаженный полигон); при малом радиусе — обычный."""
    if r < 1.5 or x1 - x0 < 4 or y1 - y0 < 4:
        return c.create_rectangle(x0, y0, x1, y1, **kw)
    return c.create_polygon(rr_points(x0, y0, x1, y1, r), smooth=True, splinesteps=8, **kw)


class Starfield:
    """Космический фон: градиент, туманности, мерцающие звёзды с параллаксом и метеоры.
    Цвета берутся из активной темы; отдельные слои отключаются флагами fx."""
    TINTS = ("#ffffff", "#9fe8ff", "#d9b3ff", "#fff1c2")

    def __init__(self, n=90, seed=1):
        r = random.Random(seed)
        self.stars = [(r.random(), r.random(), r.choice((1, 1, 1, 2, 2, 3)), r.random() * 6.283,
                       r.uniform(0.7, 2.4), r.uniform(0.03, 0.3), r.choice(self.TINTS)) for _ in range(n)]
        self.neb = [(r.random(), r.random(), r.uniform(0.25, 0.5)) for _ in range(3)]
        self.meteor = None
        self.next_meteor = None

    def draw(self, c, W, H, t, shift=0.0, animate=True, fx=None):
        fx = fx or {}
        tt = t if animate else 0.0
        if fx.get("gradient", True):
            bands = 8
            for i in range(bands):
                c.create_rectangle(0, H * i / bands, W, H * (i + 1) / bands + 1, outline="",
                                   fill=blend(SKY_A, SKY_B, i / (bands - 1)))
        else:
            c.create_rectangle(0, 0, W, H, fill=BG0, outline="")
        if fx.get("nebula", True):
            for k, (nx, ny, nr) in enumerate(self.neb):
                col = NEB_COLS[k % len(NEB_COLS)]
                cx = (nx * W * 1.4 - shift * 0.05 - tt * (0.6 + 0.4 * k)) % (W * 1.4) - W * 0.2
                cy = ny * H
                R = nr * max(W, H) * 0.6
                for j in range(5):
                    rr = R * (1 - j * 0.18)
                    c.create_oval(cx - rr, cy - rr * 0.5, cx + rr, cy + rr * 0.5, outline="",
                                  fill=blend(SKY_A, col, 0.10 + 0.075 * j))
        if fx.get("stars", True):
            for sx, sy, sz, ph, fr, depth, tint in self.stars:
                x = (sx * W - shift * depth - tt * depth * 12.0) % W
                y = sy * H
                f = 0.5 + 0.5 * math.sin(tt * fr + ph) if animate else 0.6
                c.create_rectangle(x, y, x + sz, y + sz, fill=blend(STAR_DIM, tint, 0.25 + 0.75 * f), outline="")
                if sz == 3 and f > 0.8:
                    gl = blend(SKY_A, tint, 0.45)
                    c.create_line(x - 3, y + 1, x + 6, y + 1, fill=gl)
                    c.create_line(x + 1, y - 3, x + 1, y + 6, fill=gl)
        if animate and fx.get("meteors", True):
            if self.next_meteor is None:
                self.next_meteor = tt + random.uniform(3, 7)
            if self.meteor is None and tt >= self.next_meteor:
                self.meteor = (tt, random.uniform(0.35, 1.0) * W, random.uniform(0.0, 0.35) * H,
                               random.uniform(0.8, 1.2))
            if self.meteor is not None:
                t0, x0, y0, dur = self.meteor
                p = (tt - t0) / dur
                if p >= 1.0:
                    self.meteor = None
                    self.next_meteor = tt + random.uniform(6, 13)
                else:
                    def pos(q_):
                        return x0 - q_ * W * 0.6, y0 + q_ * W * 0.33
                    fade = min(1.0, (1.0 - p) * 3.0)
                    for i in range(8):
                        a, b = pos(max(0.0, p - i * 0.012)), pos(max(0.0, p - (i + 1) * 0.012))
                        c.create_line(a[0], a[1], b[0], b[1], width=max(1, 3 - i // 3),
                                      fill=blend(SKY_A, "#ffffff", (1 - i / 8.0) * fade))


# ----------------------------------------------------------------------------
# ТЕМЫ: мини-CSS
# ----------------------------------------------------------------------------
VERSION = "1.0"
THEME_MODES = ("cosmic", "light", "contrast", "plain", "css")
FONT_NAMES = ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont")

_NAMED = {"white": "#ffffff", "black": "#000000", "red": "#ff0000", "green": "#008000", "blue": "#0000ff",
          "cyan": "#00ffff", "magenta": "#ff00ff", "yellow": "#ffff00", "gray": "#808080", "grey": "#808080",
          "orange": "#ffa500", "purple": "#800080", "pink": "#ffc0cb", "gold": "#ffd700",
          "transparent": "#00000000"}


def parse_color(v):
    """'#rgb' | '#rgba' | '#rrggbb' | '#rrggbbaa' | rgb()/rgba()/hsl()/hsla() | имя  ->  (r, g, b, a) или None."""
    if v is None:
        return None
    v = v.strip().lower()
    v = _NAMED.get(v, v)
    m = re.fullmatch(r"#([0-9a-f]+)", v)
    if m:
        h = m.group(1)
        if len(h) in (3, 4):
            h = "".join(ch * 2 for ch in h)
        if len(h) == 6:
            h += "ff"
        if len(h) != 8:
            return None
        return (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16), int(h[6:8], 16) / 255.0)
    m = re.fullmatch(r"(rgba?|hsla?)\(\s*([^)]*)\)", v)
    if not m:
        return None
    parts = [p for p in re.split(r"[\s,/]+", m.group(2).strip()) if p]
    if len(parts) not in (3, 4):
        return None
    try:
        a = 1.0
        if len(parts) == 4:
            a = float(parts[3][:-1]) / 100.0 if parts[3].endswith("%") else float(parts[3])
        if m.group(1).startswith("rgb"):
            rgb = [float(p[:-1]) * 2.55 if p.endswith("%") else float(p) for p in parts[:3]]
        else:
            h = (float(parts[0].replace("deg", "")) % 360) / 360.0
            s_ = float(parts[1].rstrip("%")) / 100.0
            l_ = float(parts[2].rstrip("%")) / 100.0
            rgb = [x * 255 for x in colorsys.hls_to_rgb(h, l_, s_)]
        r, g, b = [int(min(255, max(0, round(x)))) for x in rgb]
        return (r, g, b, min(1.0, max(0.0, a)))
    except ValueError:
        return None


def color_hex(c, over="#000000"):
    """(r, g, b, a) -> '#rrggbb'; прозрачность смешивается с цветом подложки over."""
    r, g, b, a = c
    if a < 1.0:
        orr, og, ob = _rgb(over)
        r, g, b = r * a + orr * (1 - a), g * a + og * (1 - a), b * a + ob * (1 - a)
    return "#%02x%02x%02x" % (int(round(r)), int(round(g)), int(round(b)))


def parse_num(v, default=None):
    m = re.fullmatch(r"\s*(-?\d+(?:\.\d+)?|-?\.\d+)\s*(px|ms|s|%)?\s*", v or "")
    if not m:
        return default
    x = float(m.group(1))
    if m.group(2) == "s":
        return x * 1000.0
    if m.group(2) == "%":
        return x / 100.0
    return x


def parse_flag(v, default=None):
    v = (v or "").strip().lower()
    if v in ("on", "true", "yes", "1"):
        return True
    if v in ("off", "false", "no", "0", "none"):
        return False
    return default


COSMIC_CSS = r"""/* TTML Word Editor - "Cosmos" theme (the built-in default).
   Copy this file, change what you like, then: Theme > Load custom CSS...
   Keep only the lines you change - everything else comes from the base theme.
   Start the file with  @base light;  (cosmic | light | contrast | plain)  to pick another base.
   The file is watched: save it and the editor refreshes instantly (F9 = force reload).
   Full reference: Help > CSS theme reference. */

:root {
  /* surfaces */
  --bg0: #070a1a;            /* timeline, tree, canvases */
  --bg1: #0d1230;            /* panels, menu bar */
  --bg2: #151b45;            /* buttons, inputs */
  --border: #2a3170;
  /* text */
  --fg: #dfe6ff;
  --fg-dim: #8a94c8;
  /* accents */
  --accent: #4de1ff;         /* neon cyan */
  --accent-dark: #1f6fd1;    /* selection background */
  --selection-text: #ffffff;
  --accent2: #c86bff;        /* neon magenta */
  --gold: #ffd166;
  --green: #5cf2a0;
  --playhead: #ff5d9e;
  /* word blocks on the timeline */
  --word: #1b2358;
  --word-line: #27357f;
  --word-bg: #3a2470;
  --word-selected: #2b6bff;
  --word-now: #12a56c;
  --word-text: #eaf0ff;
  --word-text-now: #04241a;
  --word-border: #3a4590;
  --word-border-bg: #6a4fb0;
  --hover: #ffb84d;
  --grid: #1a2152;
  /* sky */
  --sky-a: #070a1a;
  --sky-b: #0f1538;
  --star-dim: #2a3170;
  --nebula-1: #3a1a8a;
  --nebula-2: #0d4a8c;
  --nebula-3: #6a1f7a;
  /* tree + minimap */
  --tree-line: #141b48;
  --tree-now: #0c5c3c;
  --tree-bg-text: #c9a0ff;
  --mini-a: #3fa9d6;
  --mini-b: #8e5bd6;
  /* glass menus */
  --menu-bg: rgba(13, 18, 48, 0.80);
  --menu-border: rgba(77, 225, 255, 0.35);
  --menu-hover: rgba(77, 225, 255, 0.18);
}

app      { ttk-theme: clam; native-menus: off; font-family: ""; font-size: 0; }
menubar  { background: var(--bg1); color: var(--fg); hover-background: var(--menu-hover); hover-color: #ffffff;
           radius: 8px; brand: "✦ TTML Word Editor"; brand-color: var(--fg-dim); border-color: var(--border); }
menu     { background: var(--menu-bg); color: var(--fg); accel-color: var(--fg-dim);
           border-color: var(--menu-border); border-width: 1px; border-radius: 12px; padding: 6px;
           item-padding: 7px 14px; item-radius: 8px; hover-background: var(--menu-hover); hover-color: #ffffff;
           separator-color: var(--border); header-color: var(--accent); blur: on; effects: on; fade: 140ms; }
timeline { stars: on; nebula: on; meteors: on; gradient: on; }
word     { radius: 6px; gloss: on; }
karaoke  { stars: on; nebula: on; meteors: on; font-family: ""; font-size: 44px; color-future: #e8ecff;
           color-sung: var(--gold); color-current: #ff6b9d; color-dim: #4a5288;
           color-bg-future: #c9a0ff; color-bg-sung: #efd9ff; }
tree     { row-height: 24px; }
"""

LIGHT_CSS = r"""/* Built-in light theme */
:root {
  --bg0: #f6f7fb; --bg1: #eceff7; --bg2: #ffffff; --border: #c9d0e6;
  --fg: #1d2340; --fg-dim: #6a7398;
  --accent: #2563eb; --accent-dark: #2f6fe4; --selection-text: #ffffff; --accent2: #9333ea;
  --gold: #d97706; --green: #16a34a; --playhead: #e11d48;
  --word: #dfe6fb; --word-line: #c9d6f7; --word-bg: #eadcfb; --word-selected: #7aa7ff; --word-now: #7ee2a8;
  --word-text: #1d2340; --word-text-now: #053b1e; --word-border: #aab5dd; --word-border-bg: #b79be6;
  --hover: #f59e0b; --grid: #dfe3f1;
  --sky-a: #f6f7fb; --sky-b: #e6ebfa; --star-dim: #c5cbe3;
  --nebula-1: #dfe6ff; --nebula-2: #e8dcff; --nebula-3: #d9f0ff;
  --tree-line: #e4e9f8; --tree-now: #c9f4dc; --tree-bg-text: #7c3aed;
  --mini-a: #6f95e8; --mini-b: #a879e8;
  --menu-bg: rgba(255, 255, 255, 0.86); --menu-border: rgba(30, 40, 90, 0.18); --menu-hover: rgba(37, 99, 235, 0.12);
}
app      { ttk-theme: clam; native-menus: off; font-family: ""; font-size: 0; }
menubar  { background: var(--bg1); color: var(--fg); hover-background: var(--menu-hover); hover-color: var(--fg);
           radius: 8px; brand: "TTML Word Editor"; brand-color: var(--fg-dim); border-color: var(--border); }
menu     { background: var(--menu-bg); color: var(--fg); accel-color: var(--fg-dim);
           border-color: var(--menu-border); border-width: 1px; border-radius: 12px; padding: 6px;
           item-padding: 7px 14px; item-radius: 8px; hover-background: var(--menu-hover); hover-color: var(--fg);
           separator-color: var(--border); header-color: var(--accent); blur: on; effects: on; fade: 120ms; }
timeline { stars: off; nebula: on; meteors: off; gradient: on; }
word     { radius: 6px; gloss: on; }
karaoke  { stars: off; nebula: on; meteors: off; font-family: ""; font-size: 44px; color-future: #1d2340;
           color-sung: #d97706; color-current: #db2777; color-dim: #b4bad3;
           color-bg-future: #7c3aed; color-bg-sung: #a78bfa; }
tree     { row-height: 24px; }
"""

CONTRAST_CSS = r"""/* Built-in high-contrast theme */
:root {
  --bg0: #000000; --bg1: #000000; --bg2: #1a1a1a; --border: #ffffff;
  --fg: #ffffff; --fg-dim: #d0d0d0;
  --accent: #ffe600; --accent-dark: #0050ff; --selection-text: #ffffff; --accent2: #00e5ff;
  --gold: #ffe600; --green: #00ff66; --playhead: #ff3b3b;
  --word: #1f1f1f; --word-line: #333333; --word-bg: #3a1a55; --word-selected: #0050ff; --word-now: #00b050;
  --word-text: #ffffff; --word-text-now: #000000; --word-border: #ffffff; --word-border-bg: #ffffff;
  --hover: #ffe600; --grid: #444444;
  --sky-a: #000000; --sky-b: #000000; --star-dim: #000000;
  --nebula-1: #000000; --nebula-2: #000000; --nebula-3: #000000;
  --tree-line: #1a1a1a; --tree-now: #006b2d; --tree-bg-text: #ffccff;
  --mini-a: #00e5ff; --mini-b: #ff66ff;
  --menu-bg: #000000; --menu-border: #ffffff; --menu-hover: #ffe600;
}
app      { ttk-theme: clam; native-menus: off; font-family: ""; font-size: 0; }
menubar  { background: #000000; color: #ffffff; hover-background: #ffe600; hover-color: #000000;
           radius: 4px; brand: "TTML Word Editor"; brand-color: #d0d0d0; border-color: #ffffff; }
menu     { background: #000000; color: #ffffff; accel-color: #d0d0d0; border-color: #ffffff; border-width: 2px;
           border-radius: 6px; padding: 6px; item-padding: 8px 14px; item-radius: 4px;
           hover-background: #ffe600; hover-color: #000000; separator-color: #ffffff; header-color: #ffe600;
           blur: off; effects: off; fade: 0ms; }
timeline { stars: off; nebula: off; meteors: off; gradient: off; }
word     { radius: 3px; gloss: off; }
karaoke  { stars: off; nebula: off; meteors: off; font-family: ""; font-size: 44px; color-future: #ffffff;
           color-sung: #ffe600; color-current: #00e5ff; color-dim: #8a8a8a;
           color-bg-future: #ff99ff; color-bg-sung: #ffccff; }
tree     { row-height: 26px; }
"""

PLAIN_CSS = LIGHT_CSS + r"""
/* "System" theme: native widgets and menus of your operating system */
app      { ttk-theme: native; native-menus: on; }
timeline { stars: off; nebula: off; meteors: off; gradient: off; }
karaoke  { stars: off; nebula: off; meteors: off; }
word     { radius: 3px; gloss: off; }
"""

BUILTIN_CSS = {"cosmic": COSMIC_CSS, "light": LIGHT_CSS, "contrast": CONTRAST_CSS, "plain": PLAIN_CSS}

KNOWN_PROPS = {
    "app": {"ttk-theme", "native-menus", "font-family", "font-size"},
    "menubar": {"background", "color", "hover-background", "hover-color", "radius", "brand", "brand-color",
                "border-color", "height"},
    "menu": {"background", "color", "opacity", "border-color", "border-width", "border-radius", "padding",
             "item-padding", "item-radius", "hover-background", "hover-color", "accel-color", "separator-color",
             "header-color", "blur", "effects", "fade", "min-width"},
    "timeline": {"stars", "nebula", "meteors", "gradient"},
    "word": {"radius", "border-radius", "gloss"},
    "karaoke": {"stars", "nebula", "meteors", "font-family", "font-size", "color-future", "color-sung",
                "color-current", "color-dim", "color-bg-future", "color-bg-sung"},
    "tree": {"row-height"},
}

CSS_REFERENCE = r"""TTML Word Editor - CSS theme reference
=======================================

How it works
  * Theme > Load custom CSS... (or drop *.css files into the themes folder: Theme > Open themes folder).
  * Your CSS is layered over a base theme, so a few lines are enough.
    Pick the base with the first line:   @base light;    (cosmic | light | contrast | plain)
  * The file is watched - save it and the window updates by itself. F9 reloads manually.
  * Theme > Save CSS template... writes the complete default theme with comments.
  * Typos are reported in the status bar (unknown selector / property).

Syntax
  /* comments */   selector { property: value; }   :root { --name: value; }   var(--name)   var(--name, fallback)
  Colors : #rgb  #rgba  #rrggbb  #rrggbbaa  rgb(r,g,b)  rgba(r,g,b,a)  hsl(h,s%,l%)  hsla(...)  names
           (transparency is blended with the surface under it; on menus it becomes window opacity)
  Lengths: 12px      Times: 140ms / 0.2s      Flags: on | off | true | false

Variables (:root)
  --bg0 --bg1 --bg2 --border --fg --fg-dim --accent --accent-dark --selection-text --accent2 --gold --green
  --playhead --word --word-line --word-bg --word-selected --word-now --word-text --word-text-now
  --word-border --word-border-bg --hover --grid --sky-a --sky-b --star-dim --nebula-1 --nebula-2 --nebula-3
  --tree-line --tree-now --tree-bg-text --mini-a --mini-b --menu-bg --menu-border --menu-hover
  You may define your own variables and use them with var().

Selectors and properties
  app       ttk-theme (clam | native)   native-menus (on | off)   font-family   font-size (px, 0 = system)
  menubar   background color hover-background hover-color radius brand brand-color border-color height
  menu      background color opacity border-color border-width border-radius padding item-padding item-radius
            hover-background hover-color accel-color separator-color header-color min-width
            blur (on | off)  effects (on | off)  fade (ms)
  timeline  stars nebula meteors gradient          (on | off)
  word      radius (or border-radius)   gloss (on | off)
  karaoke   stars nebula meteors  font-family font-size color-future color-sung color-current color-dim
            color-bg-future color-bg-sung
  tree      row-height

Glass menus
  * Menus are semi-transparent and rounded on Windows, macOS and Linux (Linux needs a compositing window manager).
  * Real background blur uses the Windows 10/11 acrylic API. On other systems the menus are frosted-translucent
    without blur. `effects: off` (or --no-effects, or Theme > Glass effects) switches all of it off.
  * `native-menus: on` replaces the glass menu bar with your operating system's native one.
"""


def _strip_at_rules(text):
    """Выбрасывает @-правила, которых движок не знает (@import, @charset, @media {...}, @keyframes {...}),
    чтобы они не портили соседние правила. '@' внутри значений (например в строках) не трогаем."""
    out, i, n, prev = [], 0, len(text), ""
    while i < n:
        c = text[i]
        if c == "@" and prev in ("", ";", "{", "}"):
            k = i
            while k < n and text[k] not in ";{":
                k += 1
            if k < n and text[k] == "{":
                depth = 0
                while k < n:
                    depth += (text[k] == "{") - (text[k] == "}")
                    k += 1
                    if depth == 0:
                        break
                prev = "}"
            else:
                k += 1
                prev = ";"
            i = k
            continue
        out.append(c)
        if not c.isspace():
            prev = c
        i += 1
    return "".join(out)


def css_title(path):
    """Отображаемое имя темы из строки  @name My theme;  (если есть)."""
    try:
        with open(path, "r", encoding="utf-8-sig") as f:
            head = f.read(4000)
    except OSError:
        return None
    m = re.search(r"@name\s+[\"']?([^\"';\r\n]+)", head)
    return m.group(1).strip() if m else None


def parse_css(text):
    """-> (@base | None, [(selector, {property: value}), ...])"""
    text = re.sub(r"/\*.*?\*/", "", text or "", flags=re.S)
    base = None
    m = re.search(r"@base\s+([\w-]+)\s*;", text)
    if m:
        base = m.group(1).lower()
    text = _strip_at_rules(text)
    rules = []
    for sel, body in re.findall(r"([^{}]+)\{([^{}]*)\}", text):
        decl = {}
        for d in body.split(";"):
            if ":" in d:
                k, v = d.split(":", 1)
                decl[k.strip().lower()] = re.sub(r"\s*!important\s*$", "", v.strip())
        for one in sel.split(","):
            if one.strip():
                rules.append((one.strip().lower(), decl))
    return base, rules


class Theme:
    """Слой «базовая тема + пользовательский CSS»."""

    def __init__(self, mode="cosmic", user_css=""):
        self.mode = mode
        base_name = mode if mode in BUILTIN_CSS else "cosmic"
        ubase, urules = parse_css(user_css) if user_css else (None, [])
        if mode == "css" and ubase in BUILTIN_CSS:
            base_name = ubase
        self.base = base_name
        self.vars, self.props, self.warnings = {}, {}, []
        _, rules = parse_css(BUILTIN_CSS[base_name])
        for sel, decl in rules + urules:
            if sel in (":root", "root", "*"):
                for k, v in decl.items():
                    if k.startswith("--"):
                        self.vars[k[2:]] = v
            else:
                self.props.setdefault(sel, {}).update(decl)
        for sel, decl in urules:
            if sel in (":root", "root", "*"):
                self.warnings += [f"{sel}: '{k}' is not a --variable" for k in decl if not k.startswith("--")]
            elif sel not in KNOWN_PROPS:
                self.warnings.append(f"unknown selector '{sel}'")
            else:
                self.warnings += [f"{sel}: unknown property '{k}'" for k in decl if k not in KNOWN_PROPS[sel]]

    def _resolve(self, v, depth=0):
        if v is None or depth > 8 or "var(" not in v:
            return v

        def sub(m):
            name, fb = m.group(1), m.group(2)
            if name in self.vars:
                return self._resolve(self.vars[name], depth + 1)
            return (fb or "").strip()
        return re.sub(r"var\(\s*--([\w-]+)\s*(?:,\s*((?:[^()]|\([^()]*\))*))?\)", sub, v)

    def raw(self, sel, prop, default=None):
        d = self.props.get(sel)
        if d and prop in d:
            return self._resolve(d[prop]).strip()
        return default

    def tok(self, name, default, over=None):
        v = self.vars.get(name)
        c = parse_color(self._resolve(v)) if v is not None else None
        return color_hex(c or parse_color(default), over or "#000000")

    def col(self, sel, prop, default, over="#000000"):
        v = self.raw(sel, prop)
        c = parse_color(v) if v is not None else None
        return color_hex(c or parse_color(default), over)

    def rgba_of(self, sel, prop, default):
        v = self.raw(sel, prop)
        return (parse_color(v) if v is not None else None) or parse_color(default)

    def num(self, sel, prop, default):
        v = self.raw(sel, prop)
        return parse_num(v, default) if v is not None else default

    def nums(self, sel, prop, default):
        v = self.raw(sel, prop)
        if v is None:
            return default
        out = [x for x in (parse_num(p, None) for p in v.split()) if x is not None]
        return out or default

    def flag(self, sel, prop, default):
        v = self.raw(sel, prop)
        return parse_flag(v, default) if v is not None else default


def set_palette(T):
    """Переносит токены темы в глобальные цвета (их читают функции отрисовки)."""
    global BG0, BG1, BG2, BORDER, FG, FG_DIM, ACC, ACC_D, MAG, GOLD, GREEN, SEL_FG
    global C_BG, C_WORD, C_WORD_LINE, C_WORD_BG, C_WORD_SEL, C_WORD_NOW, C_PLAYHEAD
    global SKY_A, SKY_B, STAR_DIM, NEB_COLS, TREE_LINE, TREE_NOW, TREE_BGFG
    global GRID, WORD_TEXT, WORD_TEXT_NOW, WORD_BORDER, WORD_BORDER_BG, HOVER_COL, MINI_A, MINI_B
    global WORD_R, GLOSS
    BG0 = T.tok("bg0", "#070a1a")
    BG1 = T.tok("bg1", "#0d1230", BG0)
    BG2 = T.tok("bg2", "#151b45", BG0)
    BORDER = T.tok("border", "#2a3170", BG0)
    FG = T.tok("fg", "#dfe6ff", BG0)
    FG_DIM = T.tok("fg-dim", "#8a94c8", BG0)
    ACC = T.tok("accent", "#4de1ff", BG0)
    ACC_D = T.tok("accent-dark", "#1f6fd1", BG0)
    SEL_FG = T.tok("selection-text", "#ffffff", BG0)
    MAG = T.tok("accent2", "#c86bff", BG0)
    GOLD = T.tok("gold", "#ffd166", BG0)
    GREEN = T.tok("green", "#5cf2a0", BG0)
    C_BG = BG1
    C_WORD = T.tok("word", blend(BG1, ACC_D, 0.3), BG0)
    C_WORD_LINE = T.tok("word-line", blend(BG1, ACC_D, 0.5), BG0)
    C_WORD_BG = T.tok("word-bg", blend(BG1, MAG, 0.35), BG0)
    C_WORD_SEL = T.tok("word-selected", ACC_D, BG0)
    C_WORD_NOW = T.tok("word-now", blend(BG0, GREEN, 0.6), BG0)
    C_PLAYHEAD = T.tok("playhead", "#ff5d9e", BG0)
    SKY_A = T.tok("sky-a", BG0, BG0)
    SKY_B = T.tok("sky-b", BG1, BG0)
    STAR_DIM = T.tok("star-dim", BORDER, BG0)
    NEB_COLS = tuple(T.tok(f"nebula-{i}", d, BG0) for i, d in
                     ((1, blend(BG0, MAG, 0.4)), (2, blend(BG0, ACC, 0.3)), (3, blend(BG0, MAG, 0.25))))
    TREE_LINE = T.tok("tree-line", blend(BG0, ACC_D, 0.2), BG0)
    TREE_NOW = T.tok("tree-now", blend(BG0, GREEN, 0.35), BG0)
    TREE_BGFG = T.tok("tree-bg-text", MAG, BG0)
    GRID = T.tok("grid", blend(BG1, BORDER, 0.5), BG0)
    WORD_TEXT = T.tok("word-text", FG, BG0)
    WORD_TEXT_NOW = T.tok("word-text-now", BG0, BG0)
    WORD_BORDER = T.tok("word-border", BORDER, BG0)
    WORD_BORDER_BG = T.tok("word-border-bg", blend(BORDER, MAG, 0.4), BG0)
    HOVER_COL = T.tok("hover", "#ffb84d", BG0)
    MINI_A = T.tok("mini-a", blend(BG0, ACC, 0.7), BG0)
    MINI_B = T.tok("mini-b", blend(BG0, MAG, 0.7), BG0)
    WORD_R = T.num("word", "radius", T.num("word", "border-radius", 6.0))
    GLOSS = T.flag("word", "gloss", True)


# ----------------------------------------------------------------------------
# НАСТРОЙКИ, ЯЗЫК, ПЛАТФОРМА
# ----------------------------------------------------------------------------
def config_dir():
    """Папка настроек: %APPDATA% / ~/Library/Application Support / $XDG_CONFIG_HOME."""
    if sys.platform == "win32":
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
    elif sys.platform == "darwin":
        base = os.path.expanduser("~/Library/Application Support")
    else:
        base = os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config")
    d = os.path.join(base, "TTMLWordEditor")
    try:
        os.makedirs(d, exist_ok=True)
    except OSError:
        pass
    return d


def sub_dir(name):
    d = os.path.join(config_dir(), name)
    try:
        os.makedirs(d, exist_ok=True)
    except OSError:
        pass
    return d


def settings_path():
    return os.path.join(config_dir(), "settings.json")


def load_config():
    try:
        with open(settings_path(), "r", encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def save_config(d):
    try:
        with open(settings_path(), "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=2)
    except OSError:
        pass


def user_themes():
    """[(имя, путь)] для всех *.css из папки тем; имя берётся из  @name ...;  или из имени файла."""
    d = sub_dir("themes")
    try:
        files = [n for n in os.listdir(d) if n.lower().endswith(".css")]
    except OSError:
        return []
    out = []
    for n in files:
        p = os.path.join(d, n)
        out.append((css_title(p) or os.path.splitext(n)[0], p))
    return sorted(out, key=lambda t: t[0].lower())


def open_path(p):
    try:
        if sys.platform == "win32":
            os.startfile(p)
        else:
            import subprocess
            subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", p])
    except Exception:
        pass


EN = {  # русская строка -> английский перевод
    'Это не TTML: корневой элемент не <tt>': 'Not a TTML file: the root element is not <tt>',
    'CSS: предупреждения': 'CSS warnings',
    'Перезагрузка нужна только для своего CSS-файла': 'Reload is only needed for a custom CSS file',
    'CSS обновлён': 'CSS reloaded',
    'Все файлы': 'All files',
    'Ошибка': 'Error',
    'Тема': 'Theme',
    'Шаблон сохранён. Применить его как свою тему и открыть в текстовом редакторе? Правки будут подхватываться сразу после сохранения файла.': 'Template saved. Apply it as your theme and open it in a text editor? Changes are picked up as soon as you save the file.',
    'Перевод': 'Translation',
    'Шаблон сохранён. Переведите значения (ключи не менять), измените имя файла на код языка (например de.json) и положите файл в папку lang — язык появится в меню «Справка».': 'Template saved. Translate the values (keep the keys), rename the file to the language code (e.g. de.json) and put it in the lang folder - the language will appear in the Help menu.',
    'нет (pip install pygame)': 'not installed (pip install pygame)',
    'нет (pip install numpy)': 'not installed (pip install numpy)',
    'Windows: размытие фона (10/11) и скруглённые меню': 'Windows: background blur (10/11) and rounded menus',
    'macOS: скруглённые полупрозрачные меню (без размытия)': 'macOS: rounded translucent menus (no blur)',
    'Linux: полупрозрачные меню (нужен композитор), без размытия': 'Linux: translucent menus (needs a compositor), no blur',
    'О программе': 'About',
    'Пословный редактор TTML (Apple Music / Spicy Lyrics).': 'Word-level TTML editor (Apple Music / Spicy Lyrics).',
    'Звук: {v}': 'Audio: {v}',
    'Замедление: {v}': 'Slow-down: {v}',
    'Эффекты меню: {v}': 'Menu effects: {v}',
    'Тема: {t}    Язык: {l}': 'Theme: {t}    Language: {l}',
    'Папка настроек:': 'Settings folder:',
    'Справка по CSS-темам': 'CSS theme reference',
    'Закрыть': 'Close',
    'Что-то пошло не так — подробности записаны в error.log (Справка → Открыть папку настроек).\n\n': 'Something went wrong - details were written to error.log (Help > Open settings folder).\n\n',
    'Файл': 'File',
    'Правка': 'Edit',
    'Вид': 'View',
    'Инструменты': 'Tools',
    'Справка': 'Help',
    'Новый': 'New',
    'Открыть TTML…': 'Open TTML…',
    'Сохранить': 'Save',
    'Сохранить как…': 'Save as…',
    'Вставить текст песни (новый файл)…': 'Paste song lyrics (new file)…',
    'Импорт LRC…': 'Import LRC…',
    'Экспорт LRC…': 'Export LRC…',
    'Загрузить аудио…': 'Load audio…',
    'Выход': 'Quit',
    'Отменить': 'Undo',
    'Повторить': 'Redo',
    'Найти / заменить…': 'Find / replace…',
    'Сдвиг времени…': 'Shift time…',
    'Метаданные (язык, агенты)…': 'Metadata (language, agents)…',
    'Караоке-окно (что поётся сейчас)': 'Karaoke window (what is being sung now)',
    'Медленнее': 'Slower',
    'Быстрее': 'Faster',
    'Нормальная скорость': 'Normal speed',
    'Масштаб таймлайна +': 'Timeline zoom in',
    'Масштаб таймлайна −': 'Timeline zoom out',
    'Развернуть все строки': 'Expand all lines',
    'Свернуть все строки': 'Collapse all lines',
    'Анимации': 'Animations',
    'Размер интерфейса: больше': 'UI size: larger',
    'Размер интерфейса: меньше': 'UI size: smaller',
    'Размер интерфейса: по умолчанию': 'UI size: default',
    'Темы': 'Themes',
    'Космос (по умолчанию)': 'Cosmos (default)',
    'Светлая': 'Light',
    'Высокий контраст': 'High contrast',
    'Системная (без темы)': 'System (no theme)',
    'Мои темы': 'My themes',
    'Свой CSS': 'Custom CSS',
    'Загрузить CSS-файл…': 'Load CSS file…',
    'Перезагрузить CSS': 'Reload CSS',
    'Сохранить шаблон CSS…': 'Save CSS template…',
    'Открыть папку тем': 'Open themes folder',
    'Следить за файлом CSS': 'Watch the CSS file',
    'Меню': 'Menus',
    'Стеклянные эффекты (размытие, скругления)': 'Glass effects (blur, rounded corners)',
    'Меню операционной системы': 'Native OS menus',
    'Убрать перекрытия слов': 'Fix overlapping words',
    'Сомкнуть маленькие зазоры…': 'Close small gaps…',
    'Округлить время до 10 мс': 'Round times to 10 ms',
    'Равномерно распределить слова в строке': 'Distribute words in the line evenly',
    'Переименовать агента во всех строках…': 'Rename agent in all lines…',
    'Авто (язык системы)': 'Auto (system language)',
    'Русский': 'Русский',
    'Сохранить шаблон перевода…': 'Save translation template…',
    'Открыть папку настроек': 'Open settings folder',
    '▶ Проиграть слово': '▶ Play word',
    'Начало слова = плейхед (Tap)': 'Word start = playhead (Tap)',
    'Конец слова = плейхед': 'Word end = playhead',
    'Вставить слово после…': 'Insert word after…',
    'Слить со следующим': 'Merge with next',
    'Бэк-вокал': 'Backing vocal',
    'Пробел после слова': 'Space after word',
    'Удалить слово': 'Delete word',
    '▶ Проиграть строку': '▶ Play line',
    'Разделить строку перед словом': 'Split line before word',
    'Слить со следующей строкой': 'Merge with next line',
    'Новая строка после…': 'New line after…',
    'Новая строка…': 'New line…',
    'Поставить плейхед сюда': 'Put playhead here',
    'Горячие клавиши': 'Keyboard shortcuts',
    "ВОСПРОИЗВЕДЕНИЕ\nSpace — играть / пауза       F5 — строка       F6 — слово\nF7 / F8 — медленнее / быстрее (0.25× … 1.5×)\nF4 — караоке-окно (текущая строка и буква)\n\nTAP\nT (или F2) — начало слова = плейхед, потом следующее слово\nE (или F3) — конец слова = плейхед\n\nПРАВКА ВЫБРАННОГО СЛОВА\n, и . — сдвиг слова −/+10 мс (Shift — 50 мс)\n[ и ] — начало −/+10 мс;   ; и ' — конец −/+10 мс\nDelete — удалить слово/строку;  Ctrl+Z / Ctrl+Y — undo / redo\nCtrl+S / Ctrl+O / Ctrl+F — сохранить / открыть / поиск\nПравая кнопка мыши (дерево, таймлайн) — контекстное меню\n\nТАЙМЛАЙН (кликните по нему, чтобы он получил фокус)\n← / → — прокрутка (Shift — на страницу);  ↑ / ↓ — масштаб\nPgUp / PgDn — предыдущее / следующее слово\nHome / End — плейхед на начало / конец слова;  Enter — проиграть слово\nCtrl+←/→ и Ctrl+↑/↓ — то же самое из любого места (в том числе из дерева)\nколесо — прокрутка, Ctrl+колесо — масштаб; мини-карта над таймлайном — быстрый переход\nShift при перетаскивании — без магнита\n\nДЕРЕВО\nДвойной клик по ячейке — правка; клик по «пробел»/«bg» — переключатель.\nПробел внутри текста слова разобьёт его на два слова.\n\nТЕМЫ\nМеню «Тема»: Космос / Светлая / Высокий контраст / Системная или свой CSS.\nF9 — перезагрузить CSS; F1 — эта справка. Подробности — «Справка по CSS-темам».\nКлавиши T/E/Ctrl+… работают и на русской раскладке.": 'PLAYBACK\nSpace - play / pause       F5 - line       F6 - word\nF7 / F8 - slower / faster (0.25x ... 1.5x)\nF4 - karaoke window (current line and letter)\n\nTAP\nT (or F2) - word start = playhead, then move to the next word\nE (or F3) - word end = playhead\n\nEDITING THE SELECTED WORD\n, and . - shift the word by -/+10 ms (Shift - 50 ms)\n[ and ] - start -/+10 ms;   ; and \' - end -/+10 ms\nDelete - delete word/line;  Ctrl+Z / Ctrl+Y - undo / redo\nCtrl+S / Ctrl+O / Ctrl+F - save / open / find\nRight mouse button (tree, timeline) - context menu\n\nTIMELINE (click it to give it focus)\nLeft / Right - scroll (Shift - a page);  Up / Down - zoom\nPgUp / PgDn - previous / next word\nHome / End - playhead to the start / end of the word;  Enter - play the word\nCtrl+Arrows - the same from anywhere (including the tree)\nmouse wheel - scroll, Ctrl+wheel - zoom; the mini-map above the timeline - quick jump\nShift while dragging - no snapping\n\nTREE\nDouble-click a cell to edit; click "space"/"bg" to toggle.\nA space inside a word\'s text splits it into two words.\n\nTHEMES\nTheme menu: Cosmos / Light / High contrast / System, or your own CSS.\nF9 - reload CSS; F1 - this help. Details - "CSS theme reference".\nT/E/Ctrl+... keys also work on the Russian keyboard layout.',
    'Текст (двойной клик — правка)': 'Text (double-click to edit)',
    'начало': 'start',
    'конец': 'end',
    'пробел': 'space',
    'агент': 'agent',
    'часть': 'part',
    '▶ Играть': '▶ Play',
    'Аудио…': 'Audio…',
    '(нет pygame: pip install pygame)': '(no pygame: pip install pygame)',
    'Скорость': 'Speed',
    'сохранять тон': 'keep pitch',
    '🎤 Караоке-окно': '🎤 Karaoke window',
    'По строке': 'Fit line',
    'Следовать': 'Follow',
    'Следить в дереве': 'Track in tree',
    'Магнит': 'Snap',
    '✦ Анимации': '✦ Animations',
    'конец пред. слова = начало': 'prev. word end = start',
    'задержка, мс': 'latency, ms',
    ' Слово ': ' Word ',
    'Текст': 'Text',
    'Начало': 'Start',
    'Конец': 'End',
    'Всё слово': 'Whole word',
    'Бэк-вокал (bg)': 'Backing vocal (bg)',
    'Разбить по курсору': 'Split at cursor',
    'Вставить после': 'Insert after',
    ' Строка ': ' Line ',
    'Часть': 'Part',
    'Разделить перед словом': 'Split before word',
    'Слить со следующей': 'Merge with next',
    'Новая строка после': 'New line after',
    'Удалить строку': 'Delete line',
    '▲ Выше': '▲ Up',
    '▼ Ниже': '▼ Down',
    'Слова равномерно': 'Spread words evenly',
    'Сдвиг…': 'Shift…',
    ' Прослушивание ': ' Playback ',
    '▶ Слово (F6)': '▶ Word (F6)',
    '▶ Строка (F5)': '▶ Line (F5)',
    'без имени': 'untitled',
    'Строк: {l}   слов: {w}   длительность: {d}': 'Lines: {l}   words: {w}   duration: {d}',
    'Разбить слово': 'Split word',
    'Поставьте курсор в поле «Текст» внутри слова — там, где нужно разрезать (на слоги).': 'Put the cursor inside the word in the "Text" field where it should be cut (into syllables).',
    'Вставить слово': 'Insert word',
    'Текст слова:': 'Word text:',
    'Разделить строку': 'Split line',
    'Выберите слово, с которого начнётся новая строка (не первое).': 'Select the word that will start the new line (not the first one).',
    'Новая строка': 'New line',
    'Текст строки:': 'Line text:',
    'Сдвиг': 'Shift',
    'Нечего сдвигать — выберите слово/строку в дереве.': 'Nothing to shift - select a word or line in the tree.',
    'Сдвиг времени': 'Time shift',
    'Только выбранное слово': 'Selected word only',
    'От выбранного слова до конца строки': 'From the selected word to the end of the line',
    'Вся выбранная строка': 'The whole selected line',
    'От выбранного слова до конца песни': 'From the selected word to the end of the song',
    'Вся песня': 'The whole song',
    'Сдвиг, мс (можно отрицательный):': 'Shift, ms (may be negative):',
    'Отмена': 'Cancel',
    'Перекрытия': 'Overlaps',
    'Исправлено: {n}': 'Fixed: {n}',
    'Зазоры': 'Gaps',
    'Смыкать зазоры между словами в строке короче, мс:': 'Close gaps between words in a line shorter than, ms:',
    'Сомкнуто: {n}': 'Closed: {n}',
    'Агент': 'Agent',
    'Какого агента заменить (например v1):': 'Which agent to replace (e.g. v1):',
    'Заменить {old} на:': 'Replace {old} with:',
    'Найти / заменить': 'Find / replace',
    'Найти': 'Find',
    'Заменить на': 'Replace with',
    'Далее': 'Next',
    'Заменить': 'Replace',
    'Заменить все': 'Replace all',
    'Поиск': 'Search',
    'Не найдено.': 'Not found.',
    'Замена': 'Replace',
    'Заменено слов: {n}': 'Words replaced: {n}',
    'Несохранённые изменения': 'Unsaved changes',
    'Сохранить изменения?': 'Save changes?',
    'Не удалось открыть файл:\n{ex}': 'Could not open the file:\n{ex}',
    'Ошибка сохранения': 'Save error',
    'Текст песни': 'Song lyrics',
    'Вставьте текст (одна строка = одна строка песни; пустая строка = новая часть).': 'Paste the lyrics (one line = one song line; an empty line = a new section).',
    'В файле не найдено строк с таймкодами.': 'No lines with timestamps were found in the file.',
    'Экспорт LRC': 'Export LRC',
    'Писать пословные метки (Enhanced LRC)?': 'Write word-level tags (Enhanced LRC)?',
    'Метаданные': 'Metadata',
    'Язык (xml:lang) — первая строка, далее агенты «id тип» (v1 person, v2 person, v1000 other):': 'Language (xml:lang) - first line, then agents "id type" (v1 person, v2 person, v1000 other):',
    'Аудио': 'Audio',
    'Для воспроизведения установите pygame:\n\n    pip install pygame\n\nБез него плейхед работает как тихий таймер.': 'To play audio install pygame:\n\n    pip install pygame\n\nWithout it the playhead works as a silent timer.',
    'Не удалось загрузить: {ex}': 'Could not load: {ex}',
    'Замедление': 'Slow-down',
    'Для замедления аудио нужен numpy:\n\n    pip install numpy': 'Slowing audio down requires numpy:\n\n    pip install numpy',
    'готовлю {v}…': 'preparing {v}…',
    'Не удалось подготовить звук: {ex}': 'Could not prepare the audio: {ex}',
    '⏸ Пауза': '⏸ Pause',
    'Строка {n}': 'Line {n}',
    ' · слово «{w}» {i}/{n}': ' · word "{w}" {i}/{n}',
    'Файл → Открыть TTML… или Вставить текст песни…': 'File → Open TTML… or Paste song lyrics…',
    '«{w}»  {b} → {e}  ({ms} мс)  ·  строка {n}': '"{w}"  {b} → {e}  ({ms} ms)  ·  line {n}',
    'Караоке-просмотр — что поётся сейчас': 'Karaoke view - what is being sung now',
    'Поверх всех окон': 'Always on top',
    '   ·   скорость ×{s:g}': '   ·   speed ×{s:g}',
    'Нет строк': 'No lines',
    '   ·   до начала: {v}': '   ·   until start: {v}',
    'строка {c}/{t}  ·  слово «{w}» {i}/{k}  ·  буква «{ch}» {n}/{m}': 'line {c}/{t}  ·  word "{w}" {i}/{k}  ·  letter "{ch}" {n}/{m}',
    'строка {c}/{t}  ·  пауза': 'line {c}/{t}  ·  pause',
    'строка {c}/{t}': 'line {c}/{t}',
}
_LANG = "ru"
_TR = {}


def tr(s):
    """Перевод строки интерфейса (исходные тексты — русские)."""
    return _TR.get(s, s) if _TR else s


def detect_language():
    try:
        if sys.platform == "win32":
            import ctypes
            lid = ctypes.windll.kernel32.GetUserDefaultUILanguage() & 0x3FF
            return "ru" if lid == 0x19 else "en"
    except Exception:
        pass
    for var in ("LC_ALL", "LC_MESSAGES", "LANGUAGE", "LANG"):
        v = os.environ.get(var, "")
        if v:
            return "ru" if v.lower().startswith("ru") else "en"
    try:
        import locale
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            loc = locale.getlocale()[0] or ""
        return "ru" if loc.lower().startswith(("ru", "russian")) else "en"
    except Exception:
        return "en"


def language_packs():
    """Пользовательские переводы: <папка настроек>/lang/<код>.json  ->  [(код, название, путь)]"""
    out = []
    d = sub_dir("lang")
    try:
        for n in sorted(os.listdir(d)):
            if n.lower().endswith(".json"):
                p = os.path.join(d, n)
                code = os.path.splitext(n)[0]
                try:
                    with open(p, "r", encoding="utf-8") as f:
                        name = str(json.load(f).get("__name__", code))
                except (OSError, ValueError, AttributeError):
                    continue
                out.append((code, name, p))
    except OSError:
        pass
    return out


def load_language(code):
    global _LANG, _TR
    if code in (None, "", "auto"):
        code = detect_language()
    _LANG = code
    if code == "ru":
        _TR = {}
        return
    _TR = dict(EN)
    if code != "en":
        for c, _name, p in language_packs():
            if c == code:
                try:
                    with open(p, "r", encoding="utf-8") as f:
                        pack = json.load(f)
                    _TR.update({k: v for k, v in pack.items()
                                if isinstance(v, str) and v and not k.startswith("__")})
                except (OSError, ValueError):
                    pass


def win_fx(win, radius, w, h, blur, tint_hex, tint_alpha):
    """Windows 10/11: скругление окна (SetWindowRgn) и размытие фона (acrylic / blur-behind).
    Любая ошибка молча игнорируется — меню просто остаётся полупрозрачным."""
    if sys.platform != "win32":
        return False
    try:
        import ctypes
        user32 = ctypes.windll.user32
        user32.GetParent.restype = ctypes.c_void_p
        user32.GetParent.argtypes = [ctypes.c_void_p]
        hwnd = user32.GetParent(win.winfo_id()) or win.winfo_id()
        if radius > 0:
            gdi = ctypes.windll.gdi32
            gdi.CreateRoundRectRgn.restype = ctypes.c_void_p
            rgn = gdi.CreateRoundRectRgn(0, 0, int(w) + 1, int(h) + 1, int(radius * 2), int(radius * 2))
            user32.SetWindowRgn.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]
            user32.SetWindowRgn(hwnd, rgn, True)
        if blur:
            class ACCENT(ctypes.Structure):
                _fields_ = [("AccentState", ctypes.c_int), ("AccentFlags", ctypes.c_int),
                            ("GradientColor", ctypes.c_uint), ("AnimationId", ctypes.c_int)]

            class WCAD(ctypes.Structure):
                _fields_ = [("Attribute", ctypes.c_int), ("Data", ctypes.c_void_p),
                            ("SizeOfData", ctypes.c_size_t)]
            r, g, b = _rgb(tint_hex)
            acc = ACCENT()
            acc.AccentState = 4 if sys.getwindowsversion().build >= 17134 else 3
            acc.AccentFlags = 2 if acc.AccentState == 4 else 0
            acc.GradientColor = (int(tint_alpha * 255) << 24) | (b << 16) | (g << 8) | r
            data = WCAD()
            data.Attribute = 19
            data.Data = ctypes.cast(ctypes.byref(acc), ctypes.c_void_p)
            data.SizeOfData = ctypes.sizeof(acc)
            fn = user32.SetWindowCompositionAttribute
            fn.argtypes = [ctypes.c_void_p, ctypes.POINTER(WCAD)]
            fn.restype = ctypes.c_int
            fn(hwnd, ctypes.byref(data))
        return True
    except Exception:
        return False


LANE_MAIN = (34, 88)
LANE_BG = (98, 140)
SPEEDS = [0.25, 0.4, 0.5, 0.6, 0.75, 0.9, 1.0, 1.25, 1.5]


def mi(label, cmd=None, accel="", check=None, enabled=True):
    """Пункт меню."""
    return {"label": label, "cmd": cmd, "accel": accel, "check": check, "enabled": enabled}


MSEP = {"sep": True}


def mhead(text):
    return {"header": text}


class PopupMenu(tk.Toplevel):
    """Стеклянное скруглённое меню: полупрозрачное окно с плавным появлением и «плывущей» подсветкой.
    Windows 10/11 — ещё и размытие фона; macOS — настоящие скруглённые прозрачные углы;
    Linux — полупрозрачность (нужен композитор)."""

    def __init__(self, app, items, x, y, owner=None):
        super().__init__(app)
        self.withdraw()
        self.overrideredirect(True)
        self.app, self.owner = app, owner
        self._dead = False
        self._anim_id = None
        self.hover = None
        T = app.theme
        self.effects = app.effects_enabled()
        bgc = T.rgba_of("menu", "background", "rgba(13,18,48,0.8)")
        self.panel = color_hex(bgc, BG0)
        op = T.num("menu", "opacity", None)
        self.alpha = min(1.0, max(0.35, op if op is not None else bgc[3])) if self.effects else 1.0
        self.blur = self.effects and T.flag("menu", "blur", True)
        self.radius = T.num("menu", "border-radius", 12.0)
        self.pad = T.num("menu", "padding", 6.0)
        ip = T.nums("menu", "item-padding", [7.0, 14.0])
        self.ipy = ip[0]
        self.ipx = ip[1] if len(ip) > 1 else ip[0]
        self.iradius = T.num("menu", "item-radius", 8.0)
        self.bw = T.num("menu", "border-width", 1.0)
        P = self.panel
        self.c_text = T.col("menu", "color", FG, P)
        self.c_accel = T.col("menu", "accel-color", FG_DIM, P)
        self.c_hbg = T.col("menu", "hover-background", "rgba(77,225,255,0.16)", P)
        self.c_hfg = T.col("menu", "hover-color", "#ffffff", P)
        self.c_sep = T.col("menu", "separator-color", BORDER, P)
        self.c_border = T.col("menu", "border-color", BORDER, P)
        self.c_head = T.col("menu", "header-color", ACC, P)
        self.c_dis = blend(P, self.c_text, 0.4)
        self.fade = T.num("menu", "fade", 140.0) if (app.anim_on.get() and self.effects) else 0.0
        self.font = tkfont.nametofont("TkMenuFont")
        lh = self.font.metrics("linespace")

        self.rows = []
        y_ = self.pad
        lw = aw = 0
        for it in items:
            if it.get("sep"):
                kind, h = "sep", 9
            elif it.get("header"):
                kind, h = "head", lh + 8
                lw = max(lw, self.font.measure(it["header"]))
            else:
                kind, h = "item", lh + 2 * self.ipy
                lw = max(lw, self.font.measure(it["label"]))
                aw = max(aw, self.font.measure(it.get("accel") or ""))
            self.rows.append((kind, y_, y_ + h, it))
            y_ += h
        self.H = int(y_ + self.pad)
        self.W = int(max(T.num("menu", "min-width", 180.0),
                         2 * self.pad + 2 * self.ipx + 22 + lw + ((28 + aw) if aw else 0)))
        W, H = self.W, self.H

        self.cv = tk.Canvas(self, width=W, height=H, bg=P, bd=0, highlightthickness=0)
        self.cv.pack()
        cv = self.cv
        b = self.bw / 2.0
        rrect(cv, b, b, W - b, H - b, self.radius, fill=P, outline=self.c_border, width=self.bw)
        # порядок создания: панель -> подсветка -> тексты, поэтому подсветка всегда между ними
        self.hl = cv.create_polygon(rr_points(0, 0, 10, 10, self.iradius), smooth=True, splinesteps=8,
                                    fill=self.c_hbg, outline="", state="hidden")
        self.ids = {}
        xl = self.pad + self.ipx
        for i, (kind, y0, y1, it) in enumerate(self.rows):
            cy = (y0 + y1) / 2.0
            if kind == "sep":
                cv.create_line(xl, cy, W - xl, cy, fill=self.c_sep)
            elif kind == "head":
                cv.create_text(xl, cy, text=it["header"], anchor="w", fill=self.c_head, font=self.font)
            else:
                ok = self._selectable(i)
                chk = it.get("check")
                chk = chk() if callable(chk) else chk
                if chk:
                    cv.create_text(xl + 2, cy, text="✓", anchor="w", fill=ACC, font=self.font)
                lab = cv.create_text(xl + 22, cy, text=it["label"], anchor="w", font=self.font,
                                     fill=self.c_text if ok else self.c_dis)
                acc = cv.create_text(W - xl, cy, text=it.get("accel") or "", anchor="e", font=self.font,
                                     fill=self.c_accel if ok else self.c_dis)
                self.ids[i] = (lab, acc)

        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        x = int(max(0, min(x, sw - W - 2)))
        y = int(y if y + H <= sh - 2 else max(0, sh - H - 2))
        self.geometry(f"{W}x{H}+{x}+{y}")
        try:
            self.attributes("-topmost", True)
            self.attributes("-alpha", 0.0 if self.fade > 0 else self.alpha)
        except tk.TclError:
            pass
        if sys.platform == "darwin" and self.effects:
            try:
                self.attributes("-transparent", True)
                self.config(bg="systemTransparent")
                self.cv.config(bg="systemTransparent")
            except tk.TclError:
                pass
        self.deiconify()
        self.update_idletasks()
        if self.effects:
            win_fx(self, self.radius, W, H, self.blur, P, 0.55)
        self.bind("<Motion>", self._motion)
        self.bind("<Leave>", lambda e: self._set_hover(None))
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Key>", self._key)
        self._t0 = time.perf_counter()
        if self.fade > 0:
            self._fade_step()
        self.after(1, self._grab)

    # ---- служебное
    def _grab(self):
        if self._dead:
            return
        try:
            self.grab_set()
        except tk.TclError:
            pass
        try:
            self.focus_force()
        except tk.TclError:
            pass

    def _fade_step(self):
        if self._dead:
            return
        e = min(1.0, (time.perf_counter() - self._t0) * 1000.0 / max(self.fade, 1.0))
        try:
            self.attributes("-alpha", self.alpha * (1 - (1 - e) ** 3))
        except tk.TclError:
            return
        if e < 1.0:
            self.after(16, self._fade_step)

    def _selectable(self, i):
        if i is None or not (0 <= i < len(self.rows)):
            return False
        kind, _y0, _y1, it = self.rows[i]
        return kind == "item" and it.get("enabled", True) and it.get("cmd") is not None

    def _row_at(self, y):
        for i, (_k, y0, y1, _it) in enumerate(self.rows):
            if y0 <= y < y1:
                return i
        return None

    def _paint(self, i, on):
        ids = self.ids.get(i)
        if ids:
            self.cv.itemconfig(ids[0], fill=self.c_hfg if on else self.c_text)
            self.cv.itemconfig(ids[1], fill=self.c_hfg if on else self.c_accel)

    def _set_hover(self, i):
        if i is not None and not self._selectable(i):
            i = None
        if i == self.hover:
            return
        if self.hover is not None:
            self._paint(self.hover, False)
        first = self.hover is None
        self.hover = i
        if i is None:
            self.cv.itemconfig(self.hl, state="hidden")
            return
        _k, y0, y1, _it = self.rows[i]
        self._paint(i, True)
        self.ty0, self.ty1 = y0, y1
        if first or not self.app.anim_on.get():
            self.cy0, self.cy1 = y0, y1
            self._place_hl()
        elif self._anim_id is None:
            self._step()

    def _place_hl(self):
        self.cv.coords(self.hl, *rr_points(self.pad, self.cy0, self.W - self.pad, self.cy1, self.iradius))
        self.cv.itemconfig(self.hl, state="normal")

    def _step(self):
        self._anim_id = None
        if self._dead or self.hover is None:
            return
        self.cy0 += (self.ty0 - self.cy0) * 0.4
        self.cy1 += (self.ty1 - self.cy1) * 0.4
        done = abs(self.ty0 - self.cy0) < 0.6 and abs(self.ty1 - self.cy1) < 0.6
        if done:
            self.cy0, self.cy1 = self.ty0, self.ty1
        self._place_hl()
        if not done:
            self._anim_id = self.after(16, self._step)

    # ---- события
    def _inside(self, e):
        rx, ry = self.winfo_rootx(), self.winfo_rooty()
        return rx <= e.x_root < rx + self.W and ry <= e.y_root < ry + self.H

    def _local_y(self, e):
        return e.y_root - self.winfo_rooty()

    def _motion(self, e):
        if self._inside(e):
            self._set_hover(self._row_at(self._local_y(e)))
            return
        self._set_hover(None)
        bar = self.owner if isinstance(self.owner, MenuBar) else None
        if bar is not None:
            i = bar.index_at_root(e.x_root, e.y_root)
            if i is not None and i != bar.open_idx:
                bar.open(i)

    def _press(self, e):
        if self._inside(e):
            return
        bar = self.owner if isinstance(self.owner, MenuBar) else None
        i = bar.index_at_root(e.x_root, e.y_root) if bar else None
        cur = bar.open_idx if bar else None
        self.dismiss()
        if bar is not None and i is not None and i != cur:
            bar.open(i)

    def _release(self, e):
        if self._inside(e):
            self._activate(self._row_at(self._local_y(e)))

    def _activate(self, i):
        if not self._selectable(i):
            return
        cmd = self.rows[i][3].get("cmd")
        self.dismiss()
        if cmd:
            self.app.after(15, cmd)

    def _key(self, e):
        ks = e.keysym
        n = len(self.rows)
        if ks == "Escape":
            self.dismiss()
        elif ks in ("Down", "Up") and n:
            d = 1 if ks == "Down" else -1
            i = self.hover if self.hover is not None else (-1 if d == 1 else n)
            for _ in range(n):
                i = (i + d) % n
                if self._selectable(i):
                    self._set_hover(i)
                    break
        elif ks in ("Return", "KP_Enter", "space"):
            self._activate(self.hover)
        elif ks in ("Left", "Right") and isinstance(self.owner, MenuBar):
            self.owner.step(-1 if ks == "Left" else 1)
        return "break"

    def dismiss(self):
        if self._dead:
            return
        self._dead = True
        try:
            self.grab_release()
        except tk.TclError:
            pass
        try:
            self.destroy()
        except tk.TclError:
            pass
        if self.owner is not None:
            self.owner.menu_closed(self)


class MenuBar(tk.Canvas):
    """Собственная строка меню (в стиле темы) — открывает PopupMenu; справа — бренд и переключатель языка."""

    def __init__(self, app, parent, menus):
        T = app.theme
        f = tkfont.nametofont("TkDefaultFont")
        self.h = int(T.num("menubar", "height", 0) or max(30, f.metrics("linespace") + 14))
        super().__init__(parent, height=self.h, bg=T.col("menubar", "background", BG1, BG0),
                         highlightthickness=0, bd=0)
        self.app, self.menus = app, menus
        self.hover = None
        self.open_idx = None
        self.popup = None
        self.pos = []
        self.chip = None
        self.bind("<Configure>", lambda e: self.draw())
        self.bind("<Motion>", self._motion)
        self.bind("<Leave>", lambda e: self._hover(None))
        self.bind("<ButtonPress-1>", self._press)

    def draw(self):
        c = self
        c.delete("all")
        T = self.app.theme
        W = c.winfo_width() or 800
        bg = T.col("menubar", "background", BG1, BG0)
        fg = T.col("menubar", "color", FG, bg)
        hbg = T.col("menubar", "hover-background", "rgba(77,225,255,0.16)", bg)
        hfg = T.col("menubar", "hover-color", "#ffffff", bg)
        r = T.num("menubar", "radius", 8.0)
        c.config(bg=bg)
        f = tkfont.nametofont("TkDefaultFont")
        x = 8
        self.pos = []
        for i, (title, _factory) in enumerate(self.menus):
            w = f.measure(title)
            x0, x1 = x, x + w + 22
            self.pos.append((x0, x1))
            active = (i == self.open_idx) or (self.open_idx is None and i == self.hover)
            if active:
                rrect(c, x0, 4, x1, self.h - 4, r, fill=hbg, outline="")
            c.create_text((x0 + x1) / 2, self.h / 2, text=title, fill=hfg if active else fg, font=f)
            x = x1 + 2
        brand = T.raw("menubar", "brand", "TTML Word Editor").strip("\"' ")
        bid = c.create_text(W - 14, self.h / 2, text=brand, anchor="e", font=f,
                            fill=T.col("menubar", "brand-color", FG_DIM, bg))
        bb = c.bbox(bid)
        lx1 = (bb[0] - 14) if bb else W - 120
        chip_text = "🌐 " + _LANG.upper()[:5]
        cw = f.measure(chip_text) + 18
        self.chip = (lx1 - cw, lx1)
        active = self.hover == "chip"
        if active:
            rrect(c, self.chip[0], 4, self.chip[1], self.h - 4, r, fill=hbg, outline="")
        c.create_text((self.chip[0] + self.chip[1]) / 2, self.h / 2, text=chip_text, font=f,
                      fill=hfg if active else fg)
        c.create_line(0, self.h - 1, W, self.h - 1, fill=T.col("menubar", "border-color", BORDER, bg))

    def index_at(self, x):
        for i, (x0, x1) in enumerate(self.pos):
            if x0 <= x < x1:
                return i
        return None

    def index_at_root(self, xr, yr):
        x, y = xr - self.winfo_rootx(), yr - self.winfo_rooty()
        if not (0 <= y < self.h):
            return None
        return self.index_at(x)

    def _hover(self, i):
        if i != self.hover:
            self.hover = i
            self.draw()

    def _motion(self, e):
        if self.chip and self.chip[0] <= e.x < self.chip[1]:
            self._hover("chip")
        else:
            self._hover(self.index_at(e.x))

    def _press(self, e):
        if self.chip and self.chip[0] <= e.x < self.chip[1]:
            self.app.open_language_menu(self.winfo_rootx() + self.chip[0], self.winfo_rooty() + self.h + 2)
            return
        i = self.index_at(e.x)
        if i is not None:
            self.open(i)

    def open(self, idx):
        if self.popup is not None:
            self.popup.dismiss()
        _title, factory = self.menus[idx]
        x0, _x1 = self.pos[idx]
        self.open_idx = idx
        self.popup = PopupMenu(self.app, factory(), self.winfo_rootx() + x0, self.winfo_rooty() + self.h + 2,
                               owner=self)
        self.draw()

    def step(self, d):
        if self.open_idx is not None:
            self.open((self.open_idx + d) % len(self.menus))

    def menu_closed(self, popup):
        if self.popup is popup:
            self.popup = None
            self.open_idx = None
            self.draw()



class App(tk.Tk):
    def __init__(self, path=None, opts=None):
        opts = opts or {}
        self.cfg = load_config()
        self.lang_choice = self.cfg.get("language", "auto")
        load_language(opts.get("lang") or self.lang_choice)
        super().__init__()
        self.geometry("1320x860")
        self.minsize(1050, 680)
        self.doc = Doc.new()
        self.path = None
        self.dirty = False
        self.undo_stack, self.redo_stack = [], []
        self.sel = None
        self.playhead = 0.0
        self.playing = False
        self.stop_at = None
        self.pos0 = 0.0
        self.t0 = 0.0
        self.audio_path = None
        self.audio_ok = False
        self.audio_len = 0.0
        self.view_start = 0.0
        self.view_len = 12.0
        self.drag = None
        self.tl_items = []
        self._bak_done = False
        self.find_dlg = None
        self.karaoke = None
        self.view_goal = None
        self._anim_n = 0
        self.stars_tl = Starfield(n=95, seed=3)
        self.speed = 1.0
        self.audio_arr = None
        self.slow_cache = {}
        self.snd = None
        self.snd_ch = None
        self.now_iid = None
        self.hover = None
        self._last_t = -1.0
        self._loc_dirty = True
        self.mini_dirty = True
        self._mini_w = 0
        self._mini_total = 0.0
        self.mini_view = None
        self.mini_ph = None

        self.speed_var = tk.StringVar(value="1×")
        self.keep_pitch = tk.BooleanVar(value=True)
        self.follow_tree = tk.BooleanVar(value=True)
        self.anim_on = tk.BooleanVar(value=bool(self.cfg.get("animations", True)))
        self.latency = tk.IntVar(value=100)
        self.chain = tk.BooleanVar(value=True)
        self.follow = tk.BooleanVar(value=True)
        self.snap = tk.BooleanVar(value=True)

        self._capture_system_defaults()
        self.no_effects = bool(opts.get("no_effects"))
        self.effects_override = self.cfg.get("menu_effects", None)
        self.native_override = self.cfg.get("native_menus", None)
        self.css_watch = bool(self.cfg.get("css_watch", True))
        try:
            self.font_scale = min(2.0, max(0.7, float(self.cfg.get("font_scale", 1.0))))
        except (TypeError, ValueError):
            self.font_scale = 1.0
        self.theme_mode = opts.get("theme") or self.cfg.get("theme", "cosmic")
        self.css_path = opts.get("css") or self.cfg.get("css_path", "")
        if opts.get("css"):
            self.theme_mode = "css"
        if self.theme_mode not in THEME_MODES or (self.theme_mode == "css" and not self.css_path):
            self.theme_mode = "cosmic"
        self._css_mtime = self._mtime()
        self._pending_hint = ""
        self._hint_token = None
        self.menubar_widget = None
        self.theme = self._make_theme()
        self.apply_theme()
        self.build_ui()
        self.install_menu()
        self.bind_keys()
        self.rebuild(reset_open=True)
        self.update_title()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        if path:
            self.open_file(path)
        self.after(30, self.tick)
        self.after(40, self.anim_tick)
        self.after(800, self.css_poll)
        self.after(500, self._startup_hint)

    # ------------------------------------------------------------ настройки, тема, язык
    def _capture_system_defaults(self):
        """Запоминаем системные цвета/шрифты, чтобы можно было вернуться к «Системной» теме."""
        self._sys_bg = self.cget("bg")
        self._native_theme = ttk.Style(self).theme_use()
        opts = [("*Toplevel.background", self._sys_bg)]
        try:
            m = tk.Menu(self)
            for pat, key in (("*Menu.background", "background"), ("*Menu.foreground", "foreground"),
                             ("*Menu.activeBackground", "activebackground"),
                             ("*Menu.activeForeground", "activeforeground")):
                opts.append((pat, str(m.cget(key))))
            m.destroy()
            lb = tk.Listbox(self)
            for pat, key in (("*TCombobox*Listbox.background", "background"),
                             ("*TCombobox*Listbox.foreground", "foreground"),
                             ("*TCombobox*Listbox.selectBackground", "selectbackground"),
                             ("*TCombobox*Listbox.selectForeground", "selectforeground")):
                opts.append((pat, str(lb.cget(key))))
            lb.destroy()
        except tk.TclError:
            pass
        self._sys_options = opts
        self._font_defaults = {}
        for n in FONT_NAMES:
            try:
                self._font_defaults[n] = tkfont.nametofont(n).actual()
            except tk.TclError:
                pass

    def _mtime(self):
        try:
            return os.path.getmtime(self.css_path) if self.css_path else 0.0
        except OSError:
            return 0.0

    def _make_theme(self):
        css = ""
        if self.theme_mode == "css":
            try:
                with open(self.css_path, "r", encoding="utf-8-sig") as f:
                    css = f.read()
            except OSError as ex:
                self._pending_hint = f"CSS: {ex}"
                self.theme_mode = "cosmic"
                return Theme("cosmic")
        return Theme(self.theme_mode, css)

    def effects_enabled(self):
        if self.no_effects:
            return False
        if self.effects_override is not None:
            return bool(self.effects_override)
        return self.theme.flag("menu", "effects", True)

    def native_menus(self):
        if self.native_override is not None:
            return bool(self.native_override)
        return self.theme.flag("app", "native-menus", False)

    def _config_tree_tags(self):
        self.tree.tag_configure("line", background=TREE_LINE, foreground=ACC)
        self.tree.tag_configure("bg", foreground=TREE_BGFG)
        self.tree.tag_configure("now", background=TREE_NOW, foreground=FG)

    def apply_theme(self):
        T = self.theme
        set_palette(T)
        fam = T.raw("app", "font-family", "").strip("\"' ")
        size = int(T.num("app", "font-size", 0) or 0)
        for n, base in self._font_defaults.items():
            try:
                sz = size if size > 0 else base["size"]
                if abs(self.font_scale - 1.0) > 1e-6:
                    sz = int(round(sz * self.font_scale)) or sz
                tkfont.nametofont(n).configure(family=fam or base["family"], size=sz)
            except tk.TclError:
                pass
        native = T.raw("app", "ttk-theme", "clam").lower() in ("native", "system", "default", "os")
        self._ttk_native = native
        row_h = int(T.num("tree", "row-height", 24) * max(1.0, self.font_scale))
        st = ttk.Style(self)
        if native:
            try:
                st.theme_use(self._native_theme)
            except tk.TclError:
                pass
            for pat, val in self._sys_options:
                self.option_add(pat, val)
            self.configure(bg=self._sys_bg)
            st.configure("Treeview", rowheight=row_h)
        else:
            self.configure(bg=BG0)
            for pat, val in (("*Menu.background", BG1), ("*Menu.foreground", FG), ("*Menu.activeBackground", ACC_D),
                             ("*Menu.activeForeground", SEL_FG), ("*Toplevel.background", BG1),
                             ("*TCombobox*Listbox.background", BG2), ("*TCombobox*Listbox.foreground", FG),
                             ("*TCombobox*Listbox.selectBackground", ACC_D),
                             ("*TCombobox*Listbox.selectForeground", SEL_FG)):
                self.option_add(pat, val)
            try:
                st.theme_use("clam")
            except tk.TclError:
                pass
            st.configure(".", background=BG1, foreground=FG, fieldbackground=BG2, bordercolor=BORDER,
                         lightcolor=BG2, darkcolor=BG1, troughcolor=BG0, focuscolor=ACC,
                         selectbackground=ACC_D, selectforeground=SEL_FG, insertcolor=ACC)
            st.configure("TFrame", background=BG1)
            st.configure("TLabel", background=BG1, foreground=FG)
            st.configure("TLabelframe", background=BG1, bordercolor=BORDER)
            st.configure("TLabelframe.Label", background=BG1, foreground=ACC)
            st.configure("TButton", background=BG2, foreground=FG, bordercolor=BORDER, padding=(8, 3),
                         relief="flat")
            st.map("TButton", background=[("pressed", ACC_D), ("active", blend(BG2, ACC, 0.18))],
                   foreground=[("active", FG)], bordercolor=[("active", ACC)])
            for w in ("TCheckbutton", "TRadiobutton"):
                st.configure(w, background=BG1, foreground=FG, indicatorcolor=BG2)
                st.map(w, background=[("active", BG1)], foreground=[("active", ACC)],
                       indicatorcolor=[("selected", ACC), ("!selected", BG2)])
            st.configure("TEntry", fieldbackground=BG2, foreground=FG, insertcolor=ACC, bordercolor=BORDER)
            st.map("TEntry", bordercolor=[("focus", ACC)])
            st.configure("TCombobox", fieldbackground=BG2, background=BG2, foreground=FG, arrowcolor=ACC,
                         bordercolor=BORDER)
            st.map("TCombobox", fieldbackground=[("readonly", BG2)], foreground=[("readonly", FG)],
                   selectbackground=[("readonly", BG2)], selectforeground=[("readonly", FG)],
                   bordercolor=[("focus", ACC)])
            st.configure("TSpinbox", fieldbackground=BG2, background=BG2, foreground=FG, arrowcolor=ACC,
                         bordercolor=BORDER, insertcolor=ACC)
            st.configure("Treeview", background=BG0, fieldbackground=BG0, foreground=FG, rowheight=row_h,
                         bordercolor=BORDER)
            st.map("Treeview", background=[("selected", ACC_D)], foreground=[("selected", SEL_FG)])
            st.configure("Treeview.Heading", background=BG2, foreground=ACC, relief="flat",
                         font=("TkDefaultFont", 9, "bold"))
            st.map("Treeview.Heading", background=[("active", blend(BG2, ACC, 0.18))])
            st.configure("TScrollbar", background=BG2, troughcolor=BG0, bordercolor=BG0, arrowcolor=ACC)
            st.map("TScrollbar", background=[("active", blend(BG2, ACC, 0.2))])
            st.configure("TPanedwindow", background=BORDER)
            st.configure("Sash", sashthickness=6, gripsize=0)
            st.configure("TSeparator", background=BORDER)
        self.tl_fx = {k: T.flag("timeline", k, True) for k in ("gradient", "stars", "nebula", "meteors")}
        self.kara_fx = {k: T.flag("karaoke", k, True) for k in ("stars", "nebula", "meteors")}
        self.kara_fx["gradient"] = self.tl_fx["gradient"]

    def restyle_widgets(self):
        """Перекрашивает уже созданные tk-виджеты (ttk перекрашивается сам через стиль)."""
        self.configure(bg=self._sys_bg if self._ttk_native else BG0)
        self.bar_host.config(bg=self.theme.col("menubar", "background", BG1, BG0))
        self.mini.config(bg=BG0, highlightbackground=BORDER)
        self.canvas.config(bg=BG0, highlightbackground=BORDER, highlightcolor=ACC)
        self.lbl_hint.config(foreground=FG_DIM)
        self.lbl_now.config(foreground=GREEN)
        self.lbl_pos.config(foreground=ACC)
        self._config_tree_tags()
        self.mini_dirty = True

    def after_theme_change(self):
        self.apply_theme()
        self.restyle_widgets()
        self.install_menu()
        self._loc_dirty = True
        self.mini_dirty = True
        self.redraw_timeline()
        if self.karaoke:
            self.karaoke.retheme()
            self.karaoke.render(force=True)
        w = self.theme.warnings
        if w:
            self._flash_hint(tr("CSS: предупреждения") + f" ({len(w)}): {w[0]}", 9000)
        elif self._pending_hint:
            self._flash_hint(self._pending_hint, 9000)
        self._pending_hint = ""

    def set_theme_mode(self, mode, css_path=None):
        if css_path is not None:
            self.css_path = css_path
        self.theme_mode = mode
        self._css_mtime = self._mtime()
        self.theme = self._make_theme()
        self.after_theme_change()
        self.save_settings()

    def reload_css(self, quiet=False):
        if self.theme_mode != "css":
            if not quiet:
                self._flash_hint(tr("Перезагрузка нужна только для своего CSS-файла"), 4000)
            return
        self._css_mtime = self._mtime()
        self.theme = self._make_theme()
        self.after_theme_change()
        if not quiet and not self.theme.warnings:
            self._flash_hint(tr("CSS обновлён"), 2500)

    def css_poll(self):
        try:
            if self.theme_mode == "css" and self.css_watch and self.css_path:
                mt = self._mtime()
                if mt and mt != self._css_mtime:
                    self.reload_css(quiet=True)
        finally:
            self.after(800, self.css_poll)

    def _flash_hint(self, text, ms=5000):
        tok = object()
        self._hint_token = tok
        try:
            self.lbl_hint.config(text=text)
        except tk.TclError:
            return

        def clear():
            if self._hint_token is tok:
                try:
                    self.lbl_hint.config(text="")
                except tk.TclError:
                    pass
        self.after(ms, clear)

    def _startup_hint(self):
        w = self.theme.warnings
        if w:
            self._flash_hint(tr("CSS: предупреждения") + f" ({len(w)}): {w[0]}", 9000)
        elif self._pending_hint:
            self._flash_hint(self._pending_hint, 9000)
            self._pending_hint = ""

    def save_settings(self):
        self.cfg.update({"theme": self.theme_mode, "css_path": self.css_path, "css_watch": bool(self.css_watch),
                         "animations": bool(self.anim_on.get()), "native_menus": self.native_override,
                         "menu_effects": self.effects_override, "language": self.lang_choice,
                         "font_scale": self.font_scale})
        save_config(self.cfg)

    def toggle_anim(self):
        self.anim_on.set(not self.anim_on.get())
        self.save_settings()

    def toggle_css_watch(self):
        self.css_watch = not self.css_watch
        self.save_settings()

    def toggle_effects(self):
        self.effects_override = not self.effects_enabled()
        self.save_settings()

    def toggle_native(self):
        self.native_override = not self.native_menus()
        self.install_menu()
        self.save_settings()

    def set_font_scale(self, v):
        self.font_scale = round(min(2.0, max(0.7, v)), 2)
        self.apply_theme()
        self.restyle_widgets()
        self.install_menu()
        self.redraw_timeline()
        self.save_settings()

    def cmd_load_css(self):
        p = filedialog.askopenfilename(initialdir=sub_dir("themes"),
                                       filetypes=[("CSS", "*.css"), (tr("Все файлы"), "*.*")])
        if p:
            self.set_theme_mode("css", p)

    def cmd_export_css(self):
        p = filedialog.asksaveasfilename(initialdir=sub_dir("themes"), initialfile="my-theme.css",
                                         defaultextension=".css", filetypes=[("CSS", "*.css")])
        if not p:
            return
        try:
            with open(p, "w", encoding="utf-8") as f:
                f.write(COSMIC_CSS)
        except OSError as ex:
            messagebox.showerror(tr("Ошибка"), str(ex))
            return
        if messagebox.askyesno(tr("Тема"), tr("Шаблон сохранён. Применить его как свою тему и открыть в текстовом "
                                       "редакторе? Правки будут подхватываться сразу после сохранения файла.")):
            self.set_theme_mode("css", p)
            open_path(p)

    def open_themes_dir(self):
        open_path(sub_dir("themes"))

    def open_settings_dir(self):
        open_path(config_dir())

    def open_css_external(self):
        if self.css_path:
            open_path(self.css_path)

    def cmd_export_lang(self):
        p = filedialog.asksaveasfilename(initialdir=sub_dir("lang"), initialfile="xx.json",
                                         defaultextension=".json", filetypes=[("JSON", "*.json")])
        if not p:
            return
        data = {"__name__": "My language"}
        data.update(EN)
        try:
            with open(p, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=1)
        except OSError as ex:
            messagebox.showerror(tr("Ошибка"), str(ex))
            return
        messagebox.showinfo(tr("Перевод"), tr("Шаблон сохранён. Переведите значения (ключи не менять), измените "
                                       "имя файла на код языка (например de.json) и положите файл в папку "
                                       "lang — язык появится в меню «Справка»."))

    def set_language(self, code):
        self.lang_choice = code
        self.save_settings()
        if messagebox.askyesno("Language / Язык", "Language changed — restart now?\nЯзык изменён — перезапустить сейчас?"):
            self.restart_app()

    def restart_app(self):
        if not self.confirm_discard():
            return
        self.dirty = False
        self.save_settings()
        try:
            import subprocess
            args = [sys.executable, os.path.abspath(sys.argv[0])]
            if self.path:
                args.append(self.path)
            subprocess.Popen(args)
        except Exception as ex:
            messagebox.showerror(tr("Ошибка"), str(ex))
            return
        self.on_close()

    def show_about(self):
        import platform
        pg = f"pygame {pygame.version.ver}" if HAVE_PYGAME else tr("нет (pip install pygame)")
        try:
            import numpy
            npv = "numpy " + numpy.__version__
        except ImportError:
            npv = tr("нет (pip install numpy)")
        if sys.platform == "win32":
            fx = tr("Windows: размытие фона (10/11) и скруглённые меню")
        elif sys.platform == "darwin":
            fx = tr("macOS: скруглённые полупрозрачные меню (без размытия)")
        else:
            fx = tr("Linux: полупрозрачные меню (нужен композитор), без размытия")
        messagebox.showinfo(tr("О программе"), (
            f"TTML Word Editor {VERSION}\n"
            + tr("Пословный редактор TTML (Apple Music / Spicy Lyrics).") + "\n\n"
            f"Python {platform.python_version()}  ·  Tk {self.tk.call('info', 'patchlevel')}  ·  "
            f"{platform.system()}\n"
            + tr("Звук: {v}").format(v=pg) + "\n"
            + tr("Замедление: {v}").format(v=npv) + "\n"
            + tr("Эффекты меню: {v}").format(v=fx) + "\n"
            + tr("Тема: {t}    Язык: {l}").format(t=self.theme_mode, l=_LANG) + "\n\n"
            + tr("Папка настроек:") + f"\n{config_dir()}"))

    def show_css_reference(self):
        d = tk.Toplevel(self)
        d.title(tr("Справка по CSS-темам"))
        d.geometry("780x580")
        bf = ttk.Frame(d)
        bf.pack(side="bottom", fill="x", padx=8, pady=6)
        ttk.Button(bf, text=tr("Сохранить шаблон CSS…"), command=self.cmd_export_css).pack(side="left", padx=4)
        ttk.Button(bf, text=tr("Открыть папку тем"), command=self.open_themes_dir).pack(side="left", padx=4)
        ttk.Button(bf, text=tr("Закрыть"), command=d.destroy).pack(side="right", padx=4)
        sb = ttk.Scrollbar(d)
        sb.pack(side="right", fill="y")
        txt = tk.Text(d, wrap="word", bg=BG2, fg=FG, insertbackground=ACC, relief="flat", padx=14, pady=10,
                      font=("TkFixedFont", 10), yscrollcommand=sb.set, highlightthickness=0)
        txt.pack(fill="both", expand=True)
        sb.config(command=txt.yview)
        txt.insert("1.0", CSS_REFERENCE)
        txt.config(state="disabled")

    def report_callback_exception(self, exc, val, tb):
        text = "".join(traceback.format_exception(exc, val, tb))
        try:
            with open(os.path.join(config_dir(), "error.log"), "a", encoding="utf-8") as f:
                f.write(time.strftime("%Y-%m-%d %H:%M:%S") + "\n" + text + "\n")
        except OSError:
            pass
        now = time.time()
        if now - getattr(self, "_last_err_ts", 0.0) > 30:
            self._last_err_ts = now
            try:
                messagebox.showerror(tr("Ошибка"), tr("Что-то пошло не так — подробности записаны в error.log "
                                               "(Справка → Открыть папку настроек).\n\n") + str(val))
            except Exception:
                pass
        else:
            print(text, file=sys.stderr)

    # ------------------------------------------------------------ меню (общие данные для стеклянного и системного вида)
    def menus(self):
        return [(tr("Файл"), self._m_file), (tr("Правка"), self._m_edit), (tr("Вид"), self._m_view),
                (tr("Тема"), self._m_theme), (tr("Инструменты"), self._m_tools), (tr("Справка"), self._m_help)]

    def _m_file(self):
        return [mi(tr("Новый"), self.cmd_new),
                mi(tr("Открыть TTML…"), self.cmd_open, "Ctrl+O"),
                mi(tr("Сохранить"), self.cmd_save, "Ctrl+S"),
                mi(tr("Сохранить как…"), self.cmd_save_as), MSEP,
                mi(tr("Вставить текст песни (новый файл)…"), self.cmd_paste_text),
                mi(tr("Импорт LRC…"), self.cmd_import_lrc),
                mi(tr("Экспорт LRC…"), self.cmd_export_lrc), MSEP,
                mi(tr("Загрузить аудио…"), self.cmd_load_audio), MSEP,
                mi(tr("Выход"), self.on_close)]

    def _m_edit(self):
        return [mi(tr("Отменить"), self.undo, "Ctrl+Z"), mi(tr("Повторить"), self.redo, "Ctrl+Y"), MSEP,
                mi(tr("Найти / заменить…"), self.cmd_find, "Ctrl+F"),
                mi(tr("Сдвиг времени…"), self.cmd_shift), MSEP,
                mi(tr("Метаданные (язык, агенты)…"), self.cmd_meta)]

    def _m_view(self):
        return [mi(tr("Караоке-окно (что поётся сейчас)"), self.open_karaoke, "F4"), MSEP,
                mi(tr("Медленнее"), lambda: self.step_speed(-1), "F7"),
                mi(tr("Быстрее"), lambda: self.step_speed(1), "F8"),
                mi(tr("Нормальная скорость"), lambda: self.set_speed(1.0)), MSEP,
                mi(tr("Масштаб таймлайна +"), lambda: self.zoom(0.8), "↑"),
                mi(tr("Масштаб таймлайна −"), lambda: self.zoom(1.25), "↓"),
                mi(tr("Развернуть все строки"), lambda: self.expand_all(True)),
                mi(tr("Свернуть все строки"), lambda: self.expand_all(False)), MSEP,
                mi(tr("Анимации"), self.toggle_anim, check=lambda: self.anim_on.get()), MSEP,
                mi(tr("Размер интерфейса: больше"), lambda: self.set_font_scale(self.font_scale + 0.1)),
                mi(tr("Размер интерфейса: меньше"), lambda: self.set_font_scale(self.font_scale - 0.1)),
                mi(tr("Размер интерфейса: по умолчанию"), lambda: self.set_font_scale(1.0))]

    def _m_theme(self):
        cur = self.theme_mode
        items = [mhead(tr("Темы")),
                 mi(tr("Космос (по умолчанию)"), lambda: self.set_theme_mode("cosmic"), check=cur == "cosmic"),
                 mi(tr("Светлая"), lambda: self.set_theme_mode("light"), check=cur == "light"),
                 mi(tr("Высокий контраст"), lambda: self.set_theme_mode("contrast"), check=cur == "contrast"),
                 mi(tr("Системная (без темы)"), lambda: self.set_theme_mode("plain"), check=cur == "plain")]
        themes = user_themes()
        paths = [p for _n, p in themes]
        if themes or (self.css_path and self.css_path not in paths):
            items += [MSEP, mhead(tr("Мои темы"))]
            if self.css_path and self.css_path not in paths:
                items.append(mi(os.path.basename(self.css_path),
                                lambda: self.set_theme_mode("css", self.css_path), check=cur == "css"))
            for name, p in themes:
                items.append(mi(name, lambda p=p: self.set_theme_mode("css", p),
                                check=(cur == "css" and self.css_path == p)))
        items += [MSEP, mhead(tr("Свой CSS")),
                  mi(tr("Загрузить CSS-файл…"), self.cmd_load_css),
                  mi(tr("Перезагрузить CSS"), self.reload_css, "F9"),
                  mi(tr("Сохранить шаблон CSS…"), self.cmd_export_css),
                  mi(tr("Открыть папку тем"), self.open_themes_dir),
                  mi(tr("Следить за файлом CSS"), self.toggle_css_watch, check=lambda: self.css_watch),
                  MSEP, mhead(tr("Меню")),
                  mi(tr("Стеклянные эффекты (размытие, скругления)"), self.toggle_effects,
                     check=lambda: self.effects_enabled()),
                  mi(tr("Меню операционной системы"), self.toggle_native, check=lambda: self.native_menus())]
        return items

    def _m_tools(self):
        return [mi(tr("Убрать перекрытия слов"), self.tool_fix_overlaps),
                mi(tr("Сомкнуть маленькие зазоры…"), self.tool_close_gaps),
                mi(tr("Округлить время до 10 мс"), self.tool_round),
                mi(tr("Равномерно распределить слова в строке"), self.cmd_distribute),
                mi(tr("Переименовать агента во всех строках…"), self.tool_rename_agent)]

    def lang_items(self):
        cur = self.lang_choice
        items = [mi(tr("Авто (язык системы)"), lambda: self.set_language("auto"), check=cur == "auto"),
                 mi(tr("Русский"), lambda: self.set_language("ru"), check=cur == "ru"),
                 mi("English", lambda: self.set_language("en"), check=cur == "en")]
        for code, name, _p in language_packs():
            if code not in ("ru", "en"):
                items.append(mi(name, lambda c=code: self.set_language(c), check=cur == code))
        items += [MSEP, mi(tr("Сохранить шаблон перевода…"), self.cmd_export_lang)]
        return items

    def _m_help(self):
        return ([mi(tr("Горячие клавиши"), self.show_help, "F1"),
                 mi(tr("Справка по CSS-темам"), self.show_css_reference),
                 mi(tr("Открыть папку настроек"), self.open_settings_dir), MSEP,
                 mhead("Language / Язык")] + self.lang_items() +
                [MSEP, mi(tr("О программе"), self.show_about)])

    def open_language_menu(self, x=None, y=None):
        if x is None:
            x, y = self.winfo_rootx() + self.winfo_width() - 280, self.winfo_rooty() + 40
        self.popup_items([mhead("Language / Язык")] + self.lang_items(), x, y)

    def install_menu(self):
        for w in self.bar_host.winfo_children():
            w.destroy()
        self.menubar_widget = None
        if self.native_menus():
            self.bar_host.pack_forget()
            nm = tk.Menu(self)
            for title, factory in self.menus():
                sub = tk.Menu(nm, tearoff=0)
                sub.configure(postcommand=lambda s=sub, f=factory: self._fill_native(s, f))
                nm.add_cascade(label=title, menu=sub)
            self.config(menu=nm)
        else:
            self.config(menu="")
            self.bar_host.config(bg=self.theme.col("menubar", "background", BG1, BG0))
            self.bar_host.pack(fill="x", before=self.outer)
            self.menubar_widget = MenuBar(self, self.bar_host, self.menus())
            self.menubar_widget.pack(fill="x")

    def _fill_native(self, menu, factory):
        menu.delete(0, "end")
        for it in factory():
            if it.get("sep"):
                menu.add_separator()
            elif it.get("header"):
                menu.add_command(label="— " + it["header"] + " —", state="disabled")
            else:
                chk = it.get("check")
                chk = chk() if callable(chk) else chk
                label = ("✓ " if chk else "") + it["label"] + (("    " + it["accel"]) if it.get("accel") else "")
                ok = it.get("enabled", True) and it.get("cmd") is not None
                menu.add_command(label=label, command=it.get("cmd"), state="normal" if ok else "disabled")

    def popup_items(self, items, x, y):
        if self.native_menus():
            m = tk.Menu(self, tearoff=0)
            self._fill_native(m, lambda: items)
            try:
                m.tk_popup(x, y)
            finally:
                m.grab_release()
        else:
            PopupMenu(self, items, x, y, owner=None)

    # ---- контекстные меню (правая кнопка)
    def ctx_items(self):
        items = []
        w = self.cur_word()
        if w is not None:
            items += [mi(tr("▶ Проиграть слово"), self.play_word, "F6"),
                      mi(tr("Начало слова = плейхед (Tap)"), self.tap_begin, "T"),
                      mi(tr("Конец слова = плейхед"), self.tap_end, "E"), MSEP,
                      mi(tr("Вставить слово после…"), self.op_insert_word),
                      mi(tr("Слить со следующим"), self.op_merge_word),
                      mi(tr("Бэк-вокал"), self.ctx_toggle_bg, check=w.bg),
                      mi(tr("Пробел после слова"), self.ctx_toggle_space, check=w.space),
                      mi(tr("Удалить слово"), self.op_delete_word, "Del"), MSEP]
        if self.sel:
            items += [mi(tr("▶ Проиграть строку"), self.play_line, "F5"),
                      mi(tr("Разделить строку перед словом"), self.op_split_line),
                      mi(tr("Слить со следующей строкой"), self.op_merge_line),
                      mi(tr("Новая строка после…"), self.op_new_line),
                      mi(tr("Слова равномерно"), self.cmd_distribute),
                      mi(tr("Сдвиг времени…"), self.cmd_shift),
                      mi(tr("Удалить строку"), self.op_delete_line)]
        else:
            items += [mi(tr("Новая строка…"), self.op_new_line)]
        return items

    def ctx_toggle_bg(self):
        w = self.cur_word()
        if w is not None:
            self.push_undo()
            w.bg = not w.bg
            self.after_change(False)

    def ctx_toggle_space(self):
        w = self.cur_word()
        if w is not None:
            self.push_undo()
            w.space = not w.space
            self.after_change(False)

    def on_tree_rclick(self, e):
        iid = self.tree.identify_row(e.y)
        if iid:
            self.tree.selection_set(iid)
            self.on_select()
        self.popup_items(self.ctx_items(), e.x_root, e.y_root)
        return "break"

    def on_tl_rclick(self, e):
        h = None if e.y < 26 else self.hit(e.x, e.y)
        if h:
            self.select(h[0], h[1], scroll=False)
        t = self.x2t(e.x)
        self.popup_items([mi(tr("Поставить плейхед сюда"), lambda: self.seek(t)), MSEP] + self.ctx_items(),
                         e.x_root, e.y_root)
        return "break"

    def show_help(self):
        messagebox.showinfo(tr("Горячие клавиши"), (
            tr("ВОСПРОИЗВЕДЕНИЕ\n"
            "Space — играть / пауза       F5 — строка       F6 — слово\n"
            "F7 / F8 — медленнее / быстрее (0.25× … 1.5×)\n"
            "F4 — караоке-окно (текущая строка и буква)\n\n"
            "TAP\n"
            "T (или F2) — начало слова = плейхед, потом следующее слово\n"
            "E (или F3) — конец слова = плейхед\n\n"
            "ПРАВКА ВЫБРАННОГО СЛОВА\n"
            ", и . — сдвиг слова −/+10 мс (Shift — 50 мс)\n"
            "[ и ] — начало −/+10 мс;   ; и ' — конец −/+10 мс\n"
            "Delete — удалить слово/строку;  Ctrl+Z / Ctrl+Y — undo / redo\n"
            "Ctrl+S / Ctrl+O / Ctrl+F — сохранить / открыть / поиск\n"
            "Правая кнопка мыши (дерево, таймлайн) — контекстное меню\n\n"
            "ТАЙМЛАЙН (кликните по нему, чтобы он получил фокус)\n"
            "← / → — прокрутка (Shift — на страницу);  ↑ / ↓ — масштаб\n"
            "PgUp / PgDn — предыдущее / следующее слово\n"
            "Home / End — плейхед на начало / конец слова;  Enter — проиграть слово\n"
            "Ctrl+←/→ и Ctrl+↑/↓ — то же самое из любого места (в том числе из дерева)\n"
            "колесо — прокрутка, Ctrl+колесо — масштаб; мини-карта над таймлайном — быстрый переход\n"
            "Shift при перетаскивании — без магнита\n\n"
            "ДЕРЕВО\n"
            "Двойной клик по ячейке — правка; клик по «пробел»/«bg» — переключатель.\n"
            "Пробел внутри текста слова разобьёт его на два слова.\n\n"
            "ТЕМЫ\n"
            "Меню «Тема»: Космос / Светлая / Высокий контраст / Системная или свой CSS.\n"
            "F9 — перезагрузить CSS; F1 — эта справка. Подробности — «Справка по CSS-темам».\n"
            "Клавиши T/E/Ctrl+… работают и на русской раскладке.")))


    # ------------------------------------------------------------ интерфейс
    def build_ui(self):
        self.bar_host = tk.Frame(self, bd=0, highlightthickness=0)
        outer = ttk.PanedWindow(self, orient="vertical")
        outer.pack(fill="both", expand=True)
        self.outer = outer
        top = ttk.PanedWindow(outer, orient="horizontal")
        outer.add(top, weight=3)

        # дерево
        left = ttk.Frame(top)
        top.add(left, weight=4)
        cols = ("begin", "end", "sp", "bg", "agent", "part")
        self.tree = ttk.Treeview(left, columns=cols, selectmode="browse", show="tree headings")
        self.tree.heading("#0", text=tr("Текст (двойной клик — правка)"))
        self.tree.column("#0", width=380, stretch=True)
        for c, title, w in (("begin", tr("начало"), 80), ("end", tr("конец"), 80), ("sp", tr("пробел"), 52),
                            ("bg", "bg", 36), ("agent", tr("агент"), 56), ("part", tr("часть"), 84)):
            self.tree.heading(c, text=title)
            self.tree.column(c, width=w, minwidth=30, stretch=False, anchor="center")
        vs = ttk.Scrollbar(left, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vs.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vs.pack(side="right", fill="y")
        self._config_tree_tags()
        self.tree.bind("<<TreeviewSelect>>", self.on_select)
        self.tree.bind("<Double-1>", self.on_tree_dblclick)
        self.tree.bind("<Button-1>", self.on_tree_click, add="+")
        self.tree.bind("<Button-2>" if sys.platform == "darwin" else "<Button-3>", self.on_tree_rclick)
        self.tree.bind("<space>", lambda e: (self.toggle_play(), "break")[1])
        for k in ("Left", "Right", "Up", "Down"):
            self.tree.bind(f"<Control-{k}>", lambda e, k=k: (self.ctrl_arrow(k.lower(), bool(e.state & 1)), "break")[1])

        # инспектор
        right = ttk.Frame(top, width=380)
        top.add(right, weight=1)
        self.build_inspector(right)

        # нижняя часть: транспорт + таймлайн
        bottom = ttk.Frame(outer)
        outer.add(bottom, weight=2)
        self.build_transport(bottom)
        self.mini = tk.Canvas(bottom, height=38, bg=BG0, highlightthickness=1,
                              highlightbackground=BORDER, cursor="hand2")
        self.mini.pack(fill="x", padx=6, pady=(0, 3))
        self.mini.bind("<ButtonPress-1>", self.on_mini)
        self.mini.bind("<B1-Motion>", self.on_mini)
        self.mini.bind("<Configure>", lambda e: self.redraw_mini())
        self.canvas = tk.Canvas(bottom, height=170, bg=BG0, highlightthickness=2, takefocus=1,
                                highlightbackground=BORDER, highlightcolor=ACC)
        self.canvas.pack(fill="both", expand=True, padx=6)
        self.hbar = ttk.Scrollbar(bottom, orient="horizontal", command=self.on_hbar)
        self.hbar.pack(fill="x", padx=6)
        sf = ttk.Frame(bottom)
        sf.pack(fill="x", padx=8, pady=(2, 4))
        self.status = ttk.Label(sf, text="", anchor="w")
        self.status.pack(side="left")
        self.lbl_hint = ttk.Label(sf, text="", anchor="e", foreground=FG_DIM)
        self.lbl_hint.pack(side="right")
        self.lbl_now = ttk.Label(sf, text="", anchor="center", foreground=GREEN,
                                 font=("TkDefaultFont", 9, "bold"))
        self.lbl_now.pack(side="right", padx=16)
        c = self.canvas
        c.bind("<Configure>", lambda e: self.redraw_timeline())
        c.bind("<ButtonPress-1>", self.on_tl_press)
        c.bind("<B1-Motion>", self.on_tl_motion)
        c.bind("<ButtonRelease-1>", self.on_tl_release)
        c.bind("<Double-Button-1>", self.on_tl_double)
        c.bind("<Motion>", self.on_tl_hover)
        c.bind("<Leave>", self.on_tl_leave)
        c.bind("<Button-2>" if sys.platform == "darwin" else "<Button-3>", self.on_tl_rclick)
        c.bind("<MouseWheel>", self.on_wheel)
        c.bind("<Button-4>", self.on_wheel)
        c.bind("<Button-5>", self.on_wheel)

    def build_transport(self, parent):
        bar = ttk.Frame(parent)
        bar.pack(fill="x", padx=6, pady=(4, 0))
        bar2 = ttk.Frame(parent)
        bar2.pack(fill="x", padx=6, pady=(2, 3))

        def B(par, t, cmd, w=None):
            return ttk.Button(par, text=t, command=cmd, takefocus=False, width=w)

        self.btn_play = B(bar, tr("▶ Играть"), self.toggle_play, 10)
        self.btn_play.pack(side="left")
        B(bar, "⏮", lambda: self.seek(0.0), 3).pack(side="left", padx=(2, 0))
        self.lbl_pos = ttk.Label(bar, text="0.000", width=18, font=("TkFixedFont", 11, "bold"), foreground=ACC)
        self.lbl_pos.pack(side="left", padx=8)
        B(bar, tr("Аудио…"), self.cmd_load_audio).pack(side="left")
        self.lbl_audio = ttk.Label(bar, text="" if HAVE_PYGAME else tr("(нет pygame: pip install pygame)"))
        self.lbl_audio.pack(side="left", padx=6)
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Label(bar, text=tr("Скорость")).pack(side="left")
        B(bar, "◀", lambda: self.step_speed(-1), 2).pack(side="left", padx=(4, 0))
        cb = ttk.Combobox(bar, textvariable=self.speed_var, width=6, state="readonly",
                          values=[f"{v:g}×" for v in SPEEDS], takefocus=False)
        cb.pack(side="left", padx=2)
        cb.bind("<<ComboboxSelected>>", self.on_speed_selected)
        B(bar, "▶", lambda: self.step_speed(1), 2).pack(side="left")
        ttk.Checkbutton(bar, text=tr("сохранять тон"), variable=self.keep_pitch, takefocus=False,
                        command=lambda: self.set_speed(self.speed)).pack(side="left", padx=6)
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=8)
        B(bar, tr("🎤 Караоке-окно"), self.open_karaoke).pack(side="left")

        B(bar2, "−", lambda: self.zoom(1.25), 2).pack(side="left")
        B(bar2, "+", lambda: self.zoom(0.8), 2).pack(side="left", padx=(2, 0))
        B(bar2, tr("По строке"), self.fit_line).pack(side="left", padx=4)
        ttk.Checkbutton(bar2, text=tr("Следовать"), variable=self.follow, takefocus=False).pack(side="left", padx=4)
        ttk.Checkbutton(bar2, text=tr("Следить в дереве"), variable=self.follow_tree,
                        takefocus=False).pack(side="left", padx=4)
        ttk.Checkbutton(bar2, text=tr("Магнит"), variable=self.snap, takefocus=False).pack(side="left", padx=4)
        ttk.Checkbutton(bar2, text=tr("✦ Анимации"), variable=self.anim_on, takefocus=False,
                        command=self.save_settings).pack(side="left", padx=4)
        ttk.Separator(bar2, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Label(bar2, text="Tap:").pack(side="left")
        ttk.Checkbutton(bar2, text=tr("конец пред. слова = начало"), variable=self.chain,
                        takefocus=False).pack(side="left", padx=4)
        ttk.Label(bar2, text=tr("задержка, мс")).pack(side="left")
        ttk.Spinbox(bar2, from_=0, to=500, increment=10, width=5, textvariable=self.latency).pack(side="left", padx=3)

    def build_inspector(self, parent):
        self.v_wtext = tk.StringVar()
        self.v_wbegin = tk.StringVar()
        self.v_wend = tk.StringVar()
        self.v_wsp = tk.BooleanVar()
        self.v_wbg = tk.BooleanVar()
        self.v_ltext = tk.StringVar()
        self.v_lagent = tk.StringVar()
        self.v_lpart = tk.StringVar()
        pad = dict(padx=4, pady=2)

        fw = ttk.LabelFrame(parent, text=tr(" Слово "))
        fw.pack(fill="x", padx=6, pady=(6, 3))
        fw.columnconfigure(1, weight=1)
        ttk.Label(fw, text=tr("Текст")).grid(row=0, column=0, sticky="w", **pad)
        e = ttk.Entry(fw, textvariable=self.v_wtext)
        e.grid(row=0, column=1, columnspan=5, sticky="ew", **pad)
        self.e_wtext = e
        e.bind("<Return>", lambda ev: self.apply_word_fields())
        e.bind("<FocusOut>", lambda ev: self.focus_out_apply())
        steps = [("−50", -0.05), ("−10", -0.01), ("+10", 0.01), ("+50", 0.05)]
        for r, (label, var, which) in enumerate(
                [(tr("Начало"), self.v_wbegin, "begin"), (tr("Конец"), self.v_wend, "end"), (tr("Всё слово"), None, "both")],
                start=1):
            ttk.Label(fw, text=label).grid(row=r, column=0, sticky="w", **pad)
            if var is not None:
                ent = ttk.Entry(fw, textvariable=var, width=10)
                ent.grid(row=r, column=1, sticky="w", **pad)
                ent.bind("<Return>", lambda ev: self.apply_word_fields())
                ent.bind("<FocusOut>", lambda ev: self.focus_out_apply())
            for c, (txt, dt) in enumerate(steps, start=2):
                ttk.Button(fw, text=txt, width=4, takefocus=False,
                           command=lambda w=which, d=dt: self.nudge(w, d)).grid(row=r, column=c, padx=1, pady=1)
        ttk.Checkbutton(fw, text=tr("Пробел после слова"), variable=self.v_wsp, takefocus=False,
                        command=self.ui_toggle_space).grid(row=4, column=0, columnspan=3, sticky="w", **pad)
        ttk.Checkbutton(fw, text=tr("Бэк-вокал (bg)"), variable=self.v_wbg, takefocus=False,
                        command=self.ui_toggle_bg).grid(row=4, column=3, columnspan=3, sticky="w", **pad)
        bf = ttk.Frame(fw)
        bf.grid(row=5, column=0, columnspan=6, sticky="ew", pady=(2, 4))
        for i, (t, cmd) in enumerate(((tr("Разбить по курсору"), self.op_split_word),
                                      (tr("Слить со следующим"), self.op_merge_word),
                                      (tr("Вставить после"), self.op_insert_word),
                                      (tr("Удалить слово"), self.op_delete_word))):
            ttk.Button(bf, text=t, command=cmd, takefocus=False).grid(row=i // 2, column=i % 2, sticky="ew",
                                                                      padx=2, pady=1)
            bf.columnconfigure(i % 2, weight=1)

        fl = ttk.LabelFrame(parent, text=tr(" Строка "))
        fl.pack(fill="x", padx=6, pady=3)
        fl.columnconfigure(1, weight=1)
        ttk.Label(fl, text=tr("Текст")).grid(row=0, column=0, sticky="w", **pad)
        e2 = ttk.Entry(fl, textvariable=self.v_ltext)
        e2.grid(row=0, column=1, columnspan=3, sticky="ew", **pad)
        e2.bind("<Return>", lambda ev: self.apply_line_text())
        ttk.Label(fl, text=tr("Агент")).grid(row=1, column=0, sticky="w", **pad)
        self.cb_agent = ttk.Combobox(fl, textvariable=self.v_lagent, width=8)
        self.cb_agent.grid(row=1, column=1, sticky="w", **pad)
        self.cb_agent.bind("<<ComboboxSelected>>", lambda ev: self.apply_line_meta())
        self.cb_agent.bind("<Return>", lambda ev: self.apply_line_meta())
        ttk.Label(fl, text=tr("Часть")).grid(row=1, column=2, sticky="e", **pad)
        self.cb_part = ttk.Combobox(fl, textvariable=self.v_lpart, values=PARTS, width=12)
        self.cb_part.grid(row=1, column=3, sticky="w", **pad)
        self.cb_part.bind("<<ComboboxSelected>>", lambda ev: self.apply_line_meta())
        self.cb_part.bind("<Return>", lambda ev: self.apply_line_meta())
        lf = ttk.Frame(fl)
        lf.grid(row=2, column=0, columnspan=4, sticky="ew", pady=(2, 4))
        btns = ((tr("Разделить перед словом"), self.op_split_line), (tr("Слить со следующей"), self.op_merge_line),
                (tr("Новая строка после"), self.op_new_line), (tr("Удалить строку"), self.op_delete_line),
                (tr("▲ Выше"), lambda: self.op_move_line(-1)), (tr("▼ Ниже"), lambda: self.op_move_line(1)),
                (tr("Слова равномерно"), self.cmd_distribute), (tr("Сдвиг…"), self.cmd_shift))
        for i, (t, cmd) in enumerate(btns):
            ttk.Button(lf, text=t, command=cmd, takefocus=False).grid(row=i // 2, column=i % 2, sticky="ew",
                                                                      padx=2, pady=1)
            lf.columnconfigure(i % 2, weight=1)

        fp = ttk.LabelFrame(parent, text=tr(" Прослушивание "))
        fp.pack(fill="x", padx=6, pady=3)
        ttk.Button(fp, text=tr("▶ Слово (F6)"), command=self.play_word, takefocus=False).pack(side="left", padx=4, pady=4)
        ttk.Button(fp, text=tr("▶ Строка (F5)"), command=self.play_line, takefocus=False).pack(side="left", padx=4)

    # ------------------------------------------------------------ клавиши
    def bind_keys(self):
        self.bind_all("<Key>", self.on_key)

    @staticmethod
    def _ctrl_is(e, latin, cyr):
        ks = e.keysym.lower()
        if ks == latin or ks == cyr:
            return True
        return sys.platform == "win32" and e.keycode == ord(latin.upper())

    def on_key(self, e):
        try:
            if e.widget.winfo_toplevel() is not self:
                return None
        except Exception:
            return None
        cls = e.widget.winfo_class() if hasattr(e.widget, "winfo_class") else ""
        ctrl = bool(e.state & 0x4)
        shift = bool(e.state & 0x1)
        if ctrl:
            if self._ctrl_is(e, "s", "cyrillic_yeru"):
                self.cmd_save()
                return "break"
            if self._ctrl_is(e, "o", "cyrillic_shcha"):
                self.cmd_open()
                return "break"
            if self._ctrl_is(e, "f", "cyrillic_a"):
                self.cmd_find()
                return "break"
            if cls in TEXT_CLASSES:
                return None
            if e.keysym.lower() in ("left", "right", "up", "down"):
                self.ctrl_arrow(e.keysym.lower(), shift)
                return "break"
            if self._ctrl_is(e, "z", "cyrillic_ya"):
                self.redo() if shift else self.undo()
                return "break"
            if self._ctrl_is(e, "y", "cyrillic_en"):
                self.redo()
                return "break"
            return None
        if cls in TEXT_CLASSES:
            return None
        ks = e.keysym.lower()
        if e.widget is self.canvas and self.canvas_key(ks, shift):
            return "break"
        if ks == "space":
            self.toggle_play()
        elif ks == "f4":
            self.open_karaoke()
        elif ks == "f7":
            self.step_speed(-1)
        elif ks == "f8":
            self.step_speed(1)
        elif ks == "f9":
            self.reload_css()
        elif ks == "f1":
            self.show_help()
        elif ks in ("t", "cyrillic_ie", "f2"):
            self.tap_begin()
        elif ks in ("e", "cyrillic_u", "f3"):
            self.tap_end()
        elif ks == "f5":
            self.play_line()
        elif ks == "f6":
            self.play_word()
        elif ks == "delete":
            self.op_delete_word() if (self.sel and self.sel[1] is not None) else self.op_delete_line()
        elif ks in ("comma", "less", "cyrillic_be"):
            self.nudge("both", -(0.05 if shift else 0.01))
        elif ks in ("period", "greater", "cyrillic_yu"):
            self.nudge("both", 0.05 if shift else 0.01)
        elif ks in ("bracketleft", "cyrillic_ha"):
            self.nudge("begin", -0.01)
        elif ks in ("bracketright", "cyrillic_hardsign"):
            self.nudge("begin", 0.01)
        elif ks in ("semicolon", "cyrillic_zhe"):
            self.nudge("end", -0.01)
        elif ks in ("apostrophe", "cyrillic_e"):
            self.nudge("end", 0.01)
        else:
            return None
        return "break"

    # ------------------------------------------------------------ навигация стрелками
    def scroll_view(self, frac):
        bs, bl = self._view_base()
        self.set_view(bs + frac * bl)

    def ctrl_arrow(self, k, shift=False):
        if k == "left":
            self.scroll_view(-(0.5 if shift else 0.1))
        elif k == "right":
            self.scroll_view(0.5 if shift else 0.1)
        elif k == "up":
            self.zoom(0.8)
        elif k == "down":
            self.zoom(1.25)

    def canvas_key(self, ks, shift):
        if ks == "left":
            self.scroll_view(-(0.9 if shift else 0.1))
        elif ks == "right":
            self.scroll_view(0.9 if shift else 0.1)
        elif ks == "up":
            self.zoom(0.8)
        elif ks == "down":
            self.zoom(1.25)
        elif ks == "prior":
            self.select_rel(-1)
        elif ks == "next":
            self.select_rel(1)
        elif ks == "home":
            self.seek_to_selection(False)
        elif ks == "end":
            self.seek_to_selection(True)
        elif ks == "return":
            self.play_word() if self.cur_word() else self.play_line()
        else:
            return False
        return True

    def select_rel(self, d):
        if not self.lines:
            return
        li, wi = self.sel if self.sel else (0, 0)
        wi = 0 if wi is None else wi
        if d > 0:
            n = self._next_word(li, wi)
        elif wi > 0:
            n = (li, wi - 1)
        elif li > 0:
            n = (li - 1, max(0, len(self.lines[li - 1].words) - 1))
        else:
            n = None
        if n:
            self.select(n[0], n[1])

    def seek_to_selection(self, to_end):
        if not self.sel or self.sel[0] >= len(self.lines):
            return
        w = self.cur_word()
        L = self.lines[self.sel[0]]
        t = (w.end if to_end else w.begin) if w else (L.end if to_end else L.begin)
        self.seek(t)

    def expand_all(self, flag):
        for iid in self.tree.get_children(""):
            self.tree.item(iid, open=flag)

    # ------------------------------------------------------------ вспомогательное
    @property
    def lines(self):
        return self.doc.lines

    def cur_word(self):
        if not self.sel or self.sel[1] is None:
            return None
        li, wi = self.sel
        if li < len(self.lines) and wi < len(self.lines[li].words):
            return self.lines[li].words[wi]
        return None

    def valid_sel(self, sel):
        if not sel or not self.lines:
            return None
        li, wi = sel
        li = min(max(li, 0), len(self.lines) - 1)
        if wi is not None:
            n = len(self.lines[li].words)
            wi = min(wi, n - 1) if n else None
            if wi is not None and wi < 0:
                wi = None
        return (li, wi)

    def snapshot(self):
        return (copy.deepcopy(self.doc.lines), copy.deepcopy(self.doc.agents), self.doc.lang)

    def push_undo(self):
        self.undo_stack.append(self.snapshot())
        if len(self.undo_stack) > 300:
            self.undo_stack.pop(0)
        self.redo_stack.clear()

    def _restore(self, snap):
        self.doc.lines, self.doc.agents, self.doc.lang = copy.deepcopy(snap)

    def undo(self):
        if not self.undo_stack:
            return
        self.redo_stack.append(self.snapshot())
        self._restore(self.undo_stack.pop())
        self.after_change(True)

    def redo(self):
        if not self.redo_stack:
            return
        self.undo_stack.append(self.snapshot())
        self._restore(self.redo_stack.pop())
        self.after_change(True)

    def after_change(self, structural=True, select=None, reset_open=False):
        self.dirty = True
        sel = select if select is not None else self.valid_sel(self.sel)
        if structural:
            self.rebuild(sel, reset_open)
        else:
            self.sel = sel
            self.refresh_rows()
        self.update_inspector()
        self.redraw_timeline()
        self.update_title()
        self.update_status()
        self._loc_dirty = True
        if self.karaoke:
            self.karaoke.render(force=True)

    def update_title(self):
        name = os.path.basename(self.path) if self.path else tr("без имени")
        self.title(f"TTML Word Editor — {name}{' *' if self.dirty else ''}")

    def update_status(self):
        n_w = sum(len(l.words) for l in self.lines)
        end = max((l.end for l in self.lines), default=0.0)
        self.status.config(text=tr("Строк: {l}   слов: {w}   длительность: {d}").format(l=len(self.lines), w=n_w, d=fmt_time(end)))

    # ------------------------------------------------------------ дерево
    @staticmethod
    def line_values(L):
        return (fmt_time(L.begin), fmt_time(L.end), "", "", L.agent, L.part)

    @staticmethod
    def word_values(w):
        return (fmt_time(w.begin), fmt_time(w.end), "✓" if w.space else "", "♪" if w.bg else "", "", "")

    def rebuild(self, select="keep", reset_open=False):
        t = self.tree
        closed = set()
        if not reset_open:
            for li, iid in enumerate(t.get_children("")):
                if not t.item(iid, "open"):
                    closed.add(li)
        for iid in t.get_children(""):
            t.delete(iid)
        for li, L in enumerate(self.lines):
            liid = f"L{li}"
            t.insert("", "end", iid=liid, text=f"{li + 1}. {L.text()}", values=self.line_values(L),
                     open=(li not in closed), tags=("line",))
            for wi, w in enumerate(L.words):
                t.insert(liid, "end", iid=f"L{li}W{wi}", text=w.text, values=self.word_values(w),
                         tags=("bg",) if w.bg else ())
        sel = self.valid_sel(self.sel) if select == "keep" else select
        self.now_iid = None
        self._loc_dirty = True
        self.mini_dirty = True
        if sel:
            self.select(sel[0], sel[1], scroll=False)
        else:
            self.sel = None
        self.update_status()

    def refresh_rows(self):
        t = self.tree
        if len(t.get_children("")) != len(self.lines):
            return self.rebuild()
        for li, L in enumerate(self.lines):
            liid = f"L{li}"
            if len(t.get_children(liid)) != len(L.words):
                return self.rebuild()
            t.item(liid, text=f"{li + 1}. {L.text()}", values=self.line_values(L))
            for wi, w in enumerate(L.words):
                t.item(f"L{li}W{wi}", text=w.text, values=self.word_values(w),
                       tags=("bg",) if w.bg else ())
        self.now_iid = None
        self._loc_dirty = True
        self.mini_dirty = True
        self.update_status()

    def refresh_word_row(self, li, wi):
        iid = f"L{li}W{wi}"
        if self.tree.exists(iid):
            w = self.lines[li].words[wi]
            tg = self.tree.item(iid, "tags")
            tg = list(tg) if isinstance(tg, (list, tuple)) else str(tg).split()
            self.tree.item(iid, text=w.text, values=self.word_values(w),
                           tags=tuple(["now"] if "now" in tg else []) + (("bg",) if w.bg else ()))
            self.mini_dirty = True
            L = self.lines[li]
            self.tree.item(f"L{li}", text=f"{li + 1}. {L.text()}", values=self.line_values(L))

    def select(self, li, wi=None, scroll=True):
        if li < 0 or li >= len(self.lines):
            return
        self.sel = (li, wi)
        iid = f"L{li}" if wi is None else f"L{li}W{wi}"
        if self.tree.exists(iid):
            self.tree.selection_set(iid)
            self.tree.focus(iid)
            self.tree.see(iid)
        self.update_inspector()
        if scroll:
            self.ensure_visible()
        self.redraw_timeline()

    def on_select(self, _e=None):
        s = self.tree.selection()
        if not s:
            return
        m = re.fullmatch(r"L(\d+)(?:W(\d+))?", s[0])
        if not m:
            return
        new = (int(m.group(1)), int(m.group(2)) if m.group(2) else None)
        if new == self.sel:
            return
        self.sel = new
        self.update_inspector()
        self.ensure_visible()
        self.redraw_timeline()

    def on_tree_click(self, e):
        if self.tree.identify_region(e.x, e.y) != "cell":
            return
        iid = self.tree.identify_row(e.y)
        col = self.tree.identify_column(e.x)
        m = re.fullmatch(r"L(\d+)W(\d+)", iid or "")
        if not m or col not in ("#3", "#4"):
            return
        li, wi = int(m.group(1)), int(m.group(2))
        self.push_undo()
        w = self.lines[li].words[wi]
        if col == "#3":
            w.space = not w.space
        else:
            w.bg = not w.bg
        self.sel = (li, wi)
        self.after_change(False)

    def on_tree_dblclick(self, e):
        iid = self.tree.identify_row(e.y)
        if not iid:
            return None
        if self.tree.identify_element(e.x, e.y) == "Treeitem.indicator":
            return None
        col = self.tree.identify_column(e.x)
        field_ = {"#0": "text", "#1": "begin", "#2": "end", "#5": "agent", "#6": "part"}.get(col)
        if field_:
            self.edit_cell(iid, col, field_)
        return "break"

    def edit_cell(self, iid, col, field_):
        m = re.fullmatch(r"L(\d+)(?:W(\d+))?", iid)
        if not m:
            return
        li = int(m.group(1))
        wi = int(m.group(2)) if m.group(2) else None
        L = self.lines[li]
        w = L.words[wi] if wi is not None else None
        if field_ in ("agent", "part") and w is not None:
            return
        if field_ == "text":
            init = w.text if w else L.text()
        elif field_ == "begin":
            init = fmt_time(w.begin if w else L.begin)
        elif field_ == "end":
            init = fmt_time(w.end if w else L.end)
        else:
            init = getattr(L, field_)
        bbox = self.tree.bbox(iid, col)
        if not bbox:
            return
        x, y, wd, ht = bbox
        ent = ttk.Entry(self.tree)
        ent.insert(0, init)
        ent.select_range(0, "end")
        ent.place(x=x, y=y, width=max(wd, 70), height=ht)
        ent.focus_set()
        done = [False]

        def commit(_ev=None):
            if done[0]:
                return
            done[0] = True
            val = ent.get()
            ent.destroy()
            self.tree.focus_set()
            self.apply_cell(li, wi, field_, val)

        def cancel(_ev=None):
            if done[0]:
                return
            done[0] = True
            ent.destroy()
            self.tree.focus_set()

        ent.bind("<Return>", commit)
        ent.bind("<Escape>", cancel)
        ent.bind("<FocusOut>", commit)

    def apply_cell(self, li, wi, field_, val):
        L = self.lines[li]
        if field_ == "text":
            if wi is None:
                self.set_line_text(li, val)
            else:
                self.set_word_text(li, wi, val)
            return
        if field_ in ("agent", "part"):
            val = val.strip()
            if field_ == "agent" and not val:
                return
            self.push_undo()
            setattr(L, field_, val)
            if field_ == "agent":
                self.ensure_agent(val)
            self.select_keep(li, wi)
            self.after_change(False)
            return
        try:
            t = parse_time(val)
        except ValueError:
            self.bell()
            return
        self.push_undo()
        if wi is None:
            if field_ == "begin":
                d = t - L.begin
                d = max(d, -L.begin)
                for w in L.words:
                    w.begin += d
                    w.end += d
            else:
                last = max(L.words, key=lambda x: x.end)
                if t > last.begin:
                    last.end = t
        else:
            w = L.words[wi]
            if field_ == "begin":
                dur = w.end - w.begin
                w.begin = t
                if w.end <= t:
                    w.end = t + max(dur, MIN_DUR)
            else:
                if t <= w.begin:
                    self.undo_stack.pop()
                    self.bell()
                    return
                w.end = t
        self.select_keep(li, wi)
        self.after_change(False)

    def select_keep(self, li, wi):
        self.sel = (li, wi)

    def ensure_agent(self, aid):
        if not any(a[0] == aid for a in self.doc.agents):
            self.doc.agents.append([aid, "other" if aid.startswith("v1000") else "person"])

    # ------------------------------------------------------------ инспектор
    def update_inspector(self):
        for v in (self.v_wtext, self.v_wbegin, self.v_wend, self.v_ltext, self.v_lagent, self.v_lpart):
            v.set("")
        self.v_wsp.set(False)
        self.v_wbg.set(False)
        self.cb_agent.config(values=[a[0] for a in self.doc.agents])
        if not self.sel or self.sel[0] >= len(self.lines):
            return
        li, wi = self.sel
        L = self.lines[li]
        self.v_ltext.set(L.text())
        self.v_lagent.set(L.agent)
        self.v_lpart.set(L.part)
        if wi is not None and wi < len(L.words):
            w = L.words[wi]
            self.v_wtext.set(w.text)
            self.v_wbegin.set(fmt_time(w.begin))
            self.v_wend.set(fmt_time(w.end))
            self.v_wsp.set(w.space)
            self.v_wbg.set(w.bg)

    def focus_out_apply(self):
        # значения фиксируем сейчас: к моменту after_idle выбор в дереве уже может смениться
        sel = self.sel
        vals = (self.v_wtext.get(), self.v_wbegin.get(), self.v_wend.get())
        self.after_idle(lambda: self.apply_word_fields(sel, vals))

    def apply_word_fields(self, sel=None, vals=None):
        sel = sel or self.sel
        if not sel or sel[1] is None:
            return
        li, wi = sel
        if li >= len(self.lines) or wi >= len(self.lines[li].words):
            return
        w = self.lines[li].words[wi]
        if vals is None:
            vals = (self.v_wtext.get(), self.v_wbegin.get(), self.v_wend.get())
        try:
            b = parse_time(vals[1])
            e = parse_time(vals[2])
        except ValueError:
            self.bell()
            self.update_inspector()
            return
        txt = vals[0].strip()
        ch_time = abs(b - w.begin) > 1e-4 or abs(e - w.end) > 1e-4
        ch_text = txt != w.text
        if not (ch_time or ch_text):
            return
        self.push_undo()
        if ch_time:
            if e <= b:
                e = b + max(w.end - w.begin, MIN_DUR) if abs(b - w.begin) > 1e-4 else b + MIN_DUR
            w.begin, w.end = b, e
        structural = False
        if ch_text:
            structural = self._set_text(li, wi, txt)
        self.after_change(structural, select=self.valid_sel(self.sel))

    def _set_text(self, li, wi, text):
        """Меняет текст слова. Возвращает True, если поменялась структура."""
        L = self.lines[li]
        w = L.words[wi]
        parts = text.split()
        if not parts:
            del L.words[wi]
            if not L.words:
                del self.lines[li]
            return True
        if len(parts) == 1:
            w.text = parts[0]
            return False
        n = len(parts)
        d = (w.end - w.begin) / n
        new = [Word(p, w.begin + i * d, w.begin + (i + 1) * d, space=(i < n - 1 or w.space), bg=w.bg)
               for i, p in enumerate(parts)]
        L.words[wi:wi + 1] = new
        return True

    def set_word_text(self, li, wi, text):
        if text.strip() == self.lines[li].words[wi].text:
            return
        self.push_undo()
        structural = self._set_text(li, wi, text)
        self.after_change(structural)

    def set_line_text(self, li, text):
        toks = text.split()
        L = self.lines[li]
        if not toks or toks == [w.text for w in L.words]:
            return
        self.push_undo()
        if len(toks) == len(L.words):
            for w, t in zip(L.words, toks):
                w.text = t
        else:
            L.words = make_words(text, L.begin, L.end)
        self.after_change(True)

    def apply_line_text(self):
        if self.sel:
            self.set_line_text(self.sel[0], self.v_ltext.get())

    def apply_line_meta(self):
        if not self.sel:
            return
        L = self.lines[self.sel[0]]
        agent = self.v_lagent.get().strip() or L.agent
        part = self.v_lpart.get().strip()
        if agent == L.agent and part == L.part:
            return
        self.push_undo()
        L.agent, L.part = agent, part
        self.ensure_agent(agent)
        self.after_change(False)

    def ui_toggle_space(self):
        w = self.cur_word()
        if w is None:
            return
        self.push_undo()
        w.space = self.v_wsp.get()
        self.after_change(False)

    def ui_toggle_bg(self):
        w = self.cur_word()
        if w is None:
            return
        self.push_undo()
        w.bg = self.v_wbg.get()
        self.after_change(False)

    def nudge(self, which, dt):
        w = self.cur_word()
        if w is None:
            self.bell()
            return
        self.push_undo()
        if which == "both":
            dt = max(dt, -w.begin)
            w.begin += dt
            w.end += dt
        elif which == "begin":
            w.begin = min(max(0.0, w.begin + dt), w.end - MIN_DUR)
        else:
            w.end = max(w.end + dt, w.begin + MIN_DUR)
        self.after_change(False)

    # ------------------------------------------------------------ операции со словами/строками
    def op_split_word(self):
        w = self.cur_word()
        if w is None:
            return
        pos = self.e_wtext.index(tk.INSERT)
        text = w.text
        if pos <= 0 or pos >= len(text):
            messagebox.showinfo(tr("Разбить слово"),
                                tr("Поставьте курсор в поле «Текст» внутри слова — там, где нужно разрезать (на слоги)."))
            return
        li, wi = self.sel
        self.push_undo()
        tm = w.begin + (w.end - w.begin) * pos / len(text)
        a = Word(text[:pos], w.begin, tm, space=False, bg=w.bg)
        b = Word(text[pos:], tm, w.end, space=w.space, bg=w.bg)
        self.lines[li].words[wi:wi + 1] = [a, b]
        self.after_change(True, select=(li, wi))

    def op_merge_word(self):
        w = self.cur_word()
        if w is None:
            return
        li, wi = self.sel
        L = self.lines[li]
        if wi + 1 >= len(L.words):
            self.bell()
            return
        self.push_undo()
        n = L.words[wi + 1]
        w.text += n.text
        w.end = max(w.end, n.end)
        w.space = n.space
        del L.words[wi + 1]
        self.after_change(True, select=(li, wi))

    def op_insert_word(self):
        if not self.sel:
            return
        li, wi = self.sel
        L = self.lines[li]
        text = simpledialog.askstring(tr("Вставить слово"), tr("Текст слова:"), parent=self)
        if not text or not text.strip():
            return
        self.push_undo()
        idx = (wi if wi is not None else len(L.words) - 1) + 1
        base = L.words[idx - 1].end if idx - 1 >= 0 and L.words else L.begin
        new = make_words(text, base, base + DEFAULT_WORD * len(text.split()))
        if idx > 0 and L.words:
            L.words[idx - 1].space = True
        if idx >= len(L.words) and new:
            new[-1].space = False
        L.words[idx:idx] = new
        self.after_change(True, select=(li, idx))

    def op_delete_word(self):
        if not self.sel or self.sel[1] is None:
            return
        li, wi = self.sel
        self.push_undo()
        L = self.lines[li]
        del L.words[wi]
        if not L.words:
            del self.lines[li]
            self.after_change(True, select=self.valid_sel((li, None)))
        else:
            self.after_change(True, select=(li, min(wi, len(L.words) - 1)))

    def op_split_line(self):
        if not self.sel or self.sel[1] is None or self.sel[1] == 0:
            messagebox.showinfo(tr("Разделить строку"), tr("Выберите слово, с которого начнётся новая строка (не первое)."))
            return
        li, wi = self.sel
        L = self.lines[li]
        self.push_undo()
        new = Line(words=L.words[wi:], agent=L.agent, part=L.part, extras=[])
        L.words = L.words[:wi]
        L.words[-1].space = False
        self.lines.insert(li + 1, new)
        self.after_change(True, select=(li + 1, 0))

    def op_merge_line(self):
        if not self.sel:
            return
        li = self.sel[0]
        if li + 1 >= len(self.lines):
            self.bell()
            return
        self.push_undo()
        L, N = self.lines[li], self.lines[li + 1]
        if L.words:
            L.words[-1].space = True
        L.words.extend(N.words)
        L.extras.extend(N.extras)
        del self.lines[li + 1]
        self.after_change(True, select=(li, self.sel[1]))

    def op_new_line(self):
        li = self.sel[0] if self.sel else len(self.lines) - 1
        text = simpledialog.askstring(tr("Новая строка"), tr("Текст строки:"), parent=self)
        if not text or not text.strip():
            return
        self.push_undo()
        base = self.lines[li].end + 0.3 if self.lines else 0.0
        agent = self.lines[li].agent if self.lines else self.doc.agents[0][0]
        part = self.lines[li].part if self.lines else ""
        n = len(text.split())
        words = make_words(text, base, base + DEFAULT_WORD * n)
        words[-1].space = False
        self.lines.insert(li + 1, Line(words=words, agent=agent, part=part))
        self.after_change(True, select=(li + 1, 0))

    def op_delete_line(self):
        if not self.sel:
            return
        li = self.sel[0]
        self.push_undo()
        del self.lines[li]
        self.after_change(True, select=self.valid_sel((li, None)))

    def op_move_line(self, d):
        if not self.sel:
            return
        li = self.sel[0]
        nj = li + d
        if nj < 0 or nj >= len(self.lines):
            return
        self.push_undo()
        self.lines[li], self.lines[nj] = self.lines[nj], self.lines[li]
        self.after_change(True, select=(nj, self.sel[1]))

    def cmd_distribute(self):
        if not self.sel:
            return
        li = self.sel[0]
        L = self.lines[li]
        if not L.words:
            return
        self.push_undo()
        b, e = L.begin, L.end
        n = len(L.words)
        if e - b < 0.05 * n:
            e = b + DEFAULT_WORD * n
        d = (e - b) / n
        for i, w in enumerate(L.words):
            w.begin, w.end = b + i * d, b + (i + 1) * d
        self.after_change(False)

    # ------------------------------------------------------------ сдвиг
    def cmd_shift(self):
        res = self.ask_shift()
        if not res:
            return
        scope, ms = res
        d = ms / 1000.0
        targets = []
        sel = self.sel
        for li, L in enumerate(self.lines):
            for wi, w in enumerate(L.words):
                if scope == "all":
                    ok = True
                elif not sel:
                    ok = False
                elif scope == "word":
                    ok = (li, wi) == sel
                elif scope == "restline":
                    ok = li == sel[0] and wi >= (sel[1] or 0)
                elif scope == "line":
                    ok = li == sel[0]
                else:  # restsong
                    ok = li >= sel[0] and (li > sel[0] or wi >= (sel[1] or 0))
                if ok:
                    targets.append(w)
        if not targets:
            messagebox.showinfo(tr("Сдвиг"), tr("Нечего сдвигать — выберите слово/строку в дереве."))
            return
        d = max(d, -min(w.begin for w in targets))
        self.push_undo()
        for w in targets:
            w.begin += d
            w.end += d
        self.after_change(False)

    def ask_shift(self):
        dlg = tk.Toplevel(self)
        dlg.title(tr("Сдвиг времени"))
        dlg.transient(self)
        res = {"v": None}
        scope = tk.StringVar(value="line" if self.sel else "all")
        ms = tk.StringVar(value="100")
        opts = (("word", tr("Только выбранное слово")), ("restline", tr("От выбранного слова до конца строки")),
                ("line", tr("Вся выбранная строка")), ("restsong", tr("От выбранного слова до конца песни")),
                ("all", tr("Вся песня")))
        for v, t in opts:
            ttk.Radiobutton(dlg, text=t, variable=scope, value=v).pack(anchor="w", padx=12, pady=1)
        fr = ttk.Frame(dlg)
        fr.pack(fill="x", padx=12, pady=8)
        ttk.Label(fr, text=tr("Сдвиг, мс (можно отрицательный):")).pack(side="left")
        ent = ttk.Entry(fr, textvariable=ms, width=8)
        ent.pack(side="left", padx=6)

        def ok(_e=None):
            try:
                res["v"] = (scope.get(), float(ms.get().replace(",", ".")))
            except ValueError:
                self.bell()
                return
            dlg.destroy()

        bf = ttk.Frame(dlg)
        bf.pack(pady=(0, 8))
        ttk.Button(bf, text="OK", command=ok).pack(side="left", padx=4)
        ttk.Button(bf, text=tr("Отмена"), command=dlg.destroy).pack(side="left", padx=4)
        ent.bind("<Return>", ok)
        dlg.grab_set()
        ent.focus_set()
        ent.select_range(0, "end")
        self.wait_window(dlg)
        return res["v"]

    # ------------------------------------------------------------ инструменты
    def tool_fix_overlaps(self):
        self.push_undo()
        last = {}
        n = 0
        for L in self.lines:
            for w in L.words:
                if w.bg:
                    continue
                p = last.get(L.agent)
                if p and p.end > w.begin > p.begin:
                    p.end = w.begin
                    n += 1
                last[L.agent] = w
        self.after_change(False)
        messagebox.showinfo(tr("Перекрытия"), tr("Исправлено: {n}").format(n=n))

    def tool_close_gaps(self):
        ms = simpledialog.askinteger(tr("Зазоры"), tr("Смыкать зазоры между словами в строке короче, мс:"),
                                     initialvalue=250, minvalue=1, maxvalue=5000, parent=self)
        if not ms:
            return
        self.push_undo()
        n = 0
        for L in self.lines:
            ws = [w for w in L.words if not w.bg]
            for a, b in zip(ws, ws[1:]):
                gap = b.begin - a.end
                if 0 < gap <= ms / 1000.0:
                    a.end = b.begin
                    n += 1
        self.after_change(False)
        messagebox.showinfo(tr("Зазоры"), tr("Сомкнуто: {n}").format(n=n))

    def tool_round(self):
        self.push_undo()
        for L in self.lines:
            for w in L.words:
                w.begin = round(w.begin * 100) / 100
                w.end = max(round(w.end * 100) / 100, w.begin + MIN_DUR)
        self.after_change(False)

    def tool_rename_agent(self):
        old = simpledialog.askstring(tr("Агент"), tr("Какого агента заменить (например v1):"), parent=self)
        if not old:
            return
        new = simpledialog.askstring(tr("Агент"), tr("Заменить {old} на:").format(old=old), parent=self)
        if not new:
            return
        self.push_undo()
        for L in self.lines:
            if L.agent == old:
                L.agent = new
        self.ensure_agent(new)
        self.after_change(False)

    # ------------------------------------------------------------ поиск
    def cmd_find(self):
        if self.find_dlg and self.find_dlg.winfo_exists():
            self.find_dlg.lift()
            return
        d = tk.Toplevel(self)
        self.find_dlg = d
        d.title(tr("Найти / заменить"))
        d.transient(self)
        fv, rv = tk.StringVar(), tk.StringVar()
        ttk.Label(d, text=tr("Найти")).grid(row=0, column=0, padx=6, pady=4, sticky="w")
        ttk.Entry(d, textvariable=fv, width=28).grid(row=0, column=1, padx=6)
        ttk.Label(d, text=tr("Заменить на")).grid(row=1, column=0, padx=6, pady=4, sticky="w")
        ttk.Entry(d, textvariable=rv, width=28).grid(row=1, column=1, padx=6)
        bf = ttk.Frame(d)
        bf.grid(row=2, column=0, columnspan=2, pady=6)
        ttk.Button(bf, text=tr("Далее"), command=lambda: self.find_next(fv.get())).pack(side="left", padx=3)
        ttk.Button(bf, text=tr("Заменить"), command=lambda: self.replace_one(fv.get(), rv.get())).pack(side="left", padx=3)
        ttk.Button(bf, text=tr("Заменить все"), command=lambda: self.replace_all(fv.get(), rv.get())).pack(side="left", padx=3)

    def find_next(self, needle):
        if not needle:
            return
        flat = [(li, wi) for li, L in enumerate(self.lines) for wi in range(len(L.words))]
        if not flat:
            return
        cur = (self.sel[0], self.sel[1] or 0) if self.sel else (0, -1)
        start = flat.index(cur) + 1 if cur in flat else 0
        for k in range(len(flat)):
            li, wi = flat[(start + k) % len(flat)]
            if needle.lower() in self.lines[li].words[wi].text.lower():
                self.select(li, wi)
                return
        messagebox.showinfo(tr("Поиск"), tr("Не найдено."), parent=self.find_dlg)

    def replace_one(self, needle, repl):
        w = self.cur_word()
        if w is None or not needle or needle.lower() not in w.text.lower():
            return self.find_next(needle)
        self.push_undo()
        w.text = re.sub(re.escape(needle), repl.replace("\\", "\\\\"), w.text, flags=re.I) or w.text
        self.after_change(False)
        self.find_next(needle)

    def replace_all(self, needle, repl):
        if not needle:
            return
        self.push_undo()
        n = 0
        for L in self.lines:
            for w in L.words:
                if needle.lower() in w.text.lower():
                    new = re.sub(re.escape(needle), repl.replace("\\", "\\\\"), w.text, flags=re.I)
                    if new:
                        w.text = new
                        n += 1
        if n == 0:
            self.undo_stack.pop()
        else:
            self.after_change(False)
        messagebox.showinfo(tr("Замена"), tr("Заменено слов: {n}").format(n=n), parent=self.find_dlg)

    # ------------------------------------------------------------ файлы
    def confirm_discard(self):
        if not self.dirty:
            return True
        r = messagebox.askyesnocancel(tr("Несохранённые изменения"), tr("Сохранить изменения?"))
        if r is None:
            return False
        if r:
            return self.cmd_save()
        return True

    def cmd_new(self):
        if not self.confirm_discard():
            return
        self.load_doc(Doc.new(), None)

    def cmd_open(self):
        if not self.confirm_discard():
            return
        p = filedialog.askopenfilename(filetypes=[("TTML", "*.ttml *.xml"), (tr("Все файлы"), "*.*")])
        if p:
            self.open_file(p)

    def open_file(self, p):
        try:
            doc = Doc.load(p)
        except Exception as ex:
            messagebox.showerror(tr("Ошибка"), tr("Не удалось открыть файл:\n{ex}").format(ex=ex))
            return
        self.load_doc(doc, p)

    def load_doc(self, doc, path):
        self.doc = doc
        self.path = path
        self.dirty = False
        self.undo_stack.clear()
        self.redo_stack.clear()
        self._bak_done = False
        self.sel = (0, 0) if doc.lines else None
        self.view_start = 0.0
        self.playhead = 0.0
        if self.playing:
            self.pause()
        self.rebuild(self.sel, reset_open=True)
        self.update_inspector()
        self.fit_line()
        self.update_title()

    def cmd_save(self):
        if not self.path:
            return self.cmd_save_as()
        return self._save_to(self.path)

    def cmd_save_as(self):
        p = filedialog.asksaveasfilename(defaultextension=".ttml",
                                         filetypes=[("TTML", "*.ttml"), ("XML", "*.xml")])
        if not p:
            return False
        return self._save_to(p)

    def _save_to(self, p):
        try:
            if os.path.exists(p) and not self._bak_done:
                shutil.copy2(p, p + ".bak")
                self._bak_done = True
            self.doc.save(p)
        except Exception as ex:
            messagebox.showerror(tr("Ошибка сохранения"), str(ex))
            return False
        self.path = p
        self.dirty = False
        self.update_title()
        return True

    def cmd_paste_text(self):
        if not self.confirm_discard():
            return
        txt = self.ask_text(tr("Текст песни"), tr("Вставьте текст (одна строка = одна строка песни; пустая строка = новая часть)."))
        if not txt or not txt.strip():
            return
        doc = Doc.new()
        t = 0.0
        for raw in txt.splitlines():
            if not raw.strip():
                t += 1.0
                continue
            words = make_words(raw.strip(), t, t + DEFAULT_WORD * len(raw.split()))
            words[-1].space = False
            doc.lines.append(Line(words=words, agent="v1"))
            t = words[-1].end + 0.3
        self.load_doc(doc, None)
        self.dirty = True
        self.update_title()

    def cmd_import_lrc(self):
        if not self.confirm_discard():
            return
        p = filedialog.askopenfilename(filetypes=[("LRC", "*.lrc"), (tr("Текст"), "*.txt"), (tr("Все файлы"), "*.*")])
        if not p:
            return
        try:
            with open(p, "r", encoding="utf-8-sig") as f:
                lines = parse_lrc(f.read())
        except Exception as ex:
            messagebox.showerror(tr("Ошибка"), str(ex))
            return
        if not lines:
            messagebox.showinfo("LRC", tr("В файле не найдено строк с таймкодами."))
            return
        doc = Doc.new()
        doc.lines = lines
        self.load_doc(doc, None)
        self.dirty = True
        self.update_title()

    def cmd_export_lrc(self):
        enh = messagebox.askyesno(tr("Экспорт LRC"), tr("Писать пословные метки (Enhanced LRC)?"))
        p = filedialog.asksaveasfilename(defaultextension=".lrc", filetypes=[("LRC", "*.lrc")])
        if not p:
            return
        with open(p, "w", encoding="utf-8") as f:
            f.write(to_lrc(self.doc, enh))

    def cmd_meta(self):
        init = "\n".join(f"{a[0]} {a[1]}" for a in self.doc.agents)
        txt = self.ask_text(tr("Метаданные"), tr("Язык (xml:lang) — первая строка, далее агенты «id тип» (v1 person, v2 person, v1000 other):"), f"{self.doc.lang}\n{init}", height=8)
        if txt is None:
            return
        rows = [r.strip() for r in txt.splitlines() if r.strip()]
        if not rows:
            return
        self.push_undo()
        self.doc.lang = rows[0]
        ag = []
        for r in rows[1:]:
            parts = r.split()
            ag.append([parts[0], parts[1] if len(parts) > 1 else "person"])
        if ag:
            self.doc.agents = ag
        self.after_change(False)

    def open_karaoke(self):
        if self.karaoke and self.karaoke.winfo_exists():
            self.karaoke.deiconify()
            self.karaoke.lift()
            self.karaoke.render(force=True)
            return
        self.karaoke = KaraokeWindow(self)

    def ask_text(self, title, prompt, initial="", height=18):
        dlg = tk.Toplevel(self)
        dlg.title(title)
        dlg.transient(self)
        ttk.Label(dlg, text=prompt, wraplength=560, justify="left").pack(anchor="w", padx=8, pady=(8, 2))
        txt = tk.Text(dlg, width=72, height=height, wrap="word", undo=True, bg=BG2, fg=FG, insertbackground=ACC,
                      selectbackground=ACC_D, relief="flat", highlightthickness=1, highlightbackground=BORDER,
                      highlightcolor=ACC)
        txt.pack(fill="both", expand=True, padx=8)
        txt.insert("1.0", initial)
        res = {"v": None}

        def ok():
            res["v"] = txt.get("1.0", "end-1c")
            dlg.destroy()

        bf = ttk.Frame(dlg)
        bf.pack(pady=8)
        ttk.Button(bf, text="OK", command=ok).pack(side="left", padx=4)
        ttk.Button(bf, text=tr("Отмена"), command=dlg.destroy).pack(side="left", padx=4)
        dlg.grab_set()
        txt.focus_set()
        self.wait_window(dlg)
        return res["v"]

    # ------------------------------------------------------------ аудио / воспроизведение
    def cmd_load_audio(self):
        if not HAVE_PYGAME:
            messagebox.showinfo(tr("Аудио"), tr("Для воспроизведения установите pygame:\n\n    pip install pygame\n\n"
                                "Без него плейхед работает как тихий таймер."))
            return
        p = filedialog.askopenfilename(filetypes=[(tr("Аудио"), "*.mp3 *.ogg *.wav *.flac"), (tr("Все файлы"), "*.*")])
        if not p:
            return
        if self.playing:
            self.pause()
        try:
            if not pygame.mixer.get_init():
                pygame.mixer.init(frequency=44100, size=-16, channels=2)
            pygame.mixer.music.load(p)
            try:
                self.audio_len = pygame.mixer.Sound(p).get_length()
            except Exception:
                self.audio_len = 0.0
        except Exception as ex:
            messagebox.showerror(tr("Аудио"), tr("Не удалось загрузить: {ex}").format(ex=ex))
            return
        self.audio_path, self.audio_ok = p, True
        self.audio_arr = None
        self.slow_cache.clear()
        self.lbl_audio.config(text=os.path.basename(p))
        self.redraw_timeline()

    # ---- скорость
    @staticmethod
    def _speed_label(s):
        return f"{s:g}×"

    def on_speed_selected(self, _e=None):
        try:
            self.set_speed(float(self.speed_var.get().replace("×", "").replace(",", ".")))
        except ValueError:
            pass

    def step_speed(self, d):
        i = min(range(len(SPEEDS)), key=lambda k: abs(SPEEDS[k] - self.speed))
        self.set_speed(SPEEDS[min(max(i + d, 0), len(SPEEDS) - 1)])

    def set_speed(self, s):
        s = min(max(float(s), 0.2), 2.0)
        was, stop_at = self.playing, self.stop_at
        pos = self.cur_pos()
        if was:
            self.pause()
        self.speed = s
        if self.audio_ok and abs(s - 1.0) > 1e-6 and not self._prepare_slow():
            self.speed = 1.0
        self.speed_var.set(self._speed_label(self.speed))
        self._loc_dirty = True
        if was:
            self.play(pos, stop_at)

    def _slow_key(self):
        return (round(self.speed, 3), bool(self.keep_pitch.get()))

    def _prepare_slow(self):
        """Готовит замедленную копию аудио (кэшируется). True — можно играть."""
        key = self._slow_key()
        if key in self.slow_cache:
            return True
        try:
            import numpy  # noqa: F401
        except ImportError:
            messagebox.showinfo(tr("Замедление"), tr("Для замедления аудио нужен numpy:\n\n    pip install numpy"))
            return False
        self.config(cursor="watch")
        self.lbl_audio.config(text=tr("готовлю {v}…").format(v=self._speed_label(self.speed)))
        self.update()
        ok = True
        try:
            if self.audio_arr is None:
                self.audio_arr = pygame.sndarray.array(pygame.mixer.Sound(self.audio_path))
            arr = time_stretch(self.audio_arr, self.speed, key[1])
            while len(self.slow_cache) >= 3:
                self.slow_cache.pop(next(iter(self.slow_cache)))
            self.slow_cache[key] = arr
        except Exception as ex:
            messagebox.showerror(tr("Замедление"), tr("Не удалось подготовить звук: {ex}").format(ex=ex))
            ok = False
        finally:
            self.config(cursor="")
            self.lbl_audio.config(text=os.path.basename(self.audio_path or ""))
        return ok

    # ---- воспроизведение
    def _slow_mode(self):
        return abs(self.speed - 1.0) > 1e-6

    def _stop_audio(self):
        if not self.audio_ok:
            return
        try:
            pygame.mixer.music.stop()
        except Exception:
            pass
        if self.snd_ch is not None:
            try:
                self.snd_ch.stop()
            except Exception:
                pass
        self.snd_ch = self.snd = None

    def _audio_busy(self):
        if not self._slow_mode():
            return pygame.mixer.music.get_busy()
        return self.snd_ch is not None and self.snd_ch.get_busy()

    def _start_audio(self, pos, stop_at):
        """Запускает звук с позиции pos (сек. песни). Возвращает фактическую позицию."""
        if not self._slow_mode():
            try:
                pygame.mixer.music.play(start=pos)
            except Exception:
                try:
                    pygame.mixer.music.play()
                    pos = 0.0
                except Exception:
                    pass
            return pos
        import numpy as np
        arr = self.slow_cache.get(self._slow_key())
        if arr is None:
            return pos
        freq = pygame.mixer.get_init()[0]
        i0 = int(pos / self.speed * freq)
        i1 = len(arr) if stop_at is None else min(len(arr), int((stop_at / self.speed + 1.0) * freq))
        if i0 < i1:
            self.snd = pygame.sndarray.make_sound(np.ascontiguousarray(arr[i0:i1]))
            self.snd_ch = self.snd.play()
        return pos

    def cur_pos(self):
        if not self.playing:
            return self.playhead
        if self.audio_ok and not self._slow_mode():
            p = pygame.mixer.music.get_pos()
            if p >= 0:
                return self.pos0 + p / 1000.0
        return self.pos0 + (time.perf_counter() - self.t0) * self.speed

    def toggle_play(self):
        self.pause() if self.playing else self.play()

    def play(self, start=None, stop_at=None):
        pos = self.playhead if start is None else max(0.0, start)
        self._stop_audio()
        self.stop_at = stop_at
        if self.audio_ok:
            if self._slow_mode() and not self._prepare_slow():
                self.speed = 1.0
                self.speed_var.set(self._speed_label(1.0))
            pos = self._start_audio(pos, stop_at)
        self.pos0, self.t0 = pos, time.perf_counter()
        self.playhead = pos
        self.playing = True
        self.btn_play.config(text=tr("⏸ Пауза"))

    def pause(self):
        pos = self.cur_pos()
        self._stop_audio()
        self.playing = False
        self.stop_at = None
        self.playhead = pos
        self.btn_play.config(text=tr("▶ Играть"))
        self.redraw_timeline()

    def seek(self, t):
        t = max(0.0, t)
        if self.playing:
            self.play(t, self.stop_at)
        else:
            self.playhead = t
        self.redraw_timeline()

    def play_word(self):
        w = self.cur_word()
        if w:
            self.play(w.begin - 0.4, w.end + 0.2)

    def play_line(self):
        if self.sel and self.sel[0] < len(self.lines):
            L = self.lines[self.sel[0]]
            self.play(L.begin - 0.4, L.end + 0.3)

    def tick(self):
        try:
            self._tick()
        finally:
            self.after(30, self.tick)

    def _tick(self):
        if self.playing:
            pos = self.cur_pos()
            self.playhead = pos
            if self.stop_at is not None and pos >= self.stop_at:
                self.pause()
            elif self.audio_ok and pos > self.pos0 + 0.3 and not self._audio_busy():
                self.pause()
            else:
                if self.follow.get() and not self.drag:
                    if pos > self.view_start + 0.88 * self.view_len or pos < self.view_start:
                        self.view_goal = None
                        self.view_start = max(0.0, pos - 0.12 * self.view_len)
                self.redraw_timeline()
        spd = f"   ×{self.speed:g}" if self._slow_mode() else ""
        self.lbl_pos.config(text=f"{fmt_time(self.playhead)}{spd}")
        if self.anim_on.get() and self.playing:
            self.lbl_pos.config(foreground=blend(ACC, "#ffffff", 0.5 + 0.5 * math.sin(time.perf_counter() * 6)))
        elif self._anim_n % 5 == 0:
            self.lbl_pos.config(foreground=ACC)
        if self.playing or self._loc_dirty or abs(self.playhead - self._last_t) > 1e-6:
            self._last_t = self.playhead
            self._loc_dirty = False
            cur, word = self.locate(self.playhead)
            self.update_now(cur, word)
            if self.karaoke:
                self.karaoke.render()

    def locate(self, t):
        """(индекс текущей строки, индекс текущего слова или None) для момента t."""
        cur, best = None, -1.0
        for li, L in enumerate(self.lines):
            if L.words:
                b = L.begin
                if b <= t and b >= best:
                    cur, best = li, b
        if cur is None:
            return None, None
        word = None
        ws = self.lines[cur].words
        for wi, w in enumerate(ws):
            if w.begin <= t < w.end and (word is None or (ws[word].bg and not w.bg)):
                word = wi
        return cur, word

    def update_now(self, cur, word):
        t = self.tree
        new = f"L{cur}W{word}" if cur is not None and word is not None else None
        if new != self.now_iid:
            for iid, add in ((self.now_iid, False), (new, True)):
                if iid and t.exists(iid):
                    tg = t.item(iid, "tags")
                    tg = list(tg) if isinstance(tg, (list, tuple)) else str(tg).split()
                    tg = [x for x in tg if x != "now"]
                    t.item(iid, tags=tuple((["now"] if add else []) + tg))
            self.now_iid = new
            if new and self.playing and self.follow_tree.get() and t.exists(new):
                par = f"L{cur}"
                t.see(new if t.item(par, "open") else par)
        if cur is None:
            self.lbl_now.config(text="")
        else:
            L = self.lines[cur]
            txt = tr("Строка {n}").format(n=cur + 1)
            if word is not None:
                txt += tr(" · слово «{w}» {i}/{n}").format(w=L.words[word].text, i=word + 1, n=len(L.words))
            self.lbl_now.config(text=txt)

    # ------------------------------------------------------------ Tap
    def tap_time(self):
        try:
            lat = self.latency.get()
        except tk.TclError:
            lat = 0
        return max(0.0, self.cur_pos() - lat / 1000.0 * self.speed)

    def _next_word(self, li, wi):
        if wi + 1 < len(self.lines[li].words):
            return li, wi + 1
        if li + 1 < len(self.lines):
            return li + 1, 0
        return None

    def tap_begin(self):
        if not self.sel or not self.lines:
            return
        li, wi = self.sel
        wi = 0 if wi is None else wi
        L = self.lines[li]
        if not L.words:
            return
        t = self.tap_time()
        self.push_undo()
        w = L.words[wi]
        dur = max(w.end - w.begin, MIN_DUR)
        w.begin, w.end = t, t + dur
        if self.chain.get() and wi > 0:
            p = L.words[wi - 1]
            if p.bg == w.bg and t > p.begin:
                p.end = t
        nxt = self._next_word(li, wi)
        self.dirty = True
        self.refresh_rows()
        if nxt:
            self.select(nxt[0], nxt[1], scroll=False)
        else:
            self.select(li, wi, scroll=False)
        self.update_title()

    def tap_end(self):
        w = self.cur_word()
        if w is None:
            return
        t = self.tap_time()
        if t <= w.begin:
            self.bell()
            return
        self.push_undo()
        w.end = t
        self.after_change(False)

    # ------------------------------------------------------------ таймлайн
    def total_len(self):
        end = max((l.end for l in self.lines), default=0.0)
        return max(end, self.audio_len, self.view_start + self.view_len, 20.0) + 5.0

    def x2t(self, x):
        return self.view_start + x / max(1, self.canvas.winfo_width()) * self.view_len

    def _view_base(self):
        return self.view_goal or (self.view_start, self.view_len)

    def set_view(self, start=None, length=None, animate=True):
        gs, gl = self._view_base()
        if length is not None:
            gl = min(max(length, 0.5), 240.0)
        if start is not None:
            gs = max(0.0, start)
        if animate and self.anim_on.get():
            self.view_goal = (gs, gl)
        else:
            self.view_goal = None
            self.view_start, self.view_len = gs, gl
            self.redraw_timeline()

    def zoom(self, factor, anchor_t=None, anchor_x=None):
        W = max(1, self.canvas.winfo_width())
        bs, bl = self._view_base()
        if anchor_t is None:
            anchor_t, anchor_x = bs + bl / 2, W / 2
        nl = min(max(bl * factor, 0.5), 240.0)
        self.set_view(anchor_t - anchor_x / W * nl, nl)

    def fit_line(self):
        if self.sel and self.sel[0] < len(self.lines):
            L = self.lines[self.sel[0]]
            span = max(L.end - L.begin, 1.0)
            vl = min(max(span * 1.4, 2.0), 240.0)
            self.set_view(L.begin - (vl - span) / 2, vl)
        else:
            self.set_view(0.0, 12.0)

    def ensure_visible(self):
        if self.drag or (self.playing and self.follow.get()) or not self.sel:
            return
        li, wi = self.sel
        if li >= len(self.lines):
            return
        L = self.lines[li]
        w = L.words[wi] if wi is not None and wi < len(L.words) else None
        t0, t1 = (w.begin, w.end) if w else (L.begin, L.end)
        bs, bl = self._view_base()
        nl = bl
        if t1 - t0 > bl * 0.9:
            nl = min((t1 - t0) * 1.2, 240.0)
        if t0 < bs or t1 > bs + nl or nl != bl:
            self.set_view(t0 - 0.15 * nl, nl)

    def on_hbar(self, *a):
        total = self.total_len()
        self.view_goal = None
        if a[0] == "moveto":
            self.view_start = max(0.0, float(a[1]) * total)
        elif a[0] == "scroll":
            n = int(a[1])
            self.view_start = max(0.0, self.view_start + n * self.view_len * (0.1 if a[2] == "units" else 0.9))
        self.redraw_timeline()

    def on_wheel(self, e):
        d = 1 if (e.num == 4 or getattr(e, "delta", 0) > 0) else -1
        if e.state & 0x4:
            self.zoom(0.8 if d > 0 else 1.25, self.x2t(e.x), e.x)
        else:
            bs, bl = self._view_base()
            self.set_view(bs - d * bl * 0.1)
        return "break"

    # ------------------------------------------------------------ анимация
    def anim_tick(self):
        try:
            self._anim()
        finally:
            self.after(40, self.anim_tick)

    def _anim(self):
        self._anim_n += 1
        moved = False
        g = self.view_goal
        if g:
            gs, gl = g
            self.view_start += (gs - self.view_start) * 0.35
            self.view_len += (gl - self.view_len) * 0.35
            if abs(gs - self.view_start) < 0.002 * gl and abs(gl - self.view_len) < 0.002 * gl:
                self.view_start, self.view_len = gs, gl
                self.view_goal = None
            moved = True
        if self.playing:
            return          # во время игры всё перерисовывает tick()
        if moved or (self.anim_on.get() and self._anim_n % 2 == 0):
            self.redraw_timeline()
        if self.karaoke and self.anim_on.get() and self._anim_n % 2 == 0:
            self.karaoke.render(force=True)

    def redraw_timeline(self):
        c = self.canvas
        c.delete("all")
        W, H = c.winfo_width(), c.winfo_height()
        if W < 20:
            return
        vs, vl = self.view_start, self.view_len
        pps = W / vl
        anim = self.anim_on.get()
        tnow = time.perf_counter()
        pulse = 0.5 + 0.5 * math.sin(tnow * 5.0) if anim else 0.6
        self.stars_tl.draw(c, W, H, tnow, vs * 40.0, anim, self.tl_fx)
        # линейка
        step = 60.0
        for s_ in (0.05, 0.1, 0.25, 0.5, 1, 2, 5, 10, 15, 30, 60):
            if s_ * pps >= 70:
                step = s_
                break
        c.create_rectangle(0, 0, W, 26, fill=C_BG, outline="")
        c.create_line(0, 26, W, 26, fill=BORDER)
        t = math.ceil(vs / step) * step
        while t < vs + vl:
            x = (t - vs) * pps
            c.create_line(x, 16, x, H, fill=GRID)
            c.create_text(x + 3, 3, text=fmt_time(t), anchor="nw", font=("TkDefaultFont", 8), fill=FG_DIM)
            t += step
        # слова
        self.tl_items = []
        sel_line = self.sel[0] if self.sel else None
        sel_word = self.sel[1] if self.sel else None
        ph = self.playhead
        for li, L in enumerate(self.lines):
            if not L.words or L.end < vs or L.begin > vs + vl:
                continue
            for wi, w in enumerate(L.words):
                if w.end < vs or w.begin > vs + vl:
                    continue
                x0 = (w.begin - vs) * pps
                x1 = max(x0 + 3, (w.end - vs) * pps)
                y0, y1 = LANE_BG if w.bg else LANE_MAIN
                is_sel = (li == sel_line and wi == sel_word)
                is_hov = (li, wi) == self.hover
                sung_now = w.begin <= ph < w.end
                fill = C_WORD_NOW if sung_now else (C_WORD_SEL if is_sel else
                                                    (C_WORD_BG if w.bg else (C_WORD_LINE if li == sel_line else C_WORD)))
                if sung_now:
                    g = blend(BG0, GREEN, 0.25 + 0.25 * pulse)
                    rrect(c, x0 - 3, y0 - 3, x1 + 3, y1 + 3, WORD_R + 3, fill="", outline=g, width=2)
                if is_sel:
                    outline = blend(ACC, MAG, pulse)
                elif is_hov:
                    outline = HOVER_COL
                else:
                    outline = WORD_BORDER if not w.bg else WORD_BORDER_BG
                rrect(c, x0, y0, x1, y1, WORD_R, fill=fill, outline=outline, width=2 if (is_sel or is_hov) else 1)
                if GLOSS and x1 - x0 > 8:
                    inset = 2 + WORD_R * 0.35
                    rrect(c, x0 + inset, y0 + 2, x1 - inset, y0 + 6, 2, fill=blend(fill, "#ffffff", 0.14),
                          outline="")
                if sung_now and w.end > w.begin:
                    xp = x0 + (x1 - x0) * (ph - w.begin) / (w.end - w.begin)
                    c.create_rectangle(x0 + 2, y1 - 7, max(x0 + 2, xp - 1), y1 - 2, fill=GREEN, outline="")
                maxc = int((x1 - x0 - 6) / 7)
                if maxc >= 1:
                    label = w.text if len(w.text) <= maxc else w.text[:max(1, maxc - 1)] + "…"
                    c.create_text(x0 + 4, (y0 + y1) / 2, text=label, anchor="w",
                                  fill=WORD_TEXT_NOW if sung_now else (SEL_FG if is_sel else WORD_TEXT))
                if wi == 0:
                    c.create_text(x0, y0 - 2, text=str(li + 1), anchor="sw", font=("TkDefaultFont", 8), fill=FG_DIM)
                self.tl_items.append((x0, x1, w.bg, li, wi))
        if not self.lines:
            c.create_text(W / 2, H / 2, text=tr("Файл → Открыть TTML… или Вставить текст песни…"), fill=FG_DIM)
        # плейхед с неоновым свечением
        x = (ph - vs) * pps
        if 0 <= x <= W:
            k = 0.7 + 0.3 * pulse if self.playing else 0.7
            for wd, f in ((9, 0.10), (5, 0.26)):
                c.create_line(x, 26, x, H, fill=blend(BG0, C_PLAYHEAD, f * k), width=wd)
            c.create_line(x, 0, x, H, fill=C_PLAYHEAD, width=2)
            c.create_polygon(x - 6, 0, x + 6, 0, x, 10, fill=C_PLAYHEAD, outline="")
        total = self.total_len()
        self.hbar.set(min(vs / total, 1.0), min((vs + vl) / total, 1.0))
        self.redraw_mini()

    def hit(self, x, y):
        want_bg = y >= LANE_BG[0] - 6
        for x0, x1, bg, li, wi in reversed(self.tl_items):
            if bg != want_bg:
                continue
            if x0 - 3 <= x <= x1 + 3:
                edge = min(7.0, (x1 - x0) / 3)
                zone = "l" if x <= x0 + edge else ("r" if x >= x1 - edge else "m")
                return li, wi, zone
        return None

    def on_tl_press(self, e):
        self.canvas.focus_set()
        h = None if e.y < 26 else self.hit(e.x, e.y)
        if h is None:
            self.drag = None
            self.seek(self.x2t(e.x))
            return
        li, wi, zone = h
        self.select(li, wi, scroll=False)
        w = self.lines[li].words[wi]
        self.push_undo()
        W = max(1, self.canvas.winfo_width())
        vs, vl = self.view_start, self.view_len
        edges = []
        for i, L in enumerate(self.lines):
            if L.end < vs - vl or L.begin > vs + 2 * vl:
                continue
            for j, o in enumerate(L.words):
                if (i, j) != (li, wi):
                    edges += [o.begin, o.end]
        self.drag = dict(li=li, wi=wi, zone=zone, x0=e.x, b=w.begin, e=w.end, moved=False, edges=edges)

    def _snap(self, t, thr, edges):
        best, bd = t, thr
        for ed in edges:
            d = abs(ed - t)
            if d <= bd:
                best, bd = ed, d
        return best

    def on_tl_motion(self, e):
        d = self.drag
        if not d:
            return
        W = max(1, self.canvas.winfo_width())
        dt = (e.x - d["x0"]) / W * self.view_len
        if abs(e.x - d["x0"]) < 2 and not d["moved"]:
            return
        w = self.lines[d["li"]].words[d["wi"]]
        snap = self.snap.get() and not (e.state & 0x1)
        thr = 8 / W * self.view_len
        b, en = d["b"], d["e"]
        if d["zone"] == "m":
            nb, ne = b + dt, en + dt
            if snap:
                sb = self._snap(nb, thr, d["edges"])
                se = self._snap(ne, thr, d["edges"])
                if sb != nb:
                    ne += sb - nb
                    nb = sb
                elif se != ne:
                    nb += se - ne
                    ne = se
            if nb < 0:
                ne -= nb
                nb = 0.0
        elif d["zone"] == "l":
            nb = b + dt
            if snap:
                nb = self._snap(nb, thr, d["edges"])
            nb = min(max(nb, 0.0), en - MIN_DUR)
            ne = en
        else:
            ne = en + dt
            if snap:
                ne = self._snap(ne, thr, d["edges"])
            ne = max(ne, b + MIN_DUR)
            nb = b
        w.begin, w.end = nb, ne
        d["moved"] = True
        self.mini_dirty = True
        self.refresh_word_row(d["li"], d["wi"])
        self.v_wbegin.set(fmt_time(nb))
        self.v_wend.set(fmt_time(ne))
        self.redraw_timeline()

    def on_tl_release(self, _e):
        d, self.drag = self.drag, None
        if not d:
            return
        if not d["moved"]:
            if self.undo_stack:
                self.undo_stack.pop()
            return
        self.dirty = True
        self.update_title()
        self.update_status()

    def on_tl_hover(self, e):
        if self.drag:
            return
        h = None if e.y < 26 else self.hit(e.x, e.y)
        self.canvas.config(cursor=("arrow" if not h else ("fleur" if h[2] == "m" else "sb_h_double_arrow")))
        new = (h[0], h[1]) if h else None
        if new == self.hover:
            return
        self.hover = new
        if new:
            w = self.lines[new[0]].words[new[1]]
            self.lbl_hint.config(text=tr("«{w}»  {b} → {e}  ({ms} мс)  ·  строка {n}").format(
                w=w.text, b=fmt_time(w.begin), e=fmt_time(w.end), ms=int(round((w.end - w.begin) * 1000)), n=new[0] + 1))
        else:
            self.lbl_hint.config(text="")
        if not self.playing:
            self.redraw_timeline()

    def on_tl_leave(self, _e):
        if self.hover is not None and not self.drag:
            self.hover = None
            self.lbl_hint.config(text="")
            if not self.playing:
                self.redraw_timeline()

    # ---- мини-карта всей песни
    def on_mini(self, e):
        W = max(1, self.mini.winfo_width())
        t = e.x / W * self.total_len()
        self.set_view(t - self.view_len / 2, animate=False)

    def redraw_mini(self):
        m = self.mini
        W, H = m.winfo_width(), m.winfo_height()
        if W < 20:
            return
        total = self.total_len()
        if self.mini_dirty or W != self._mini_w or abs(total - self._mini_total) > 1e-6:
            m.delete("all")
            for L in self.lines:
                for w in L.words:
                    x0 = w.begin / total * W
                    x1 = max(x0 + 1, w.end / total * W)
                    y0, y1 = (21, 31) if w.bg else (6, 18)
                    m.create_rectangle(x0, y0, x1, y1, fill=MINI_B if w.bg else MINI_A, outline="")
            self.mini_view = m.create_rectangle(0, 0, 0, 0, outline=ACC, width=2)
            self.mini_ph = m.create_line(0, 0, 0, H, fill=C_PLAYHEAD, width=2)
            self.mini_dirty = False
            self._mini_w, self._mini_total = W, total
        vs, vl = self.view_start, self.view_len
        m.coords(self.mini_view, vs / total * W, 1, min((vs + vl) / total, 1.0) * W, H - 1)
        px = self.playhead / total * W
        m.coords(self.mini_ph, px, 0, px, H)

    def on_tl_double(self, e):
        h = self.hit(e.x, e.y) if e.y >= 26 else None
        if h:
            self.select(h[0], h[1], scroll=False)
            self.play_word()

    # ------------------------------------------------------------ выход
    def on_close(self):
        if not self.confirm_discard():
            return
        self.save_settings()
        if self.karaoke:
            self.karaoke.close()
        if self.audio_ok:
            try:
                pygame.mixer.quit()
            except Exception:
                pass
        self.destroy()


class KaraokeWindow(tk.Toplevel):
    """Караоке-окно: предыдущая / текущая / следующая строки, допетые буквы подсвечены,
    поющаяся буква светится, над ней прыгает шарик. Цвета и шрифт берутся из темы (раздел karaoke)."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title(tr("Караоке-просмотр — что поётся сейчас"))
        self.geometry("1000x470")
        self.minsize(420, 240)
        self.fsize = int(app.theme.num("karaoke", "font-size", 44) or 44)
        self._key = None
        self._cur_line = None
        self._line_t0 = 0.0
        self._last_draw = 0.0
        self.stars = Starfield(n=150, seed=21)
        self.bar = tk.Frame(self)
        self.bar.pack(fill="x")
        self.btns = []
        for text, d in (("A−", -4), ("A+", 4)):
            b = tk.Button(self.bar, text=text, width=3, takefocus=0, relief="flat", bd=0,
                          command=lambda d=d: self.resize(d))
            b.pack(side="left", padx=3, pady=3)
            self.btns.append(b)
        self.top = tk.BooleanVar(value=False)
        self.chk = tk.Checkbutton(self.bar, text=tr("Поверх всех окон"), variable=self.top, takefocus=0,
                                  command=lambda: self.attributes("-topmost", self.top.get()))
        self.chk.pack(side="left", padx=8)
        self.info = tk.Label(self.bar, text="", anchor="e")
        self.info.pack(side="right", padx=10)
        self.cv = tk.Canvas(self, highlightthickness=0)
        self.cv.pack(fill="both", expand=True)
        self.cv.bind("<Configure>", lambda e: self.render(force=True))
        self.bind("<space>", lambda e: self.app.toggle_play())
        self.bind("<F7>", lambda e: self.app.step_speed(-1))
        self.bind("<F8>", lambda e: self.app.step_speed(1))
        self.bind("<Left>", lambda e: self.app.seek(self.app.cur_pos() - 1.0))
        self.bind("<Right>", lambda e: self.app.seek(self.app.cur_pos() + 1.0))
        self.bind("<Escape>", lambda e: self.close())
        self.bind("<MouseWheel>", lambda e: self.resize(2 if e.delta > 0 else -2))
        self.bind("<Button-4>", lambda e: self.resize(2))
        self.bind("<Button-5>", lambda e: self.resize(-2))
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.retheme()
        self.render(force=True)

    def retheme(self):
        T = self.app.theme
        self.configure(bg=BG0)
        self.bar.config(bg=BG2)
        for b in self.btns:
            b.config(bg=BG1, fg=FG, activebackground=ACC_D, activeforeground=SEL_FG)
        self.chk.config(bg=BG2, fg=FG, activebackground=BG2, activeforeground=ACC, selectcolor=BG0)
        self.info.config(bg=BG2, fg=FG_DIM)
        self.cv.config(bg=BG0)
        self.C_FUTURE = T.col("karaoke", "color-future", FG, BG0)
        self.C_SUNG = T.col("karaoke", "color-sung", GOLD, BG0)
        self.C_CUR = T.col("karaoke", "color-current", "#ff6b9d", BG0)
        self.C_DIM = T.col("karaoke", "color-dim", blend(BG0, FG_DIM, 0.45), BG0)
        self.C_BG_FUT = T.col("karaoke", "color-bg-future", MAG, BG0)
        self.C_BG_SUNG = T.col("karaoke", "color-bg-sung", blend(MAG, "#ffffff", 0.5), BG0)
        fam = T.raw("karaoke", "font-family", "").strip("\"' ")
        self.family = fam or tkfont.nametofont("TkDefaultFont").actual("family")
        self.fx = self.app.kara_fx
        self.make_fonts()

    def close(self):
        self.app.karaoke = None
        try:
            self.destroy()
        except tk.TclError:
            pass

    def make_fonts(self):
        self.f_big = tkfont.Font(family=self.family, size=self.fsize, weight="bold")
        self.f_small = tkfont.Font(family=self.family, size=max(10, int(self.fsize * 0.5)))

    def resize(self, d):
        self.fsize = max(14, min(150, self.fsize + d))
        self.make_fonts()
        self.render(force=True)

    @staticmethod
    def layout(L, font, maxw):
        """Разбивает слова на строки по ширине. -> [(ширина_строки, [(wi, слово, x, ширина)])]"""
        sp = font.measure(" ")
        rows, items, x, x_end = [], [], 0, 0
        for wi, w in enumerate(L.words):
            wpx = font.measure(w.text)
            if items and x + wpx > maxw:
                rows.append((x_end, items))
                items, x = [], 0
            items.append((wi, w, x, wpx))
            x_end = x + wpx
            x += wpx + (sp if w.space else 0)
        if items:
            rows.append((x_end, items))
        return rows

    def draw_rows(self, rows, y, font, W, mode, t, now, anim):
        """mode: 'dim' — приглушённая строка, 'cur' — текущая. Возвращает (высота, инфо о букве)."""
        c = self.cv
        lh = int(font.metrics("linespace") * 1.15)
        info = None
        pulse = 0.5 + 0.5 * math.sin(now * 9.0) if anim else 0.5
        for r, (rw, items) in enumerate(rows):
            x0 = (W - rw) / 2
            yy = y + r * lh
            for wi, w, xo, wpx in items:
                x = x0 + xo
                if mode == "dim":
                    c.create_text(x, yy, text=w.text, anchor="nw", font=font, fill=self.C_DIM)
                    continue
                fut = self.C_BG_FUT if w.bg else self.C_FUTURE
                sung = self.C_BG_SUNG if w.bg else self.C_SUNG
                if t >= w.end:
                    c.create_text(x, yy, text=w.text, anchor="nw", font=font, fill=sung)
                elif t >= w.begin:
                    frac = (t - w.begin) / max(w.end - w.begin, 1e-6)
                    n = min(int(frac * len(w.text)), len(w.text) - 1)
                    pre, ch, post = w.text[:n], w.text[n], w.text[n + 1:]
                    x1 = x + font.measure(pre)
                    x2 = x1 + font.measure(ch)
                    if pre:
                        c.create_text(x, yy, text=pre, anchor="nw", font=font, fill=sung)
                    glow = blend(BG0, self.C_CUR, 0.45)
                    for dx, dy in ((-2, 0), (2, 0), (0, -2), (0, 2)):
                        c.create_text(x1 + dx, yy + dy, text=ch, anchor="nw", font=font, fill=glow)
                    c.create_text(x1, yy, text=ch, anchor="nw", font=font,
                                  fill=blend(self.C_CUR, "#ffffff", 0.35 * pulse))
                    c.create_rectangle(x1, yy + lh - 6, x2, yy + lh - 2, fill=self.C_CUR, outline="")
                    if post:
                        c.create_text(x2, yy, text=post, anchor="nw", font=font, fill=fut)
                    arc = 4 * frac * (1 - frac)
                    bx, by = (x1 + x2) / 2, yy - 8 - 22 * arc
                    c.create_oval(bx - 10, by - 10, bx + 10, by + 10, fill=blend(BG0, ACC, 0.30), outline="")
                    c.create_oval(bx - 5, by - 5, bx + 5, by + 5, fill=ACC, outline="")
                    info = (wi, w.text, n, ch)
                else:
                    c.create_text(x, yy, text=w.text, anchor="nw", font=font, fill=fut)
        return len(rows) * lh, info

    def render(self, force=False):
        app = self.app
        try:
            if not self.winfo_exists():
                return
        except tk.TclError:
            return
        now = time.perf_counter()
        anim = app.anim_on.get()
        t = app.playhead
        cur, wi = app.locate(t)
        key = (cur, wi, int(t * 40))
        if not force:
            if now - self._last_draw < 0.025:
                return
            if key == self._key and not anim:
                return
        self._key = key
        self._last_draw = now
        c = self.cv
        c.delete("all")
        W, H = c.winfo_width(), c.winfo_height()
        if W < 60 or H < 60:
            return
        self.stars.draw(c, W, H, now, t * 25.0, anim, self.fx)
        lines = app.lines
        spd = tr("   ·   скорость ×{s:g}").format(s=app.speed) if app._slow_mode() else ""
        if not lines:
            c.create_text(W / 2, H / 2, text=tr("Нет строк"), fill=self.C_DIM, font=self.f_small)
            self.info.config(text=f"{fmt_time(t)}{spd}")
            return
        maxw = max(100, W - 80)
        gap = 18
        if cur is None:                      # песня ещё не началась
            rows = self.layout(lines[0], self.f_small, maxw)
            self.draw_rows(rows, H / 2 - 20, self.f_small, W, "dim", t, now, anim)
            c.create_text(W / 2, H / 2 - 50, text="✦  ♪  ✦", fill=blend(BG0, ACC, 0.5 + 0.4 * math.sin(now * 3)),
                          font=self.f_small)
            self.info.config(text=fmt_time(t) + tr("   ·   до начала: {v}").format(v=fmt_time(lines[0].begin - t)) + spd)
            return
        if cur != self._cur_line:            # новая строка «выплывает» снизу
            self._cur_line = cur
            self._line_t0 = now
        e = min(1.0, (now - self._line_t0) / 0.30) if anim else 1.0
        off = (1 - e) ** 3 * 28
        L = lines[cur]
        rows = self.layout(L, self.f_big, maxw)
        lh_big = int(self.f_big.metrics("linespace") * 1.15)
        total_h = len(rows) * lh_big
        y0 = max(4, (H - total_h) / 2) + off
        ended = t > L.end + 2.5
        if cur > 0:
            prow = self.layout(lines[cur - 1], self.f_small, maxw)
            ph = len(prow) * int(self.f_small.metrics("linespace") * 1.15)
            self.draw_rows(prow, max(2, y0 - gap - ph), self.f_small, W, "dim", t, now, anim)
        _, inf = self.draw_rows(rows, y0, self.f_big, W, "cur", t, now, anim)
        if cur + 1 < len(lines):
            nrow = self.layout(lines[cur + 1], self.f_small, maxw)
            self.draw_rows(nrow, y0 + total_h + gap, self.f_small, W, "dim", t, now, anim)
        if L.end > L.begin:
            frac = min(max((t - L.begin) / (L.end - L.begin), 0.0), 1.0)
            c.create_rectangle(0, H - 5, W, H, fill=blend(BG0, BORDER, 0.6), outline="")
            c.create_rectangle(0, H - 5, W * frac, H, fill=self.C_SUNG, outline="")
            hx = W * frac
            c.create_oval(hx - 8, H - 10, hx + 8, H + 4, fill=blend(BG0, self.C_SUNG, 0.4), outline="")
        if inf:
            iw, wtxt, n, ch = inf
            txt = tr("строка {c}/{t}  ·  слово «{w}» {i}/{k}  ·  буква «{ch}» {n}/{m}").format(
                c=cur + 1, t=len(lines), w=wtxt, i=iw + 1, k=len(L.words), ch=ch, n=n + 1, m=len(wtxt))
        elif ended:
            txt = tr("строка {c}/{t}  ·  пауза").format(c=cur + 1, t=len(lines))
        else:
            txt = tr("строка {c}/{t}").format(c=cur + 1, t=len(lines))
        self.info.config(text=f"{txt}   ·   {fmt_time(t)}{spd}")


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description="TTML Word Editor — word-level editor for Apple Music / Spicy Lyrics TTML")
    ap.add_argument("file", nargs="?", help="TTML file to open")
    ap.add_argument("--lang", help="UI language: auto, ru, en, or the code of a pack from the lang folder")
    ap.add_argument("--theme", choices=THEME_MODES[:-1], help="built-in theme for this session")
    ap.add_argument("--css", help="path to a custom CSS theme for this session")
    ap.add_argument("--no-effects", action="store_true", help="disable glass / blur / rounded menu effects")
    ap.add_argument("--reset-settings", action="store_true", help="delete saved settings and start fresh")
    ap.add_argument("--version", action="version", version="TTML Word Editor " + VERSION)
    a = ap.parse_args(argv)
    if a.reset_settings:
        try:
            os.remove(settings_path())
        except OSError:
            pass
    path = a.file if a.file and os.path.exists(a.file) else None
    if a.file and not path:
        print(f"File not found: {a.file}", file=sys.stderr)
    App(path, {"lang": a.lang, "theme": a.theme, "css": a.css, "no_effects": a.no_effects}).mainloop()


if __name__ == "__main__":
    main()
