import os
import sys
import re
import json
import queue
import threading
import time
import tempfile
import winsound
import math
import base64
import requests
import uuid
import random
import wave
import struct
import asyncio
import edge_tts
import pygame
import io
import pyttsx3
import pythoncom
import concurrent.futures
import subprocess
import webbrowser
import pyautogui
from datetime import datetime
from ddgs import DDGS
from PIL import Image
import speech_recognition as sr
from faster_whisper import WhisperModel

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QLabel, 
    QPushButton, QHBoxLayout, QScrollArea, QGraphicsOpacityEffect,
    QSizePolicy, QFileDialog, QComboBox, QTextEdit, QListWidget, QListWidgetItem, 
    QFrame, QStackedLayout, QMenu, QDialog, QCheckBox, QToolButton, QTextBrowser, 
    QStyledItemDelegate, QAbstractItemView
)
from PyQt6.QtCore import (
    QTimer, pyqtSignal, Qt, QPropertyAnimation, QRect, QRectF, 
    QEasingCurve, QPoint, QVariantAnimation, QObject, pyqtProperty  # <--- ДОБАВЛЕНО СЮДА
)
from PyQt6.QtGui import (
    QFont, QFontDatabase, QPainter, QColor, QPen, QFontMetrics, QTextOption, 
    QPixmap, QKeySequence, QIcon
)

# Настройка кэша для Torch
os.environ["TORCH_HOME"] = r"C:\torch_cache"

def get_base_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

def get_resource_path(relative_path):
    external_path = os.path.join(get_base_dir(), relative_path)
    if os.path.exists(external_path):
        return external_path
    if hasattr(sys, "_MEIPASS"):
        return os.path.join(sys._MEIPASS, relative_path)
    return external_path

# --- ИНИЦИАЛИЗАЦИЯ МИКШЕРА ---
pygame.mixer.pre_init(44100, -16, 2, 512)
pygame.init()
pygame.mixer.init()
pygame.mixer.set_num_channels(32)

# ---------- БЕЗОПАСНЫЙ СПИСОК С ПЛАВНЫМ СЛАЙДЕРОМ ----------
class SlidingListWidget(QListWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._highlight_y = 0
        self.text_color = "#e0e0e0"
        self.select_color = "#2a2a2a"
        self.anim = QVariantAnimation(self)
        self.anim.setDuration(200)
        self.anim.setEasingCurve(QEasingCurve.Type.InOutQuad)
        self.anim.valueChanged.connect(self._update_highlight)
        self.currentRowChanged.connect(self._on_row_changed)
        self.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.setStyleSheet("QListWidget { background: transparent; border: none; outline: none; }")
        self.setItemDelegate(SlidingDelegate(self))

    def update_colors(self, text, select):
        self.text_color = text
        self.select_color = select
        self.viewport().update()

    def _on_row_changed(self, row):
        try:
            if row < 0 or row >= self.count():
                return
            item = self.item(row)
            if not item:
                return
            target_rect = self.visualItemRect(item)
            if target_rect.isValid():
                self.anim.stop()
                self.anim.setStartValue(self._highlight_y)
                self.anim.setEndValue(target_rect.y())
                self.anim.start()
        except RuntimeError:
            pass

    def _update_highlight(self, val):
        self._highlight_y = val
        self.viewport().update()

    def paintEvent(self, event):
        painter = QPainter(self.viewport())
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        try:
            if 0 <= self.currentRow() < self.count():
                item = self.item(self.currentRow())
                if item:
                    rect = self.visualItemRect(item)
                    if rect.isValid():
                        rect.setY(int(self._highlight_y))
                        painter.setBrush(QColor(self.select_color))
                        painter.setPen(Qt.PenStyle.NoPen)
                        painter.drawRoundedRect(rect.adjusted(4, 2, -4, -2), 10, 10)
        except RuntimeError:
            pass
        super().paintEvent(event)

    def set_highlight_instantly(self, row):
        try:
            if 0 <= row < self.count():
                item = self.item(row)
                if item:
                    self._highlight_y = self.visualItemRect(item).y()
                    self.viewport().update()
        except RuntimeError:
            pass

class SlidingDelegate(QStyledItemDelegate):
    def __init__(self, list_widget):
        super().__init__(list_widget)
        self.lw = list_widget

    def paint(self, painter, option, index):
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        text = index.data(Qt.ItemDataRole.DisplayRole)
        painter.setPen(QColor(self.lw.text_color))
        painter.setFont(QFont("Onest", 10))
        painter.drawText(
            option.rect.adjusted(14, 0, -10, 0),
            Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
            text
        )
        painter.restore()

class AutoResizingTextBrowser(QTextBrowser):
    def __init__(self, max_width=520):
        super().__init__()
        self.max_bubble_width = max_width
        self.setOpenExternalLinks(True)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        self.document().documentLayout().documentSizeChanged.connect(self.adjust_size)
        self.document().setDocumentMargin(0)
        opt = self.document().defaultTextOption()
        opt.setWrapMode(QTextOption.WrapMode.WrapAtWordBoundaryOrAnywhere)
        self.setAlignment(Qt.AlignmentFlag.AlignLeft)
        self.document().setDefaultTextOption(opt)

    def adjust_size(self):
        if getattr(self, "_is_adjusting", False):
            return
        self._is_adjusting = True
        try:
            doc = self.document()
            doc.setTextWidth(-1)
            ideal_w = doc.idealWidth()
            target_w = min(max(int(math.ceil(ideal_w)) + 6, 24), self.max_bubble_width)
            doc.setTextWidth(target_w)
            target_h = int(math.ceil(doc.size().height())) + 2
            self.setFixedSize(target_w, max(target_h, 22))
        finally:
            self._is_adjusting = False

class EmittingStream(QObject):
    textWritten = pyqtSignal(str)

    def write(self, text):
        try:
            if sys.__stderr__:
                sys.__stderr__.write(text)
                sys.__stderr__.flush()
            self.textWritten.emit(str(text))
        except Exception:
            pass

    def flush(self):
        try:
            sys.__stdout__.flush()
        except Exception:
            pass

def generate_timer_sound():
    sounds_dir = get_resource_path("sounds")
    os.makedirs(sounds_dir, exist_ok=True)
    file_path = os.path.join(sounds_dir, "jerry_timer_sound.wav")
    if not os.path.exists(file_path):
        print(f"Создаю звук таймера: {file_path}")
        sample_rate = 44100
        duration = 1.0
        freq1, freq2 = 880.0, 1108.73
        with wave.open(file_path, "w") as f:
            f.setnchannels(1)
            f.setsampwidth(2)
            f.setframerate(sample_rate)
            for i in range(int(sample_rate * duration)):
                t = i / sample_rate
                env = math.exp(-3.0 * t)
                val = int(32767 * env * 0.4 * (math.sin(2 * math.pi * freq1 * t) + math.sin(2 * math.pi * freq2 * t)))
                f.writeframes(struct.pack("<h", val))
    return file_path

class TimerPopup(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowFlags(Qt.WindowType.WindowStaysOnTopHint | Qt.WindowType.FramelessWindowHint | Qt.WindowType.Dialog)
        self.setFixedSize(300, 150)
        self.setStyleSheet("""
            QDialog {
                background-color: #111111;
                border-radius: 15px;
                border: 2px solid #333333;
            }
        """)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 20, 20, 20)
        label = QLabel("Время вышло!")
        label.setFont(QFont("Onest", 16, QFont.Weight.Bold))
        label.setStyleSheet("color: #ffffff; border: none; background: transparent;")
        label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(label)
        layout.addSpacing(10)
        self.btn = QPushButton("Остановить")
        self.btn.setFixedHeight(40)
        self.btn.setFont(QFont("Onest", 12, QFont.Weight.Bold))
        self.btn.setStyleSheet("""
            QPushButton {
                background-color: #333333;
                color: #ffffff;
                border-radius: 10px;
                border: none;
            }
            QPushButton:hover { background-color: #444444; }
        """)
        self.btn.clicked.connect(self.stop_sound)
        layout.addWidget(self.btn)

    def stop_sound(self):
        winsound.PlaySound(None, winsound.SND_PURGE)
        self.accept()

CHATS_FILE = os.path.join(get_base_dir(), "chats.json")

def load_chats():
    if os.path.exists(CHATS_FILE):
        try:
            with open(CHATS_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def save_chats(chats):
    with open(CHATS_FILE, "w", encoding="utf-8") as f:
        json.dump(chats, f, ensure_ascii=False, indent=2)

class TTSWorker(threading.Thread):
    def __init__(self, base_dir):
        super().__init__(daemon=True)
        self.q = queue.Queue()
        self.base_dir = base_dir
        self.stop_event = threading.Event()

    def run(self):
        while True:
            text = self.q.get()
            if text is None:
                break
            self.stop_event.clear()
            clean_text = re.sub(r"<[^>]+>", " ", text)
            clean_text = clean_text.replace("/", " ").replace("+", " ")
            clean_text = re.sub(r"[^а-яА-ЯёЁa-zA-Z0-9\s\.,!?]", " ", clean_text)
            clean_text = re.sub(r"([.,!?])\1+", r"\1", clean_text)
            clean_text = re.sub(r"\s+([.,!?])", r"\1", clean_text)
            clean_text = re.sub(r"\s+", " ", clean_text).strip()
            if not clean_text:
                continue

            success = False
            try:
                temp_file = os.path.join(tempfile.gettempdir(), f"jerry_voice_{uuid.uuid4().hex}.mp3")

                async def generate():
                    communicate = edge_tts.Communicate(clean_text, "ru-RU-DmitryNeural", rate="+40%")
                    await communicate.save(temp_file)

                asyncio.run(generate())
                if os.path.exists(temp_file) and os.path.getsize(temp_file) > 0:
                    pygame.mixer.music.load(temp_file)
                    pygame.mixer.music.play()
                    while pygame.mixer.music.get_busy():
                        if self.stop_event.is_set():
                            pygame.mixer.music.stop()
                            break
                        time.sleep(0.05)
                    pygame.mixer.music.unload()
                    success = True
            except Exception as e:
                print(f"[Edge-TTS Error]: {e}")

            if not success and not self.stop_event.is_set():
                print("[TTS] Переключаюсь на системный голос Windows...")
                try:
                    pythoncom.CoInitialize()
                    engine = pyttsx3.init()
                    voices = engine.getProperty("voices")
                    for voice in voices:
                        if "ru" in voice.id.lower() or "russian" in voice.name.lower():
                            engine.setProperty("voice", voice.id)
                            break
                    rate = engine.getProperty("rate")
                    engine.setProperty("rate", rate + 80)

                    def check_stop():
                        while not self.stop_event.is_set():
                            time.sleep(0.05)
                        if self.stop_event.is_set():
                            engine.stop()

                    stop_thread = threading.Thread(target=check_stop, daemon=True)
                    stop_thread.start()
                    engine.say(clean_text)
                    engine.runAndWait()
                    self.stop_event.set()
                    pythoncom.CoUninitialize()
                except Exception as e:
                    print(f"[pyttsx3 Error]: {e}")

    def say(self, text):
        self.q.put(text)

    def stop_audio(self):
        self.stop_event.set()
        try:
            pygame.mixer.music.stop()
        except Exception:
            pass

class SafeTextEdit(QTextEdit):
    returnPressed = pyqtSignal()
    image_pasted = pyqtSignal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(45)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textChanged.connect(self.adjust_height)
        self.typing_sounds = []
        self.last_type_sound_time = 0
        for i in range(1, 4):
            path = get_resource_path(os.path.join("sounds", f"type_{i}.wav"))
            if os.path.exists(path):
                try:
                    self.typing_sounds.append(pygame.mixer.Sound(path))
                except Exception as e:
                    print(f"[Typing Sound Error] {path}: {e}")

    def play_typing_sound(self):
        if self.typing_sounds:
            now = time.time()
            if now - self.last_type_sound_time > 0.03:
                sound = random.choice(self.typing_sounds)
                channel = sound.play()
                if channel:
                    channel.set_volume(random.uniform(0.4, 0.8))
                self.last_type_sound_time = now

    def keyPressEvent(self, event):
        if event.key() not in (Qt.Key.Key_Shift, Qt.Key.Key_Control, Qt.Key.Key_Alt, Qt.Key.Key_CapsLock, Qt.Key.Key_Meta):
            self.play_typing_sound()
        if event.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            if event.modifiers() != Qt.KeyboardModifier.ShiftModifier:
                self.returnPressed.emit()
                return
        if event.matches(QKeySequence.StandardKey.Paste):
            cb = QApplication.clipboard()
            if cb.mimeData().hasImage():
                img = cb.image()
                if not img.isNull():
                    temp_path = os.path.join(tempfile.gettempdir(), f"clip_{uuid.uuid4().hex}.png")
                    img.save(temp_path)
                    self.image_pasted.emit(temp_path)
                    return
        super().keyPressEvent(event)

    def adjust_height(self):
        doc_height = self.document().size().height()
        new_height = min(max(45, int(doc_height) + 12), 180)
        if self.height() != new_height:
            self.setFixedHeight(new_height)
            if new_height == 180:
                self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
            else:
                self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

    def text(self):
        return self.toPlainText()

    def clear(self):
        super().setText("")
        self.setFixedHeight(45)

class ScaleButton(QPushButton):
    def __init__(self, text, bg_color, text_color, size_w=None, size_h=None, parent=None):
        super().__init__(text, parent)
        self.setFixedSize(size_w, size_h)
        self.bg_color = bg_color
        self.text_color = text_color
        self.border_color = None
        self._scale = 1.0
        self.anim = QPropertyAnimation(self, b"scale")
        self.anim.setDuration(100)

    def _get_scale(self):
        return self._scale

    def _set_scale(self, val):
        self._scale = val
        self.update()

    scale = pyqtProperty(float, _get_scale, _set_scale)

    def mousePressEvent(self, event):
        self.anim.stop()
        self.anim.setStartValue(self._scale)
        self.anim.setEndValue(0.92)
        self.anim.start()
        super().mousePressEvent(event)

    def mouseReleaseEvent(self, event):
        self.anim.stop()
        self.anim.setStartValue(self._scale)
        self.anim.setEndValue(1.0)
        self.anim.start()
        super().mouseReleaseEvent(event)

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        rect = QRectF(self.rect())
        center = rect.center()
        p.translate(center)
        p.scale(self._scale, self._scale)
        p.translate(-center)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(self.bg_color))
        p.drawRoundedRect(rect, rect.height() / 2, rect.height() / 2)
        if self.border_color:
            p.setPen(QPen(QColor(self.border_color), 1))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(rect, rect.height() / 2, rect.height() / 2)
        p.setPen(QColor(self.text_color))
        p.setFont(self.font())
        p.drawText(rect, Qt.AlignmentFlag.AlignCenter, self.text())

class JerryWindow(QMainWindow):
    ai_stream_chunk = pyqtSignal(str, str)
    ai_stream_done = pyqtSignal(str)
    timer_finished_signal = pyqtSignal()
    voice_recognized = pyqtSignal(str)
    title_generated = pyqtSignal()
    search_status_changed = pyqtSignal(str, str)

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Джери")
        self.resize(1100, 750)
        self.setMinimumSize(800, 600)
        self.setAcceptDrops(True)

        self.c = {
            "bg": "#1a1a1a", "sidebar": "#111111", "border": "#2a2a2a",
            "text": "#ffffff", "bubble": "#2a2a2a", "btn_bg": "#2a2a2a",
            "btn_text": "#ffffff", "btn_border": "#444444"
        }

        self.click_sound = None
        click_path = get_resource_path(os.path.join("sounds", "click.wav"))
        if os.path.exists(click_path):
            try:
                self.click_sound = pygame.mixer.Sound(click_path)
                self.click_sound.set_volume(0.6)
            except Exception as e:
                print(f"[Click Sound Error]: {e}")

        self.done_sound = None
        done_path = get_resource_path(os.path.join("sounds", "done.wav"))
        if os.path.exists(done_path):
            try:
                self.done_sound = pygame.mixer.Sound(done_path)
                self.done_sound.set_volume(0.7)
            except Exception as e:
                print(f"[Done Sound Error]: {e}")

        self.chats = load_chats()
        self.current_chat_id = None
        self.current_ai_label = None
        self.fly_anims = []
        self.is_always_listening = False
        self._is_listening = False
        self.mic_worker = None
        self.whisper_model = None

        self.active_streams = {}
        self.currently_speaking_chat_id = None
        self.timer_active = False
        self.timer_end_time = 0
        self.timer_display_timer = QTimer(self)
        self.timer_display_timer.setTimerType(Qt.TimerType.PreciseTimer)
        self.timer_display_timer.timeout.connect(self._update_timer_display)
        self.scroll_timer = QTimer(self)
        self.scroll_timer.setSingleShot(True)
        self.scroll_timer.timeout.connect(self._do_scroll)
        self.timer_sound_path = generate_timer_sound()
        self.current_model = "llama3.1:8b"
        self.attached_images = []

        central = QWidget()
        self.stacked_layout = QStackedLayout(central)
        self.stacked_layout.setStackingMode(QStackedLayout.StackingMode.StackAll)
        self.setCentralWidget(central)

        self.ui_layer = QWidget()
        main_layout = QHBoxLayout(self.ui_layer)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)
        self.ui_effect = QGraphicsOpacityEffect(self.ui_layer)
        self.ui_effect.setOpacity(0.0)
        self.ui_layer.setGraphicsEffect(self.ui_effect)

        self.sidebar = QWidget()
        sidebar_layout = QVBoxLayout(self.sidebar)
        sidebar_layout.setContentsMargins(15, 20, 15, 15)
        sidebar_layout.setSpacing(10)
        main_layout.addWidget(self.sidebar)

        self.new_chat_btn = ScaleButton("+ Новый чат", self.c["btn_bg"], self.c["btn_text"], 230, 42)
        self.new_chat_btn.border_color = self.c["btn_border"]
        self.new_chat_btn.setFont(QFont("Onest", 11, QFont.Weight.Bold))
        self.new_chat_btn.clicked.connect(self._play_click_sound)
        self.new_chat_btn.clicked.connect(self._create_new_chat)
        sidebar_layout.addWidget(self.new_chat_btn)

        self.chat_list = SlidingListWidget()
        self.chat_list.update_colors(self.c["text"], self.c["bubble"])
        self.chat_list.currentRowChanged.connect(self._on_chat_row_changed)
        self.chat_list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.chat_list.customContextMenuRequested.connect(self._show_chat_context_menu)
        sidebar_layout.addWidget(self.chat_list)

        self.model_combo = QComboBox()
        self.model_combo.currentIndexChanged.connect(self._on_model_changed)
        sidebar_layout.addWidget(self.model_combo)
        self.sidebar.setMaximumWidth(260)

        self.chat_area = QWidget()
        chat_area_layout = QVBoxLayout(self.chat_area)
        chat_area_layout.setContentsMargins(0, 0, 0, 0)
        chat_area_layout.setSpacing(0)

        self.top_bar = QWidget()
        top_bar_layout = QHBoxLayout(self.top_bar)
        self.toggle_btn = QPushButton("☰")
        self.toggle_btn.setStyleSheet(f"background: transparent; color: {self.c['text']}; font-size: 20px; border: none;")
        self.toggle_btn.clicked.connect(self._play_click_sound)
        self.toggle_btn.clicked.connect(self._toggle_sidebar)
        top_bar_layout.addWidget(self.toggle_btn)

        self.tts_checkbox = QCheckBox("Озвучка")
        self.tts_checkbox.setChecked(True)
        self.tts_checkbox.setStyleSheet(f"QCheckBox {{ color: {self.c['text']}; font-size: 14px; margin-left: 20px; }}")
        self.tts_checkbox.stateChanged.connect(self._on_tts_toggled)
        top_bar_layout.addWidget(self.tts_checkbox)
        
        self.timer_display = QLabel("")
        self.timer_display.setFont(QFont("Onest", 13, QFont.Weight.Bold))
        self.timer_display.setStyleSheet(f"color: {self.c['text']}; margin-left: 20px; background: transparent;")
        self.timer_display.hide()
        top_bar_layout.addWidget(self.timer_display)
        top_bar_layout.addStretch()

        self.dev_btn = QPushButton(">_ Консоль")
        self.dev_btn.setStyleSheet(
            f"background: {self.c['btn_bg']}; color: {self.c['btn_text']}; "
            f"border-radius: 10px; padding: 5px 10px; font-size: 12px; border: 1px solid {self.c['btn_border']};"
        )
        self.dev_btn.clicked.connect(self._play_click_sound)
        self.dev_btn.clicked.connect(self._toggle_dev_console)
        top_bar_layout.addWidget(self.dev_btn)
        chat_area_layout.addWidget(self.top_bar)
        
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_area.setStyleSheet("QScrollArea { border: none; background: transparent; }")
        self.chat_container = QWidget()
        self.chat_layout = QVBoxLayout(self.chat_container)
        self.chat_layout.setAlignment(Qt.AlignmentFlag.AlignTop)
        self.chat_layout.setSpacing(15)
        
        self.empty_state_label = QLabel("Я Джери, чем могу помочь?")
        self.empty_state_label.setFont(QFont("Onest", 22, QFont.Weight.Bold))
        self.empty_state_label.setStyleSheet(f"color: {self.c['text']}; background: transparent;")
        self.empty_state_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.chat_layout.addStretch(1)
        self.chat_layout.addWidget(self.empty_state_label)
        self.chat_layout.addStretch(1)
        
        self.scroll_area.setWidget(self.chat_container)
        chat_area_layout.addWidget(self.scroll_area)

        self.dev_console = QTextEdit()
        self.dev_console.setReadOnly(True)
        self.dev_console.setFixedHeight(180)
        self.dev_console.setStyleSheet(
            "background: #000000; color: #00ff00; font-family: Consolas; "
            "font-size: 12px; border-top: 2px solid #333; padding: 5px;"
        )
        self.dev_console.hide()
        chat_area_layout.addWidget(self.dev_console)
        self.emitting_stream = EmittingStream()
        self.emitting_stream.textWritten.connect(self.dev_console.insertPlainText)
        sys.stdout = self.emitting_stream
        sys.stderr = self.emitting_stream

        self.preview_scroll = QScrollArea()
        self.preview_scroll.setFixedHeight(85)
        self.preview_scroll.setWidgetResizable(True)
        self.preview_scroll.setStyleSheet("background: transparent;")
        self.preview_widget = QWidget()
        self.preview_layout = QHBoxLayout(self.preview_widget)
        self.preview_layout.setAlignment(Qt.AlignmentFlag.AlignLeft)
        self.preview_scroll.setWidget(self.preview_widget)
        self.preview_scroll.hide()
        chat_area_layout.addWidget(self.preview_scroll)

        bottom_layout = QHBoxLayout()
        bottom_layout.setContentsMargins(20, 10, 20, 20)
        bottom_layout.setSpacing(10)

        self.attach_btn = ScaleButton("📎", self.c["btn_bg"], self.c["btn_text"], 45, 45)
        self.attach_btn.border_color = self.c["btn_border"]
        self.attach_btn.clicked.connect(self._play_click_sound)
        self.attach_btn.clicked.connect(self._select_file)
        bottom_layout.addWidget(self.attach_btn)

        self.text_input = SafeTextEdit()
        self.text_input.setStyleSheet(
            f"QTextEdit {{ background: {self.c['btn_bg']}; color: {self.c['text']}; "
            f"border: 2px solid {self.c['btn_border']}; border-radius: 22px; padding: 10px 15px; }}"
        )
        self.text_input.returnPressed.connect(self._on_text_submitted)
        self.text_input.image_pasted.connect(self._add_image_to_preview)
        bottom_layout.addWidget(self.text_input)

        self.always_listen_btn = QToolButton()
        self.always_listen_btn.setText("🎤")
        self.always_listen_btn.setCheckable(True)
        self.always_listen_btn.setFixedSize(45, 45)
        self.always_listen_btn.setStyleSheet(f"""
            QToolButton {{ background: {self.c['btn_bg']}; border-radius: 22px; font-size: 18px; border: 1px solid {self.c['btn_border']}; }}
            QToolButton:checked {{ background: #f38ba8; color: #1e1e2e; }}
        """)
        self.always_listen_btn.clicked.connect(self._play_click_sound)
        self.always_listen_btn.clicked.connect(self._toggle_always_listen)
        bottom_layout.addWidget(self.always_listen_btn)

        self.send_btn = ScaleButton("↑", "#3b82f6", "#ffffff", 45, 45)
        self.send_btn.setFont(QFont("Onest", 16, QFont.Weight.Bold))
        self.send_btn.clicked.connect(self._play_click_sound)
        self.send_btn.clicked.connect(self._on_text_submitted)
        bottom_layout.addWidget(self.send_btn)

        chat_area_layout.addLayout(bottom_layout)
        main_layout.addWidget(self.chat_area)

        self.setStyleSheet(f"background-color: {self.c['bg']};")
        self.sidebar.setStyleSheet(f"background-color: {self.c['sidebar']}; border-right: 1px solid {self.c['border']};")
        self.top_bar.setStyleSheet(f"background-color: transparent; border-bottom: 1px solid {self.c['border']};")
        self.model_combo.setStyleSheet(
            f"QComboBox {{ background: {self.c['btn_bg']}; color: {self.c['text']}; "
            f"border-radius: 10px; padding: 5px; border: 1px solid {self.c['btn_border']}; }}"
        )

        self.recognizer = sr.Recognizer()
        self.recognizer.energy_threshold = 300
        self.recognizer.pause_threshold = 0.8
        self.tts = TTSWorker(get_base_dir())
        self.tts.start()

        self.ai_stream_chunk.connect(self._append_stream_chunk)
        self.ai_stream_done.connect(self._on_stream_finished)
        self.timer_finished_signal.connect(self._on_timer_finished)
        self.voice_recognized.connect(self._on_voice_recognized)
        self.title_generated.connect(self._load_chat_list)
        self.search_status_changed.connect(self._on_search_status_changed)
        
        self._load_chat_list()
        self._refresh_models()
        self.stacked_layout.addWidget(self.ui_layer)

        # --- ЗАСТАВКА ---
        self.splash = QWidget(self)
        self.splash.setStyleSheet("background-color: #1a1a1a;")
        self.splash.setGeometry(0, 0, self.width(), self.height())
        self.splash.show()
        self.splash.raise_()
        self.splash_label = QLabel("Привет, я Джери!", self.splash)
        self.splash_label.setFont(QFont("Onest", 28, QFont.Weight.Bold))
        self.splash_label.setStyleSheet("color: #ffffff;")
        self.splash_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.splash_label.setGeometry(0, 0, self.width(), self.height())
        self.splash_texts = ["Привет, я Джери!", "Я Джери, чем могу помочь?"]
        self.splash_index = 0
        self.splash_timer = QTimer(self)
        self.splash_timer.timeout.connect(self._update_splash)
        self.splash_timer.start(1200)

    def _play_click_sound(self):
        if self.click_sound:
            self.click_sound.play()

    def _on_search_status_changed(self, chat_id, status_text):
        if self.current_chat_id == chat_id:
            stream = self.active_streams.get(chat_id)
            if stream and stream.get("label"):
                try:
                    stream["label"].setHtml(f'<span style="color: #888;">{status_text}</span>')
                    stream["label"].adjust_size()
                except RuntimeError:
                    pass

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self, "splash") and self.splash.isVisible():
            self.splash.setGeometry(0, 0, self.width(), self.height())
            self.splash_label.setGeometry(0, 0, self.width(), self.height())

    def _update_splash(self):
        self.splash_index += 1
        self.splash_label.setText(self.splash_texts[self.splash_index])
        if self.splash_index >= len(self.splash_texts) - 1:
            self.splash_timer.stop()
            self._play_splash_sound()
            QTimer.singleShot(1500, self._fade_out_splash)

    def _play_splash_sound(self):
        sound_file = get_resource_path(os.path.join("sounds", "splash_sound.wav"))
        if os.path.exists(sound_file):
            try:
                self.splash_sound = pygame.mixer.Sound(sound_file)
                self.splash_sound.set_volume(1.0)
                self.splash_sound.play()
            except Exception as e:
                print(f"[Splash Sound Error]: {e}")

    def _fade_out_splash(self):
        self.splash_effect = QGraphicsOpacityEffect(self.splash)
        self.splash.setGraphicsEffect(self.splash_effect)
        self.splash_anim = QPropertyAnimation(self.splash_effect, b"opacity")
        self.splash_anim.setDuration(500)
        self.splash_anim.setStartValue(1.0)
        self.splash_anim.setEndValue(0.0)
        self.splash_anim.finished.connect(self.splash.hide)
        self.splash_anim.start()
        self.ui_anim = QPropertyAnimation(self.ui_effect, b"opacity")
        self.ui_anim.setDuration(500)
        self.ui_anim.setStartValue(0.0)
        self.ui_anim.setEndValue(1.0)
        self.ui_anim.start()

    def _toggle_dev_console(self):
        self.dev_console.setVisible(not self.dev_console.isVisible())

    def _markdown_to_html(self, text):
        safe = text.replace("<", "&lt;").replace(">", "&gt;")
        safe = re.sub(r"\*\*(.*?)\*\*", r"<b>\1</b>", safe)
        safe = re.sub(r"^\s*#{4,6}\s+(.*?)$", r"<b style='font-size: 15px;'>\1</b>", safe, flags=re.MULTILINE)
        safe = re.sub(r"^\s*###\s+(.*?)$", r'<h3 style="color: #89b4fa; margin-top: 10px; margin-bottom: 5px;">\1</h3>', safe, flags=re.MULTILINE)
        safe = re.sub(r"^\s*##\s+(.*?)$", r'<h2 style="color: #89b4fa; margin-top: 10px; margin-bottom: 5px;">\1</h2>', safe, flags=re.MULTILINE)
        safe = re.sub(r"^\s*#\s+(.*?)$", r'<h1 style="color: #89b4fa; margin-top: 10px; margin-bottom: 5px;">\1</h1>', safe, flags=re.MULTILINE)
        lines = safe.split("\n")
        in_list = False
        new_lines = []
        for line in lines:
            if line.strip().startswith("- "):
                if not in_list:
                    new_lines.append("<ul style='margin-top: 4px; margin-bottom: 4px; padding-left: 18px;'>")
                    in_list = True
                new_lines.append(f"<li style='margin-bottom: 2px;'>{line.strip()[2:]}</li>")
            else:
                if in_list:
                    new_lines.append("</ul>")
                    in_list = False
                if line.strip():
                    new_lines.append(line + "<br>")
        if in_list:
            new_lines.append("</ul>")
        return "".join(new_lines)

    def _update_timer_display(self):
        remaining = math.ceil(self.timer_end_time - time.monotonic())
        if remaining <= 0:
            self.timer_display_timer.stop()
            self.timer_display.hide()
            self.timer_active = False
            self.timer_finished_signal.emit()
            return
        h = remaining // 3600
        m = (remaining % 3600) // 60
        s = remaining % 60
        time_str = f"{h:02d}:{m:02d}:{s:02d}"
        self.timer_display.setText(time_str)

    def _on_tts_toggled(self, state):
        if state != 2:
            self.tts.stop_audio()
            self.currently_speaking_chat_id = None

    def _show_chat_context_menu(self, pos):
        item = self.chat_list.itemAt(pos)
        if not item:
            return
        menu = QMenu()
        delete_action = menu.addAction("Удалить чат")
        action = menu.exec(self.chat_list.viewport().mapToGlobal(pos))
        if action == delete_action:
            cid = item.data(Qt.ItemDataRole.UserRole)
            self._delete_chat(cid)

    def _delete_chat(self, cid):
        if cid in self.chats:
            del self.chats[cid]
            save_chats(self.chats)
            if self.current_chat_id == cid:
                if len(self.chats) > 0:
                    self.current_chat_id = list(self.chats.keys())[0]
                else:
                    self.current_chat_id = None
                self._load_chat_list()
                if self.current_chat_id:
                    self._switch_chat_by_id(self.current_chat_id)
                else:
                    self._go_to_new_chat_screen()
            else:
                self._load_chat_list()

    def _generate_chat_title(self, cid, first_message):
        try:
            prompt = (
                f"Придумай очень короткое название (до 3-4 слов) для этого чата "
                f"на основе первого сообщения: '{first_message}'. "
                f"Ответь только названием, без кавычек и точек."
            )
            payload = {
                "model": self.current_model,
                "messages": [{"role": "user", "content": prompt}],
                "stream": False
            }
            res = requests.post("http://localhost:11434/api/chat", json=payload, timeout=15)
            if res.status_code == 200:
                title = res.json().get("message", {}).get("content", "").strip().replace('"', "").replace("'", "")
                if title:
                    self.chats[cid]["title"] = title[:35]
                    save_chats(self.chats)
                    self.title_generated.emit()
                    return
            raise Exception("Ollama error")
        except Exception:
            fallback_title = first_message[:25] + "..." if len(first_message) > 25 else first_message
            self.chats[cid]["title"] = fallback_title if fallback_title else "Новый чат"
            save_chats(self.chats)
            self.title_generated.emit()

    def _add_image_to_preview(self, path):
        if path not in self.attached_images:
            self.attached_images.append(path)
            self._update_preview_ui()

    def _remove_image(self, path):
        if path in self.attached_images:
            self.attached_images.remove(path)
            self._update_preview_ui()

    def _update_preview_ui(self):
        while self.preview_layout.count():
            child = self.preview_layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()
        if not self.attached_images:
            self.preview_scroll.hide()
            return
        self.preview_scroll.show()
        for path in self.attached_images:
            frame = QFrame()
            frame.setFixedSize(70, 70)
            frame.setStyleSheet("background: #202020; border-radius: 8px;")
            lbl = QLabel(frame)
            pixmap = QPixmap(path).scaled(60, 60, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
            lbl.setPixmap(pixmap)
            lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
            lbl.setGeometry(5, 5, 60, 60)
            btn = QPushButton("×", frame)
            btn.setFixedSize(20, 20)
            btn.move(48, 2)
            btn.setStyleSheet("background: #f38ba8; color: #1e1e2e; border-radius: 10px; font-weight: bold; border: none;")
            btn.clicked.connect(lambda checked, p=path: self._remove_image(p))
            self.preview_layout.addWidget(frame)

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.accept()
        else:
            event.ignore()

    def dropEvent(self, event):
        files = [u.toLocalFile() for u in event.mimeData().urls() if u.isLocalFile()]
        images = [f for f in files if f.lower().endswith((".png", ".jpg", ".jpeg", ".bmp", ".webp"))]
        for img in images:
            self._add_image_to_preview(img)

    def _select_file(self):
        files, _ = QFileDialog.getOpenFileNames(self, "Выберите картинку", "", "Images (*.png *.jpg *.jpeg *.bmp *.webp)")
        for f in files:
            self._add_image_to_preview(f)

    def _toggle_always_listen(self):
        if self.always_listen_btn.isChecked():
            self.mic_worker = MicWorker(self.recognizer, None, self.voice_recognized.emit)
            self.mic_worker.start()
        else:
            if self.mic_worker:
                self.mic_worker.stop()
                self.mic_worker = None

    def _load_whisper(self):
        try:
            self.whisper_model = WhisperModel("small", device="cpu", compute_type="int8")
        except Exception as e:
            print(f"Whisper Error: {e}")

    def _toggle_sidebar(self):
        anim = QPropertyAnimation(self.sidebar, b"maximumWidth")
        anim.setDuration(250)
        anim.setEasingCurve(QEasingCurve.Type.InOutCubic)
        anim.setStartValue(self.sidebar.maximumWidth())
        anim.setEndValue(0 if self.sidebar.maximumWidth() > 0 else 260)
        anim.start()
        self.sidebar_anim = anim

    def _refresh_models(self):
        try:
            res = requests.get("http://localhost:11434/api/tags", timeout=2)
            if res.status_code == 200:
                self.model_combo.blockSignals(True)
                self.model_combo.clear()
                self.model_combo.addItems([m["name"] for m in res.json().get("models", [])])
                if self.current_model in [self.model_combo.itemText(i) for i in range(self.model_combo.count())]:
                    self.model_combo.setCurrentText(self.current_model)
                self.model_combo.blockSignals(False)
        except Exception:
            pass

    def _on_model_changed(self, idx):
        if idx >= 0:
            self.current_model = self.model_combo.currentText()

    def _go_to_new_chat_screen(self):
        self.current_chat_id = None
        self.chat_list.clearSelection()
        for i in reversed(range(self.chat_layout.count())):
            item = self.chat_layout.itemAt(i)
            if item.widget() and item.widget() != self.empty_state_label:
                w = item.widget()
                self.chat_layout.removeWidget(w)
                w.deleteLater()
        if self.chat_layout.count() == 0:
            self.chat_layout.addStretch(1)
        self.empty_state_label.setVisible(True)
        self.text_input.setFocus()

    def _create_new_chat(self):
        for cid, cdata in self.chats.items():
            if not cdata["messages"]:
                self._switch_chat_by_id(cid)
                return
        cid = str(datetime.now().timestamp())
        self.chats[cid] = {"title": "Новый чат", "messages": []}
        save_chats(self.chats)
        self._load_chat_list()
        self._switch_chat_by_id(cid)

    def _load_chat_list(self):
        self.chat_list.blockSignals(True)
        self.chat_list.clear()
        for cid, cdata in self.chats.items():
            item = QListWidgetItem(cdata["title"])
            item.setData(Qt.ItemDataRole.UserRole, cid)
            self.chat_list.addItem(item)
        self.chat_list.blockSignals(False)
        if self.current_chat_id in self.chats:
            for i in range(self.chat_list.count()):
                item = self.chat_list.item(i)
                if item and item.data(Qt.ItemDataRole.UserRole) == self.current_chat_id:
                    self.chat_list.blockSignals(True)
                    self.chat_list.setCurrentRow(i)
                    self.chat_list.blockSignals(False)
                    self.chat_list.set_highlight_instantly(i)
                    break

    def _on_chat_row_changed(self, row):
        try:
            if row >= 0 and row < self.chat_list.count():
                item = self.chat_list.item(row)
                if item:
                    cid = item.data(Qt.ItemDataRole.UserRole)
                    if self.current_chat_id != cid:
                        self._switch_chat_by_id(cid)
        except RuntimeError:
            pass

    def _switch_chat_by_id(self, cid):
        if self.currently_speaking_chat_id and self.currently_speaking_chat_id != cid:
            self.tts.stop_audio()
            self.currently_speaking_chat_id = None
        self.current_chat_id = cid
        for anim in self.fly_anims:
            anim.stop()
        self.fly_anims.clear()
        for stream in self.active_streams.values():
            stream["active"] = False
        for i in reversed(range(self.chat_layout.count())):
            item = self.chat_layout.itemAt(i)
            if item.widget() and item.widget() != self.empty_state_label:
                w = item.widget()
                self.chat_layout.removeWidget(w)
                w.deleteLater()
        if self.chat_layout.count() == 0:
            self.chat_layout.addStretch(1)
        msgs = self.chats[cid]["messages"]
        self.empty_state_label.setVisible(len(msgs) == 0)
        for m in msgs:
            self._add_message_to_ui(m["role"] == "user", m["content"], animate=False)
            
        if cid in self.active_streams:
            self.current_ai_container = QWidget()
            c_layout = QHBoxLayout(self.current_ai_container)
            c_layout.setContentsMargins(20, 5, 20, 5)
            area_w = self.scroll_area.width() if self.scroll_area.width() > 100 else 800
            max_w = int(area_w * 0.75)
            bubble = QFrame()
            bubble.setStyleSheet(f"background-color: {self.c['bubble']}; border-radius: 18px;")
            bubble.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Maximum)
            b_layout = QVBoxLayout(bubble)
            b_layout.setContentsMargins(14, 10, 14, 10)
            self.current_ai_label = AutoResizingTextBrowser(max_w - 28)
            self.current_ai_label.setFont(QFont("Onest", 11))
            b_layout.addWidget(self.current_ai_label)
            c_layout.addWidget(bubble)
            c_layout.addStretch()
            self.chat_layout.insertWidget(self.chat_layout.count() - 1, self.current_ai_container)
            self.active_streams[cid]["label"] = self.current_ai_label
            if self.active_streams[cid]["text"]:
                self.current_ai_label.setHtml(self._markdown_to_html(self.active_streams[cid]["text"]))
                self.current_ai_label.setStyleSheet(f"QTextBrowser {{ color: {self.c['text']}; background: transparent; padding: 0px; }}")
            else:
                self.current_ai_label.setHtml('<span style="color: #888;">...</span>')
                self.current_ai_label.setStyleSheet("QTextBrowser { background: transparent; padding: 0px; }")
            self.current_ai_label.adjust_size()
        self._scroll_to_bottom()

    def _animate_send_fly(self, text, target_label):
        fly = QLabel(text, self.ui_layer)
        fly.setWordWrap(True)
        fly.setFont(QFont("Onest", 11))
        fly.setStyleSheet(f"background-color: {self.c['bubble']}; color: {self.c['text']}; border-radius: 18px; padding: 10px 14px;")
        self.chat_layout.activate()
        QApplication.processEvents()
        start = QRect(self.text_input.mapTo(self.ui_layer, QPoint(0, 0)), self.text_input.size())
        end = QRect(target_label.mapTo(self.ui_layer, QPoint(0, 0)), target_label.size())
        fly.setGeometry(start)
        fly.show()
        anim = QPropertyAnimation(fly, b"geometry")
        anim.setDuration(300)
        anim.setStartValue(start)
        anim.setEndValue(end)
        anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        target_effect = target_label.graphicsEffect()

        def on_finished():
            try:
                target_effect.setOpacity(1.0)
            except Exception:
                pass

        anim.finished.connect(on_finished)
        anim.finished.connect(fly.deleteLater)
        self.fly_anims.append(anim)
        anim.start()

    def _add_message_to_ui(self, is_user, text, animate=False):
        container = QWidget()
        layout = QHBoxLayout(container)
        layout.setContentsMargins(20, 5, 20, 5)
        area_w = self.scroll_area.width() if self.scroll_area.width() > 100 else 800
        max_w = int(area_w * 0.75)

        bubble = QFrame()
        bubble.setStyleSheet(f"background-color: {self.c['bubble']}; border-radius: 18px;")
        bubble.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Maximum)
        b_layout = QVBoxLayout(bubble)
        b_layout.setContentsMargins(14, 10, 14, 10)

        lbl = AutoResizingTextBrowser(max_w - 28)
        lbl.setFont(QFont("Onest", 11))
        lbl.setStyleSheet(f"QTextBrowser {{ background: transparent; color: {self.c['text']}; padding: 0px; }}")

        if is_user:
            lbl.setPlainText(text)
            lbl.adjust_size()
            layout.addStretch()
            layout.addWidget(bubble)
        else:
            lbl.setHtml(self._markdown_to_html(text))
            lbl.adjust_size()
            layout.addWidget(bubble)
            layout.addStretch()

        b_layout.addWidget(lbl)
        self.chat_layout.insertWidget(self.chat_layout.count() - 1, container)
        self.scroll_timer.start(50)

        if animate:
            effect = QGraphicsOpacityEffect(bubble)
            bubble.setGraphicsEffect(effect)
            anim = QPropertyAnimation(effect, b"opacity")
            anim.setDuration(250)
            anim.setStartValue(0.0)
            anim.setEndValue(1.0)
            anim.finished.connect(lambda: bubble.setGraphicsEffect(None))
            anim.start()
            self.msg_anim = anim

        return bubble

    def _scroll_to_bottom(self):
        self.scroll_timer.start(50)

    def _do_scroll(self):
        self.scroll_area.verticalScrollBar().setValue(self.scroll_area.verticalScrollBar().maximum())

    def _on_text_submitted(self):
        text = self.text_input.text().strip()
        if not text and not self.attached_images:
            return
        self.text_input.clear()
        if self.current_chat_id is None:
            self._create_new_chat()
        cid = self.current_chat_id
        if not self.chats[cid]["messages"]:
            if text:
                threading.Thread(target=self._generate_chat_title, args=(cid, text), daemon=True).start()
        display_text = text if text else "[Анализ изображения]"
        self.chats[cid]["messages"].append({"role": "user", "content": display_text})
        save_chats(self.chats)
        self.empty_state_label.setVisible(False)
        real_label = self._add_message_to_ui(True, display_text, animate=False)
        images_to_send = list(self.attached_images)
        self.attached_images.clear()
        self._update_preview_ui()
        if self._process_system_command(text.lower()):
            self.text_input.clear()
            self._scroll_to_bottom()
            return
        self.text_input.clear()
        self._scroll_to_bottom()
        QTimer.singleShot(10, lambda: self._animate_send_fly(display_text, real_label))
        QTimer.singleShot(100, lambda: self._ask_ai(cid, text, images_to_send.copy()))

    def _find_and_launch_app(self, app_query: str) -> str | None:
        if app_query in ("браузер", "интернет", "browser"):
            webbrowser.open("https://google.com")
            return "браузер по умолчанию"

        browsers = {
            "хром": ("start chrome", "Google Chrome"),
            "chrome": ("start chrome", "Google Chrome"),
            "google chrome": ("start chrome", "Google Chrome"),
            "яндекс": ("start browser", "Яндекс Браузер"),
            "яндекс браузер": ("start browser", "Яндекс Браузер"),
            "yandex": ("start browser", "Яндекс Браузер"),
            "эдж": ("start msedge", "Microsoft Edge"),
            "edge": ("start msedge", "Microsoft Edge"),
            "опера": ("start opera", "Opera"),
            "opera": ("start opera", "Opera"),
            "оперу": ("start opera", "Opera"),
            "фаерфокс": ("start firefox", "Mozilla Firefox"),
            "firefox": ("start firefox", "Mozilla Firefox"),
            "лису": ("start firefox", "Mozilla Firefox"),
            "брейв": ("start brave", "Brave"),
            "brave": ("start brave", "Brave"),
        }
        if app_query in browsers:
            cmd_str, nice_name = browsers[app_query]
            subprocess.Popen(cmd_str, shell=True)
            return nice_name

        aliases = {
            "стим": "steam", "steam": "steam",
            "телеграм": "telegram", "телега": "telegram", "тг": "telegram", "telegram": "telegram",
            "дискорд": "discord", "дс": "discord", "discord": "discord",
            "фл студио": "fl64", "фл студия": "fl64", "фл": "fl64", "флка": "fl64", "fl studio": "fl64",
            "блокнот": "notepad", "notepad": "notepad",
            "калькулятор": "calc", "calculator": "calc",
            "проводник": "explorer", "мой компьютер": "explorer",
            "диспетчер задач": "taskmgr",
            "панель управления": "control",
            "настройки": "ms-settings:",
            "пэинт": "mspaint", "paint": "mspaint",
            "командная строка": "cmd", "консоль": "cmd",
            "обс": "obs64", "obs": "obs64",
            "спотифай": "spotify", "spotify": "spotify",
            "вк": "https://vk.com", "ютуб": "https://youtube.com", "youtube": "https://youtube.com"
        }

        import difflib
        target = aliases.get(app_query)
        if not target:
            close_alias = difflib.get_close_matches(app_query, list(aliases.keys()), n=1, cutoff=0.7)
            target = aliases[close_alias[0]] if close_alias else app_query

        if target.startswith("http") or target.startswith("ms-settings:"):
            os.startfile(target)
            return app_query

        if target in ("notepad", "calc", "explorer", "taskmgr", "control", "mspaint", "cmd"):
            subprocess.Popen(target, shell=True)
            return app_query

        search_dirs = [
            os.path.join(os.path.expanduser("~"), "Desktop"),
            os.path.join(os.environ.get("PUBLIC", r"C:\Users\Public"), "Desktop"),
            os.path.join(os.environ.get("APPDATA", ""), r"Microsoft\Windows\Start Menu\Programs"),
            os.path.join(os.environ.get("PROGRAMDATA", r"C:\ProgramData"), r"Microsoft\Windows\Start Menu\Programs"),
        ]

        shortcuts = []
        for base_dir in search_dirs:
            if not os.path.exists(base_dir):
                continue
            for root, _, files in os.walk(base_dir):
                for file in files:
                    if file.lower().endswith((".lnk", ".url")):
                        name_no_ext = os.path.splitext(file)[0]
                        shortcuts.append((name_no_ext.lower(), name_no_ext, os.path.join(root, file)))

        for low_name, orig_name, full_path in shortcuts:
            if target == low_name:
                os.startfile(full_path)
                return orig_name

        for low_name, orig_name, full_path in shortcuts:
            if target in low_name or low_name in target:
                os.startfile(full_path)
                return orig_name

        return None

    def _reply_system(self, msg: str):
        self._add_message_to_ui(False, msg)
        if self.tts_checkbox.isChecked():
            self.tts.say(msg)

    def _process_system_command(self, cmd):
        cmd_clean = re.sub(r"[^\w\s]", " ", cmd.lower())
        cmd_clean = re.sub(r"\s+", " ", cmd_clean).strip()
        cmd_clean = cmd_clean.replace("за гугли", "загугли")

        if "таймер" in cmd_clean:
            hours = re.search(r"(\d+)\s*[-]?\s*(час|ч)", cmd_clean)
            mins = re.search(r"(\d+)\s*[-]?\s*(минут|мин|м)", cmd_clean)
            secs = re.search(r"(\d+)\s*[-]?\s*(секунд|сек|с)", cmd_clean)
            total = 0
            if hours:
                total += int(hours.group(1)) * 3600
            if mins:
                total += int(mins.group(1)) * 60
            if secs:
                total += int(secs.group(1))
            if total > 0:
                self.timer_active = True
                self.timer_end_time = time.monotonic() + total
                self.timer_display_timer.start(200)
                self.timer_display.show()
                self._update_timer_display()
                self._reply_system(f"Таймер на {total} секунд запущен.")
                return True

        yt_match = re.match(r"^(найди|поищи|включи)\s+(в ютубе|на ютубе|в youtube)\s+(.+)$", cmd_clean)
        if yt_match:
            query = yt_match.group(3).strip()
            webbrowser.open(f"https://youtube.com/results?search_query={requests.utils.quote(query)}")
            self._reply_system(f"Ищу на YouTube: {query}")
            return True

        google_match = re.match(r"^(загугли|найди в гугле|найди в браузере)\s+(.+)$", cmd_clean)
        if google_match:
            query = google_match.group(2).strip()
            webbrowser.open(f"https://google.com/search?q={requests.utils.quote(query)}")
            self._reply_system(f"Ищу в Google: {query}")
            return True

        open_match = re.match(r"^(открой|запусти|включи)\s+(.+)$", cmd_clean)
        if open_match:
            app_name = open_match.group(2).strip()
            launched = self._find_and_launch_app(app_name)
            if launched:
                self._reply_system(f"Открываю {launched}.")
                return True

        close_match = re.match(r"^(закрой|выключи|убей)\s+(.+)$", cmd_clean)
        if close_match:
            app_name = close_match.group(2).strip()
            proc_map = {
                "стим": "steam.exe", "steam": "steam.exe",
                "телеграм": "Telegram.exe", "телега": "Telegram.exe",
                "дискорд": "Discord.exe", "дс": "Discord.exe",
                "хром": "chrome.exe", "браузер": "chrome.exe",
                "блокнот": "notepad.exe", "калькулятор": "CalculatorApp.exe",
                "фл студио": "FL64.exe", "флка": "FL64.exe"
            }
            exe_name = proc_map.get(app_name, f"{app_name}.exe")
            res = subprocess.run(["taskkill", "/F", "/IM", exe_name], capture_output=True)
            if res.returncode == 0:
                self._reply_system(f"Закрыл {app_name}.")
                return True

        if any(w in cmd_clean for w in ("сделай погромче", "прибавь звук", "громче")):
            for _ in range(5):
                pyautogui.press("volumeup")
            self._reply_system("Сделал погромче.")
            return True

        if any(w in cmd_clean for w in ("сделай потише", "убавь звук", "тише")):
            for _ in range(5):
                pyautogui.press("volumedown")
            self._reply_system("Сделал потише.")
            return True

        if cmd_clean in ("выключи звук", "без звука", "включи звук", "мут"):
            pyautogui.press("volumemute")
            self._reply_system("Переключил звук.")
            return True

        if cmd_clean in ("пауза", "продолжи", "стоп музыка", "играй"):
            pyautogui.press("playpause")
            self._reply_system("Готово.")
            return True

        if cmd_clean in ("следующий трек", "дальше", "переключи трек"):
            pyautogui.press("nexttrack")
            self._reply_system("Следующий трек.")
            return True

        if cmd_clean in ("предыдущий трек", "назад"):
            pyautogui.press("prevtrack")
            self._reply_system("Предыдущий трек.")
            return True

        if any(w in cmd_clean for w in ("сделай скриншот", "скриншот", "снимок экрана")):
            desktop = os.path.join(os.path.expanduser("~"), "Desktop")
            fname = os.path.join(desktop, f"Jerry_Screenshot_{int(time.time())}.png")
            pyautogui.screenshot(fname)
            self._reply_system("Скриншот сохранён на Рабочий стол.")
            return True

        if any(w in cmd_clean for w in ("сверни все окна", "рабочий стол", "сверни окна")):
            pyautogui.hotkey("win", "d")
            self._reply_system("Свернул все окна.")
            return True

        if cmd_clean in ("выключи компьютер", "выключение пк"):
            self._reply_system("Выключаю компьютер через 5 секунд.")
            subprocess.Popen("shutdown /s /t 5", shell=True)
            return True

        if cmd_clean in ("перезагрузи компьютер", "перезагрузка пк"):
            self._reply_system("Перезагружаю компьютер через 5 секунд.")
            subprocess.Popen("shutdown /r /t 5", shell=True)
            return True

        return False

    def _on_timer_finished(self):
        if self.tts_checkbox.isChecked():
            self.tts.say("Время вышло")
        winsound.PlaySound(self.timer_sound_path, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_LOOP)
        popup = TimerPopup(self)
        popup.exec()

    def _on_voice_recognized(self, text):
        self.text_input.setText(text)
        self._on_text_submitted()

    def _search_web(self, query):
        clean_q = re.sub(
            r"\b(хорош ли|хорош за свои деньги|сколько он стоит|подскажи|расскажи|пожалуйста|какой мне взять|что лучше)\b",
            "", query, flags=re.IGNORECASE
        )
        clean_q = re.sub(r"[?!.,]", " ", clean_q)
        clean_q = re.sub(r"\s+", " ", clean_q).strip()
        if len(clean_q) < 3:
            clean_q = query

        print(f"[Поиск] Запуск поиска: '{clean_q}'")

        def search(reg):
            with DDGS() as ddgs:
                return list(ddgs.text(clean_q, region=reg, max_results=6))

        results = []
        for reg in ("ru-ru", "wt-wt"):
            with concurrent.futures.ThreadPoolExecutor() as executor:
                future = executor.submit(search, reg)
                try:
                    results = future.result(timeout=15)
                except Exception as e:
                    print(f"[Поиск {reg}] Ошибка: {e}")
                    results = []
            if results:
                break

        if not results:
            print("[Поиск] Результатов нет ни в одном регионе.")
            return ""

        print(f"[Поиск] Найдено {len(results)} ссылок. Читаю содержимое страниц...")
        formatted = "=== СВЕЖИЕ ДАННЫЕ ИЗ ИНТЕРНЕТА ===\n"
        pages_read = 0

        for i, r in enumerate(results, 1):
            title = r.get("title", "")
            body = r.get("body", "")
            href = r.get("href", "")
            formatted += f"{i}. {title}: {body}\n"
            print(f"  > {title}")

            if pages_read < 2 and href and not any(bad in href for bad in ("youtube.com", "ozon.ru", "wildberries.ru", "market.yandex")):
                try:
                    resp = requests.get(href, headers={"User-Agent": "Mozilla/5.0"}, timeout=5)
                    if resp.status_code == 200:
                        raw_html = re.sub(r"<(script|style).*?>.*?</\1>", "", resp.text, flags=re.DOTALL | re.IGNORECASE)
                        clean_page = re.sub(r"<[^>]+>", " ", raw_html)
                        clean_page = re.sub(r"\s+", " ", clean_page).strip()
                        if len(clean_page) > 400:
                            formatted += f"--- Текст со страницы ({title}) ---\n{clean_page[:3500]}\n\n"
                            pages_read += 1
                            print(f"  [+] Прочитана статья: {href[:50]}...")
                except Exception:
                    pass

        return formatted

    def _ask_ai(self, cid, prompt, images):
        self.active_streams[cid] = {"label": None, "text": "", "active": True}
        if self.current_chat_id == cid:
            self.current_ai_container = QWidget()
            c_layout = QHBoxLayout(self.current_ai_container)
            c_layout.setContentsMargins(20, 5, 20, 5)
            area_w = self.scroll_area.width() if self.scroll_area.width() > 100 else 800
            max_w = int(area_w * 0.75)
            bubble = QFrame()
            bubble.setStyleSheet(f"background-color: {self.c['bubble']}; border-radius: 18px;")
            bubble.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Maximum)
            b_layout = QVBoxLayout(bubble)
            b_layout.setContentsMargins(14, 10, 14, 10)
            self.current_ai_label = AutoResizingTextBrowser(max_w - 28)
            self.current_ai_label.setFont(QFont("Onest", 11))
            b_layout.addWidget(self.current_ai_label)
            c_layout.addWidget(bubble)
            c_layout.addStretch()
            self.chat_layout.insertWidget(self.chat_layout.count() - 1, self.current_ai_container)
            self.active_streams[cid]["label"] = self.current_ai_label
            effect = QGraphicsOpacityEffect(self.current_ai_container)
            self.current_ai_container.setGraphicsEffect(effect)
            anim = QPropertyAnimation(effect, b"opacity")
            anim.setDuration(250)
            anim.setStartValue(0.0)
            anim.setEndValue(1.0)
            anim.start()
            self.ai_anim = anim

        def worker():
            try:
                search_keywords = (
                    "найди", "поищи", "узнай", "погода", "новости", "курс",
                    "что такое", "какой", "какая", "какое", "какие", "кто",
                    "где", "когда", "сколько", "почему", "зачем", "сейчас",
                    "актуальн", "последн", "нов", "цен", "стоит", "рейтинг",
                    "топ", "лучш", "сравни", "2024", "2025", "2026"
                )
                if any(kw in prompt.lower() for kw in search_keywords):
                    self.search_status_changed.emit(cid, "Ищу в интернете...")
                    web_results = self._search_web(prompt)
                    if web_results:
                        system_prompt = (
                            "Ты — профессиональный ИИ-ассистент. Твоя задача — дать ответ, "
                            "опираясь ТОЛЬКО на предоставленный текст из интернета.\n"
                            "КРИТИЧЕСКИЕ ПРАВИЛА:\n"
                            "1. ЗАПРЕЩЕНО придумывать характеристики или повторять одинаковый шаблон для разных моделей.\n"
                            "2. ЗАПРЕЩЕНО писать ссылки (URL) и названия сайтов.\n"
                            "3. Если просят порекомендовать технику, выведи конкретные модели с их реальными характеристиками из текста.\n"
                            "4. Используй заголовки (### или #### ) и списки (- ) для структуры.\n"
                            "5. Никаких эмодзи."
                        )
                        user_prompt = f"Вопрос пользователя: {prompt}\n\nТекст из интернета для анализа:\n{web_results}"
                        messages = [
                            {"role": "system", "content": system_prompt},
                            {"role": "user", "content": user_prompt}
                        ]
                    else:
                        messages = [
                            {"role": "system", "content": "Ты — ИИ-ассистент. Поиск не дал результатов. Напиши: 'Не удалось найти актуальные данные в интернете'. Не выдумывай ничего."},
                            {"role": "user", "content": prompt}
                        ]
                else:
                    messages = [{"role": "user", "content": prompt}]

                if images:
                    image_data = []
                    for img_path in images:
                        with Image.open(img_path) as img:
                            img.thumbnail((800, 800))
                            buffered = io.BytesIO()
                            img.save(buffered, format="PNG")
                            encoded = base64.b64encode(buffered.getvalue()).decode("utf-8")
                            image_data.append(encoded)
                    messages[-1]["images"] = image_data

                payload = {
                    "model": self.current_model,
                    "messages": messages,
                    "options": {"num_ctx": 4096},
                    "stream": True
                }
                res = requests.post("http://localhost:11434/api/chat", json=payload, stream=True, timeout=120)
                if res.status_code != 200:
                    error_msg = res.text
                    print(f"Ollama Error {res.status_code}: {error_msg}")
                    self.ai_stream_chunk.emit(cid, f"❌ Ошибка Ollama (HTTP {res.status_code}).\n")
                    self.ai_stream_done.emit(cid)
                    return

                self.active_streams[cid]["text"] = ""
                if res.status_code == 200:
                    for line in res.iter_lines():
                        if not line:
                            continue
                        chunk = json.loads(line.decode("utf-8"))
                        content = chunk.get("message", {}).get("content", "")
                        if content:
                            self.active_streams[cid]["text"] += content
                            self.ai_stream_chunk.emit(cid, content)
                        if chunk.get("done"):
                            break
                    self.ai_stream_done.emit(cid)
            except Exception as e:
                print(f"Worker Error: {e}")
                self.ai_stream_chunk.emit(cid, f"\n❌ Ошибка подключения: {e}")
                self.ai_stream_done.emit(cid)

        threading.Thread(target=worker, daemon=True).start()

    def _append_stream_chunk(self, cid, chunk):
        if self.current_chat_id == cid:
            stream = self.active_streams.get(cid)
            if stream and stream["label"]:
                try:
                    if "Ищу" in stream["label"].toPlainText() or stream["label"].toPlainText() == "...":
                        stream["label"].setText("")
                        stream["label"].setStyleSheet(f"QTextBrowser {{ color: {self.c['text']}; background: transparent; padding: 0px; }}")
                    html_text = self._markdown_to_html(stream["text"])
                    stream["label"].setHtml(html_text)
                    stream["label"].adjust_size()
                    self._scroll_to_bottom()
                except RuntimeError:
                    stream["label"] = None

    def _on_stream_finished(self, cid):
        if cid in self.active_streams:
            full_text = self.active_streams[cid]["text"]
            if full_text and cid in self.chats:
                self.chats[cid]["messages"].append({"role": "assistant", "content": full_text})
                save_chats(self.chats)
            if self.current_chat_id == cid:
                if self.done_sound:
                    self.done_sound.play()
                if self.tts_checkbox.isChecked():
                    self.currently_speaking_chat_id = cid
                    self.tts.say(full_text)
            if cid in self.active_streams:
                del self.active_streams[cid]

class MicWorker(threading.Thread):
    def __init__(self, recognizer, model, callback):
        super().__init__(daemon=True)
        self.recognizer = recognizer
        self.callback = callback
        self.running = True

    def run(self):
        import sounddevice as sd
        import numpy as np

        sample_rate = 16000
        block_size = 1600  # 0.1 сек
        print("[Mic] Микрофон (sounddevice) запущен, слушаю...")

        audio_buffer = []
        silent_blocks = 0
        is_speaking = False

        try:
            with sd.InputStream(samplerate=sample_rate, channels=1, dtype="int16", blocksize=block_size) as stream:
                while self.running:
                    data, _ = stream.read(block_size)
                    volume = np.abs(data).mean()

                    if volume > 220:  # Порог громкости речи
                        is_speaking = True
                        silent_blocks = 0
                        audio_buffer.append(data.copy())
                    elif is_speaking:
                        audio_buffer.append(data.copy())
                        silent_blocks += 1
                        if silent_blocks >= 8 or len(audio_buffer) > 80:
                            raw_bytes = np.concatenate(audio_buffer).tobytes()
                            audio_buffer.clear()
                            is_speaking = False
                            silent_blocks = 0

                            audio_data = sr.AudioData(raw_bytes, sample_rate, 2)
                            try:
                                text = self.recognizer.recognize_google(audio_data, language="ru-RU").strip()
                                if text and self.running:
                                    print(f"[Mic] Распознано: {text}")
                                    self.callback(text)
                            except sr.UnknownValueError:
                                pass
                            except Exception as e:
                                print(f"[Mic Google Error]: {e}")
        except Exception as e:
            print(f"[Mic Stream Error]: {e}")

    def stop(self):
        self.running = False

def main():
    app = QApplication(sys.argv)
    
    # Установка иконки
    icon_path = get_resource_path("logo.ico")
    if os.path.exists(icon_path):
        app.setWindowIcon(QIcon(icon_path))

    # Загрузка кастомных шрифтов
    fonts_dir = get_resource_path("fonts")
    if os.path.exists(fonts_dir):
        for file in os.listdir(fonts_dir):
            if file.lower().endswith((".ttf", ".otf")):
                try:
                    with open(os.path.join(fonts_dir, file), "rb") as f:
                        font_id = QFontDatabase.addApplicationFontFromData(f.read())
                        if font_id != -1:
                            families = QFontDatabase.applicationFontFamilies(font_id)
                            if families:
                                app.setFont(QFont(families[0], 10))
                                print(f"[FONT] Загружен шрифт: {file} ({families})")
                except Exception as e:
                    print(f"[FONT Error] {file}: {e}")

    import traceback
    def log_exc(exc_type, exc_value, exc_tb):
        err_text = "".join(traceback.format_exception(exc_type, exc_value, exc_tb))
        with open("error.txt", "w", encoding="utf-8") as f:
            f.write(err_text)
        if sys.__stderr__:
            sys.__stderr__.write(err_text)
    sys.excepthook = log_exc

    w = JerryWindow()
    w.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()