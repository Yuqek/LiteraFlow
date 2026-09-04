"""LiteraFlow — однофайловая среда перевода новелл на Flet 0.28.x.

Файл рассчитан на запуск как desktop-приложение и на упаковку в Android APK.
Базовые форматы и SQLite работают на стандартной библиотеке Python. Для UI
нужен Flet; ``cryptography``, ``pyspellchecker``, ``pymorphy3`` и
``flet-audio`` включают шифрованный сейф, офлайн-морфологию и озвучку.
"""

from __future__ import annotations

import asyncio
import base64
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass
from difflib import SequenceMatcher
from functools import lru_cache
import hashlib
import hmac
import io
import json
import os
import posixpath
import random
import re
import sqlite3
import tempfile
import threading
import time
import uuid
import zipfile
import zlib
from datetime import datetime, timezone
from html import escape
from html.entities import name2codepoint
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Iterable
from urllib.error import HTTPError, URLError
from urllib.parse import quote, unquote, urlencode, urldefrag, urlsplit, urlunsplit
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET

import flet as ft

try:
    import flet_audio as ft_audio

    HAS_FLET_AUDIO = True
except ImportError:
    ft_audio = None
    HAS_FLET_AUDIO = False

try:
    import keyring

    HAS_KEYRING = True
except ImportError:
    keyring = None
    HAS_KEYRING = False

try:
    from cryptography.fernet import Fernet, InvalidToken

    HAS_CRYPTOGRAPHY = True
except ImportError:
    Fernet = None
    InvalidToken = Exception
    HAS_CRYPTOGRAPHY = False

try:
    from spellchecker import SpellChecker

    HAS_PYSPELLCHECKER = True
except ImportError:
    SpellChecker = None
    HAS_PYSPELLCHECKER = False

try:
    from pymorphy3 import MorphAnalyzer

    HAS_PYMORPHY3 = True
except ImportError:
    MorphAnalyzer = None
    HAS_PYMORPHY3 = False


APP_TITLE = "LiteraFlow"
APP_TAGLINE = "Переводи историю, а не строки"
APP_WINDOW_TITLE = f"{APP_TITLE} — {APP_TAGLINE}"
APP_DATA_DIR = Path(os.environ.get("FLET_APP_STORAGE_DATA") or Path.cwd())
CONFIG_FILE = APP_DATA_DIR / "translator_config.json"
TRANSLATION_MEMORY_FILE = APP_DATA_DIR / "translation_memory.json"
DATABASE_FILE = APP_DATA_DIR / "literaflow.db"
SECRET_VAULT_FILE = APP_DATA_DIR / "literaflow.secrets.json"
SECRET_KEY_FILE = APP_DATA_DIR / ".literaflow.key"
SUPPORTED_EXTENSIONS = {".txt", ".md", ".docx", ".epub", ".fb2", ".xlf", ".xliff"}
LARGE_DOCUMENT_THRESHOLD = 1200
LARGE_DOCUMENT_WINDOW = 120
READER_PAGE_SIZE = 80
DATABASE_SCHEMA_VERSION = 3
TRANSLATION_VARIANT_SLOTS = ("literal", "literary", "machine")
TRANSLATION_VARIANT_LABELS = {
    "literal": "Буквальный",
    "literary": "Художественный",
    "machine": "Машинный",
}

DEFAULT_CONFIG: dict[str, Any] = {
    "config_version": 7,
    "model": "qwen2.5:3b",
    "target_lang": "ru",
    "source_lang": "auto",
    "api_type": "google",
    "ollama_url": "http://localhost:11434/api/generate",
    "custom_api_name": "Мой API",
    "custom_api_url": "https://api.openai.com/v1/chat/completions",
    "custom_api_key": "",
    "custom_api_key_header": "Authorization",
    "custom_api_model": "",
    "custom_api_headers": "",
    "remember_api_key": False,
    "api_profiles": [],
    "active_api_profile": "",
    "fallback_enabled": False,
    "fallback_order": ["google", "custom", "ollama"],
    "show_local_ai": False,
    "auto_fetch": False,
    "segmentation_method": "advanced",
    "theme": "dark",
    "last_file": "",
    "last_export": "",
    "font_size": 14,
    "translation_style": "literary",
    "recent_files": [],
    "accent_color_preset": "cyan",
    "spellcheck_mode": "off",
    "languagetool_url": "https://api.languagetool.org/v2/check",
    "short_word_nbsp": True,
    "short_word_nbsp_words": "а,в,и,к,о,с,у,но,на,по,во,ко,со",
    "google_request_interval": 1.0,
    "send_neighbor_context": True,
    "mobile_symbol_order": ["«", "»", "—", "…", "„", "“", "\u00a0"],
    "complex_format_policy": "error",
}

LANG_NAMES = {
    "auto": "автоматически определяемого языка",
    "ru": "русский",
    "en": "английский",
    "de": "немецкий",
    "fr": "французский",
    "es": "испанский",
    "ja": "японский",
    "zh-CN": "китайский (упрощённый)",
    "ko": "корейский",
}

ACCENT_PRESETS = {
    "cyan": {"dark": "#67C9BE", "light": "#167F76", "name": "Морская волна"},
    "purple": {"dark": "#A99BE8", "light": "#6957AE", "name": "Чернильный"},
    "orange": {"dark": "#DDA15E", "light": "#9A5A18", "name": "Янтарный"},
    "green": {"dark": "#83BE91", "light": "#39764A", "name": "Шалфейный"},
    "pink": {"dark": "#D391A1", "light": "#9A4960", "name": "Брусничный"},
}

STATUS_EMPTY = "empty"
STATUS_DRAFT = "draft"
STATUS_CONFIRMED = "confirmed"
STATUS_COLORS = {
    STATUS_EMPTY: "#C96E70",
    STATUS_DRAFT: "#D0A052",
    STATUS_CONFIRMED: "#67A77B",
}
STATUS_TITLES = {
    STATUS_EMPTY: "Не переведён",
    STATUS_DRAFT: "Черновик — требует подтверждения",
    STATUS_CONFIRMED: "Подтверждён",
}

STYLE_INSTRUCTIONS = {
    "general": "Сохрани смысл, естественную лексику и тон оригинала.",
    "technical": "Переводи точно, без художественных добавлений и потери деталей.",
    "literary": "Сделай естественный художественный перевод, сохрани голос персонажей и атмосферу.",
    "literal": "Переводи максимально близко к исходной конструкции, но грамотно.",
}

ABBREVIATIONS = {
    "mr.", "mrs.", "ms.", "dr.", "prof.", "sr.", "jr.", "st.",
    "vs.", "etc.", "e.g.", "i.e.", "г.", "ул.", "д.", "стр.", "рис.",
    "им.", "тов.", "акад.", "проф.", "доц.", "т.е.", "т.к.", "т.д.",
    "т.п.", "см.", "гл.", "ред.", "пер.", "руб.", "коп.",
}

NON_TERMINAL_ABBREVIATIONS = {
    "mr.", "mrs.", "ms.", "dr.", "prof.", "sr.", "jr.", "st.", "vs.",
    "г.", "ул.", "д.", "стр.", "рис.", "им.", "тов.", "акад.", "проф.",
    "доц.", "см.", "гл.", "ред.", "пер.",
}

W_NS = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
R_NS = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"


class TranslationError(RuntimeError):
    """Понятная пользователю ошибка выбранного AI-бэкенда."""


@dataclass(slots=True)
class TranslationResult:
    """Результат перевода вместе с фактическим источником ответа."""

    text: str
    provider: str
    request_id: str
    latency_ms: int
    from_memory: bool = False
    raw_text: str = ""


@dataclass(slots=True)
class _ProviderState:
    last_started: float = 0.0
    consecutive_errors: int = 0
    blocked_until: float = 0.0


class ProviderRateLimiter:
    """Потокобезопасно ограничивает каждый переводчик независимо."""

    def __init__(self) -> None:
        self._states: dict[str, _ProviderState] = {}
        self._slots: dict[str, threading.BoundedSemaphore] = {}
        self._lock = threading.Lock()

    def acquire(self, provider: str) -> None:
        with self._lock:
            slot = self._slots.setdefault(provider, threading.BoundedSemaphore(1))
        slot.acquire()

    def release(self, provider: str) -> None:
        with self._lock:
            slot = self._slots.setdefault(provider, threading.BoundedSemaphore(1))
        slot.release()

    def wait(self, provider: str, minimum_interval: float) -> None:
        minimum_interval = max(0.0, float(minimum_interval))
        while True:
            with self._lock:
                state = self._states.setdefault(provider, _ProviderState())
                now = time.monotonic()
                delay = max(state.blocked_until - now, state.last_started + minimum_interval - now, 0.0)
                if delay <= 0:
                    state.last_started = now
                    return
            time.sleep(min(delay, 1.0))

    def success(self, provider: str) -> None:
        with self._lock:
            state = self._states.setdefault(provider, _ProviderState())
            state.consecutive_errors = 0
            state.blocked_until = 0.0

    def failure(self, provider: str, error: Exception) -> None:
        retry_after = 0.0
        http_error = error if isinstance(error, HTTPError) else error.__cause__ if isinstance(error.__cause__, HTTPError) else None
        if http_error is not None:
            try:
                retry_after = float(http_error.headers.get("Retry-After", "0") or 0)
            except (TypeError, ValueError):
                retry_after = 0.0
        with self._lock:
            state = self._states.setdefault(provider, _ProviderState())
            state.consecutive_errors += 1
            exponential = min(30.0, 2.0 ** min(state.consecutive_errors - 1, 5))
            if http_error is not None and http_error.code not in {429, 500, 502, 503, 504}:
                exponential = 0.0
            state.blocked_until = max(
                state.blocked_until,
                time.monotonic() + max(retry_after, exponential) + random.uniform(0.05, 0.25),
            )

    def is_open(self, provider: str) -> bool:
        with self._lock:
            state = self._states.setdefault(provider, _ProviderState())
            return state.consecutive_errors >= 3 and state.blocked_until > time.monotonic()


PROVIDER_RATE_LIMITER = ProviderRateLimiter()


class SecureSecretStore:
    """Хранилище ключей: системный keyring, затем зашифрованный локальный сейф.

    В конфигурационный JSON секреты никогда не записываются. Локальный fallback
    использует Fernet и отдельный ключ с правами только для владельца. Если ни
    один безопасный backend недоступен, ключ остаётся только в памяти процесса.
    """

    service_name = "LiteraFlow API profiles"

    def __init__(self, vault_path: Path = SECRET_VAULT_FILE, key_path: Path = SECRET_KEY_FILE) -> None:
        self.vault_path = Path(vault_path)
        self.key_path = Path(key_path)

    @property
    def backend(self) -> str:
        if HAS_KEYRING:
            return "system"
        return "encrypted_file"

    @property
    def available(self) -> bool:
        return True

    def description(self) -> str:
        if self.backend == "system":
            return "Системное защищённое хранилище"
        if self.backend == "encrypted_file":
            return "Зашифрованный локальный сейф"
        return "Зашифрованный локальный сейф"

    def _device_key(self) -> bytes:
        self.key_path.parent.mkdir(parents=True, exist_ok=True)
        try:
            key = self.key_path.read_bytes()
            if len(key) == 32:
                return key
        except OSError:
            pass
        key = os.urandom(32)
        _atomic_write_bytes(self.key_path, key)
        try:
            os.chmod(self.key_path, 0o600)
        except OSError:
            pass
        return key

    def _encrypt_portable(self, secret: str) -> str:
        key = self._device_key()
        nonce = os.urandom(16)
        plain = secret.encode("utf-8")
        stream = b"".join(hmac.new(key, nonce + counter.to_bytes(4, "big"), hashlib.sha256).digest() for counter in range((len(plain) + 31) // 32))
        cipher = bytes(left ^ right for left, right in zip(plain, stream))
        tag = hmac.new(key, b"LiteraFlow-v1" + nonce + cipher, hashlib.sha256).digest()
        return "S1:" + base64.urlsafe_b64encode(nonce + tag + cipher).decode("ascii")

    def _decrypt_portable(self, token: str) -> str:
        raw = base64.urlsafe_b64decode(token[3:].encode("ascii"))
        if len(raw) < 48:
            return ""
        nonce, tag, cipher = raw[:16], raw[16:48], raw[48:]
        key = self._device_key()
        expected = hmac.new(key, b"LiteraFlow-v1" + nonce + cipher, hashlib.sha256).digest()
        if not hmac.compare_digest(tag, expected):
            return ""
        stream = b"".join(hmac.new(key, nonce + counter.to_bytes(4, "big"), hashlib.sha256).digest() for counter in range((len(cipher) + 31) // 32))
        return bytes(left ^ right for left, right in zip(cipher, stream)).decode("utf-8")

    def _fernet(self):
        if not HAS_CRYPTOGRAPHY or Fernet is None:
            raise RuntimeError("модуль cryptography не установлен")
        self.key_path.parent.mkdir(parents=True, exist_ok=True)
        try:
            key = self.key_path.read_bytes().strip()
            return Fernet(key)
        except (OSError, ValueError):
            key = Fernet.generate_key()
            _atomic_write_bytes(self.key_path, key)
            try:
                os.chmod(self.key_path, 0o600)
            except OSError:
                pass
            return Fernet(key)

    def _read_vault(self) -> dict[str, str]:
        try:
            value = json.loads(self.vault_path.read_text(encoding="utf-8"))
            return {str(key): str(token) for key, token in value.items()} if isinstance(value, dict) else {}
        except (OSError, ValueError, TypeError):
            return {}

    def get(self, profile_id: str) -> str:
        if not profile_id:
            return ""
        if HAS_KEYRING and keyring is not None:
            try:
                return str(keyring.get_password(self.service_name, profile_id) or "")
            except Exception:
                pass
        token = self._read_vault().get(profile_id, "")
        if token:
            try:
                if token.startswith("F1:") and HAS_CRYPTOGRAPHY:
                    return self._fernet().decrypt(token[3:].encode("ascii")).decode("utf-8")
                if token.startswith("S1:"):
                    return self._decrypt_portable(token)
            except (InvalidToken, OSError, UnicodeError, ValueError):
                return ""
        return ""

    def set(self, profile_id: str, secret: str) -> bool:
        if not profile_id:
            return False
        if not secret:
            self.delete(profile_id)
            return True
        if HAS_KEYRING and keyring is not None:
            try:
                keyring.set_password(self.service_name, profile_id, secret)
                return True
            except Exception:
                pass
        values = self._read_vault()
        values[profile_id] = (
            "F1:" + self._fernet().encrypt(secret.encode("utf-8")).decode("ascii")
            if HAS_CRYPTOGRAPHY
            else self._encrypt_portable(secret)
        )
        _atomic_write_json(self.vault_path, values)
        try:
            os.chmod(self.vault_path, 0o600)
        except OSError:
            pass
        return True

    def delete(self, profile_id: str) -> None:
        if not profile_id:
            return
        if HAS_KEYRING and keyring is not None:
            try:
                keyring.delete_password(self.service_name, profile_id)
            except Exception:
                pass
        values = self._read_vault()
        if profile_id in values:
            del values[profile_id]
            _atomic_write_json(self.vault_path, values)


class ProjectStore:
    """Транзакционное хранилище проектов, исходников и истории LiteraFlow."""

    def __init__(self, path: Path = DATABASE_FILE) -> None:
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._initialise()

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.path, timeout=8)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA synchronous=NORMAL")
        connection.execute("PRAGMA foreign_keys=ON")
        return connection

    @contextmanager
    def _session(self):
        """Открывает короткую транзакцию и всегда закрывает дескриптор БД."""

        connection = self._connect()
        try:
            with connection:
                yield connection
        finally:
            connection.close()

    def _backup_for_migration(self, current_version: int) -> Path | None:
        if not self.path.is_file() or self.path.stat().st_size <= 0:
            return None
        backup_path = self.path.with_name(f"{self.path.stem}.v{current_version}.bak{self.path.suffix}")
        if backup_path.exists():
            return backup_path
        source = sqlite3.connect(self.path, timeout=8)
        target = sqlite3.connect(backup_path, timeout=8)
        try:
            source.backup(target)
        finally:
            target.close()
            source.close()
        return backup_path

    def _initialise(self) -> None:
        with self._session() as connection:
            current_version = int(connection.execute("PRAGMA user_version").fetchone()[0])
        if current_version > DATABASE_SCHEMA_VERSION:
            raise RuntimeError(
                f"База LiteraFlow создана более новой версией: {current_version} > {DATABASE_SCHEMA_VERSION}"
            )
        if 0 < current_version < DATABASE_SCHEMA_VERSION:
            self._backup_for_migration(current_version)
        with self._session() as connection:
            connection.execute("PRAGMA journal_mode=WAL")
            connection.executescript(
                """
                BEGIN IMMEDIATE;
                CREATE TABLE IF NOT EXISTS projects (
                    project_id TEXT PRIMARY KEY,
                    title TEXT NOT NULL,
                    source_name TEXT NOT NULL,
                    source_path TEXT NOT NULL DEFAULT '',
                    updated_at TEXT NOT NULL,
                    segment_count INTEGER NOT NULL DEFAULT 0,
                    translated_count INTEGER NOT NULL DEFAULT 0,
                    confirmed_count INTEGER NOT NULL DEFAULT 0,
                    current_index INTEGER NOT NULL DEFAULT 0
                );
                CREATE INDEX IF NOT EXISTS projects_updated_idx ON projects(updated_at DESC);
                CREATE TABLE IF NOT EXISTS chapters (
                    project_id TEXT NOT NULL,
                    chapter_index INTEGER NOT NULL,
                    title TEXT NOT NULL,
                    start_segment INTEGER NOT NULL,
                    end_segment INTEGER NOT NULL,
                    PRIMARY KEY(project_id, chapter_index)
                );
                CREATE TABLE IF NOT EXISTS history (
                    project_id TEXT NOT NULL,
                    stack_name TEXT NOT NULL,
                    stack_index INTEGER NOT NULL,
                    reason TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    snapshot BLOB NOT NULL,
                    PRIMARY KEY(project_id, stack_name, stack_index)
                );
                CREATE TABLE IF NOT EXISTS project_sources (
                    project_id TEXT PRIMARY KEY,
                    source_name TEXT NOT NULL,
                    extension TEXT NOT NULL DEFAULT '',
                    source_hash TEXT NOT NULL,
                    source_blob BLOB NOT NULL,
                    original_size INTEGER NOT NULL DEFAULT 0,
                    metadata_json TEXT NOT NULL DEFAULT '{}',
                    stored_at TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS paragraphs (
                    project_id TEXT NOT NULL,
                    paragraph_index INTEGER NOT NULL,
                    source_text TEXT NOT NULL,
                    PRIMARY KEY(project_id, paragraph_index)
                );
                CREATE TABLE IF NOT EXISTS segments (
                    project_id TEXT NOT NULL,
                    segment_index INTEGER NOT NULL,
                    paragraph_index INTEGER NOT NULL,
                    source_text TEXT NOT NULL,
                    translation TEXT NOT NULL DEFAULT '',
                    status TEXT NOT NULL DEFAULT 'empty',
                    bookmark INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY(project_id, segment_index)
                );
                CREATE INDEX IF NOT EXISTS segments_project_paragraph_idx
                    ON segments(project_id, paragraph_index, segment_index);
                CREATE TABLE IF NOT EXISTS glossary_entries (
                    project_id TEXT NOT NULL,
                    entry_index INTEGER NOT NULL,
                    source TEXT NOT NULL,
                    target TEXT NOT NULL,
                    note TEXT NOT NULL DEFAULT '',
                    case_sensitive INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY(project_id, entry_index)
                );
                CREATE TABLE IF NOT EXISTS character_entries (
                    project_id TEXT NOT NULL,
                    entry_index INTEGER NOT NULL,
                    source TEXT NOT NULL,
                    target TEXT NOT NULL,
                    role TEXT NOT NULL DEFAULT '',
                    note TEXT NOT NULL DEFAULT '',
                    aliases_json TEXT NOT NULL DEFAULT '[]',
                    target_forms_json TEXT NOT NULL DEFAULT '[]',
                    relationships TEXT NOT NULL DEFAULT '',
                    voice TEXT NOT NULL DEFAULT '',
                    formality TEXT NOT NULL DEFAULT '',
                    PRIMARY KEY(project_id, entry_index)
                );
                CREATE TABLE IF NOT EXISTS project_dictionary (
                    project_id TEXT NOT NULL,
                    word TEXT NOT NULL,
                    PRIMARY KEY(project_id, word)
                );
                CREATE TABLE IF NOT EXISTS edit_examples (
                    project_id TEXT NOT NULL,
                    example_index INTEGER NOT NULL,
                    source TEXT NOT NULL,
                    draft TEXT NOT NULL DEFAULT '',
                    final TEXT NOT NULL,
                    PRIMARY KEY(project_id, example_index)
                );
                CREATE TABLE IF NOT EXISTS segment_variants (
                    project_id TEXT NOT NULL,
                    segment_index INTEGER NOT NULL,
                    slot TEXT NOT NULL CHECK(slot IN ('literal','literary','machine')),
                    label TEXT NOT NULL DEFAULT '',
                    text TEXT NOT NULL DEFAULT '',
                    provider TEXT NOT NULL DEFAULT '',
                    raw_text TEXT NOT NULL DEFAULT '',
                    updated_at TEXT NOT NULL,
                    PRIMARY KEY(project_id, segment_index, slot),
                    FOREIGN KEY(project_id, segment_index)
                        REFERENCES segments(project_id, segment_index) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS segment_variant_state (
                    project_id TEXT NOT NULL,
                    segment_index INTEGER NOT NULL,
                    active_slot TEXT NOT NULL DEFAULT 'literary'
                        CHECK(active_slot IN ('literal','literary','machine')),
                    PRIMARY KEY(project_id, segment_index),
                    FOREIGN KEY(project_id, segment_index)
                        REFERENCES segments(project_id, segment_index) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS change_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    project_id TEXT NOT NULL,
                    group_id TEXT NOT NULL,
                    entity_type TEXT NOT NULL,
                    entity_id TEXT NOT NULL,
                    field_name TEXT NOT NULL,
                    before_json TEXT NOT NULL,
                    after_json TEXT NOT NULL,
                    reason TEXT NOT NULL DEFAULT 'Изменение',
                    created_at TEXT NOT NULL
                );
                CREATE INDEX IF NOT EXISTS change_log_project_group_idx
                    ON change_log(project_id, group_id, id);
                CREATE TABLE IF NOT EXISTS segment_notes (
                    note_id TEXT PRIMARY KEY,
                    project_id TEXT NOT NULL,
                    segment_index INTEGER NOT NULL,
                    position INTEGER NOT NULL DEFAULT 0,
                    text TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL,
                    FOREIGN KEY(project_id, segment_index)
                        REFERENCES segments(project_id, segment_index) ON DELETE CASCADE
                );
                CREATE INDEX IF NOT EXISTS segment_notes_project_segment_idx
                    ON segment_notes(project_id, segment_index, position);
                CREATE TABLE IF NOT EXISTS secondary_sources (
                    source_id TEXT PRIMARY KEY,
                    project_id TEXT NOT NULL,
                    name TEXT NOT NULL,
                    language TEXT NOT NULL DEFAULT 'auto',
                    source_hash TEXT NOT NULL,
                    source_blob BLOB NOT NULL,
                    original_size INTEGER NOT NULL DEFAULT 0,
                    metadata_json TEXT NOT NULL DEFAULT '{}',
                    created_at TEXT NOT NULL
                );
                CREATE INDEX IF NOT EXISTS secondary_sources_project_idx
                    ON secondary_sources(project_id);
                CREATE TABLE IF NOT EXISTS secondary_segments (
                    source_id TEXT NOT NULL,
                    segment_index INTEGER NOT NULL,
                    paragraph_index INTEGER NOT NULL,
                    source_text TEXT NOT NULL,
                    PRIMARY KEY(source_id, segment_index),
                    FOREIGN KEY(source_id) REFERENCES secondary_sources(source_id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS segment_alignments (
                    project_id TEXT NOT NULL,
                    primary_segment_index INTEGER NOT NULL,
                    source_id TEXT NOT NULL,
                    secondary_segment_index INTEGER NOT NULL,
                    order_index INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY(project_id, primary_segment_index, source_id, secondary_segment_index),
                    FOREIGN KEY(project_id, primary_segment_index)
                        REFERENCES segments(project_id, segment_index) ON DELETE CASCADE,
                    FOREIGN KEY(source_id, secondary_segment_index)
                        REFERENCES secondary_segments(source_id, segment_index) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS honorific_rules (
                    rule_id TEXT PRIMARY KEY,
                    project_id TEXT NOT NULL,
                    source TEXT NOT NULL,
                    language TEXT NOT NULL DEFAULT 'auto',
                    category TEXT NOT NULL DEFAULT 'address',
                    policy TEXT NOT NULL DEFAULT 'warn'
                        CHECK(policy IN ('keep','transliterate','remove','replace','warn')),
                    target TEXT NOT NULL DEFAULT '',
                    priority INTEGER NOT NULL DEFAULT 0,
                    conditions_json TEXT NOT NULL DEFAULT '{}'
                );
                CREATE INDEX IF NOT EXISTS honorific_rules_project_idx
                    ON honorific_rules(project_id, priority DESC);
                CREATE TABLE IF NOT EXISTS segment_qa (
                    project_id TEXT NOT NULL,
                    segment_index INTEGER NOT NULL,
                    rule_code TEXT NOT NULL,
                    severity TEXT NOT NULL,
                    message TEXT NOT NULL,
                    content_revision INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY(project_id, segment_index, rule_code, message),
                    FOREIGN KEY(project_id, segment_index)
                        REFERENCES segments(project_id, segment_index) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS morph_cache (
                    dictionary_version TEXT NOT NULL,
                    token TEXT NOT NULL,
                    analysis_json TEXT NOT NULL,
                    last_used_at TEXT NOT NULL,
                    PRIMARY KEY(dictionary_version, token)
                );
                CREATE TABLE IF NOT EXISTS project_settings (
                    project_id TEXT NOT NULL,
                    key TEXT NOT NULL,
                    value_json TEXT NOT NULL,
                    PRIMARY KEY(project_id, key)
                );
                """
            )
            variant_columns = {
                str(row[1]) for row in connection.execute("PRAGMA table_info(segment_variants)").fetchall()
            }
            if "raw_text" not in variant_columns:
                connection.execute("ALTER TABLE segment_variants ADD COLUMN raw_text TEXT NOT NULL DEFAULT ''")
            connection.execute(f"PRAGMA user_version={DATABASE_SCHEMA_VERSION}")

    def upsert_project(
        self,
        project_id: str,
        *,
        title: str,
        source_name: str,
        source_path: str,
        segment_count: int,
        translated_count: int,
        confirmed_count: int,
        current_index: int,
    ) -> None:
        if not project_id:
            return
        with self._session() as connection:
            connection.execute(
                """
                INSERT INTO projects(project_id,title,source_name,source_path,updated_at,segment_count,translated_count,confirmed_count,current_index)
                VALUES(?,?,?,?,?,?,?,?,?)
                ON CONFLICT(project_id) DO UPDATE SET
                    title=excluded.title, source_name=excluded.source_name,
                    source_path=CASE WHEN excluded.source_path='' THEN projects.source_path ELSE excluded.source_path END,
                    updated_at=excluded.updated_at, segment_count=excluded.segment_count,
                    translated_count=excluded.translated_count, confirmed_count=excluded.confirmed_count,
                    current_index=excluded.current_index
                """,
                (
                    project_id,
                    title,
                    source_name,
                    source_path,
                    datetime.now().isoformat(timespec="seconds"),
                    int(segment_count),
                    int(translated_count),
                    int(confirmed_count),
                    int(current_index),
                ),
            )

    def list_projects(self, limit: int = 30) -> list[dict[str, Any]]:
        with self._session() as connection:
            rows = connection.execute(
                """
                SELECT projects.*,
                       EXISTS(SELECT 1 FROM project_sources WHERE project_sources.project_id=projects.project_id) AS has_source
                FROM projects ORDER BY updated_at DESC LIMIT ?
                """,
                (max(1, min(int(limit), 200)),),
            ).fetchall()
        return [dict(row) for row in rows]

    @staticmethod
    def _json(value: Any) -> str:
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"))

    @staticmethod
    def _load_json(value: str, default: Any) -> Any:
        try:
            result = json.loads(value)
        except (TypeError, ValueError):
            return default
        return result

    def save_source(
        self,
        project_id: str,
        *,
        source_name: str,
        extension: str,
        source_hash: str,
        source_bytes: bytes,
        metadata: dict[str, Any] | None = None,
    ) -> None:
        """Сохраняет сам исходник, чтобы проект открывался без внешнего файла."""

        if not project_id or not source_bytes:
            return
        with self._session() as connection:
            existing = connection.execute(
                "SELECT source_hash,original_size FROM project_sources WHERE project_id=?", (project_id,)
            ).fetchone()
        if existing is not None and existing["source_hash"] == source_hash and int(existing["original_size"] or 0) == len(source_bytes):
            with self._session() as connection:
                connection.execute(
                    "UPDATE project_sources SET source_name=?,extension=?,metadata_json=?,stored_at=? WHERE project_id=?",
                    (
                        source_name,
                        extension,
                        self._json(metadata or {}),
                        datetime.now().isoformat(timespec="seconds"),
                        project_id,
                    ),
                )
            return
        packed = zlib.compress(source_bytes, 6)
        with self._session() as connection:
            connection.execute(
                """
                INSERT INTO project_sources(project_id,source_name,extension,source_hash,source_blob,original_size,metadata_json,stored_at)
                VALUES(?,?,?,?,?,?,?,?)
                ON CONFLICT(project_id) DO UPDATE SET
                    source_name=excluded.source_name, extension=excluded.extension,
                    source_hash=excluded.source_hash, source_blob=excluded.source_blob,
                    original_size=excluded.original_size, metadata_json=excluded.metadata_json,
                    stored_at=excluded.stored_at
                """,
                (
                    project_id,
                    source_name,
                    extension,
                    source_hash,
                    sqlite3.Binary(packed),
                    len(source_bytes),
                    self._json(metadata or {}),
                    datetime.now().isoformat(timespec="seconds"),
                ),
            )

    def load_source(self, project_id: str) -> tuple[bytes, str, dict[str, Any]] | None:
        with self._session() as connection:
            row = connection.execute(
                "SELECT source_name,source_blob,original_size,metadata_json FROM project_sources WHERE project_id=?",
                (project_id,),
            ).fetchone()
        if row is None:
            return None
        try:
            data = zlib.decompress(bytes(row["source_blob"]))
        except (TypeError, ValueError, zlib.error) as exc:
            raise ValueError("встроенный исходник проекта повреждён") from exc
        expected_size = int(row["original_size"] or 0)
        if expected_size and len(data) != expected_size:
            raise ValueError("размер встроенного исходника не совпадает")
        metadata = self._load_json(str(row["metadata_json"] or "{}"), {})
        return data, str(row["source_name"] or "novel.txt"), metadata if isinstance(metadata, dict) else {}

    def replace_document(
        self,
        project_id: str,
        *,
        paragraphs: list[str],
        sentences: list[str],
        sentence_to_paragraph: list[int],
        translations: list[str],
        statuses: list[str],
        bookmarks: list[bool],
    ) -> None:
        """Атомарно заменяет нормализованное текстовое состояние проекта."""

        if len(sentences) != len(sentence_to_paragraph):
            raise ValueError("число сегментов не совпадает с картой абзацев")
        with self._session() as connection:
            connection.execute("DELETE FROM paragraphs WHERE project_id=?", (project_id,))
            connection.execute("DELETE FROM segments WHERE project_id=?", (project_id,))
            connection.executemany(
                "INSERT INTO paragraphs(project_id,paragraph_index,source_text) VALUES(?,?,?)",
                [(project_id, index, str(value)) for index, value in enumerate(paragraphs)],
            )
            connection.executemany(
                """
                INSERT INTO segments(project_id,segment_index,paragraph_index,source_text,translation,status,bookmark)
                VALUES(?,?,?,?,?,?,?)
                """,
                [
                    (
                        project_id,
                        index,
                        int(sentence_to_paragraph[index]),
                        str(source),
                        str(translations[index] if index < len(translations) else ""),
                        str(statuses[index] if index < len(statuses) else STATUS_EMPTY),
                        int(bool(bookmarks[index] if index < len(bookmarks) else False)),
                    )
                    for index, source in enumerate(sentences)
                ],
            )

    def upsert_segments(
        self,
        project_id: str,
        rows: Iterable[tuple[int, int, str, str, str, bool]],
    ) -> None:
        values = [
            (project_id, int(index), int(paragraph), source, translation, status, int(bool(bookmark)))
            for index, paragraph, source, translation, status, bookmark in rows
        ]
        if not values:
            return
        with self._session() as connection:
            connection.executemany(
                """
                INSERT INTO segments(project_id,segment_index,paragraph_index,source_text,translation,status,bookmark)
                VALUES(?,?,?,?,?,?,?)
                ON CONFLICT(project_id,segment_index) DO UPDATE SET
                    paragraph_index=excluded.paragraph_index, source_text=excluded.source_text,
                    translation=excluded.translation, status=excluded.status, bookmark=excluded.bookmark
                """,
                values,
            )

    def replace_references(
        self,
        project_id: str,
        *,
        glossary: Iterable[dict[str, Any]],
        characters: Iterable[dict[str, Any]],
        dictionary: Iterable[str],
        edit_examples: Iterable[dict[str, str]],
    ) -> None:
        with self._session() as connection:
            for table in ("glossary_entries", "character_entries", "project_dictionary", "edit_examples"):
                connection.execute(f"DELETE FROM {table} WHERE project_id=?", (project_id,))
            connection.executemany(
                """
                INSERT INTO glossary_entries(project_id,entry_index,source,target,note,case_sensitive)
                VALUES(?,?,?,?,?,?)
                """,
                [
                    (
                        project_id,
                        index,
                        str(entry.get("source", "")),
                        str(entry.get("target", "")),
                        str(entry.get("note", "")),
                        int(bool(entry.get("case_sensitive", False))),
                    )
                    for index, entry in enumerate(glossary)
                ],
            )
            connection.executemany(
                """
                INSERT INTO character_entries(
                    project_id,entry_index,source,target,role,note,aliases_json,target_forms_json,
                    relationships,voice,formality
                ) VALUES(?,?,?,?,?,?,?,?,?,?,?)
                """,
                [
                    (
                        project_id,
                        index,
                        str(entry.get("source", "")),
                        str(entry.get("target", "")),
                        str(entry.get("role", "")),
                        str(entry.get("note", "")),
                        self._json(entry.get("aliases", [])),
                        self._json(entry.get("target_forms", [])),
                        str(entry.get("relationships", "")),
                        str(entry.get("voice", "")),
                        str(entry.get("formality", "")),
                    )
                    for index, entry in enumerate(characters)
                ],
            )
            connection.executemany(
                "INSERT INTO project_dictionary(project_id,word) VALUES(?,?)",
                [(project_id, str(word)) for word in dictionary if str(word).strip()],
            )
            connection.executemany(
                "INSERT INTO edit_examples(project_id,example_index,source,draft,final) VALUES(?,?,?,?,?)",
                [
                    (project_id, index, str(item.get("source", "")), str(item.get("draft", "")), str(item.get("final", "")))
                    for index, item in enumerate(edit_examples)
                    if item.get("source") and item.get("final")
                ],
            )

    def load_document(self, project_id: str) -> dict[str, Any] | None:
        with self._session() as connection:
            project_row = connection.execute(
                "SELECT current_index FROM projects WHERE project_id=?", (project_id,)
            ).fetchone()
            paragraph_rows = connection.execute(
                "SELECT source_text FROM paragraphs WHERE project_id=? ORDER BY paragraph_index", (project_id,)
            ).fetchall()
            segment_rows = connection.execute(
                """
                SELECT segment_index,paragraph_index,source_text,translation,status,bookmark
                FROM segments WHERE project_id=? ORDER BY segment_index
                """,
                (project_id,),
            ).fetchall()
            if not segment_rows:
                return None
            glossary_rows = connection.execute(
                "SELECT source,target,note,case_sensitive FROM glossary_entries WHERE project_id=? ORDER BY entry_index",
                (project_id,),
            ).fetchall()
            character_rows = connection.execute(
                """
                SELECT source,target,role,note,aliases_json,target_forms_json,relationships,voice,formality
                FROM character_entries WHERE project_id=? ORDER BY entry_index
                """,
                (project_id,),
            ).fetchall()
            dictionary_rows = connection.execute(
                "SELECT word FROM project_dictionary WHERE project_id=? ORDER BY word COLLATE NOCASE", (project_id,)
            ).fetchall()
            example_rows = connection.execute(
                "SELECT source,draft,final FROM edit_examples WHERE project_id=? ORDER BY example_index", (project_id,)
            ).fetchall()
        return {
            "original_paragraphs": [str(row["source_text"]) for row in paragraph_rows],
            "sentences": [str(row["source_text"]) for row in segment_rows],
            "sentence_to_paragraph": [int(row["paragraph_index"]) for row in segment_rows],
            "translations": [str(row["translation"] or "") for row in segment_rows],
            "statuses": [str(row["status"] or STATUS_EMPTY) for row in segment_rows],
            "bookmarks": [bool(row["bookmark"]) for row in segment_rows],
            "glossary": [
                {"source": row["source"], "target": row["target"], "note": row["note"], "case_sensitive": bool(row["case_sensitive"])}
                for row in glossary_rows
            ],
            "characters": [
                {
                    "source": row["source"], "target": row["target"], "role": row["role"], "note": row["note"],
                    "aliases": self._load_json(row["aliases_json"], []),
                    "target_forms": self._load_json(row["target_forms_json"], []),
                    "relationships": row["relationships"], "voice": row["voice"], "formality": row["formality"],
                }
                for row in character_rows
            ],
            "custom_dictionary": [str(row["word"]) for row in dictionary_rows],
            "edit_examples": [dict(row) for row in example_rows],
            "current_index": int(project_row["current_index"] or 0) if project_row is not None else 0,
        }

    def replace_chapters(self, project_id: str, chapters: Iterable[dict[str, Any]]) -> None:
        if not project_id:
            return
        with self._session() as connection:
            connection.execute("DELETE FROM chapters WHERE project_id=?", (project_id,))
            connection.executemany(
                "INSERT INTO chapters(project_id,chapter_index,title,start_segment,end_segment) VALUES(?,?,?,?,?)",
                [
                    (
                        project_id,
                        int(index),
                        str(chapter.get("title", f"Глава {index + 1}")),
                        int(chapter.get("start", 0)),
                        int(chapter.get("end", 0)),
                    )
                    for index, chapter in enumerate(chapters)
                ],
            )

    @staticmethod
    def _pack_snapshot(snapshot: dict[str, Any]) -> bytes:
        return zlib.compress(json.dumps(snapshot, ensure_ascii=False, separators=(",", ":")).encode("utf-8"), 6)

    @staticmethod
    def _unpack_snapshot(value: bytes) -> dict[str, Any]:
        result = json.loads(zlib.decompress(value).decode("utf-8"))
        if not isinstance(result, dict):
            raise ValueError("неверный снимок истории")
        return result

    def save_history(self, project_id: str, undo: list[dict[str, Any]], redo: list[dict[str, Any]]) -> None:
        if not project_id:
            return
        with self._session() as connection:
            connection.execute("DELETE FROM history WHERE project_id=?", (project_id,))
            rows = []
            for stack_name, values in (("undo", undo[-40:]), ("redo", redo[-40:])):
                for index, item in enumerate(values):
                    rows.append(
                        (
                            project_id,
                            stack_name,
                            index,
                            str(item.get("reason", "Изменение")),
                            str(item.get("timestamp", "")),
                            self._pack_snapshot(item.get("snapshot", {})),
                        )
                    )
            connection.executemany(
                "INSERT INTO history(project_id,stack_name,stack_index,reason,created_at,snapshot) VALUES(?,?,?,?,?,?)",
                rows,
            )

    def load_history(self, project_id: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        stacks: dict[str, list[dict[str, Any]]] = {"undo": [], "redo": []}
        if not project_id:
            return stacks["undo"], stacks["redo"]
        with self._session() as connection:
            rows = connection.execute(
                "SELECT stack_name,reason,created_at,snapshot FROM history WHERE project_id=? ORDER BY stack_name,stack_index",
                (project_id,),
            ).fetchall()
        for row in rows:
            try:
                stacks[str(row["stack_name"])].append(
                    {"reason": row["reason"], "timestamp": row["created_at"], "snapshot": self._unpack_snapshot(row["snapshot"])}
                )
            except (KeyError, ValueError, TypeError, zlib.error, UnicodeError):
                continue
        return stacks["undo"], stacks["redo"]

    def upsert_segment_variants(self, project_id: str, rows: Iterable[dict[str, Any]]) -> None:
        values: list[tuple[Any, ...]] = []
        now = datetime.now().isoformat(timespec="seconds")
        for item in rows:
            slot = str(item.get("slot", "literary"))
            if slot not in TRANSLATION_VARIANT_SLOTS:
                continue
            values.append(
                (
                    project_id,
                    int(item.get("segment_index", 0)),
                    slot,
                    str(item.get("label", TRANSLATION_VARIANT_LABELS[slot])),
                    str(item.get("text", "")),
                    str(item.get("provider", "")),
                    str(item.get("raw_text", "")),
                    str(item.get("updated_at", now) or now),
                )
            )
        if not values:
            return
        with self._session() as connection:
            connection.executemany(
                """
                INSERT INTO segment_variants(project_id,segment_index,slot,label,text,provider,raw_text,updated_at)
                VALUES(?,?,?,?,?,?,?,?)
                ON CONFLICT(project_id,segment_index,slot) DO UPDATE SET
                    label=excluded.label,text=excluded.text,provider=excluded.provider,
                    raw_text=excluded.raw_text,updated_at=excluded.updated_at
                """,
                values,
            )

    def upsert_variant_states(self, project_id: str, rows: Iterable[tuple[int, str]]) -> None:
        values = [
            (project_id, int(index), slot if slot in TRANSLATION_VARIANT_SLOTS else "literary")
            for index, slot in rows
        ]
        if not values:
            return
        with self._session() as connection:
            connection.executemany(
                """
                INSERT INTO segment_variant_state(project_id,segment_index,active_slot)
                VALUES(?,?,?)
                ON CONFLICT(project_id,segment_index) DO UPDATE SET active_slot=excluded.active_slot
                """,
                values,
            )

    def load_segment_variants(self, project_id: str) -> tuple[dict[int, dict[str, dict[str, str]]], dict[int, str]]:
        variants: dict[int, dict[str, dict[str, str]]] = {}
        active: dict[int, str] = {}
        with self._session() as connection:
            rows = connection.execute(
                """
                SELECT segment_index,slot,label,text,provider,raw_text,updated_at
                FROM segment_variants WHERE project_id=? ORDER BY segment_index,slot
                """,
                (project_id,),
            ).fetchall()
            state_rows = connection.execute(
                "SELECT segment_index,active_slot FROM segment_variant_state WHERE project_id=?",
                (project_id,),
            ).fetchall()
        for row in rows:
            index = int(row["segment_index"])
            variants.setdefault(index, {})[str(row["slot"])] = {
                "label": str(row["label"] or TRANSLATION_VARIANT_LABELS.get(str(row["slot"]), "Вариант")),
                "text": str(row["text"] or ""),
                "provider": str(row["provider"] or ""),
                "raw_text": str(row["raw_text"] or ""),
                "updated_at": str(row["updated_at"] or ""),
            }
        for row in state_rows:
            slot = str(row["active_slot"] or "literary")
            active[int(row["segment_index"])] = slot if slot in TRANSLATION_VARIANT_SLOTS else "literary"
        return variants, active

    def replace_segment_notes(self, project_id: str, notes: Iterable[dict[str, Any]]) -> None:
        now = datetime.now().isoformat(timespec="seconds")
        rows = [
            (
                str(item.get("note_id") or uuid.uuid4().hex),
                project_id,
                int(item.get("segment_index", 0)),
                int(item.get("position", 0)),
                str(item.get("text", "")).strip(),
                str(item.get("created_at", now) or now),
                now,
            )
            for item in notes
            if str(item.get("text", "")).strip()
        ]
        with self._session() as connection:
            connection.execute("DELETE FROM segment_notes WHERE project_id=?", (project_id,))
            connection.executemany(
                """
                INSERT INTO segment_notes(note_id,project_id,segment_index,position,text,created_at,updated_at)
                VALUES(?,?,?,?,?,?,?)
                """,
                rows,
            )

    def load_segment_notes(self, project_id: str) -> list[dict[str, Any]]:
        with self._session() as connection:
            rows = connection.execute(
                """
                SELECT note_id,segment_index,position,text,created_at,updated_at
                FROM segment_notes WHERE project_id=? ORDER BY segment_index,position,note_id
                """,
                (project_id,),
            ).fetchall()
        return [dict(row) for row in rows]

    def replace_honorific_rules(self, project_id: str, rules: Iterable[dict[str, Any]]) -> None:
        rows = [
            (
                str(item.get("rule_id") or uuid.uuid4().hex),
                project_id,
                str(item.get("source", "")).strip(),
                str(item.get("language", "auto") or "auto"),
                str(item.get("category", "address") or "address"),
                str(item.get("policy", "warn") or "warn"),
                str(item.get("target", "")),
                int(item.get("priority", 0)),
                self._json(item.get("conditions", {})),
            )
            for item in rules
            if str(item.get("source", "")).strip()
        ]
        with self._session() as connection:
            connection.execute("DELETE FROM honorific_rules WHERE project_id=?", (project_id,))
            connection.executemany(
                """
                INSERT INTO honorific_rules(rule_id,project_id,source,language,category,policy,target,priority,conditions_json)
                VALUES(?,?,?,?,?,?,?,?,?)
                """,
                rows,
            )

    def load_honorific_rules(self, project_id: str) -> list[dict[str, Any]]:
        with self._session() as connection:
            rows = connection.execute(
                """
                SELECT rule_id,source,language,category,policy,target,priority,conditions_json
                FROM honorific_rules WHERE project_id=? ORDER BY priority DESC,source COLLATE NOCASE
                """,
                (project_id,),
            ).fetchall()
        return [
            {
                "rule_id": str(row["rule_id"]),
                "source": str(row["source"]),
                "language": str(row["language"]),
                "category": str(row["category"]),
                "policy": str(row["policy"]),
                "target": str(row["target"]),
                "priority": int(row["priority"]),
                "conditions": self._load_json(row["conditions_json"], {}),
            }
            for row in rows
        ]

    def save_secondary_source(
        self,
        project_id: str,
        *,
        source_id: str,
        name: str,
        language: str,
        source_hash: str,
        source_bytes: bytes,
        segments: list[str],
        mapping: list[int],
        metadata: dict[str, Any] | None = None,
    ) -> None:
        if len(segments) != len(mapping):
            raise ValueError("число Dual-RAW сегментов не совпадает с картой абзацев")
        packed = zlib.compress(source_bytes, 6)
        now = datetime.now().isoformat(timespec="seconds")
        with self._session() as connection:
            connection.execute(
                """
                INSERT INTO secondary_sources(source_id,project_id,name,language,source_hash,source_blob,original_size,metadata_json,created_at)
                VALUES(?,?,?,?,?,?,?,?,?)
                ON CONFLICT(source_id) DO UPDATE SET
                    name=excluded.name,language=excluded.language,source_hash=excluded.source_hash,
                    source_blob=excluded.source_blob,original_size=excluded.original_size,
                    metadata_json=excluded.metadata_json
                """,
                (
                    source_id,
                    project_id,
                    name,
                    language,
                    source_hash,
                    sqlite3.Binary(packed),
                    len(source_bytes),
                    self._json(metadata or {}),
                    now,
                ),
            )
            connection.execute("DELETE FROM secondary_segments WHERE source_id=?", (source_id,))
            connection.executemany(
                """
                INSERT INTO secondary_segments(source_id,segment_index,paragraph_index,source_text)
                VALUES(?,?,?,?)
                """,
                [(source_id, index, int(mapping[index]), str(text)) for index, text in enumerate(segments)],
            )

    def replace_segment_alignments(
        self,
        project_id: str,
        source_id: str,
        alignments: Iterable[tuple[int, int, int]],
    ) -> None:
        with self._session() as connection:
            connection.execute(
                "DELETE FROM segment_alignments WHERE project_id=? AND source_id=?",
                (project_id, source_id),
            )
            connection.executemany(
                """
                INSERT INTO segment_alignments(project_id,primary_segment_index,source_id,secondary_segment_index,order_index)
                VALUES(?,?,?,?,?)
                """,
                [
                    (project_id, int(primary), source_id, int(secondary), int(order))
                    for primary, secondary, order in alignments
                ],
            )

    def load_secondary_sources(self, project_id: str) -> list[dict[str, Any]]:
        with self._session() as connection:
            source_rows = connection.execute(
                """
                SELECT source_id,name,language,source_hash,source_blob,original_size,metadata_json
                FROM secondary_sources WHERE project_id=? ORDER BY created_at,source_id
                """,
                (project_id,),
            ).fetchall()
            segment_rows = connection.execute(
                """
                SELECT secondary_segments.source_id,segment_index,paragraph_index,source_text
                FROM secondary_segments JOIN secondary_sources USING(source_id)
                WHERE secondary_sources.project_id=? ORDER BY secondary_segments.source_id,segment_index
                """,
                (project_id,),
            ).fetchall()
            alignment_rows = connection.execute(
                """
                SELECT source_id,primary_segment_index,secondary_segment_index,order_index
                FROM segment_alignments WHERE project_id=?
                ORDER BY source_id,primary_segment_index,order_index
                """,
                (project_id,),
            ).fetchall()
        segments_by_source: dict[str, list[dict[str, Any]]] = {}
        for row in segment_rows:
            segments_by_source.setdefault(str(row["source_id"]), []).append(dict(row))
        alignments_by_source: dict[str, list[dict[str, int]]] = {}
        for row in alignment_rows:
            alignments_by_source.setdefault(str(row["source_id"]), []).append(
                {
                    "primary": int(row["primary_segment_index"]),
                    "secondary": int(row["secondary_segment_index"]),
                    "order": int(row["order_index"]),
                }
            )
        result: list[dict[str, Any]] = []
        for row in source_rows:
            source_id = str(row["source_id"])
            try:
                source_bytes = zlib.decompress(bytes(row["source_blob"]))
            except (TypeError, ValueError, zlib.error):
                source_bytes = b""
            result.append(
                {
                    "source_id": source_id,
                    "name": str(row["name"]),
                    "language": str(row["language"]),
                    "source_hash": str(row["source_hash"]),
                    "source_bytes": source_bytes,
                    "metadata": self._load_json(row["metadata_json"], {}),
                    "segments": segments_by_source.get(source_id, []),
                    "alignments": alignments_by_source.get(source_id, []),
                }
            )
        return result

    def delete_secondary_source(self, project_id: str, source_id: str) -> None:
        with self._session() as connection:
            connection.execute(
                "DELETE FROM segment_alignments WHERE project_id=? AND source_id=?",
                (project_id, source_id),
            )
            connection.execute(
                "DELETE FROM secondary_sources WHERE project_id=? AND source_id=?",
                (project_id, source_id),
            )

    def save_project_settings(self, project_id: str, values: dict[str, Any]) -> None:
        with self._session() as connection:
            connection.executemany(
                """
                INSERT INTO project_settings(project_id,key,value_json) VALUES(?,?,?)
                ON CONFLICT(project_id,key) DO UPDATE SET value_json=excluded.value_json
                """,
                [(project_id, str(key), self._json(value)) for key, value in values.items()],
            )

    def load_project_settings(self, project_id: str) -> dict[str, Any]:
        with self._session() as connection:
            rows = connection.execute(
                "SELECT key,value_json FROM project_settings WHERE project_id=?",
                (project_id,),
            ).fetchall()
        return {str(row["key"]): self._load_json(row["value_json"], None) for row in rows}

    def load_morphology_cache(self, token: str, dictionary_version: str = "pymorphy3-ru-v1") -> dict[str, Any] | None:
        key = _normalise_spaces(token).casefold()
        if not key:
            return None
        with self._session() as connection:
            row = connection.execute(
                "SELECT analysis_json FROM morph_cache WHERE dictionary_version=? AND token=?",
                (dictionary_version, key),
            ).fetchone()
            if row is not None:
                connection.execute(
                    "UPDATE morph_cache SET last_used_at=? WHERE dictionary_version=? AND token=?",
                    (datetime.now().isoformat(timespec="seconds"), dictionary_version, key),
                )
        if row is None:
            return None
        value = self._load_json(str(row["analysis_json"]), None)
        return value if isinstance(value, dict) else None

    def save_morphology_cache(
        self,
        token: str,
        analysis: dict[str, Any],
        dictionary_version: str = "pymorphy3-ru-v1",
    ) -> None:
        key = _normalise_spaces(token).casefold()
        if not key or not analysis:
            return
        with self._session() as connection:
            connection.execute(
                """
                INSERT INTO morph_cache(dictionary_version,token,analysis_json,last_used_at)
                VALUES(?,?,?,?)
                ON CONFLICT(dictionary_version,token) DO UPDATE SET
                    analysis_json=excluded.analysis_json,last_used_at=excluded.last_used_at
                """,
                (
                    dictionary_version,
                    key,
                    self._json(analysis),
                    datetime.now().isoformat(timespec="seconds"),
                ),
            )
            # Общий кэш ограничен, чтобы словарь не раздувал мобильную БД.
            connection.execute(
                """
                DELETE FROM morph_cache WHERE rowid IN (
                    SELECT rowid FROM morph_cache ORDER BY last_used_at DESC LIMIT -1 OFFSET 12000
                )
                """
            )


def _deep_default_config() -> dict[str, Any]:
    return json.loads(json.dumps(DEFAULT_CONFIG, ensure_ascii=False))


def normalise_api_profiles(value: Any, legacy: dict[str, Any] | None = None) -> list[dict[str, str]]:
    profiles: list[dict[str, str]] = []
    for raw in value if isinstance(value, list) else []:
        if not isinstance(raw, dict):
            continue
        profile_id = re.sub(r"[^a-zA-Z0-9_.-]", "", str(raw.get("id", ""))) or uuid.uuid4().hex
        name = str(raw.get("name", "")).strip() or "API-профиль"
        url = str(raw.get("url", "")).strip()
        model = str(raw.get("model", "")).strip()
        headers = str(raw.get("headers", "")).strip()
        key_header = str(raw.get("key_header", "Authorization") or "Authorization").strip()
        if url or model:
            profiles.append({"id": profile_id, "name": name, "url": url, "model": model, "headers": headers, "key_header": key_header})
    if not profiles and legacy and (legacy.get("custom_api_url") or legacy.get("custom_api_model")):
        profiles.append(
            {
                "id": "default",
                "name": str(legacy.get("custom_api_name", "Мой API") or "Мой API"),
                "url": str(legacy.get("custom_api_url", DEFAULT_CONFIG["custom_api_url"]) or DEFAULT_CONFIG["custom_api_url"]),
                "model": str(legacy.get("custom_api_model", "") or ""),
                "headers": str(legacy.get("custom_api_headers", "") or ""),
                "key_header": str(legacy.get("custom_api_key_header", "Authorization") or "Authorization"),
            }
        )
    seen: set[str] = set()
    unique: list[dict[str, str]] = []
    for profile in profiles:
        if profile["id"] in seen:
            profile["id"] = uuid.uuid4().hex
        seen.add(profile["id"])
        unique.append(profile)
    return unique[:20]


def _atomic_write_bytes(path: str | Path, data: bytes) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(prefix=f".{target.name}.", suffix=".tmp", dir=str(target.parent))
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp_name, target)
    except Exception:
        try:
            os.unlink(temp_name)
        except OSError:
            pass
        raise


def _atomic_write_json(path: str | Path, payload: dict[str, Any]) -> None:
    raw = json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8")
    _atomic_write_bytes(path, raw)


def load_config() -> dict[str, Any]:
    config = _deep_default_config()
    loaded_config: dict[str, Any] = {}
    try:
        with CONFIG_FILE.open("r", encoding="utf-8") as stream:
            loaded = json.load(stream)
        if isinstance(loaded, dict):
            loaded_config = loaded
            config.update(loaded_config)
    except (OSError, ValueError, TypeError):
        pass

    try:
        loaded_version = int(loaded_config.get("config_version", 0))
    except (TypeError, ValueError):
        loaded_version = 0
    if loaded_config and loaded_version < 3:
        # В старых версиях Ollama была навязчивым значением по умолчанию.
        # Один раз переводим такие настройки на тихий онлайн-помощник.
        config["api_type"] = "google"
        config["show_local_ai"] = False
        config["auto_fetch"] = False
    config["config_version"] = DEFAULT_CONFIG["config_version"]
    if config.get("api_type") not in {"ollama", "google", "custom"}:
        config["api_type"] = "google"
    config["show_local_ai"] = bool(config.get("show_local_ai", False))
    if config["api_type"] == "ollama":
        config["show_local_ai"] = True
    config["remember_api_key"] = bool(config.get("remember_api_key", False))
    # Старый открытый ключ живёт только до миграции в защищённое хранилище.
    config["_legacy_api_key"] = str(config.get("custom_api_key", "") or "") if config["remember_api_key"] else ""
    config["custom_api_key"] = ""
    config["api_profiles"] = normalise_api_profiles(config.get("api_profiles"), config)
    profile_ids = {profile["id"] for profile in config["api_profiles"]}
    if config.get("active_api_profile") not in profile_ids:
        config["active_api_profile"] = config["api_profiles"][0]["id"] if config["api_profiles"] else ""
    config["fallback_enabled"] = bool(config.get("fallback_enabled", False))
    raw_order = config.get("fallback_order")
    order = [value for value in raw_order if value in {"google", "custom", "ollama"}] if isinstance(raw_order, list) else []
    config["fallback_order"] = list(dict.fromkeys(order or DEFAULT_CONFIG["fallback_order"]))
    if config.get("spellcheck_mode") not in {"off", "local", "languagetool"}:
        config["spellcheck_mode"] = "off"
    if config.get("theme") not in {"dark", "light"}:
        config["theme"] = "dark"
    if config.get("segmentation_method") not in {"simple", "advanced"}:
        config["segmentation_method"] = "advanced"
    if config.get("translation_style") not in STYLE_INSTRUCTIONS:
        config["translation_style"] = "literary"
    if config.get("accent_color_preset") not in ACCENT_PRESETS:
        config["accent_color_preset"] = "cyan"
    try:
        config["font_size"] = max(12, min(24, int(config.get("font_size", 14))))
    except (TypeError, ValueError):
        config["font_size"] = 14
    config["short_word_nbsp"] = bool(config.get("short_word_nbsp", True))
    config["send_neighbor_context"] = bool(config.get("send_neighbor_context", True))
    config["short_word_nbsp_words"] = str(
        config.get("short_word_nbsp_words", DEFAULT_CONFIG["short_word_nbsp_words"])
        or DEFAULT_CONFIG["short_word_nbsp_words"]
    )
    try:
        config["google_request_interval"] = max(0.8, min(10.0, float(config.get("google_request_interval", 1.0))))
    except (TypeError, ValueError):
        config["google_request_interval"] = 1.0
    symbols = config.get("mobile_symbol_order", DEFAULT_CONFIG["mobile_symbol_order"])
    config["mobile_symbol_order"] = [str(value) for value in symbols if str(value)][:12] if isinstance(symbols, list) else list(DEFAULT_CONFIG["mobile_symbol_order"])
    if config.get("complex_format_policy") not in {"error", "clean", "keep_original"}:
        config["complex_format_policy"] = "error"
    recent = config.get("recent_files")
    config["recent_files"] = [str(item) for item in recent[:5] if item] if isinstance(recent, list) else []
    return config


def save_config(config: dict[str, Any]) -> None:
    payload = dict(config)
    payload.pop("_legacy_api_key", None)
    # Секреты никогда не попадают в обычный JSON настроек.
    payload["custom_api_key"] = ""
    payload["api_profiles"] = normalise_api_profiles(payload.get("api_profiles"), payload)
    _atomic_write_json(CONFIG_FILE, payload)


def _normalise_spaces(text: str) -> str:
    return re.sub(r"[\t\u00a0 ]+", " ", text).strip()


def _looks_like_nonterminal_abbreviation(candidate: str, next_character: str) -> bool:
    lowered = candidate.lower().rstrip("\"'»”’)]}")
    last_token_match = re.search(r"(?:^|\s)([^\s]+)$", lowered)
    last_token = last_token_match.group(1) if last_token_match else lowered
    if last_token in NON_TERMINAL_ABBREVIATIONS:
        return True
    if re.search(r"(?:^|\s)[a-zа-яё]\.$", lowered, flags=re.IGNORECASE):
        return True
    if re.search(r"(?:[a-zа-яё]\.){2,}$", lowered, flags=re.IGNORECASE):
        return next_character.islower() or next_character.isdigit()
    if last_token in ABBREVIATIONS:
        return next_character.islower() or next_character.isdigit()
    return False


def split_sentences(paragraph: str, method: str = "advanced") -> list[str]:
    """Разбивает один абзац, не теряя кавычки и знаки препинания."""

    text = _normalise_spaces(paragraph)
    if not text:
        return []

    result: list[str] = []
    start = 0
    index = 0
    length = len(text)
    closers = "\"'»”’)]}"

    while index < length:
        char = text[index]
        if char not in ".!?…":
            index += 1
            continue

        punctuation_start = index
        while index + 1 < length and text[index + 1] in ".!?…":
            index += 1
        while index + 1 < length and text[index + 1] in closers:
            index += 1

        after = index + 1
        if after < length and not text[after].isspace():
            index += 1
            continue

        next_pos = after
        while next_pos < length and text[next_pos].isspace():
            next_pos += 1

        candidate = text[start:after].strip()
        should_split = bool(candidate) and (next_pos >= length or next_pos > after)
        if should_split and method == "advanced":
            punctuation = text[punctuation_start]
            previous = text[punctuation_start - 1] if punctuation_start else ""
            following = text[punctuation_start + 1] if punctuation_start + 1 < length else ""
            if punctuation == "." and previous.isdigit() and following.isdigit():
                should_split = False
            elif punctuation == ".":
                visible_next = text[next_pos] if next_pos < length else ""
                if visible_next in "\"'«“‘([{" and next_pos + 1 < length:
                    visible_next = text[next_pos + 1]
                if _looks_like_nonterminal_abbreviation(candidate, visible_next):
                    should_split = False
                elif visible_next.islower():
                    should_split = False

        if should_split:
            result.append(candidate)
            start = next_pos
            index = next_pos
        else:
            index += 1

    tail = text[start:].strip()
    if tail:
        result.append(tail)
    return result or [text]


def segment_paragraphs(paragraphs: Iterable[str], method: str = "advanced") -> tuple[list[str], list[int]]:
    sentences: list[str] = []
    sentence_to_paragraph: list[int] = []
    for paragraph_index, paragraph in enumerate(paragraphs):
        for sentence in split_sentences(paragraph, method):
            sentences.append(sentence)
            sentence_to_paragraph.append(paragraph_index)
    return sentences, sentence_to_paragraph


def proportional_segment_alignments(primary_count: int, secondary_count: int) -> list[tuple[int, int, int]]:
    """Строит безопасную первичную 0..N-привязку Dual-RAW по позиции."""

    if primary_count <= 0 or secondary_count <= 0:
        return []
    result: list[tuple[int, int, int]] = []
    for primary in range(primary_count):
        start = (primary * secondary_count) // primary_count
        end = ((primary + 1) * secondary_count) // primary_count
        if end <= start and start < secondary_count:
            end = start + 1
        for order, secondary in enumerate(range(start, min(end, secondary_count))):
            result.append((primary, secondary, order))
    return result


def detect_chapters(paragraphs: list[str], sentence_to_paragraph: list[int]) -> list[dict[str, Any]]:
    """Находит главы по типичным заголовкам и возвращает диапазоны сегментов."""

    if not sentence_to_paragraph:
        return []
    heading_pattern = re.compile(
        r"^(?:#{1,6}\s*)?(?:глава|часть|том|книга|пролог|эпилог|chapter|part|book)\b",
        re.IGNORECASE,
    )
    starts: list[tuple[int, str]] = [(0, "Начало")]
    first_segment_for_paragraph: dict[int, int] = {}
    for segment_index, paragraph_index in enumerate(sentence_to_paragraph):
        first_segment_for_paragraph.setdefault(paragraph_index, segment_index)
    for paragraph_index, paragraph in enumerate(paragraphs):
        title = _normalise_spaces(paragraph).lstrip("# ")
        if not title or len(title) > 120 or not heading_pattern.search(title):
            continue
        segment_index = first_segment_for_paragraph.get(paragraph_index)
        if segment_index is None:
            continue
        if segment_index == 0:
            starts[0] = (0, title)
        elif all(existing_index != segment_index for existing_index, _ in starts):
            starts.append((segment_index, title))
    starts.sort()
    return [
        {
            "title": title or f"Глава {index + 1}",
            "start": start,
            "end": (starts[index + 1][0] - 1) if index + 1 < len(starts) else len(sentence_to_paragraph) - 1,
        }
        for index, (start, title) in enumerate(starts)
    ]


DEFAULT_SHORT_NBSP_WORDS = ("а", "в", "и", "к", "о", "с", "у", "но", "на", "по", "во", "ко", "со")


def _typography_quotes(value: str) -> str:
    """Преобразует прямые кавычки с учётом контекста и вложенности."""

    result: list[str] = []
    levels: list[int] = []
    opening_context = "\n\r\t ([{—–-:;"
    closing_context = "\n\r\t .,!?;:)]}»”"
    length = len(value)
    for index, char in enumerate(value):
        if char in {"«", "„"}:
            levels.append(len(levels) % 2)
            result.append(char)
            continue
        if char in {"»", "“"}:
            if levels:
                levels.pop()
            result.append(char)
            continue
        if char != '"':
            result.append(char)
            continue
        previous = value[index - 1] if index else "\n"
        following = value[index + 1] if index + 1 < length else "\n"
        looks_open = previous in opening_context and following not in closing_context
        looks_close = previous not in opening_context and following in closing_context
        if looks_open and not looks_close:
            opening = True
        elif looks_close and not looks_open:
            opening = False
        else:
            opening = not levels
        if opening:
            level = len(levels) % 2
            levels.append(level)
            result.append("«" if level == 0 else "„")
        else:
            level = levels.pop() if levels else 0
            result.append("»" if level == 0 else "“")
    return "".join(result)


def _apply_short_word_nbsp(value: str, words: Iterable[str]) -> str:
    cleaned = sorted({str(word).strip() for word in words if str(word).strip()}, key=len, reverse=True)
    if not cleaned:
        return value
    pattern = re.compile(
        r"(?<![\w-])(" + "|".join(re.escape(word) for word in cleaned) + r")[ \t]+(?=[^\s])",
        flags=re.IGNORECASE,
    )
    # Не трогаем фрагменты кода в обратных кавычках.
    parts = value.split("`")
    return "`".join(pattern.sub(lambda match: match.group(1) + "\u00a0", part) if index % 2 == 0 else part for index, part in enumerate(parts))


def apply_russian_typography(
    text: str,
    *,
    use_short_nbsp: bool = True,
    short_words: Iterable[str] = DEFAULT_SHORT_NBSP_WORDS,
) -> str:
    """Приводит текст к русской типографике без уничтожения существующих NBSP."""

    if not text:
        return ""
    result_lines: list[str] = []
    for source_line in text.splitlines() or [text]:
        protected: list[str] = []

        def protect(match: re.Match[str]) -> str:
            protected.append(match.group(0))
            return f"\ue000{len(protected) - 1}\ue001"

        # Код и XML/HTML-подобные теги — непрозрачные токены: типографика
        # никогда не меняет их содержимое.
        line = re.sub(r"`[^`]*`|<[^<>\n]+>", protect, source_line)
        line = re.sub(r"[ \t]+", " ", line).strip()
        line = re.sub(r"\.{3,}", "…", line)
        line = re.sub(r"[ \t]+([,.;:!?…])", r"\1", line)
        line = re.sub(r'(?<!\d)([,;:!?])(?![\s"»”’\]\)}]|$)', r"\1 ", line)
        line = re.sub(r'(?<!\d)\.(?![\s"»”’\]\)}]|\d|$)', ". ", line)
        line = re.sub(r"[ \t]+-[ \t]+", " — ", line)
        line = re.sub(r"^[-–—][ \t]*", "— ", line)
        line = _typography_quotes(line)
        if use_short_nbsp:
            line = _apply_short_word_nbsp(line, short_words)
        for token_index, token in enumerate(protected):
            line = line.replace(f"\ue000{token_index}\ue001", token)
        result_lines.append(line)
    return "\n".join(result_lines)


def parse_tl_notes(value: str) -> tuple[str, list[dict[str, Any]]]:
    """Извлекает `[note: ...]`, сохраняя незакрытую разметку как обычный текст."""

    text = value or ""
    output: list[str] = []
    notes: list[dict[str, Any]] = []
    index = 0
    while index < len(text):
        if text[index:index + 6].casefold() != "[note:":
            output.append(text[index])
            index += 1
            continue
        cursor = index + 6
        note_chars: list[str] = []
        closed = False
        while cursor < len(text):
            if text[cursor] == "\\" and cursor + 1 < len(text) and text[cursor + 1] == "]":
                note_chars.append("]")
                cursor += 2
                continue
            if text[cursor] == "]":
                closed = True
                break
            note_chars.append(text[cursor])
            cursor += 1
        note_text = "".join(note_chars).strip()
        if not closed or not note_text:
            output.append(text[index])
            index += 1
            continue
        notes.append(
            {
                "position": len("".join(output)),
                "text": note_text,
                "source_start": index,
                "source_end": cursor + 1,
            }
        )
        index = cursor + 1
    return "".join(output), notes


def _term_present(text: str, term: str, *, case_sensitive: bool = False) -> bool:
    if not term:
        return False
    haystack = text if case_sensitive else text.casefold()
    needle = term if case_sensitive else term.casefold()
    return needle in haystack


def qa_issue_severity(issue: str) -> str:
    critical_markers = (
        "числа", "плейсхолдер", "тег", "Не закрыты", "Термин", "Имя персонажа",
    )
    style_markers = ("Типографика", "Прямые кавычки", "Дефис вместо тире")
    if any(marker in issue for marker in critical_markers):
        return "error"
    if any(marker in issue for marker in style_markers):
        return "style"
    return "warning"


def qa_issue_severity_title(issue: str) -> str:
    return {"error": "ошибка", "warning": "проверить", "style": "стиль"}[qa_issue_severity(issue)]


def summarize_export_readiness(
    translations: Iterable[str],
    statuses: Iterable[str],
    qa_issues: Iterable[Iterable[str]],
) -> dict[str, int]:
    """Возвращает компактную, пригодную для UI сводку перед экспортом."""

    translation_values = [str(value) for value in translations]
    status_values = [str(value) for value in statuses]
    issue_values = [list(items) for items in qa_issues]
    severity_counts: Counter[str] = Counter(
        qa_issue_severity(issue)
        for issues in issue_values
        for issue in issues
    )
    total = len(translation_values)
    empty = sum(not value.strip() for value in translation_values)
    return {
        "total": total,
        "empty": empty,
        "translated": total - empty,
        "draft": sum(value == STATUS_DRAFT for value in status_values),
        "confirmed": sum(value == STATUS_CONFIRMED for value in status_values),
        "qa_segments": sum(bool(items) for items in issue_values),
        "qa_errors": severity_counts["error"],
        "qa_warnings": severity_counts["warning"],
        "qa_style": severity_counts["style"],
    }


def chapter_progress_statistics(
    start: int,
    end: int,
    translations: list[str],
    statuses: list[str],
    bookmarks: list[bool],
    qa_issues: list[list[str]],
) -> dict[str, int | float]:
    """Считает прогресс главы без создания Flet-контролов."""

    stop = min(max(start, end) + 1, len(translations))
    start = max(0, min(start, stop))
    indices = range(start, stop)
    total = max(0, stop - start)
    confirmed = sum(index < len(statuses) and statuses[index] == STATUS_CONFIRMED for index in indices)
    empty = sum(not translations[index].strip() for index in range(start, stop))
    drafts = sum(index < len(statuses) and statuses[index] == STATUS_DRAFT for index in range(start, stop))
    issues = sum(index < len(qa_issues) and bool(qa_issues[index]) for index in range(start, stop))
    marked = sum(index < len(bookmarks) and bool(bookmarks[index]) for index in range(start, stop))
    return {
        "total": total,
        "confirmed": confirmed,
        "empty": empty,
        "draft": drafts,
        "qa": issues,
        "bookmarks": marked,
        "progress": confirmed / total if total else 0.0,
    }


def qa_issues_for_segment(
    source: str,
    translation: str,
    target_lang: str = "ru",
    glossary: Iterable[dict[str, Any]] = (),
    characters: Iterable[dict[str, Any]] = (),
    honorific_rules: Iterable[dict[str, Any]] = (),
) -> list[str]:
    """Локальные QA-проверки без отправки текста во внешние сервисы."""

    if not translation.strip():
        return []

    issues: list[str] = []
    if translation != translation.strip():
        issues.append("Пробел в начале или конце")
    if re.search(r"[ \t]{2,}", translation):
        issues.append("Двойные пробелы")

    number_pattern = r"\d+(?:[.,]\d+)?"
    source_numbers = sorted(value.replace(",", ".") for value in re.findall(number_pattern, source))
    translated_numbers = sorted(value.replace(",", ".") for value in re.findall(number_pattern, translation))
    if source_numbers != translated_numbers:
        issues.append("Проверьте числа")

    placeholder_pattern = r"\{\{[^{}]+\}\}|\{[^{}\n]+\}|%[A-Za-z]|\$[A-Za-z_]\w*|<[^<>\n]+>"
    if Counter(re.findall(placeholder_pattern, source)) != Counter(re.findall(placeholder_pattern, translation)):
        issues.append("Проверьте плейсхолдеры или теги")

    for opener, closer, title in (("(", ")", "круглые скобки"), ("[", "]", "квадратные скобки")):
        if translation.count(opener) != translation.count(closer):
            issues.append(f"Не закрыты {title}")

    straight_quotes = translation.count('"')
    if straight_quotes % 2 or translation.count("«") != translation.count("»"):
        issues.append("Не закрыты кавычки")

    source_marks = set(re.findall(r"[!?]", source.rstrip("\"'»”’)]}")))
    translated_marks = set(re.findall(r"[!?]", translation.rstrip("\"'»”’)]}")))
    if source_marks and not source_marks.issubset(translated_marks):
        issues.append("Проверьте ! и ?")

    source_end = re.search(r"[.!?…][\"'»”’\])}]*$", source.strip())
    target_end = re.search(r"[.!?…][\"'»”’\])}]*$", translation.strip())
    if source_end and not target_end:
        issues.append("Возможно, потерян конечный знак")

    if re.search(r"\b([A-Za-zА-Яа-яЁё]{3,})\s+\1\b", translation, flags=re.IGNORECASE):
        issues.append("Повтор слова")

    if target_lang == "ru":
        latin_words = re.findall(r"\b[A-Za-z]{3,}\b", translation)
        if len(latin_words) >= 3:
            issues.append("Возможно, остался непереведённый текст")
        if '"' in translation:
            issues.append("Прямые кавычки вместо «ёлочек»")
        if "..." in translation:
            issues.append("Типографика: замените три точки на многоточие")
        if re.search(r"(?m)^\s*[-–]\s+", translation):
            issues.append("Дефис вместо тире в реплике")
        if re.search(r"(?:[A-Za-z][А-Яа-яЁё]|[А-Яа-яЁё][A-Za-z])", translation):
            issues.append("Смешаны латинские и кириллические буквы")

    compact_source = re.sub(r"\s+", "", source)
    compact_target = re.sub(r"\s+", "", translation)
    if len(compact_source) >= 20 and compact_target:
        ratio = len(compact_target) / len(compact_source)
        if ratio < 0.28:
            issues.append("Перевод подозрительно короткий")
        elif ratio > 3.2:
            issues.append("Перевод подозрительно длинный")

    if source.count("\n") != translation.count("\n") and "\n" in source:
        issues.append("Проверьте переносы строк")

    for entry in glossary:
        source_term = str(entry.get("source", "")).strip()
        target_term = str(entry.get("target", "")).strip()
        case_sensitive = bool(entry.get("case_sensitive", False))
        if source_term and target_term and _term_present(source, source_term, case_sensitive=case_sensitive):
            if not _term_present(translation, target_term, case_sensitive=case_sensitive):
                issues.append(f"Термин «{source_term}» ожидается как «{target_term}»")

    for entry in characters:
        source_name = str(entry.get("source", "")).strip()
        source_variants = [source_name, *[str(value).strip() for value in entry.get("aliases", [])]]
        target_name = str(entry.get("target", "")).strip()
        saved_forms = [str(value).strip() for value in entry.get("target_forms", [])]
        generated_forms = list(russian_word_forms(target_name)) if target_name and not saved_forms else []
        target_variants = [target_name, *saved_forms, *generated_forms]
        used_source = next((value for value in source_variants if value and _term_present(source, value)), "")
        if used_source and target_name and not any(value and _term_present(translation, value) for value in target_variants):
            issues.append(f"Имя персонажа «{used_source}» ожидается как «{target_name}» или его форма")
    for rule in honorific_rules:
        marker = str(rule.get("source", "")).strip()
        if not marker or not _term_present(source, marker):
            continue
        policy = str(rule.get("policy", "warn"))
        target = str(rule.get("target", "")).strip()
        if policy == "warn":
            issues.append(f"Обращение «{marker}»: проверьте правило проекта")
        elif policy in {"replace", "transliterate"} and target and not _term_present(translation, target):
            issues.append(f"Обращение «{marker}» ожидается как «{target}»")
        elif policy == "remove" and _term_present(translation, marker):
            issues.append(f"Обращение «{marker}» помечено для удаления")
    return issues


def _memory_key(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip()).casefold()


def _language_matches(left: str, right: str) -> bool:
    if left == "auto" or right == "auto":
        return True
    return left.casefold() == right.casefold() or left.split("-", 1)[0].casefold() == right.split("-", 1)[0].casefold()


def load_translation_memory(path: Path = TRANSLATION_MEMORY_FILE) -> list[dict[str, Any]]:
    try:
        with path.open("r", encoding="utf-8") as stream:
            payload = json.load(stream)
    except (OSError, ValueError, TypeError):
        return []
    entries = payload.get("entries", []) if isinstance(payload, dict) else []
    result: list[dict[str, Any]] = []
    for entry in entries if isinstance(entries, list) else []:
        if not isinstance(entry, dict) or not str(entry.get("source", "")).strip() or not str(entry.get("target", "")).strip():
            continue
        try:
            uses = max(1, int(entry.get("uses", 1) or 1))
        except (TypeError, ValueError):
            uses = 1
        result.append(
            {
                "source": str(entry["source"]),
                "target": str(entry["target"]),
                "source_lang": str(entry.get("source_lang", "auto")),
                "target_lang": str(entry.get("target_lang", "ru")),
                "uses": uses,
                "updated_at": str(entry.get("updated_at", "")),
            }
        )
    return result[-5000:]


def save_translation_memory(entries: list[dict[str, Any]], path: Path = TRANSLATION_MEMORY_FILE) -> None:
    _atomic_write_json(
        path,
        {
            "version": 1,
            "updated_at": datetime.now().isoformat(timespec="seconds"),
            "entries": entries[-5000:],
        },
    )


def remember_translation_pair(
    entries: list[dict[str, Any]],
    source: str,
    target: str,
    source_lang: str,
    target_lang: str,
) -> None:
    source_key = _memory_key(source)
    if not source_key or not target.strip():
        return
    for index, entry in enumerate(entries):
        if (
            _memory_key(str(entry.get("source", ""))) == source_key
            and entry.get("source_lang", "auto") == source_lang
            and entry.get("target_lang", "ru") == target_lang
        ):
            entry["source"] = source.strip()
            entry["target"] = target.strip()
            entry["uses"] = int(entry.get("uses", 1) or 1) + 1
            entry["updated_at"] = datetime.now().isoformat(timespec="seconds")
            entries.append(entries.pop(index))
            return
    entries.append(
        {
            "source": source.strip(),
            "target": target.strip(),
            "source_lang": source_lang,
            "target_lang": target_lang,
            "uses": 1,
            "updated_at": datetime.now().isoformat(timespec="seconds"),
        }
    )
    del entries[:-5000]


def find_translation_memory_matches(
    entries: Iterable[dict[str, Any]],
    source: str,
    source_lang: str,
    target_lang: str,
    *,
    limit: int = 5,
    threshold: float = 0.58,
) -> list[tuple[float, dict[str, Any]]]:
    query = _memory_key(source)
    if not query:
        return []
    matches: list[tuple[float, dict[str, Any]]] = []
    ordered_entries = entries if isinstance(entries, list) else list(entries)
    for entry in reversed(ordered_entries):
        if not _language_matches(str(entry.get("target_lang", "ru")), target_lang):
            continue
        entry_source_lang = entry.get("source_lang", "auto")
        if not _language_matches(str(entry_source_lang), source_lang):
            continue
        candidate = _memory_key(str(entry.get("source", "")))
        if not candidate:
            continue
        if candidate == query:
            return [(1.0, entry)]
        else:
            length_ratio = min(len(candidate), len(query)) / max(len(candidate), len(query))
            if length_ratio < 0.4:
                continue
            score = SequenceMatcher(None, query, candidate).ratio()
        if score >= threshold:
            matches.append((score, entry))
    matches.sort(key=lambda item: (item[0], int(item[1].get("uses", 1) or 1)), reverse=True)
    return matches[:limit]


def make_tmx_bytes(entries: Iterable[dict[str, Any]], source_lang: str = "en", target_lang: str = "ru") -> bytes:
    root = ET.Element("tmx", {"version": "1.4"})
    ET.SubElement(
        root,
        "header",
        {
            "creationtool": APP_TITLE,
            "creationtoolversion": "6.0",
            "segtype": "sentence",
            "adminlang": "ru",
            "srclang": source_lang if source_lang != "auto" else "en",
            "datatype": "PlainText",
        },
    )
    body = ET.SubElement(root, "body")
    for entry in entries:
        source = str(entry.get("source", "")).strip()
        target = str(entry.get("target", "")).strip()
        if not source or not target:
            continue
        tu = ET.SubElement(body, "tu")
        entry_source_lang = str(entry.get("source_lang") or source_lang or "en")
        if entry_source_lang == "auto":
            entry_source_lang = source_lang if source_lang != "auto" else "en"
        entry_target_lang = str(entry.get("target_lang") or target_lang or "ru")
        source_tuv = ET.SubElement(tu, "tuv", {"{http://www.w3.org/XML/1998/namespace}lang": entry_source_lang})
        ET.SubElement(source_tuv, "seg").text = source
        target_tuv = ET.SubElement(tu, "tuv", {"{http://www.w3.org/XML/1998/namespace}lang": entry_target_lang})
        ET.SubElement(target_tuv, "seg").text = target
    return ET.tostring(root, encoding="utf-8", xml_declaration=True)


def read_tmx_entries(data: bytes, preferred_target_lang: str = "ru") -> list[dict[str, Any]]:
    try:
        root = ET.fromstring(data)
    except ET.ParseError as exc:
        raise ValueError("повреждённый TMX") from exc
    entries: list[dict[str, Any]] = []
    xml_lang = "{http://www.w3.org/XML/1998/namespace}lang"
    for tu in (node for node in root.iter() if _xml_local(node.tag) == "tu"):
        variants: list[tuple[str, str]] = []
        for tuv in (node for node in tu if _xml_local(node.tag) == "tuv"):
            language = str(tuv.get(xml_lang) or tuv.get("lang") or "auto")
            segment = next((node for node in tuv.iter() if _xml_local(node.tag) == "seg"), None)
            text = _normalise_spaces("".join(segment.itertext())) if segment is not None else ""
            if text:
                variants.append((language, text))
        if len(variants) < 2:
            continue
        target_index = next((index for index, item in enumerate(variants) if item[0].casefold().startswith(preferred_target_lang.casefold())), 1)
        source_index = 0 if target_index != 0 else 1
        source_language, source = variants[source_index]
        target_language, target = variants[target_index]
        entries.append(
            {
                "source": source,
                "target": target,
                "source_lang": source_language,
                "target_lang": target_language,
                "uses": 1,
                "updated_at": datetime.now().isoformat(timespec="seconds"),
            }
        )
    if not entries:
        raise ValueError("в TMX не найдено ни одной пары перевода")
    return entries


def decode_text_bytes(data: bytes) -> str:
    if data.startswith((b"\xff\xfe", b"\xfe\xff")):
        return data.decode("utf-16")
    if data.startswith(b"\xef\xbb\xbf"):
        return data.decode("utf-8-sig")
    for encoding in ("utf-8", "cp1251", "utf-16", "latin-1"):
        try:
            return data.decode(encoding)
        except UnicodeDecodeError:
            continue
    return data.decode("utf-8", errors="replace")


def plain_text_paragraphs(data: bytes) -> list[str]:
    text = decode_text_bytes(data).replace("\r\n", "\n").replace("\r", "\n")
    return [_normalise_spaces(line) for line in text.split("\n") if line.strip()]


def _xml_local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def _docx_paragraph_text(paragraph: ET.Element) -> str:
    pieces: list[str] = []
    for node in paragraph.iter():
        local = _xml_local(node.tag)
        if local == "t" and node.text:
            pieces.append(node.text)
        elif local == "tab":
            pieces.append("\t")
        elif local in {"br", "cr"}:
            pieces.append("\n")
    return _normalise_spaces("".join(pieces).replace("\n", " "))


def read_docx_paragraphs(data: bytes) -> list[str]:
    try:
        with zipfile.ZipFile(io.BytesIO(data), "r") as archive:
            document_xml = archive.read("word/document.xml")
    except (KeyError, zipfile.BadZipFile) as exc:
        raise ValueError("повреждённый DOCX или отсутствует word/document.xml") from exc

    root = ET.fromstring(document_xml)
    body = next((node for node in root.iter() if _xml_local(node.tag) == "body"), None)
    if body is None:
        return []

    paragraphs: list[str] = []
    for child in body:
        local = _xml_local(child.tag)
        if local == "p":
            value = _docx_paragraph_text(child)
            if value:
                paragraphs.append(value)
        elif local == "tbl":
            for row in (node for node in child if _xml_local(node.tag) == "tr"):
                cells: list[str] = []
                for cell in (node for node in row if _xml_local(node.tag) == "tc"):
                    cell_parts = [
                        _docx_paragraph_text(p)
                        for p in cell.iter()
                        if _xml_local(p.tag) == "p"
                    ]
                    cells.append(" ".join(part for part in cell_parts if part))
                joined = " | ".join(part for part in cells if part)
                if joined:
                    paragraphs.append(joined)
    return paragraphs


def read_docx_structured(data: bytes) -> tuple[list[str], dict[str, Any]]:
    """Читает DOCX в порядке XML-блоков и сохраняет метаданные для round-trip."""

    try:
        with zipfile.ZipFile(io.BytesIO(data), "r") as archive:
            document_xml = archive.read("word/document.xml")
            names = archive.namelist()
    except (KeyError, zipfile.BadZipFile) as exc:
        raise ValueError("повреждённый DOCX или отсутствует word/document.xml") from exc
    try:
        root = ET.fromstring(document_xml)
    except ET.ParseError as exc:
        raise ValueError("повреждена XML-структура DOCX") from exc
    paragraphs = [
        value
        for node in root.iter()
        if _xml_local(node.tag) == "p" and (value := _docx_paragraph_text(node))
    ]
    metadata = {
        "kind": "docx",
        "preservable": bool(paragraphs),
        "block_count": len(paragraphs),
        "image_count": sum(name.startswith("word/media/") and not name.endswith("/") for name in names),
        "style_count": sum(name in {"word/styles.xml", "word/numbering.xml"} for name in names),
        "resource_count": len(names),
        "warnings": [],
    }
    return paragraphs, metadata


def _docx_text_nodes(paragraph: ET.Element) -> list[ET.Element]:
    return [node for node in paragraph.iter() if _xml_local(node.tag) == "t"]


def _replace_docx_paragraph_text(paragraph: ET.Element, translation: str, *, complex_policy: str = "error") -> bool:
    clean, notes = parse_tl_notes(translation)
    if notes:
        raise ValueError("TL-сноски в режиме DOCX Preserve требуют чистого DOCX-экспорта")
    text_nodes = [node for node in _docx_text_nodes(paragraph) if node.text is not None]
    active_nodes = [node for node in text_nodes if str(node.text or "").strip()]
    complex_inline = len(active_nodes) > 1
    if complex_inline and complex_policy == "keep_original":
        return False
    if complex_inline and complex_policy not in {"clean", "keep_original"}:
        raise ValueError("абзац содержит несколько форматированных фрагментов")
    if not text_nodes:
        run = ET.SubElement(paragraph, f"{{{W_NS}}}r")
        text_node = ET.SubElement(run, f"{{{W_NS}}}t")
        text_nodes = [text_node]
    for node in text_nodes:
        node.text = ""
    text_nodes[0].text = clean
    text_nodes[0].set("{http://www.w3.org/XML/1998/namespace}space", "preserve")
    return True


def _validate_docx_package(data: bytes) -> None:
    """Проверяет ZIP, обязательные части и внутренние OPC relationships."""

    try:
        archive = zipfile.ZipFile(io.BytesIO(data), "r")
    except zipfile.BadZipFile as exc:
        raise ValueError("экспортированный DOCX не является ZIP-пакетом") from exc
    with archive:
        names = set(archive.namelist())
        required = {"[Content_Types].xml", "_rels/.rels", "word/document.xml"}
        missing = required.difference(names)
        if missing:
            raise ValueError("в DOCX отсутствуют обязательные части: " + ", ".join(sorted(missing)))
        damaged = archive.testzip()
        if damaged is not None:
            raise ValueError(f"повреждён ресурс DOCX: {damaged}")
        for name in names:
            if not name.endswith(".rels"):
                continue
            try:
                root = ET.fromstring(archive.read(name))
            except ET.ParseError as exc:
                raise ValueError(f"повреждены связи DOCX: {name}") from exc
            if name == "_rels/.rels":
                base_dir = ""
            else:
                owner_dir = posixpath.dirname(posixpath.dirname(name))
                base_dir = owner_dir
            for relation in root:
                if str(relation.get("TargetMode", "")).casefold() == "external":
                    continue
                target = unquote(str(relation.get("Target", ""))).split("#", 1)[0]
                if not target:
                    continue
                resolved = (
                    posixpath.normpath(target.lstrip("/"))
                    if target.startswith("/")
                    else posixpath.normpath(posixpath.join(base_dir, target)).lstrip("/")
                )
                if resolved not in names:
                    raise ValueError(f"DOCX-связь ведёт к отсутствующему ресурсу: {resolved}")


def make_preserved_docx_bytes(
    original_data: bytes,
    translated_paragraphs: list[str],
    *,
    complex_policy: str = "error",
) -> bytes:
    try:
        source = zipfile.ZipFile(io.BytesIO(original_data), "r")
    except zipfile.BadZipFile as exc:
        raise ValueError("встроенный исходный DOCX повреждён") from exc
    with source:
        try:
            raw_document = source.read("word/document.xml")
            root = ET.fromstring(raw_document)
        except (KeyError, ET.ParseError) as exc:
            raise ValueError("не удалось прочитать структуру DOCX") from exc
        paragraphs = [
            node for node in root.iter()
            if _xml_local(node.tag) == "p" and _docx_paragraph_text(node)
        ]
        if len(paragraphs) != len(translated_paragraphs):
            raise ValueError(
                f"структура DOCX изменилась: абзацев {len(paragraphs)}, переводов {len(translated_paragraphs)}"
            )
        for index, (paragraph, translation) in enumerate(zip(paragraphs, translated_paragraphs), start=1):
            try:
                _replace_docx_paragraph_text(paragraph, translation, complex_policy=complex_policy)
            except ValueError as exc:
                raise ValueError(
                    f"DOCX, абзац {index}: {exc}; выберите чистый DOCX или стратегию «Упростить блок»"
                ) from exc
        ET.register_namespace("w", W_NS)
        ET.register_namespace("r", R_NS)
        replacement = ET.tostring(root, encoding="utf-8", xml_declaration=True)
        output = io.BytesIO()
        with zipfile.ZipFile(output, "w") as target:
            for info in source.infolist():
                target.writestr(info, replacement if info.filename == "word/document.xml" else source.read(info.filename))
    result = output.getvalue()
    _validate_docx_package(result)
    with zipfile.ZipFile(io.BytesIO(result), "r") as check:
        ET.fromstring(check.read("word/document.xml"))
    return result


class _HTMLTextExtractor(HTMLParser):
    BLOCKS = {
        "address", "article", "aside", "blockquote", "div", "figcaption", "footer",
        "h1", "h2", "h3", "h4", "h5", "h6", "header", "li", "main", "p",
        "section", "td", "th", "tr",
    }

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self.skip_depth = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag = tag.lower()
        if tag in {"script", "style", "head", "svg"}:
            self.skip_depth += 1
        elif self.skip_depth == 0 and (tag in self.BLOCKS or tag == "br"):
            self.parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        tag = tag.lower()
        if tag in {"script", "style", "head", "svg"} and self.skip_depth:
            self.skip_depth -= 1
        elif self.skip_depth == 0 and tag in self.BLOCKS:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if self.skip_depth == 0:
            self.parts.append(data)

    def paragraphs(self) -> list[str]:
        return [_normalise_spaces(item) for item in re.split(r"\n+", "".join(self.parts)) if item.strip()]


def _html_paragraphs(data: bytes) -> list[str]:
    parser = _HTMLTextExtractor()
    parser.feed(decode_text_bytes(data))
    parser.close()
    return parser.paragraphs()


EPUB_TEXT_BLOCKS = {
    "p", "h1", "h2", "h3", "h4", "h5", "h6", "li", "blockquote",
    "figcaption", "td", "th", "pre", "dt", "dd", "caption", "subtitle",
}
EPUB_IGNORED_NODES = {"head", "script", "style", "svg", "math", "audio", "video"}


def _epub_package_info(archive: zipfile.ZipFile) -> dict[str, Any]:
    names = set(archive.namelist())
    opf_name = ""
    try:
        container_root = ET.fromstring(archive.read("META-INF/container.xml"))
        rootfile = next((node for node in container_root.iter() if _xml_local(node.tag) == "rootfile"), None)
        if rootfile is not None:
            opf_name = str(rootfile.get("full-path", ""))
    except (KeyError, ET.ParseError):
        pass

    ordered_files: list[str] = []
    manifest_types: dict[str, str] = {}
    if opf_name and opf_name in names:
        try:
            opf_root = ET.fromstring(archive.read(opf_name))
            base_dir = posixpath.dirname(opf_name)
            manifest: dict[str, str] = {}
            for item in opf_root.iter():
                if _xml_local(item.tag) != "item":
                    continue
                href = urldefrag(unquote(item.get("href", "")))[0]
                full = posixpath.normpath(posixpath.join(base_dir, href)).lstrip("/")
                if item.get("id") and full in names:
                    manifest[str(item.get("id", ""))] = full
                    manifest_types[full] = str(item.get("media-type", ""))
            for itemref in opf_root.iter():
                if _xml_local(itemref.tag) != "itemref":
                    continue
                filename = manifest.get(str(itemref.get("idref", "")))
                if filename and filename not in ordered_files:
                    ordered_files.append(filename)
        except (KeyError, ET.ParseError):
            ordered_files = []

    if not ordered_files:
        ordered_files = sorted(
            name for name in names
            if name.lower().endswith((".xhtml", ".html", ".htm"))
            and "toc" not in posixpath.basename(name).lower()
            and "nav" not in posixpath.basename(name).lower()
        )
    return {"opf_name": opf_name, "spine_files": ordered_files, "manifest_types": manifest_types}


def _parse_epub_xhtml(data: bytes) -> ET.Element:
    # В старых EPUB встречаются HTML-сущности, которые XML-парсер без DTD не знает.
    def replace_entity(match: re.Match[bytes]) -> bytes:
        name = match.group(1).decode("ascii", errors="ignore").lower()
        if name in {"amp", "lt", "gt", "apos", "quot"}:
            return match.group(0)
        codepoint = name2codepoint.get(name)
        return f"&#{codepoint};".encode("ascii") if codepoint is not None else match.group(0)

    safe = re.sub(
        rb"&([A-Za-z][A-Za-z0-9]+);",
        replace_entity,
        data,
    )
    parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True))
    return ET.fromstring(safe, parser=parser)


def _epub_block_elements(root: ET.Element) -> list[ET.Element]:
    body = next((node for node in root.iter() if _xml_local(node.tag).lower() == "body"), root)
    blocks: list[ET.Element] = []
    for node in body.iter():
        if not isinstance(node.tag, str) or _xml_local(node.tag).lower() not in EPUB_TEXT_BLOCKS:
            continue
        value = _normalise_spaces("".join(node.itertext()))
        if value:
            blocks.append(node)
    if blocks:
        return blocks

    # Редкий EPUB без <p>: берём только содержательные листовые контейнеры.
    for node in body.iter():
        if not isinstance(node.tag, str) or _xml_local(node.tag).lower() in EPUB_IGNORED_NODES:
            continue
        child_text_nodes = [
            child for child in list(node)
            if isinstance(child.tag, str)
            and _xml_local(child.tag).lower() not in EPUB_IGNORED_NODES
            and _normalise_spaces("".join(child.itertext()))
        ]
        value = _normalise_spaces("".join(node.itertext()))
        if value and not child_text_nodes:
            blocks.append(node)
    return blocks


def read_epub_structured(data: bytes) -> tuple[list[str], dict[str, Any]]:
    try:
        archive = zipfile.ZipFile(io.BytesIO(data), "r")
    except zipfile.BadZipFile as exc:
        raise ValueError("повреждённый EPUB") from exc

    with archive:
        package = _epub_package_info(archive)
        ordered_files = list(package["spine_files"])
        paragraphs: list[str] = []
        block_counts: dict[str, int] = {}
        preservable = True
        parse_warnings: list[str] = []
        for filename in ordered_files:
            try:
                raw = archive.read(filename)
                root = _parse_epub_xhtml(raw)
                blocks = _epub_block_elements(root)
                values = [_normalise_spaces("".join(node.itertext())) for node in blocks]
                values = [value for value in values if value]
                block_counts[filename] = len(values)
                paragraphs.extend(values)
            except (KeyError, UnicodeError, ET.ParseError) as exc:
                preservable = False
                parse_warnings.append(f"{filename}: {exc}")
                try:
                    fallback = _html_paragraphs(archive.read(filename))
                except (KeyError, UnicodeError):
                    fallback = []
                block_counts[filename] = len(fallback)
                paragraphs.extend(fallback)
        names = archive.namelist()
        metadata = {
            "kind": "epub",
            "preservable": preservable and bool(ordered_files),
            "opf_name": package["opf_name"],
            "spine_files": ordered_files,
            "block_counts": block_counts,
            "image_count": sum(name.lower().endswith((".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".avif")) for name in names),
            "style_count": sum(name.lower().endswith(".css") for name in names),
            "resource_count": len(names),
            "warnings": parse_warnings,
        }
        return paragraphs, metadata


def read_epub_paragraphs(data: bytes) -> list[str]:
    paragraphs, _ = read_epub_structured(data)
    return paragraphs


def read_fb2_paragraphs(data: bytes) -> list[str]:
    try:
        root = ET.fromstring(data)
    except ET.ParseError as exc:
        raise ValueError("повреждённый FB2") from exc

    bodies = [node for node in root if _xml_local(node.tag) == "body"]
    main_body = next((body for body in bodies if not body.get("name")), bodies[0] if bodies else None)
    if main_body is None:
        return []

    paragraphs: list[str] = []
    for node in main_body.iter():
        if _xml_local(node.tag) not in {"p", "v", "subtitle"}:
            continue
        value = _normalise_spaces("".join(node.itertext()))
        if value:
            paragraphs.append(value)
    return paragraphs


def read_xliff_paragraphs(data: bytes) -> list[str]:
    try:
        root = ET.fromstring(data)
    except ET.ParseError as exc:
        raise ValueError("повреждённый XLIFF") from exc
    paragraphs: list[str] = []
    for node in root.iter():
        if _xml_local(node.tag) != "source":
            continue
        value = _normalise_spaces("".join(node.itertext()))
        if value:
            paragraphs.append(value)
    return paragraphs


def read_source_bytes(data: bytes, filename: str) -> list[str]:
    extension = Path(filename).suffix.lower()
    if extension not in SUPPORTED_EXTENSIONS:
        raise ValueError(f"формат {extension or 'без расширения'} не поддерживается")
    if extension == ".docx":
        paragraphs = read_docx_paragraphs(data)
    elif extension == ".epub":
        paragraphs = read_epub_paragraphs(data)
    elif extension == ".fb2":
        paragraphs = read_fb2_paragraphs(data)
    elif extension in {".xlf", ".xliff"}:
        paragraphs = read_xliff_paragraphs(data)
    else:
        paragraphs = plain_text_paragraphs(data)
    if not paragraphs:
        raise ValueError("файл пуст или в нём не найден текст")
    return paragraphs


def assemble_paragraphs(
    sentences: list[str],
    translations: list[str],
    sentence_to_paragraph: list[int],
    *,
    original_for_empty: bool,
) -> list[str]:
    if not sentences:
        return []
    paragraph_count = max(sentence_to_paragraph, default=-1) + 1
    grouped: list[list[str]] = [[] for _ in range(paragraph_count)]
    for index, source in enumerate(sentences):
        target = translations[index].strip() if index < len(translations) else ""
        value = target or (source if original_for_empty else "")
        if value:
            grouped[sentence_to_paragraph[index]].append(value)
    return [" ".join(parts).strip() for parts in grouped]


def _docx_text_run(text: str, *, bold: bool = False) -> str:
    if not text:
        return ""
    run_properties = "<w:rPr><w:b/></w:rPr>" if bold else ""
    return f"<w:r>{run_properties}<w:t xml:space=\"preserve\">{escape(text)}</w:t></w:r>"


def _docx_paragraph_xml(
    text: str,
    *,
    bold: bool = False,
    footnotes: list[tuple[int, str]] | None = None,
) -> str:
    clean, notes = parse_tl_notes(text)
    runs: list[str] = []
    cursor = 0
    for note in notes:
        position = max(cursor, min(len(clean), int(note.get("position", cursor))))
        runs.append(_docx_text_run(clean[cursor:position], bold=bold))
        if footnotes is not None:
            note_id = len(footnotes) + 1
            footnotes.append((note_id, str(note.get("text", ""))))
            runs.append(
                "<w:r><w:rPr><w:rStyle w:val=\"FootnoteReference\"/></w:rPr>"
                f"<w:footnoteReference w:id=\"{note_id}\"/></w:r>"
            )
        cursor = position
    runs.append(_docx_text_run(clean[cursor:], bold=bold))
    return (
        "<w:p><w:pPr><w:spacing w:after=\"120\"/></w:pPr>"
        f"{''.join(runs)}</w:p>"
    )


def _docx_cell_xml(text: str, width: int, footnotes: list[tuple[int, str]] | None = None) -> str:
    return (
        f"<w:tc><w:tcPr><w:tcW w:w=\"{width}\" w:type=\"dxa\"/></w:tcPr>"
        f"{_docx_paragraph_xml(text, footnotes=footnotes)}</w:tc>"
    )


def make_docx_bytes(
    translated_paragraphs: list[str],
    original_paragraphs: list[str] | None = None,
) -> bytes:
    bilingual = original_paragraphs is not None
    footnotes: list[tuple[int, str]] = []
    if bilingual:
        rows = [
            "<w:tr>" + _docx_cell_xml("Оригинал", 4680).replace("<w:r>", "<w:r><w:rPr><w:b/></w:rPr>", 1)
            + _docx_cell_xml("Перевод", 4680).replace("<w:r>", "<w:r><w:rPr><w:b/></w:rPr>", 1) + "</w:tr>"
        ]
        total = max(len(original_paragraphs or []), len(translated_paragraphs))
        for index in range(total):
            source = original_paragraphs[index] if original_paragraphs and index < len(original_paragraphs) else ""
            target = translated_paragraphs[index] if index < len(translated_paragraphs) else ""
            rows.append("<w:tr>" + _docx_cell_xml(source, 4680) + _docx_cell_xml(target, 4680, footnotes) + "</w:tr>")
        body_xml = (
            "<w:tbl><w:tblPr><w:tblW w:w=\"9360\" w:type=\"dxa\"/>"
            "<w:tblBorders><w:top w:val=\"single\" w:sz=\"4\" w:color=\"B7B7B7\"/>"
            "<w:left w:val=\"single\" w:sz=\"4\" w:color=\"B7B7B7\"/>"
            "<w:bottom w:val=\"single\" w:sz=\"4\" w:color=\"B7B7B7\"/>"
            "<w:right w:val=\"single\" w:sz=\"4\" w:color=\"B7B7B7\"/>"
            "<w:insideH w:val=\"single\" w:sz=\"4\" w:color=\"D9D9D9\"/>"
            "<w:insideV w:val=\"single\" w:sz=\"4\" w:color=\"D9D9D9\"/>"
            "</w:tblBorders></w:tblPr><w:tblGrid><w:gridCol w:w=\"4680\"/>"
            "<w:gridCol w:w=\"4680\"/></w:tblGrid>" + "".join(rows) + "</w:tbl>"
        )
    else:
        body_xml = "".join(_docx_paragraph_xml(paragraph, footnotes=footnotes) for paragraph in translated_paragraphs)

    document_xml = (
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>"
        f"<w:document xmlns:w=\"{W_NS}\" xmlns:r=\"{R_NS}\"><w:body>{body_xml}"
        "<w:sectPr><w:pgSz w:w=\"11906\" w:h=\"16838\"/>"
        "<w:pgMar w:top=\"1134\" w:right=\"1134\" w:bottom=\"1134\" w:left=\"1134\"/>"
        "</w:sectPr></w:body></w:document>"
    )
    content_types = (
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
        "<Types xmlns=\"http://schemas.openxmlformats.org/package/2006/content-types\">"
        "<Default Extension=\"rels\" ContentType=\"application/vnd.openxmlformats-package.relationships+xml\"/>"
        "<Default Extension=\"xml\" ContentType=\"application/xml\"/>"
        "<Override PartName=\"/word/document.xml\" "
        "ContentType=\"application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml\"/>"
        "<Override PartName=\"/word/styles.xml\" "
        "ContentType=\"application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml\"/>"
        + (
            "<Override PartName=\"/word/footnotes.xml\" "
            "ContentType=\"application/vnd.openxmlformats-officedocument.wordprocessingml.footnotes+xml\"/>"
            if footnotes else ""
        )
        +
        "</Types>"
    )
    package_rels = (
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
        "<Relationships xmlns=\"http://schemas.openxmlformats.org/package/2006/relationships\">"
        "<Relationship Id=\"rId1\" "
        "Type=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument\" "
        "Target=\"word/document.xml\"/></Relationships>"
    )
    document_rels = (
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
        "<Relationships xmlns=\"http://schemas.openxmlformats.org/package/2006/relationships\">"
        + (
            "<Relationship Id=\"rIdFootnotes\" "
            "Type=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships/footnotes\" "
            "Target=\"footnotes.xml\"/>"
            if footnotes else ""
        )
        + "</Relationships>"
    )
    styles_xml = (
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>"
        f"<w:styles xmlns:w=\"{W_NS}\"><w:docDefaults><w:rPrDefault><w:rPr>"
        "<w:rFonts w:ascii=\"Arial\" w:hAnsi=\"Arial\" w:cs=\"Arial\"/>"
        "<w:sz w:val=\"22\"/><w:szCs w:val=\"22\"/></w:rPr></w:rPrDefault>"
        "<w:pPrDefault/></w:docDefaults><w:style w:type=\"paragraph\" w:default=\"1\" w:styleId=\"Normal\">"
        "<w:name w:val=\"Normal\"/></w:style>"
        "<w:style w:type=\"character\" w:styleId=\"FootnoteReference\"><w:name w:val=\"footnote reference\"/>"
        "<w:rPr><w:vertAlign w:val=\"superscript\"/></w:rPr></w:style></w:styles>"
    )
    footnotes_xml = ""
    if footnotes:
        note_nodes = "".join(
            f"<w:footnote w:id=\"{note_id}\"><w:p><w:r><w:footnoteRef/></w:r>"
            f"{_docx_text_run(' ' + note_text)}</w:p></w:footnote>"
            for note_id, note_text in footnotes
        )
        footnotes_xml = (
            "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>"
            f"<w:footnotes xmlns:w=\"{W_NS}\">"
            "<w:footnote w:type=\"separator\" w:id=\"-1\"><w:p><w:r><w:separator/></w:r></w:p></w:footnote>"
            "<w:footnote w:type=\"continuationSeparator\" w:id=\"0\"><w:p><w:r><w:continuationSeparator/></w:r></w:p></w:footnote>"
            f"{note_nodes}</w:footnotes>"
        )

    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("[Content_Types].xml", content_types)
        archive.writestr("_rels/.rels", package_rels)
        archive.writestr("word/document.xml", document_xml)
        archive.writestr("word/styles.xml", styles_xml)
        archive.writestr("word/_rels/document.xml.rels", document_rels)
        if footnotes_xml:
            archive.writestr("word/footnotes.xml", footnotes_xml)
    result = output.getvalue()
    _validate_docx_package(result)
    return result


def make_epub_bytes(paragraphs: list[str], title: str, language: str = "ru") -> bytes:
    book_id = f"urn:uuid:{uuid.uuid4()}"
    safe_title = escape(title or APP_TITLE)
    epub_notes: list[tuple[int, str]] = []
    body_parts: list[str] = []
    for paragraph in paragraphs:
        if not paragraph.strip():
            continue
        clean, notes = parse_tl_notes(paragraph)
        chunks: list[str] = []
        cursor = 0
        for note in notes:
            position = max(cursor, min(len(clean), int(note.get("position", cursor))))
            chunks.append(escape(clean[cursor:position]))
            note_id = len(epub_notes) + 1
            epub_notes.append((note_id, str(note.get("text", ""))))
            chunks.append(
                f'<a id="noteref-{note_id}" href="#footnote-{note_id}" epub:type="noteref" '
                f'role="doc-noteref">[{note_id}]</a>'
            )
            cursor = position
        chunks.append(escape(clean[cursor:]))
        body_parts.append(f"<p>{''.join(chunks)}</p>")
    footnote_body = "".join(
        f'<aside id="footnote-{note_id}" epub:type="footnote" role="doc-footnote"><p>'
        f'{escape(note_text)} <a href="#noteref-{note_id}">↩</a></p></aside>'
        for note_id, note_text in epub_notes
    )
    body = "".join(body_parts) + (f'<section epub:type="footnotes">{footnote_body}</section>' if footnote_body else "")
    content = (
        "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
        "<!DOCTYPE html><html xmlns=\"http://www.w3.org/1999/xhtml\" "
        "xmlns:epub=\"http://www.idpf.org/2007/ops\" lang=\"" + escape(language) + "\">"
        f"<head><title>{safe_title}</title><meta charset=\"utf-8\"/>"
        "<style>body{font-family:serif;line-height:1.55;margin:6%;}p{margin:.8em 0;}</style></head>"
        f"<body><h1>{safe_title}</h1>{body}</body></html>"
    )
    nav = (
        "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
        "<!DOCTYPE html><html xmlns=\"http://www.w3.org/1999/xhtml\" xmlns:epub=\"http://www.idpf.org/2007/ops\">"
        f"<head><title>{safe_title}</title></head><body><nav epub:type=\"toc\"><ol>"
        "<li><a href=\"text.xhtml\">Перевод</a></li></ol></nav></body></html>"
    )
    opf = (
        "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
        "<package xmlns=\"http://www.idpf.org/2007/opf\" version=\"3.0\" unique-identifier=\"bookid\">"
        "<metadata xmlns:dc=\"http://purl.org/dc/elements/1.1/\">"
        f"<dc:identifier id=\"bookid\">{book_id}</dc:identifier><dc:title>{safe_title}</dc:title>"
        f"<dc:language>{escape(language)}</dc:language><meta property=\"dcterms:modified\">{datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}</meta>"
        "</metadata><manifest><item id=\"content\" href=\"text.xhtml\" media-type=\"application/xhtml+xml\"/>"
        "<item id=\"nav\" href=\"nav.xhtml\" media-type=\"application/xhtml+xml\" properties=\"nav\"/></manifest>"
        "<spine><itemref idref=\"content\"/></spine></package>"
    )
    container = (
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
        "<container version=\"1.0\" xmlns=\"urn:oasis:names:tc:opendocument:xmlns:container\">"
        "<rootfiles><rootfile full-path=\"EPUB/package.opf\" media-type=\"application/oebps-package+xml\"/>"
        "</rootfiles></container>"
    )
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w") as archive:
        archive.writestr("mimetype", "application/epub+zip", compress_type=zipfile.ZIP_STORED)
        archive.writestr("META-INF/container.xml", container)
        archive.writestr("EPUB/package.opf", opf)
        archive.writestr("EPUB/nav.xhtml", nav)
        archive.writestr("EPUB/text.xhtml", content)
    return output.getvalue()


def _epub_text_slots(element: ET.Element) -> list[tuple[ET.Element, str, str]]:
    slots: list[tuple[ET.Element, str, str]] = []

    def visit(node: ET.Element, ignored: bool = False) -> None:
        local = _xml_local(node.tag).lower() if isinstance(node.tag, str) else ""
        skip = ignored or local in EPUB_IGNORED_NODES
        if not skip and node.text is not None:
            slots.append((node, "text", node.text))
        for child in list(node):
            visit(child, skip)
            if not skip and child.tail is not None:
                slots.append((child, "tail", child.tail))

    visit(element)
    return slots


def _epub_block_has_complex_inline(element: ET.Element) -> bool:
    for child in element.iter():
        if child is element or not isinstance(child.tag, str):
            continue
        local = _xml_local(child.tag).lower()
        if local in EPUB_IGNORED_NODES:
            continue
        if local not in {"br", "wbr"} and _normalise_spaces("".join(child.itertext())):
            return True
    return False


def _replace_epub_block_text(
    element: ET.Element,
    translation: str,
    *,
    complex_policy: str = "error",
    footnotes: list[tuple[int, str]] | None = None,
) -> bool:
    """Безопасно заменяет блок, не угадывая форматирование по длине слов."""

    complex_inline = _epub_block_has_complex_inline(element)
    if complex_inline and complex_policy == "keep_original":
        return False
    if complex_inline and complex_policy not in {"clean", "keep_original"}:
        raise ValueError("блок содержит смысловую inline-разметку")

    clean, notes = parse_tl_notes(translation)
    for node, attribute, _ in _epub_text_slots(element):
        setattr(node, attribute, "")
    element.text = ""
    cursor = 0
    last_anchor: ET.Element | None = None
    epub_namespace = "http://www.idpf.org/2007/ops"
    for note in notes:
        position = max(cursor, min(len(clean), int(note.get("position", cursor))))
        piece = clean[cursor:position]
        if last_anchor is None:
            element.text = (element.text or "") + piece
        else:
            last_anchor.tail = (last_anchor.tail or "") + piece
        if footnotes is not None:
            note_id = len(footnotes) + 1
            footnotes.append((note_id, str(note.get("text", ""))))
            anchor = ET.Element(
                f"{{{element.tag[1:].split('}', 1)[0]}}}a" if str(element.tag).startswith("{") else "a",
                {
                    "id": f"noteref-{note_id}",
                    "href": f"#footnote-{note_id}",
                    f"{{{epub_namespace}}}type": "noteref",
                    "role": "doc-noteref",
                },
            )
            anchor.text = f"[{note_id}]"
            element.append(anchor)
            last_anchor = anchor
        cursor = position
    tail = clean[cursor:]
    if last_anchor is None:
        element.text = (element.text or "") + tail
    else:
        last_anchor.tail = (last_anchor.tail or "") + tail
    return True


def _serialise_epub_xhtml(root: ET.Element, original: bytes) -> bytes:
    namespace_match = re.match(r"\{([^}]+)\}", str(root.tag))
    if namespace_match:
        ET.register_namespace("", namespace_match.group(1))
    ET.register_namespace("epub", "http://www.idpf.org/2007/ops")
    ET.register_namespace("xlink", "http://www.w3.org/1999/xlink")
    serialized = ET.tostring(root, encoding="utf-8", xml_declaration=True)
    doctype = re.search(rb"<!DOCTYPE[^>]*>", original, flags=re.IGNORECASE)
    if doctype:
        declaration_end = serialized.find(b"?>")
        if declaration_end >= 0:
            serialized = serialized[:declaration_end + 2] + b"\n" + doctype.group(0) + serialized[declaration_end + 2:]
    return serialized


def make_preserved_epub_bytes(
    original_data: bytes,
    translated_paragraphs: list[str],
    language: str = "ru",
    complex_policy: str = "error",
) -> bytes:
    """Создаёт перевод поверх исходного EPUB, сохраняя ресурсы и DOM-структуру."""

    try:
        source = zipfile.ZipFile(io.BytesIO(original_data), "r")
    except zipfile.BadZipFile as exc:
        raise ValueError("встроенный исходный EPUB повреждён") from exc
    with source:
        package = _epub_package_info(source)
        spine_files = list(package["spine_files"])
        if not spine_files:
            raise ValueError("в EPUB не найдено содержимое книги")
        replacements: dict[str, bytes] = {}
        paragraph_index = 0
        epub_notes: list[tuple[int, str]] = []
        for filename in spine_files:
            try:
                raw = source.read(filename)
                root = _parse_epub_xhtml(raw)
            except (KeyError, ET.ParseError) as exc:
                raise ValueError(
                    f"глава {filename} содержит несовместимый HTML; используйте обычный EPUB-экспорт"
                ) from exc
            blocks = _epub_block_elements(root)
            file_note_start = len(epub_notes)
            for block_number, block in enumerate(blocks, start=1):
                if paragraph_index >= len(translated_paragraphs):
                    raise ValueError("структура исходного EPUB изменилась: переводов меньше, чем текстовых блоков")
                try:
                    _replace_epub_block_text(
                        block,
                        translated_paragraphs[paragraph_index],
                        complex_policy=complex_policy,
                        footnotes=epub_notes,
                    )
                except ValueError as exc:
                    raise ValueError(
                        f"{filename}, блок {block_number}: {exc}; выберите чистый EPUB или стратегию «Упростить блок»"
                    ) from exc
                paragraph_index += 1
            file_notes = epub_notes[file_note_start:]
            if file_notes:
                namespace = str(root.tag)[1:].split("}", 1)[0] if str(root.tag).startswith("{") else ""
                def qname(name: str) -> str:
                    return f"{{{namespace}}}{name}" if namespace else name
                body = next((node for node in root.iter() if _xml_local(node.tag).lower() == "body"), root)
                section = ET.SubElement(
                    body,
                    qname("section"),
                    {"{http://www.idpf.org/2007/ops}type": "footnotes"},
                )
                for note_id, note_text in file_notes:
                    aside = ET.SubElement(
                        section,
                        qname("aside"),
                        {
                            "id": f"footnote-{note_id}",
                            "{http://www.idpf.org/2007/ops}type": "footnote",
                            "role": "doc-footnote",
                        },
                    )
                    paragraph = ET.SubElement(aside, qname("p"))
                    paragraph.text = note_text + " "
                    backlink = ET.SubElement(paragraph, qname("a"), {"href": f"#noteref-{note_id}"})
                    backlink.text = "↩"
            replacements[filename] = _serialise_epub_xhtml(root, raw)
        if paragraph_index != len(translated_paragraphs):
            raise ValueError(
                f"структура исходного EPUB изменилась: блоков {paragraph_index}, переводов {len(translated_paragraphs)}"
            )

        opf_name = str(package.get("opf_name", ""))
        if opf_name and opf_name in source.namelist():
            opf_data = source.read(opf_name)
            safe_language = escape(language or "ru").encode("utf-8")
            replacements[opf_name] = re.sub(
                rb"(<(?:[A-Za-z0-9_.-]+:)?language\b[^>]*>).*?(</(?:[A-Za-z0-9_.-]+:)?language>)",
                lambda match: match.group(1) + safe_language + match.group(2),
                opf_data,
                count=1,
                flags=re.IGNORECASE | re.DOTALL,
            )

        output = io.BytesIO()
        infos = source.infolist()
        mimetype_info = next((item for item in infos if item.filename == "mimetype"), None)
        with zipfile.ZipFile(output, "w") as target:
            if mimetype_info is not None:
                target.writestr(mimetype_info, source.read(mimetype_info), compress_type=zipfile.ZIP_STORED)
            else:
                target.writestr("mimetype", "application/epub+zip", compress_type=zipfile.ZIP_STORED)
            for info in infos:
                if info.filename == "mimetype":
                    continue
                target.writestr(info, replacements.get(info.filename, source.read(info)))
    result = output.getvalue()
    # Последняя дешёвая проверка предотвращает выдачу повреждённой книги пользователю.
    with zipfile.ZipFile(io.BytesIO(result), "r") as check:
        if check.read("mimetype") != b"application/epub+zip":
            raise ValueError("не удалось собрать корректный EPUB")
        if check.testzip() is not None:
            raise ValueError("повреждён ресурс внутри экспортированного EPUB")
    return result


def make_fb2_bytes(paragraphs: list[str], title: str, language: str = "ru") -> bytes:
    safe_title = escape(title or APP_TITLE)
    body = "".join(f"<p>{escape(paragraph)}</p>" for paragraph in paragraphs if paragraph.strip())
    xml = (
        "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
        "<FictionBook xmlns=\"http://www.gribuser.ru/xml/fictionbook/2.0\">"
        f"<description><title-info><book-title>{safe_title}</book-title><lang>{escape(language)}</lang>"
        "<author><first-name>LiteraFlow</first-name></author></title-info>"
        f"<document-info><author><nickname>{APP_TITLE}</nickname></author><program-used>{APP_TITLE}</program-used>"
        f"<date value=\"{datetime.now().date().isoformat()}\">{datetime.now().date().isoformat()}</date>"
        f"<id>{uuid.uuid4()}</id><version>1.0</version></document-info></description>"
        f"<body><title><p>{safe_title}</p></title><section>{body}</section></body></FictionBook>"
    )
    return xml.encode("utf-8")


def make_xliff_bytes(
    sentences: list[str],
    translations: list[str],
    source_lang: str = "en",
    target_lang: str = "ru",
) -> bytes:
    root = ET.Element(
        "xliff",
        {"xmlns": "urn:oasis:names:tc:xliff:document:2.0", "version": "2.0", "srcLang": source_lang if source_lang != "auto" else "en", "trgLang": target_lang},
    )
    file_node = ET.SubElement(root, "file", {"id": "literaflow", "original": "novel"})
    for index, source in enumerate(sentences):
        unit = ET.SubElement(file_node, "unit", {"id": str(index + 1)})
        segment = ET.SubElement(unit, "segment", {"state": "final" if index < len(translations) and translations[index].strip() else "initial"})
        ET.SubElement(segment, "source").text = source
        ET.SubElement(segment, "target").text = translations[index] if index < len(translations) else ""
    return ET.tostring(root, encoding="utf-8", xml_declaration=True)


def normalise_ollama_generate_url(value: str) -> str:
    raw = (value or "").strip().rstrip("/")
    if not raw:
        raw = DEFAULT_CONFIG["ollama_url"]
    if "://" not in raw:
        raw = "http://" + raw
    parts = urlsplit(raw)
    if parts.scheme not in {"http", "https"} or not parts.netloc:
        raise ValueError("укажите URL вида http://localhost:11434")
    path = parts.path.rstrip("/")
    if not path:
        path = "/api/generate"
    elif path.endswith("/api"):
        path += "/generate"
    elif not path.endswith("/api/generate"):
        path += "/api/generate"
    return urlunsplit((parts.scheme, parts.netloc, path, "", ""))


def ollama_tags_url(generate_url: str) -> str:
    parts = urlsplit(normalise_ollama_generate_url(generate_url))
    return urlunsplit((parts.scheme, parts.netloc, "/api/tags", "", ""))


def normalise_openai_chat_url(value: str) -> str:
    raw = (value or "").strip().rstrip("/")
    if not raw:
        raise ValueError("укажите адрес OpenAI-совместимого API")
    if "://" not in raw:
        raw = "https://" + raw
    parts = urlsplit(raw)
    if parts.scheme not in {"http", "https"} or not parts.netloc:
        raise ValueError("нужен URL вида https://server/v1/chat/completions")
    path = parts.path.rstrip("/")
    if not path:
        path = "/v1/chat/completions"
    elif path.endswith("/v1"):
        path += "/chat/completions"
    elif not (path.endswith("/chat/completions") or path.endswith("/responses")):
        path += "/chat/completions"
    return urlunsplit((parts.scheme, parts.netloc, path, "", ""))


def custom_api_headers(config: dict[str, Any]) -> dict[str, str]:
    headers: dict[str, str] = {}
    key = str(config.get("custom_api_key", "") or os.environ.get("LITERAFLOW_API_KEY", "")).strip()
    if key:
        key_header = str(config.get("custom_api_key_header", "Authorization") or "Authorization").strip()
        if not re.fullmatch(r"[A-Za-z0-9-]{1,64}", key_header):
            raise TranslationError("некорректное имя заголовка API-ключа")
        headers[key_header] = f"Bearer {key}" if key_header.casefold() == "authorization" else key
    raw_extra = str(config.get("custom_api_headers", "") or "").strip()
    if raw_extra:
        try:
            extra = json.loads(raw_extra)
        except ValueError as exc:
            raise TranslationError("дополнительные заголовки должны быть JSON-объектом") from exc
        if not isinstance(extra, dict) or not all(isinstance(name, str) and isinstance(value, str) for name, value in extra.items()):
            raise TranslationError("дополнительные заголовки должны содержать только строки")
        secret_names = {"authorization", "x-api-key", "api-key", "apikey", "proxy-authorization"}
        if any(name.casefold() in secret_names for name in extra):
            raise TranslationError("секретный заголовок задайте через поле «Заголовок API-ключа», чтобы значение не сохранялось открыто")
        headers.update(extra)
    return headers


def _request_json(
    url: str,
    *,
    payload: dict[str, Any] | None = None,
    timeout: float = 90,
    request_headers: dict[str, str] | None = None,
) -> Any:
    data = None
    headers = {"Accept": "application/json", "User-Agent": "LiteraFlow/6.0"}
    if request_headers:
        headers.update(request_headers)
    if payload is not None:
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        headers["Content-Type"] = "application/json"
    request = Request(url, data=data, headers=headers, method="POST" if payload is not None else "GET")
    try:
        with urlopen(request, timeout=timeout) as response:
            body = response.read()
    except HTTPError as exc:
        try:
            detail = exc.read().decode("utf-8", errors="replace")[:300]
        except Exception:
            detail = ""
        raise TranslationError(f"сервер ответил HTTP {exc.code}{': ' + detail if detail else ''}") from exc
    except (URLError, TimeoutError, OSError) as exc:
        reason = getattr(exc, "reason", exc)
        raise TranslationError(f"нет соединения с сервисом: {reason}") from exc
    try:
        return json.loads(body.decode("utf-8"))
    except (UnicodeError, ValueError) as exc:
        raise TranslationError("сервис вернул некорректный JSON") from exc


def check_with_languagetool(text: str, language: str = "ru", endpoint: str = "") -> list[dict[str, Any]]:
    """Запускает явную глубокую проверку одного сегмента через LanguageTool."""

    url = (endpoint or DEFAULT_CONFIG["languagetool_url"]).strip()
    parts = urlsplit(url)
    if parts.scheme != "https" or not parts.netloc:
        raise TranslationError("для LanguageTool требуется HTTPS-адрес")
    language_map = {"ru": "ru-RU", "en": "en-US", "de": "de-DE", "fr": "fr-FR", "es": "es"}
    body = urlencode({"text": text, "language": language_map.get(language, language)}).encode("utf-8")
    request = Request(
        url,
        data=body,
        headers={
            "Accept": "application/json",
            "Content-Type": "application/x-www-form-urlencoded; charset=utf-8",
            "User-Agent": "LiteraFlow/6.0",
        },
        method="POST",
    )
    try:
        with urlopen(request, timeout=35) as response:
            result = json.loads(response.read().decode("utf-8"))
    except HTTPError as exc:
        raise TranslationError(f"LanguageTool ответил HTTP {exc.code}") from exc
    except (URLError, TimeoutError, OSError, ValueError, UnicodeError) as exc:
        raise TranslationError(f"LanguageTool недоступен: {getattr(exc, 'reason', exc)}") from exc
    matches = result.get("matches", []) if isinstance(result, dict) else []
    parsed: list[dict[str, Any]] = []
    for match in matches if isinstance(matches, list) else []:
        if not isinstance(match, dict):
            continue
        try:
            offset = max(0, int(match.get("offset", 0)))
            length = max(0, int(match.get("length", 0)))
        except (TypeError, ValueError):
            continue
        replacements = match.get("replacements", [])
        suggestions = [str(item.get("value", "")) for item in replacements[:4] if isinstance(item, dict) and item.get("value")]
        parsed.append(
            {
                "message": str(match.get("message", "Проверьте написание")),
                "offset": offset,
                "length": length,
                "word": text[offset:offset + length],
                "suggestions": suggestions,
                "rule": str((match.get("rule") or {}).get("id", "")) if isinstance(match.get("rule"), dict) else "",
            }
        )
    return parsed


@lru_cache(maxsize=1)
def _morph_analyzer():
    if not HAS_PYMORPHY3 or MorphAnalyzer is None:
        return None
    try:
        return MorphAnalyzer()
    except Exception:
        return None


@lru_cache(maxsize=8192)
def is_known_russian_word(word: str) -> bool:
    analyzer = _morph_analyzer()
    value = re.sub(r"(^-+|-+$)", "", word.casefold())
    if analyzer is None or not value:
        return False
    try:
        return any(bool(getattr(parsed, "is_known", False)) for parsed in analyzer.parse(value))
    except Exception:
        return False


def _preserve_word_case(source: str, value: str) -> str:
    if source.isupper():
        return value.upper()
    if source[:1].isupper():
        return value[:1].upper() + value[1:]
    return value


@lru_cache(maxsize=2048)
def russian_word_forms(value: str) -> tuple[str, ...]:
    """Возвращает полезные словоформы имени/термина без сетевых запросов."""

    analyzer = _morph_analyzer()
    text = _normalise_spaces(value)
    if analyzer is None or not text:
        return ()
    words = list(re.finditer(r"[А-Яа-яЁё-]+", text))
    if not words:
        return ()
    target_match = words[-1]
    source_word = target_match.group(0)
    try:
        parses = analyzer.parse(source_word)
    except Exception:
        return ()
    if not parses:
        return ()
    preferred = next(
        (
            parsed for parsed in parses
            if {"Name", "Surn", "Patr", "NOUN"}.intersection(set(str(parsed.tag).replace(",", " ").split()))
        ),
        parses[0],
    )
    forms: list[str] = []
    seen = {text.casefold()}
    try:
        lexeme = preferred.lexeme
    except Exception:
        lexeme = ()
    for form in lexeme:
        word = _preserve_word_case(source_word, str(form.word))
        candidate = text[:target_match.start()] + word + text[target_match.end():]
        key = candidate.casefold()
        if key not in seen:
            seen.add(key)
            forms.append(candidate)
        if len(forms) >= 12:
            break
    return tuple(forms)


@lru_cache(maxsize=4096)
def russian_morphology_info(value: str) -> dict[str, Any]:
    analyzer = _morph_analyzer()
    match = re.search(r"[А-Яа-яЁё-]+", value or "")
    if analyzer is None or match is None:
        return {}
    try:
        parsed = analyzer.parse(match.group(0))[0]
    except Exception:
        return {}
    pos_names = {
        "NOUN": "существительное", "ADJF": "прилагательное", "ADJS": "краткое прилагательное",
        "COMP": "сравнительная форма", "VERB": "глагол", "INFN": "инфинитив",
        "PRTF": "причастие", "PRTS": "краткое причастие", "GRND": "деепричастие",
        "NUMR": "числительное", "ADVB": "наречие", "NPRO": "местоимение",
        "PRED": "предикатив", "PREP": "предлог", "CONJ": "союз", "PRCL": "частица", "INTJ": "междометие",
    }
    case_names = {
        "nomn": "именительный", "gent": "родительный", "datv": "дательный",
        "accs": "винительный", "ablt": "творительный", "loct": "предложный",
        "voct": "звательный", "gen2": "второй родительный", "loc2": "второй предложный",
    }
    gender_names = {"masc": "мужской род", "femn": "женский род", "neut": "средний род"}
    number_names = {"sing": "единственное число", "plur": "множественное число"}
    tag = parsed.tag
    properties = [
        pos_names.get(getattr(tag, "POS", None), str(getattr(tag, "POS", "") or "")),
        case_names.get(getattr(tag, "case", None), ""),
        gender_names.get(getattr(tag, "gender", None), ""),
        number_names.get(getattr(tag, "number", None), ""),
    ]
    return {
        "word": match.group(0),
        "lemma": str(getattr(parsed, "normal_form", "")),
        "properties": [value for value in properties if value],
        "forms": list(russian_word_forms(match.group(0))),
        "known": bool(getattr(parsed, "is_known", False)),
    }


def check_with_local_dictionary(text: str, language: str = "ru", custom_words: Iterable[str] = ()) -> list[dict[str, Any]]:
    if not HAS_PYSPELLCHECKER or SpellChecker is None:
        raise TranslationError("локальный словарь не установлен; добавьте пакет pyspellchecker")
    dictionary_language = "ru" if language == "ru" else "en"
    checker = SpellChecker(language=dictionary_language, distance=1)
    checker.word_frequency.load_words([str(word).casefold() for word in custom_words if str(word).strip()])
    tokens = [(match.group(0), match.start()) for match in re.finditer(r"[A-Za-zА-Яа-яЁё-]{3,}", text)]
    morphology_enabled = language == "ru" and _morph_analyzer() is not None
    candidates_for_spellcheck = [
        word.casefold()
        for word, _ in tokens
        if not morphology_enabled or not is_known_russian_word(word)
    ]
    unknown = checker.unknown(candidates_for_spellcheck)
    results: list[dict[str, Any]] = []
    for word, offset in tokens:
        if word.casefold() not in unknown:
            continue
        candidates = checker.candidates(word.casefold()) or set()
        if morphology_enabled:
            try:
                normal = str(_morph_analyzer().parse(word)[0].normal_form)
                if normal and normal != word.casefold():
                    candidates.add(normal)
            except Exception:
                pass
        results.append(
            {
                "message": f"слово «{word}» не найдено в офлайн-словаре",
                "offset": offset,
                "length": len(word),
                "word": word,
                "suggestions": sorted(candidates)[:4],
                "rule": "OFFLINE_MORPHOLOGY" if morphology_enabled else "LOCAL_DICTIONARY",
            }
        )
    return results


def _trim_obvious_generation_loop(value: str) -> tuple[str, bool]:
    """Удаляет только очевидный повторяющийся хвост, не литературные повторы."""

    text = value.strip()
    lines = [line.rstrip() for line in text.splitlines()]
    while len(lines) >= 4 and lines[-1].strip() and lines[-1].strip() == lines[-2].strip() == lines[-3].strip():
        lines.pop()
    line_trimmed = "\n".join(lines).strip()
    if line_trimmed != text:
        return line_trimmed, True

    # Однострочные ответы иногда зацикливаются целыми предложениями. Оставляем
    # два повтора, но убираем очевидный хвост из трёх и более одинаковых фраз.
    sentence_parts = re.findall(r"\s*.+?(?:[.!?…]+(?=\s|$)|$)", text)
    normalised_parts = [_memory_key(part) for part in sentence_parts if part.strip()]
    if len(normalised_parts) >= 3:
        tail = normalised_parts[-1]
        repeated = 0
        for item in reversed(normalised_parts):
            if item != tail:
                break
            repeated += 1
        if repeated >= 3 and len(tail) >= 6:
            kept = sentence_parts[: len(sentence_parts) - repeated + 2]
            return "".join(kept).strip(), True

    tokens = re.findall(r"\S+", text)
    # Срезаем только хвост, повторённый минимум три раза и содержащий 4+ слова.
    for size in range(min(40, len(tokens) // 3), 3, -1):
        tail = tokens[-size:]
        if tokens[-2 * size:-size] == tail and tokens[-3 * size:-2 * size] == tail:
            return " ".join(tokens[:-2 * size]).strip(), True
    return text, False


def clean_ai_translation(value: str) -> str:
    text = re.sub(r"<think>.*?</think>", "", value or "", flags=re.DOTALL | re.IGNORECASE).strip()
    text = re.sub(r"^```(?:text|markdown)?\s*|\s*```$", "", text, flags=re.IGNORECASE).strip()
    prefixes = (
        "Вот перевод:",
        "Конечно! Вот перевод:",
        "Конечно, вот перевод:",
        "Перевод:",
        "Translation:",
        "Ответ:",
    )
    for prefix in prefixes:
        if text.casefold().startswith(prefix.casefold()):
            text = text[len(prefix):].strip()
            break
    text, _ = _trim_obvious_generation_loop(text)
    return text


def build_translation_prompt(
    source: str,
    *,
    previous: str = "",
    following: str = "",
    source_lang: str = "auto",
    target_lang: str = "ru",
    style: str = "literary",
    terminology: Iterable[str] = (),
    scene_context: str = "",
    edit_examples: Iterable[dict[str, str]] = (),
) -> str:
    source_name = LANG_NAMES.get(source_lang, source_lang)
    target_name = LANG_NAMES.get(target_lang, target_lang)
    instruction = STYLE_INSTRUCTIONS.get(style, STYLE_INSTRUCTIONS["literary"])
    context_parts = []
    if previous:
        context_parts.append(f"Предыдущий сегмент (только контекст): {previous}")
    if following:
        context_parts.append(f"Следующий сегмент (только контекст): {following}")
    context = "\n".join(context_parts)
    term_lines = [str(value).strip() for value in terminology if str(value).strip()]
    terms = "Обязательные варианты: " + "; ".join(term_lines) + ".\n" if term_lines else ""
    scene = f"Сцена/глава: {scene_context}.\n" if scene_context else ""
    examples = [
        f"Оригинал: {item.get('source', '')}\nУтверждённый перевод: {item.get('final', '')}"
        for item in edit_examples
        if item.get("source") and item.get("final")
    ]
    learned = "Предпочтения переводчика по прошлым правкам:\n" + "\n".join(examples) + "\n" if examples else ""
    return (
        f"Ты переводчик художественной прозы. Переведи один сегмент с {source_name} на {target_name}.\n"
        f"{instruction}\nСохрани имена, числа, кавычки и смысл. Не добавляй пояснений. "
        "Верни только перевод текущего сегмента.\n"
        f"{scene}{terms}{learned}"
        f"{context + chr(10) if context else ''}Текущий сегмент: {source}"
    )


def translate_with_ollama(source: str, config: dict[str, Any], previous: str = "", following: str = "") -> str:
    prompt = build_translation_prompt(
        source,
        previous=previous,
        following=following,
        source_lang=config.get("source_lang", "auto"),
        target_lang=config.get("target_lang", "ru"),
        style=config.get("translation_style", "literary"),
        terminology=config.get("terminology", ()),
        scene_context=str(config.get("scene_context", "")),
        edit_examples=config.get("edit_examples", ()),
    )
    payload = {
        "model": config.get("model") or DEFAULT_CONFIG["model"],
        "prompt": prompt,
        "stream": False,
        "think": False,
        "options": {"temperature": 0.25},
    }
    response = _request_json(normalise_ollama_generate_url(config.get("ollama_url", "")), payload=payload)
    translation = clean_ai_translation(response.get("response", "") if isinstance(response, dict) else "")
    if not translation:
        raise TranslationError("Ollama вернула пустой перевод")
    return translation


def translate_with_google(source: str, config: dict[str, Any]) -> str:
    params = urlencode(
        {
            "client": "gtx",
            "sl": config.get("source_lang", "auto"),
            "tl": config.get("target_lang", "ru"),
            "dt": "t",
            "q": source,
        }
    )
    response = _request_json(f"https://translate.googleapis.com/translate_a/single?{params}", timeout=30)
    try:
        translation = "".join(part[0] for part in response[0] if part and part[0])
    except (IndexError, TypeError) as exc:
        raise TranslationError("Google Translate вернул неожиданный ответ") from exc
    translation = clean_ai_translation(translation)
    if not translation:
        raise TranslationError("Google Translate вернул пустой перевод")
    return translation


def translate_with_custom_api(
    source: str,
    config: dict[str, Any],
    previous: str = "",
    following: str = "",
) -> str:
    endpoint = normalise_openai_chat_url(str(config.get("custom_api_url", "")))
    model = str(config.get("custom_api_model", "")).strip()
    if not model:
        raise TranslationError("в настройках пользовательского API не указана модель")
    prompt = build_translation_prompt(
        source,
        previous=previous,
        following=following,
        source_lang=config.get("source_lang", "auto"),
        target_lang=config.get("target_lang", "ru"),
        style=config.get("translation_style", "literary"),
        terminology=config.get("terminology", ()),
        scene_context=str(config.get("scene_context", "")),
        edit_examples=config.get("edit_examples", ()),
    )
    if endpoint.endswith("/responses"):
        payload = {
            "model": model,
            "instructions": "Верни только перевод без пояснений и рассуждений.",
            "input": prompt,
        }
    else:
        payload = {
            "model": model,
            "messages": [
                {"role": "system", "content": "Ты профессиональный переводчик художественной прозы. Верни только перевод."},
                {"role": "user", "content": prompt},
            ],
            "stream": False,
        }
    response = _request_json(
        endpoint,
        payload=payload,
        timeout=120,
        request_headers=custom_api_headers(config),
    )
    value: Any = response.get("output_text", "") if isinstance(response, dict) else ""
    if not value and isinstance(response, dict) and isinstance(response.get("output"), list):
        output_parts: list[str] = []
        for item in response["output"]:
            for part in item.get("content", []) if isinstance(item, dict) else []:
                if isinstance(part, dict) and part.get("text"):
                    output_parts.append(str(part["text"]))
        value = "".join(output_parts)
    if not value and isinstance(response, dict):
        try:
            value = response["choices"][0]["message"]["content"]
        except (KeyError, IndexError, TypeError):
            try:
                value = response["choices"][0]["text"]
            except (KeyError, IndexError, TypeError):
                value = ""
    if isinstance(value, list):
        value = "".join(
            str(part.get("text", "")) if isinstance(part, dict) else str(part)
            for part in value
        )
    translation = clean_ai_translation(str(value or ""))
    if not translation:
        raise TranslationError("пользовательский API вернул пустой перевод")
    return translation


def translate_segment_sync(
    source: str,
    config: dict[str, Any],
    previous: str = "",
    following: str = "",
) -> TranslationResult:
    selected = str(config.get("api_type", "google"))
    providers: list[tuple[str, dict[str, Any]]] = []
    request_id = uuid.uuid4().hex

    def add(provider: str, provider_config: dict[str, Any] | None = None) -> None:
        candidate = provider_config or config
        signature = (
            provider,
            str(candidate.get("custom_api_url", "")),
            str(candidate.get("custom_api_model", "")),
        )
        if any(
            existing_provider == signature[0]
            and str(existing_config.get("custom_api_url", "")) == signature[1]
            and str(existing_config.get("custom_api_model", "")) == signature[2]
            for existing_provider, existing_config in providers
        ):
            return
        providers.append((provider, candidate))

    add(selected)
    if config.get("fallback_enabled"):
        for provider in config.get("fallback_order", DEFAULT_CONFIG["fallback_order"]):
            if provider == "custom":
                runtime_profiles = config.get("api_profiles_runtime", [])
                for profile in runtime_profiles if isinstance(runtime_profiles, list) else []:
                    if isinstance(profile, dict) and profile.get("custom_api_model"):
                        add("custom", profile)
            elif provider != "ollama" or config.get("show_local_ai"):
                add(str(provider))

    errors: list[str] = []
    for provider, provider_config in providers:
        if PROVIDER_RATE_LIMITER.is_open(provider):
            errors.append(f"{provider}: временно отключён после нескольких ошибок")
            continue
        if provider == "google":
            try:
                configured_interval = float(provider_config.get("google_request_interval", 1.0))
            except (TypeError, ValueError):
                configured_interval = 1.0
            minimum_interval = max(0.8, configured_interval) + random.uniform(0.0, 0.2)
        elif provider == "custom":
            minimum_interval = 0.1
        else:
            minimum_interval = 0.0
        PROVIDER_RATE_LIMITER.acquire(provider)
        try:
            PROVIDER_RATE_LIMITER.wait(provider, minimum_interval)
            started = time.monotonic()
            try:
                if provider == "google":
                    raw = translate_with_google(source, provider_config)
                elif provider == "custom":
                    raw = translate_with_custom_api(source, provider_config, previous, following)
                elif provider == "ollama":
                    raw = translate_with_ollama(source, provider_config, previous, following)
                else:
                    continue
                text = clean_ai_translation(str(raw or ""))
                if not text:
                    raise TranslationError(f"{provider} вернул пустой перевод")
                PROVIDER_RATE_LIMITER.success(provider)
                return TranslationResult(
                    text=text,
                    provider=provider,
                    request_id=request_id,
                    latency_ms=max(0, int((time.monotonic() - started) * 1000)),
                    raw_text=str(raw or ""),
                )
            except Exception as exc:
                PROVIDER_RATE_LIMITER.failure(provider, exc)
                errors.append(f"{provider}: {exc}")
                if not config.get("fallback_enabled"):
                    raise
        finally:
            PROVIDER_RATE_LIMITER.release(provider)
    if errors:
        raise TranslationError("Все переводчики недоступны · " + " · ".join(errors))
    raise TranslationError("не выбран доступный переводчик")


def fetch_ollama_models(url: str) -> list[str]:
    response = _request_json(ollama_tags_url(url), timeout=5)
    if not isinstance(response, dict):
        return []
    models = [item.get("name", "") for item in response.get("models", []) if isinstance(item, dict)]
    return sorted({name for name in models if name})


def source_language_for_tts(source_lang: str, text: str) -> str:
    if source_lang != "auto":
        return source_lang
    if re.search(r"[а-яё]", text, flags=re.IGNORECASE):
        return "ru"
    if re.search(r"[ぁ-んァ-ン一-龯]", text):
        return "ja"
    if re.search(r"[가-힣]", text):
        return "ko"
    return "en"


class LiteraFlowApp:
    def __init__(self, page: ft.Page) -> None:
        self.page = page
        self.config = load_config()
        self.project_store = ProjectStore()
        self.secret_store = SecureSecretStore()
        self.session_api_keys: dict[str, str] = {}
        active_profile = str(self.config.get("active_api_profile", "") or "")
        stored_key = self.secret_store.get(active_profile)
        legacy_key = str(self.config.pop("_legacy_api_key", "") or "")
        if legacy_key and active_profile and self.secret_store.set(active_profile, legacy_key):
            stored_key = legacy_key
            try:
                save_config(self.config)
            except OSError:
                pass
        if active_profile and stored_key:
            self.session_api_keys[active_profile] = stored_key

        self.original_paragraphs: list[str] = []
        self.sentences: list[str] = []
        self.sentence_to_paragraph: list[int] = []
        self.paragraph_segments: list[list[int]] = []
        self.chapters: list[dict[str, Any]] = []
        self.translations: list[str] = []
        self.statuses: list[str] = []
        self.bookmarks: list[bool] = []
        self.translation_variants: list[dict[str, dict[str, str]]] = []
        self.active_variant_slots: list[str] = []
        self.segment_notes: list[dict[str, Any]] = []
        self.secondary_sources: list[dict[str, Any]] = []
        self.honorific_rules: list[dict[str, Any]] = []
        self.current_index = 0
        self.file_loaded = False
        self.project_file_path = ""
        self.project_file_name = ""
        self.source_hash = ""
        self.source_document_bytes = b""
        self.source_document_metadata: dict[str, Any] = {}
        self.progress_path = ""
        self.project_generation = 0
        self.last_saved_segment_states: list[tuple[Any, ...]] = []
        self.last_saved_reference_fingerprint = ""
        self.last_json_save_time = 0.0
        self.dirty_segments: set[int] = set()
        self.dirty_variants: set[int] = set()
        self.dirty_references = False
        self.dirty_project_extensions = False
        self.content_revision = 0
        self.translated_count_cache = 0
        self.confirmed_count_cache = 0
        self.qa_problem_count_cache = 0

        self.text_fields: list[ft.TextField] = []
        self.status_indicators: list[ft.Container] = []
        self.ai_buttons: list[ft.IconButton] = []
        self.bookmark_buttons: list[ft.IconButton] = []
        self.original_views: list[ft.Container] = []
        self.original_text_controls: list[ft.Text] = []
        self.preview_boxes: list[ft.Container] = []
        self.preview_text_controls: list[ft.Text] = []
        self.segment_views: list[ft.Container | None] = []
        self.rendered_indices: set[int] = set()
        self.rendered_paragraphs: set[int] = set()
        self.large_document_mode = False
        self.qa_issues: list[list[str]] = []
        self.qa_labels: list[ft.Text] = []
        self.glossary_entries: list[dict[str, Any]] = []
        self.character_entries: list[dict[str, Any]] = []
        self.custom_dictionary: list[str] = []
        self.deep_qa_cache: dict[int, list[dict[str, Any]]] = {}
        self.ai_drafts: dict[int, str] = {}
        self.edit_examples: list[dict[str, str]] = []
        self.translation_memory = load_translation_memory()
        self.undo_stack: list[dict[str, Any]] = []
        self.redo_stack: list[dict[str, Any]] = []
        self.history_suspended = False
        self.last_history_key: str | None = None
        self.last_history_time = 0.0
        self.segment_filter = "all"
        self.session_api_key = self.session_api_keys.get(active_profile, "") or os.environ.get("LITERAFLOW_API_KEY", "")
        if active_profile and self.session_api_key:
            self.session_api_keys[active_profile] = self.session_api_key

        self.busy_segments: set[int] = set()
        self.loading_file = False
        self.batch_running = False
        self.batch_cancel_requested = False
        self.batch_job_id = ""
        self.segment_lock_tokens: dict[int, str] = {}
        self.navigation_generation = 0
        self.cursor_fallback_notified = False
        self.autosave_revision = 0
        self.search_matches: list[int] = []
        self.search_position = -1
        self.last_search = ""
        self.audio_player = None
        self.pending_export: tuple[str, bytes] | None = None
        self.pending_tmx_export: tuple[str, bytes] | None = None
        self.zen_mode = False
        self.layout_state: tuple[bool, bool, bool] | None = None
        self.highlighted_index = -1
        self.highlighted_paragraph = -1
        self.last_confirmation: tuple[int, int, str] | None = None
        self.last_structure_snapshot: dict[str, Any] | None = None
        self.mobile_field_syncing = False
        self.reader_chapter_index = 0
        self.reader_page_index = 0
        self.pending_export_choose_path = False

        self._set_palette()
        self._configure_page()
        self._build_controls()
        self._mount()

    def _set_palette(self) -> None:
        dark = self.config.get("theme", "dark") == "dark"
        preset = ACCENT_PRESETS.get(self.config.get("accent_color_preset", "cyan"), ACCENT_PRESETS["cyan"])
        self.theme_mode = ft.ThemeMode.DARK if dark else ft.ThemeMode.LIGHT
        self.accent = preset["dark" if dark else "light"]
        self.bg_color = "#111419" if dark else "#F4F1EB"
        self.card_bg = "#1A1F26" if dark else "#FFFCF7"
        self.editor_bg = "#20262F" if dark else "#FFFFFF"
        self.control_bg = "#272E38" if dark else "#E9E4DB"
        self.text_color = "#E8EBEF" if dark else "#27292E"
        self.muted_color = "#9CA5B1" if dark else "#68707A"
        self.appbar_bg = "#15191F" if dark else "#ECE7DE"
        self.border_color = "#303844" if dark else "#DCD6CC"
        self.divider_color = "#2A313B" if dark else "#DDD7CD"
        self.progress_track_color = "#29313B" if dark else "#DED8CE"
        self.button_text = "#10211F" if dark else "#FFFFFF"
        self.danger_bg = "#3A2529" if dark else "#F3E1E1"
        self.danger_text = "#F1A4A5" if dark else "#922F36"
        self.soft_accent = "rgba(103,201,190,0.12)" if dark else "rgba(22,127,118,0.09)"
        self.card_shadow = ft.BoxShadow(
            spread_radius=0,
            blur_radius=14,
            color="rgba(0,0,0,0.14)" if dark else "rgba(58,45,30,0.07)",
            offset=ft.Offset(0, 4),
        )

    def _configure_page(self) -> None:
        self.page.title = APP_WINDOW_TITLE
        self.page.theme_mode = self.theme_mode
        self.page.bgcolor = self.bg_color
        self.page.padding = 12
        try:
            self.page.window.width = 1300
            self.page.window.height = 850
            self.page.window.min_width = 360
            self.page.window.min_height = 600
        except (AttributeError, RuntimeError):
            self.page.window_width = 1300
            self.page.window_height = 850

    def _button(
        self,
        text: str,
        handler,
        *,
        bgcolor: str | None = None,
        icon: str | None = None,
        tooltip: str | None = None,
        primary: bool = False,
        danger: bool = False,
    ):
        resolved_bg = bgcolor or (self.danger_bg if danger else self.accent if primary else self.control_bg)
        resolved_color = self.danger_text if danger else self.button_text if primary else self.text_color
        return ft.ElevatedButton(
            text=text,
            icon=icon,
            color=resolved_color,
            bgcolor=resolved_bg,
            elevation=0,
            on_click=handler,
            tooltip=tooltip,
        )

    def _welcome_step(self, number: str, title: str, detail: str) -> ft.Container:
        return ft.Container(
            content=ft.Row(
                [
                    ft.Container(
                        content=ft.Text(number, color=self.button_text, weight=ft.FontWeight.BOLD),
                        width=30,
                        height=30,
                        border_radius=15,
                        bgcolor=self.accent,
                        alignment=ft.alignment.center,
                    ),
                    ft.Column(
                        [
                            ft.Text(title, color=self.text_color, weight=ft.FontWeight.BOLD, size=12),
                            ft.Text(detail, color=self.muted_color, size=10, max_lines=2),
                        ],
                        spacing=1,
                    ),
                ],
                spacing=8,
            ),
            width=255,
            padding=10,
            bgcolor=self.card_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=12,
        )

    def _build_controls(self) -> None:
        self.brand_mark = ft.Container(width=5, height=30, bgcolor=self.accent, border_radius=4)
        self.app_title_text = ft.Text(APP_TITLE, color=self.text_color, weight=ft.FontWeight.BOLD, size=17)
        self.app_tagline_text = ft.Text(APP_TAGLINE, color=self.muted_color, size=10)
        self.app_brand = ft.Row(
            [
                self.brand_mark,
                ft.Column([self.app_title_text, self.app_tagline_text], spacing=0),
            ],
            spacing=9,
            vertical_alignment=ft.CrossAxisAlignment.CENTER,
        )
        self.page.appbar = ft.AppBar(
            title=self.app_brand,
            bgcolor=self.appbar_bg,
            center_title=False,
            elevation=0,
            actions=[
                ft.IconButton(icon="spa_outlined", icon_color=self.muted_color, tooltip="Режим Дзен", on_click=self.toggle_zen_mode),
                ft.IconButton(icon="collections_bookmark_outlined", icon_color=self.muted_color, tooltip="Библиотека проектов", on_click=self.open_project_library),
                ft.IconButton(icon="help_outline", icon_color=self.muted_color, tooltip="Горячие клавиши", on_click=self.open_help),
                ft.IconButton(icon="settings_outlined", icon_color=self.muted_color, tooltip="Настройки", on_click=self.open_settings_sheet),
            ],
        )

        self.help_dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Работа в LiteraFlow"),
            content=ft.Text(
                "Ctrl + Enter — подтвердить текущий сегмент и перейти дальше\n"
                "Alt + ↑ / Alt + ↓ — предыдущий / следующий сегмент\n"
                "Ctrl + S — немедленно сохранить прогресс\n"
                "Ctrl + Z / Ctrl + Y — отменить / вернуть изменение\n"
                "Ctrl + Shift + Пробел — переключить вариант перевода\n"
                "Enter — обычный перенос строки внутри перевода\n\n"
                "Телефон: свайпайте по карточке оригинала для перехода между сегментами. "
                "Кнопка ✓ подтверждает перевод и открывает следующий.\n"
                "Помощник перевода запускается только вручную; автозаполнение включается отдельно в настройках.\n\n"
                "Кнопка библиотеки открывает книги, главы и сводку качества. На очень больших книгах редактор показывает окно из 120 сегментов — данные остальных сегментов остаются загружены и доступны через поиск и навигацию.\n\n"
                "EPUB: режим «сохранить оформление» оставляет обложку, иллюстрации, CSS, оглавление и структуру глав. Карточка «Оформление под защитой» показывает, что будет перенесено.\n\n"
                "Проекты хранятся в локальной SQLite-базе вместе со сжатым исходником. JSON рядом с книгой остаётся переносимой резервной копией. Русская морфология и склонения имён работают офлайн.\n\n"
                "Красный — пусто · жёлтый — черновик · зелёный — подтверждено",
                size=14,
            ),
            actions=[ft.TextButton(text="Понятно", on_click=lambda e: self._close(self.help_dialog))],
        )

        self.file_info_text = ft.Text(
            "Файл не загружен",
            size=12,
            color=self.text_color,
            weight=ft.FontWeight.W_500,
            text_align=ft.TextAlign.CENTER,
            max_lines=2,
            overflow=ft.TextOverflow.ELLIPSIS,
            expand=True,
        )
        self.file_info_banner = ft.Container(
            content=ft.Row(
                [ft.Icon(name="insert_drive_file", color=self.accent, size=16), self.file_info_text],
                spacing=8,
                alignment=ft.MainAxisAlignment.CENTER,
            ),
            padding=ft.padding.symmetric(horizontal=16, vertical=8),
            bgcolor=self.card_bg,
            border_radius=25,
            border=ft.border.all(1, self.border_color),
            alignment=ft.alignment.center,
            margin=ft.margin.only(left=12, right=12, bottom=4),
        )
        self.save_status_indicator = ft.Text("", color=STATUS_COLORS[STATUS_CONFIRMED], size=11, italic=True)
        self.progress_bar = ft.ProgressBar(value=0, bar_height=3, color=self.accent, bgcolor=self.progress_track_color, visible=False)

        self.import_picker = ft.FilePicker(on_result=self.on_import_result)
        self.export_picker = ft.FilePicker(on_result=self.on_export_result)
        self.tmx_import_picker = ft.FilePicker(on_result=self.on_tmx_import_result)
        self.tmx_export_picker = ft.FilePicker(on_result=self.on_tmx_export_result)
        self.dual_raw_picker = ft.FilePicker(on_result=self.on_dual_raw_result)
        self.page.overlay.extend([self.import_picker, self.export_picker, self.tmx_import_picker, self.tmx_export_picker, self.dual_raw_picker])

        self.drop_zone_icon = ft.Icon(name="note_add_outlined", color=self.accent, size=28)
        self.drop_zone_text = ft.Text(
            "Открыть рукопись\nTXT · MD · DOCX · EPUB · FB2 · XLIFF",
            color=self.text_color,
            size=14,
            weight=ft.FontWeight.W_500,
        )
        self.drop_zone = ft.Container(
            content=ft.Row(
                [self.drop_zone_icon, self.drop_zone_text],
                spacing=12,
                alignment=ft.MainAxisAlignment.CENTER,
                vertical_alignment=ft.CrossAxisAlignment.CENTER,
            ),
            width=360,
            height=66,
            border=ft.border.all(1, self.border_color),
            border_radius=12,
            alignment=ft.alignment.center,
            bgcolor=self.editor_bg,
            on_click=self.open_import_picker,
            on_hover=self.on_zone_hover,
        )
        self.file_path_input = ft.TextField(
            label="Путь к файлу",
            hint_text="C:/Книги/novel.epub",
            width=330,
            border_color=self.border_color,
            focused_border_color=self.accent,
            text_style=ft.TextStyle(color=self.text_color, size=14),
            value=self.config.get("last_file", ""),
            on_submit=lambda e: self.start_load_path(self.file_path_input.value),
        )
        self.load_button = self._button(
            "Загрузить",
            lambda e: self.start_load_path(self.file_path_input.value),
            icon="folder_open",
            primary=True,
        )

        self.search_input = ft.TextField(
            label="Поиск в оригинале и переводе",
            hint_text="Слово или фраза",
            width=300,
            border_color=self.border_color,
            focused_border_color=self.accent,
            text_style=ft.TextStyle(color=self.text_color, size=14),
            on_submit=lambda e: self.search_in_text(self.search_input.value),
        )
        self.search_button = self._button("Найти далее", lambda e: self.search_in_text(self.search_input.value), icon="search")

        self.file_row = ft.Row(
            [self.file_path_input, self.load_button],
            alignment=ft.MainAxisAlignment.CENTER,
            vertical_alignment=ft.CrossAxisAlignment.CENTER,
            wrap=True,
            spacing=8,
        )
        self.search_row = ft.Row(
            [self.search_input, self.search_button],
            alignment=ft.MainAxisAlignment.CENTER,
            vertical_alignment=ft.CrossAxisAlignment.CENTER,
            wrap=True,
            spacing=8,
        )
        self.header_actions = ft.Column(
            [self.file_row, self.search_row],
            width=440,
            spacing=8,
            horizontal_alignment=ft.CrossAxisAlignment.CENTER,
        )
        self.header_panel = ft.Container(
            content=ft.Row(
                [self.drop_zone, self.header_actions],
                wrap=True,
                spacing=18,
                run_spacing=10,
                alignment=ft.MainAxisAlignment.CENTER,
                vertical_alignment=ft.CrossAxisAlignment.CENTER,
            ),
            padding=12,
            bgcolor=self.card_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=14,
        )
        self.header_tile = ft.ExpansionTile(
            title=ft.Row(
                [
                    ft.Icon(name="folder_open", color=self.accent, size=18),
                    ft.Text("Файл, загрузка и поиск", size=14, weight=ft.FontWeight.W_500, color=self.text_color),
                ],
                spacing=8,
            ),
            controls=[],
            initially_expanded=False,
        )

        self.welcome_recent_column = ft.Column(spacing=6)
        self.welcome_continue_title = ft.Text(
            "Продолжить последнюю книгу",
            color=self.text_color,
            weight=ft.FontWeight.BOLD,
            size=15,
            max_lines=1,
            overflow=ft.TextOverflow.ELLIPSIS,
        )
        self.welcome_continue_details = ft.Text(
            "Приложение восстановит сегмент, варианты и заметки.",
            color=self.muted_color,
            size=11,
            max_lines=2,
            overflow=ft.TextOverflow.ELLIPSIS,
        )
        self.welcome_continue_button = self._button(
            "Продолжить перевод",
            self.continue_last_project,
            icon="play_arrow",
            primary=True,
        )
        self.welcome_continue_card = ft.Container(
            content=ft.Column(
                [
                    ft.Row(
                        [
                            ft.Container(
                                content=ft.Icon(name="auto_stories", color=self.accent, size=24),
                                width=46,
                                height=46,
                                bgcolor=self.soft_accent,
                                border_radius=12,
                                alignment=ft.alignment.center,
                            ),
                            ft.Column([self.welcome_continue_title, self.welcome_continue_details], spacing=2, expand=True),
                        ],
                        spacing=12,
                    ),
                    self.welcome_continue_button,
                ],
                spacing=12,
            ),
            padding=16,
            bgcolor=self.card_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=16,
            width=440,
        )
        self.welcome_panel = ft.Container(
            content=ft.Column(
                [
                    ft.Container(height=8),
                    ft.Text(APP_TITLE, size=34, color=self.text_color, weight=ft.FontWeight.BOLD),
                    ft.Text(APP_TAGLINE, size=15, color=self.accent, weight=ft.FontWeight.W_500),
                    ft.Text(
                        "Спокойная среда для художественного перевода: оригинал, редактор и книга остаются в одном потоке.",
                        size=13,
                        color=self.muted_color,
                        text_align=ft.TextAlign.CENTER,
                        max_lines=3,
                    ),
                    ft.Row(
                        [
                            self._button("Открыть рукопись", self.open_import_picker, icon="folder_open", primary=True),
                            self._button("Библиотека", self.open_project_library, icon="collections_bookmark_outlined"),
                        ],
                        alignment=ft.MainAxisAlignment.CENTER,
                        spacing=10,
                        wrap=True,
                    ),
                    self.welcome_continue_card,
                    ft.Row(
                        [
                            self._welcome_step("1", "Откройте", "TXT, DOCX, EPUB, FB2 или XLIFF"),
                            self._welcome_step("2", "Переводите", "Правьте сегмент и нажимайте «Готово»"),
                            self._welcome_step("3", "Вычитайте", "Проверьте книгу и экспортируйте"),
                        ],
                        alignment=ft.MainAxisAlignment.CENTER,
                        spacing=10,
                        run_spacing=10,
                        wrap=True,
                    ),
                    self.welcome_recent_column,
                    ft.Text(
                        "На телефоне используйте системное окно выбора файла — путь вручную вводить не нужно.",
                        color=self.muted_color,
                        size=10,
                        text_align=ft.TextAlign.CENTER,
                    ),
                ],
                horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                spacing=14,
                scroll=ft.ScrollMode.AUTO,
            ),
            expand=True,
            alignment=ft.alignment.top_center,
            padding=ft.padding.symmetric(horizontal=8, vertical=6),
        )

        self.left_list = ft.ListView(expand=True, spacing=4)
        self.left_column = ft.Container(
            content=ft.Column(
                [
                    ft.Row(
                        [
                            ft.Row(
                                [
                                    ft.Icon(name="menu_book_outlined", color=self.accent, size=18),
                                    ft.Text("Оригинал", color=self.text_color, weight=ft.FontWeight.BOLD, size=14),
                                ],
                                spacing=8,
                            ),
                            ft.TextButton(text="Карта глав", icon="toc", on_click=self.open_project_library),
                        ],
                        spacing=8,
                        alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                    ),
                    self.left_list,
                ],
                expand=True,
            ),
            bgcolor=self.card_bg,
            border_radius=12,
            padding=10,
            border=ft.border.all(1, self.border_color),
            expand=2,
        )

        self.preview_list = ft.ListView(expand=True, spacing=8)
        self.right_column = ft.Container(
            content=ft.Column(
                [
                    ft.Row(
                        [
                            ft.Icon(name="auto_stories_outlined", color=self.accent, size=18),
                            ft.Text("Книга", color=self.text_color, weight=ft.FontWeight.BOLD, size=14),
                            ft.Text("живой просмотр", color=self.muted_color, size=11),
                        ],
                        spacing=8,
                    ),
                    self.preview_list,
                ],
                expand=True,
            ),
            bgcolor=self.card_bg,
            border_radius=12,
            padding=10,
            border=ft.border.all(1, self.border_color),
            expand=3,
        )

        self.workspace_list = ft.ListView(expand=True, spacing=10)
        self.batch_button = self._button(
            "Автопилот пустых сегментов",
            self.toggle_batch_translation,
            tooltip="Перевести только пустые сегменты; повторное нажатие остановит процесс",
        )
        self.batch_progress_text = ft.Text("", size=11, color=self.muted_color)
        self.previous_button = self._button("Назад", lambda e: self.move_segment(-1), icon="arrow_upward")
        self.next_button = self._button("Далее", lambda e: self.move_segment(1), icon="arrow_downward")
        self.next_empty_button = self._button(
            "Непереведённый",
            self.jump_next_untranslated,
            icon="skip_next",
        )
        self.next_bookmark_button = self._button(
            "Закладка",
            self.jump_next_bookmark,
            icon="bookmark",
        )
        self.qa_button = self._button("QA", self.open_qa_sheet, icon="fact_check")
        self.undo_button = ft.IconButton(
            icon="undo",
            icon_color=self.muted_color,
            tooltip="Отменить · Ctrl+Z",
            disabled=True,
            on_click=self.undo_history,
        )
        self.redo_button = ft.IconButton(
            icon="redo",
            icon_color=self.muted_color,
            tooltip="Вернуть · Ctrl+Y",
            disabled=True,
            on_click=self.redo_history,
        )
        self.memory_button = ft.IconButton(
            icon="history",
            icon_color=self.muted_color,
            tooltip="Память переводов",
            on_click=self.open_memory_sheet,
        )
        self.reference_button = ft.IconButton(
            icon="library_books",
            icon_color=self.muted_color,
            tooltip="Глоссарий и персонажи",
            on_click=self.open_reference_sheet,
        )
        self.project_library_button = ft.IconButton(
            icon="collections_bookmark_outlined",
            icon_color=self.muted_color,
            tooltip="Книги и главы",
            on_click=self.open_project_library,
        )
        self.reader_button = ft.IconButton(
            icon="chrome_reader_mode_outlined",
            icon_color=self.muted_color,
            tooltip="Режим вычитки",
            on_click=self.open_reader_mode,
        )
        self.segment_tools_button = ft.IconButton(
            icon="more_horiz",
            icon_color=self.muted_color,
            tooltip="Инструменты текущего сегмента",
            on_click=self.open_segment_tools,
        )
        self.ai_menu_button = ft.IconButton(
            icon="translate",
            icon_color=self.muted_color,
            tooltip="Помощник перевода",
            on_click=self.open_ai_sheet,
        )
        self.editor_position_text = ft.Text("Сегмент —", size=11, color=self.muted_color)
        self.memory_hint_text = ft.Text("", size=11, color=self.accent, tooltip="Лучшее совпадение памяти переводов")
        self.desktop_variant_buttons = {
            slot: self._button(
                TRANSLATION_VARIANT_LABELS[slot],
                lambda e, selected=slot: self.switch_translation_variant(selected),
                tooltip=f"Переключить на вариант «{TRANSLATION_VARIANT_LABELS[slot]}»",
            )
            for slot in TRANSLATION_VARIANT_SLOTS
        }
        self.desktop_variant_bar = ft.Row(
            list(self.desktop_variant_buttons.values()),
            spacing=5,
            wrap=True,
        )
        self.desktop_glossary_chips = ft.Row([], spacing=4, wrap=True)
        self.desktop_dual_raw_text = ft.Text("", size=11, color=self.muted_color, selectable=True)
        self.desktop_dual_raw_card = ft.Container(
            content=self.desktop_dual_raw_text,
            visible=False,
            bgcolor=self.editor_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=8,
            padding=8,
        )
        self.desktop_cat_context = ft.Column(
            [self.desktop_variant_bar, self.desktop_glossary_chips, self.desktop_dual_raw_card],
            spacing=5,
        )
        self.workspace_heading = ft.Row(
            [
                ft.Row(
                    [
                        ft.Icon(name="edit_note", color=self.accent, size=19),
                        ft.Text("Редактор", color=self.text_color, weight=ft.FontWeight.BOLD, size=14),
                    ],
                    spacing=8,
                ),
                ft.Row([self.memory_hint_text, self.editor_position_text, self.batch_progress_text], spacing=10),
            ],
            alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
        )
        self.workspace_toolbar = ft.Row(
            [
                self.previous_button,
                self.next_button,
                self.next_empty_button,
                self.next_bookmark_button,
                self.qa_button,
                self.undo_button,
                self.redo_button,
                self.memory_button,
                self.reference_button,
                self.project_library_button,
                self.reader_button,
                self.segment_tools_button,
                self.ai_menu_button,
            ],
            wrap=True,
            spacing=6,
            run_spacing=6,
        )
        self.workspace_column = ft.Column(
            [self.workspace_heading, self.workspace_toolbar, self.desktop_cat_context, self.workspace_list],
            expand=5,
            spacing=6,
        )

        self.export_format = ft.Dropdown(
            label="Формат",
            value="txt",
            width=310,
            options=[
                ft.dropdown.Option("txt", "TXT — готовый перевод"),
                ft.dropdown.Option("docx", "DOCX — готовый перевод"),
                ft.dropdown.Option("docx_preserve", "DOCX — сохранить оформление исходника"),
                ft.dropdown.Option("docx_bilingual", "DOCX — оригинал | перевод"),
                ft.dropdown.Option("epub_preserve", "EPUB — сохранить оформление исходника"),
                ft.dropdown.Option("epub", "EPUB — новая чистая книга"),
                ft.dropdown.Option("fb2", "FB2 — электронная книга"),
                ft.dropdown.Option("xliff", "XLIFF 2.0 — обмен с CAT"),
            ],
            on_change=self.on_export_format_change,
        )
        self.export_include_original = ft.Checkbox(
            label="Подставлять оригинал вместо пустых сегментов",
            value=True,
        )
        self.export_complex_policy = ft.Dropdown(
            label="Сложное оформление",
            value=self.config.get("complex_format_policy", "error"),
            width=310,
            options=[
                ft.dropdown.Option("error", "Остановиться и предупредить"),
                ft.dropdown.Option("clean", "Упростить только сложные блоки"),
                ft.dropdown.Option("keep_original", "Оставить сложные блоки в оригинале"),
            ],
            on_change=self.on_export_format_change,
            visible=False,
        )
        self.export_path_input = ft.TextField(
            label="Путь сохранения (можно оставить пустым)",
            hint_text="C:/Книги/novel_ru.txt",
            width=350,
            border_color=self.border_color,
            focused_border_color=self.accent,
            text_style=ft.TextStyle(color=self.text_color, size=14),
            value=self.config.get("last_export", ""),
        )
        self.export_button = self._button("Экспорт", self.export_now, icon="save_alt", primary=True)
        self.export_as_button = self._button("Выбрать место", self.choose_export_path, icon="folder")
        self.copy_all_button = self._button("Копировать всё", self.copy_all_translation, icon="content_copy")
        self.export_note = ft.Text("", size=11, color=self.muted_color, text_align=ft.TextAlign.CENTER)
        self.fidelity_title = ft.Text("Оформление под защитой", color=self.text_color, weight=ft.FontWeight.BOLD, size=12)
        self.fidelity_details = ft.Text("", color=self.muted_color, size=11, max_lines=3, overflow=ft.TextOverflow.ELLIPSIS)
        self.fidelity_card = ft.Container(
            content=ft.Row(
                [
                    ft.Icon(name="verified_user_outlined", color=self.accent, size=20),
                    ft.Column([self.fidelity_title, self.fidelity_details], spacing=1, expand=True),
                ],
                spacing=10,
            ),
            visible=False,
            padding=ft.padding.symmetric(horizontal=12, vertical=9),
            bgcolor=self.soft_accent,
            border=ft.border.all(1, self.accent),
            border_radius=10,
        )
        self.export_panel = ft.Container(
            content=ft.Column(
                [
                    ft.Row(
                        [
                            ft.Icon(name="ios_share", color=self.accent, size=18),
                            ft.Text("Экспорт", color=self.text_color, weight=ft.FontWeight.BOLD, size=15),
                        ],
                        spacing=8,
                    ),
                    self.fidelity_card,
                    ft.Row([self.export_format, self.export_include_original], wrap=True, alignment=ft.MainAxisAlignment.CENTER),
                    self.export_complex_policy,
                    ft.Row(
                        [self.export_path_input, self.export_button, self.export_as_button, self.copy_all_button],
                        wrap=True,
                        spacing=8,
                        run_spacing=8,
                        alignment=ft.MainAxisAlignment.CENTER,
                    ),
                    self.export_note,
                ],
                spacing=8,
                horizontal_alignment=ft.CrossAxisAlignment.CENTER,
            ),
            bgcolor=self.card_bg,
            border_radius=12,
            padding=12,
            border=ft.border.all(1, self.border_color),
        )
        self.export_preflight_title = ft.Text("Проверка перед экспортом", color=self.text_color, weight=ft.FontWeight.BOLD, size=17)
        self.export_preflight_summary = ft.Text("", color=self.text_color, size=13)
        self.export_preflight_details = ft.Column(spacing=6)
        self.export_preflight_go_to_issue = ft.TextButton(
            text="Перейти к первой проблеме",
            icon="fact_check",
            on_click=self.jump_from_export_preflight,
        )
        self.export_preflight_dialog = ft.AlertDialog(
            modal=True,
            title=self.export_preflight_title,
            content=ft.Column(
                [
                    self.export_preflight_summary,
                    self.export_preflight_details,
                    ft.Text(
                        "Экспорт не меняет проект. Пустые сегменты будут обработаны согласно выбранной настройке.",
                        color=self.muted_color,
                        size=10,
                    ),
                ],
                spacing=10,
                tight=True,
                scroll=ft.ScrollMode.AUTO,
            ),
            actions=[
                self.export_preflight_go_to_issue,
                ft.TextButton(text="Отмена", on_click=lambda e: self._close(self.export_preflight_dialog)),
                ft.ElevatedButton(
                    text="Экспортировать",
                    icon="save_alt",
                    bgcolor=self.accent,
                    color=self.button_text,
                    elevation=0,
                    on_click=self.confirm_export_preflight,
                ),
            ],
        )

        self._build_settings_controls()
        self._build_utility_sheets()
        self._build_mobile_controls()

        self.desktop_row = ft.Row(
            [],
            expand=True,
            spacing=12,
            vertical_alignment=ft.CrossAxisAlignment.STRETCH,
        )
        self.mobile_holder = ft.Container(expand=True)
        self.mobile_panes = [self.left_column, self.mobile_editor_panel, self.reader_panel, self.export_panel]
        self.mobile_navbar = ft.NavigationBar(
            selected_index=0,
            bgcolor=self.appbar_bg,
            indicator_color=self.soft_accent,
            elevation=0,
            destinations=[
                ft.NavigationBarDestination(icon="menu_book_outlined", selected_icon="menu_book", label="Книга"),
                ft.NavigationBarDestination(icon="edit_note_outlined", selected_icon="edit_note", label="Редактор"),
                ft.NavigationBarDestination(icon="chrome_reader_mode_outlined", selected_icon="chrome_reader_mode", label="Чтение"),
                ft.NavigationBarDestination(icon="ios_share", selected_icon="ios_share", label="Экспорт"),
            ],
            on_change=self.on_mobile_nav_change,
        )
        self.swipe_dx = 0.0
        self.mobile_box = ft.Column([self.mobile_holder, self.mobile_navbar], expand=True, spacing=0)

        self.status_row = ft.Row([self.save_status_indicator], alignment=ft.MainAxisAlignment.END)
        self.divider = ft.Divider(height=8, color=self.divider_color)
        self.content_column = ft.Column([], expand=True, spacing=8)

    def _build_settings_controls(self) -> None:
        local_ai_visible = bool(self.config.get("show_local_ai", False))
        active_profile_data = self.active_api_profile_data()
        configured_backend = self.config.get("api_type", "google")
        if configured_backend == "ollama" and not local_ai_visible:
            configured_backend = "google"
        self.settings_api_type = ft.Dropdown(
            label="Способ перевода",
            options=[
                ft.dropdown.Option("google", "Google Translate · онлайн, без ключа"),
                ft.dropdown.Option("custom", "Свой API · OpenAI-совместимый"),
                *([ft.dropdown.Option("ollama", "Ollama · локальная модель")] if local_ai_visible else []),
            ],
            value=configured_backend,
            width=310,
            on_change=self.on_api_type_change,
        )
        self.settings_model = ft.Dropdown(
            label="Модель Ollama",
            options=[ft.dropdown.Option(self.config.get("model", DEFAULT_CONFIG["model"]))],
            value=self.config.get("model", DEFAULT_CONFIG["model"]),
            width=310,
        )
        self.settings_ollama_url = ft.TextField(
            label="URL Ollama",
            hint_text="http://localhost:11434 или http://192.168.1.10:11434",
            value=self.config.get("ollama_url", DEFAULT_CONFIG["ollama_url"]),
            width=310,
        )
        self.settings_api_profile = ft.Dropdown(
            label="API-профиль",
            options=[ft.dropdown.Option(profile["id"], profile["name"]) for profile in self.config.get("api_profiles", [])],
            value=self.config.get("active_api_profile", ""),
            width=310,
            on_change=self.on_api_profile_change,
        )
        self.settings_custom_name = ft.TextField(
            label="Название подключения",
            hint_text="Например, DeepSeek или OpenRouter",
            value=active_profile_data.get("name", self.config.get("custom_api_name", "Мой API")),
            width=310,
        )
        self.settings_custom_url = ft.TextField(
            label="URL chat completions / responses",
            hint_text="https://api.example.com/v1/chat/completions",
            value=active_profile_data.get("url", self.config.get("custom_api_url", DEFAULT_CONFIG["custom_api_url"])),
            width=310,
        )
        self.settings_custom_model = ft.TextField(
            label="Название модели",
            hint_text="deepseek-chat или openai/gpt-4.1-mini",
            value=active_profile_data.get("model", self.config.get("custom_api_model", "")),
            width=310,
        )
        self.settings_custom_key = ft.TextField(
            label="API-ключ",
            hint_text="Можно оставить пустым для локального сервера",
            value=self.session_api_keys.get(str(active_profile_data.get("id", "")), self.session_api_key),
            password=True,
            can_reveal_password=True,
            width=310,
        )
        self.settings_custom_key_header = ft.TextField(
            label="Заголовок API-ключа",
            hint_text="Authorization или x-api-key",
            value=active_profile_data.get("key_header", self.config.get("custom_api_key_header", "Authorization")),
            width=310,
        )
        self.settings_custom_headers = ft.TextField(
            label="Дополнительные заголовки · JSON",
            hint_text='{"HTTP-Referer":"https://example.com"}',
            value=active_profile_data.get("headers", self.config.get("custom_api_headers", "")),
            multiline=True,
            min_lines=1,
            max_lines=3,
            width=310,
        )
        self.settings_remember_api_key = ft.Switch(
            label="Хранить ключ в защищённом сейфе",
            value=bool(self.config.get("remember_api_key", False)),
        )
        self.settings_fallback_enabled = ft.Switch(
            label="Автоматически пробовать резервный переводчик при ошибке",
            value=bool(self.config.get("fallback_enabled", False)),
        )
        self.secret_storage_status = ft.Text(self.secret_store.description(), size=11, color=self.muted_color)
        self.custom_api_status = ft.Text("", size=11, color=self.muted_color)
        self.custom_api_group = ft.Column(
            [
                ft.Text(
                    "Профили подходят для DeepSeek, OpenRouter, OpenAI, LM Studio и других совместимых серверов. Секреты отделены от обычных настроек.",
                    size=11,
                    color=self.muted_color,
                ),
                self.settings_api_profile,
                ft.Row(
                    [
                        self._button("Новый профиль", self.new_api_profile, icon="add"),
                        self._button("Удалить", self.delete_api_profile, icon="delete_outline", danger=True),
                    ],
                    alignment=ft.MainAxisAlignment.CENTER,
                    wrap=True,
                ),
                self.settings_custom_name,
                self.settings_custom_url,
                self.settings_custom_model,
                self.settings_custom_key,
                self.settings_custom_key_header,
                self.settings_custom_headers,
                self.settings_remember_api_key,
                self.secret_storage_status,
                self._button("Проверить подключение", self.start_custom_api_test, icon="cable"),
                self.custom_api_status,
            ],
            visible=configured_backend == "custom",
            spacing=8,
            horizontal_alignment=ft.CrossAxisAlignment.CENTER,
        )
        language_options = [
            ft.dropdown.Option("en", "Английский"),
            ft.dropdown.Option("ja", "Японский"),
            ft.dropdown.Option("zh-CN", "Китайский"),
            ft.dropdown.Option("ko", "Корейский"),
            ft.dropdown.Option("ru", "Русский"),
            ft.dropdown.Option("de", "Немецкий"),
            ft.dropdown.Option("fr", "Французский"),
            ft.dropdown.Option("es", "Испанский"),
        ]
        self.settings_source_lang = ft.Dropdown(
            label="Язык оригинала",
            options=[ft.dropdown.Option("auto", "Определять автоматически"), *language_options],
            value=self.config.get("source_lang", "auto"),
            width=310,
        )
        self.settings_target_lang = ft.Dropdown(
            label="Язык перевода",
            options=language_options,
            value=self.config.get("target_lang", "ru"),
            width=310,
        )
        self.settings_style = ft.Dropdown(
            label="Стиль AI-перевода · свой API / Ollama",
            options=[
                ft.dropdown.Option("general", "Нейтральный"),
                ft.dropdown.Option("technical", "Точный"),
                ft.dropdown.Option("literary", "Художественный"),
                ft.dropdown.Option("literal", "Дословный"),
            ],
            value=self.config.get("translation_style", "literary"),
            width=310,
        )
        self.settings_accent = ft.Dropdown(
            label="Цветовой акцент",
            options=[ft.dropdown.Option(key, value["name"]) for key, value in ACCENT_PRESETS.items()],
            value=self.config.get("accent_color_preset", "cyan"),
            width=310,
        )
        self.settings_auto_fetch = ft.Switch(
            label="Автопереводить пустой сегмент при переходе",
            value=bool(self.config.get("auto_fetch", False)),
        )
        self.settings_send_neighbor_context = ft.Switch(
            label="Передавать AI соседние сегменты как контекст",
            value=bool(self.config.get("send_neighbor_context", True)),
        )
        self.settings_google_interval = ft.Slider(
            min=0.8,
            max=3.0,
            divisions=11,
            label="{value} с",
            value=float(self.config.get("google_request_interval", 1.0)),
            width=310,
        )
        self.settings_show_local_ai = ft.Switch(
            label="Показать расширенные настройки Ollama",
            value=local_ai_visible,
            on_change=self.on_local_ai_visibility_change,
        )
        self.settings_segmentation = ft.Dropdown(
            label="Сегментация",
            options=[
                ft.dropdown.Option("simple", "Простая"),
                ft.dropdown.Option("advanced", "Расширенная (сокращения и инициалы)"),
            ],
            value=self.config.get("segmentation_method", "advanced"),
            width=310,
        )
        self.settings_theme = ft.Dropdown(
            label="Тема",
            options=[ft.dropdown.Option("dark", "Тёмная"), ft.dropdown.Option("light", "Светлая")],
            value=self.config.get("theme", "dark"),
            width=310,
        )
        self.settings_font_size = ft.Slider(
            min=12,
            max=24,
            divisions=12,
            label="{value}px",
            value=self.config.get("font_size", 14),
            width=310,
        )
        self.models_status = ft.Text("", size=11, color=self.muted_color)
        self.ollama_settings_group = ft.Column(
            [
                ft.Text(
                    "Ollama нужна только при желании переводить своей моделью. На телефоне обычно указывается адрес Ollama на ПК или сервере.",
                    size=11,
                    color=self.muted_color,
                ),
                self.settings_model,
                self.settings_ollama_url,
                self._button("Проверить Ollama и обновить модели", self.start_loading_models),
                self.models_status,
            ],
            visible=local_ai_visible,
            spacing=8,
            horizontal_alignment=ft.CrossAxisAlignment.CENTER,
        )
        self.ai_settings_tile = ft.ExpansionTile(
            title=ft.Text("Переводчик-помощник · необязательно", color=self.text_color, weight=ft.FontWeight.BOLD),
            subtitle=ft.Text("Google, свой API или скрытая Ollama", size=11, color=self.muted_color),
            initially_expanded=False,
            controls=[
                ft.Text(
                    "Помощник ничего не переводит сам, пока не нажата кнопка перевода. Автозаполнение ниже выключено по умолчанию. Google работает без ключа, но может ограничивать слишком частые запросы.",
                    size=11,
                    color=self.muted_color,
                ),
                self.settings_api_type,
                self.custom_api_group,
                self.settings_style,
                self.settings_auto_fetch,
                self.settings_send_neighbor_context,
                self.settings_fallback_enabled,
                ft.Text("Пауза Google без ключа", size=11, color=self.muted_color),
                self.settings_google_interval,
                self.settings_show_local_ai,
                self.ollama_settings_group,
            ],
        )
        self.recent_files_column = ft.Column(spacing=2)
        self.settings_spellcheck = ft.Dropdown(
            label="Глубокая проверка орфографии",
            options=[
                ft.dropdown.Option("off", "Выключена · только локальный QA"),
                ft.dropdown.Option("local", "Офлайн-морфология + словарь · всё на устройстве"),
                ft.dropdown.Option("languagetool", "LanguageTool · вручную, текущий сегмент"),
            ],
            value=self.config.get("spellcheck_mode", "off"),
            width=310,
        )
        self.settings_short_word_nbsp = ft.Switch(
            label="Неразрывные пробелы после коротких слов",
            value=bool(self.config.get("short_word_nbsp", True)),
        )
        self.settings_short_word_nbsp_words = ft.TextField(
            label="Короткие слова · через запятую",
            value=str(self.config.get("short_word_nbsp_words", DEFAULT_CONFIG["short_word_nbsp_words"])),
            width=310,
        )
        self.settings_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="settings_outlined", color=self.accent, size=20), ft.Text("Настройки", color=self.text_color, weight=ft.FontWeight.BOLD, size=18)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        ft.Divider(color=self.divider_color, height=8),
                        self.settings_source_lang,
                        self.settings_target_lang,
                        self.ai_settings_tile,
                        self.settings_accent,
                        ft.Text("Размер шрифта", size=12, color=self.text_color),
                        self.settings_font_size,
                        self.settings_segmentation,
                        self.settings_spellcheck,
                        self.settings_short_word_nbsp,
                        self.settings_short_word_nbsp_words,
                        ft.Text(
                            "Проверка запускается только отдельной кнопкой. Локальный режим приватен; LanguageTool отправляет сервису лишь текущий перевод.",
                            size=11,
                            color=self.muted_color,
                        ),
                        self.settings_theme,
                        ft.Divider(height=8),
                        self._button("Сбросить прогресс текущего файла", self.reset_progress, danger=True),
                        self.recent_files_column,
                        ft.Row(
                            [
                                self._button("Сохранить", self.save_settings, primary=True),
                                self._button("Закрыть", lambda e: self._close(self.settings_sheet)),
                            ],
                            alignment=ft.MainAxisAlignment.CENTER,
                            spacing=12,
                        ),
                    ],
                    scroll=ft.ScrollMode.AUTO,
                    spacing=9,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
                height=680,
                alignment=ft.alignment.center,
            ),
            dismissible=True,
        )

    def _build_utility_sheets(self) -> None:
        self.ai_provider_text = ft.Text(
            self.provider_description(),
            size=11,
            color=self.muted_color,
        )
        self.ai_sheet_progress_text = ft.Text("", size=11, color=self.muted_color)
        self.ai_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="translate", color=self.accent), ft.Text("Помощник перевода", weight=ft.FontWeight.BOLD, color=self.text_color)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        self.ai_provider_text,
                        self._button("Перевести текущий сегмент", self.translate_current, icon="translate"),
                        self.batch_button,
                        self.ai_sheet_progress_text,
                        ft.Text(
                            "Автопилот заполняет только пустые сегменты и не подтверждает их за вас.",
                            size=11,
                            color=self.muted_color,
                        ),
                        self._button("Открыть настройки", self.open_settings_from_ai, icon="settings_outlined"),
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.ai_sheet)),
                    ],
                    spacing=10,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

        self.segment_tools_title = ft.Text("Инструменты сегмента", weight=ft.FontWeight.BOLD, color=self.text_color)
        self.segment_tools_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        self.segment_tools_title,
                        self._button("Применить русскую типографику", self.apply_current_typography, icon="format_quote"),
                        self._button("Помощник перевода", self.open_ai_sheet, icon="translate"),
                        self._button("Добавить TL-сноску", self.open_tl_note_dialog, icon="speaker_notes"),
                        self._button("Память переводов", self.open_memory_sheet, icon="history"),
                        self._button("Глоссарий и персонажи", self.open_reference_sheet, icon="library_books"),
                        self._button("История и резервные версии", self.open_history_sheet, icon="restore"),
                        self._button("Разделить сегмент", self.open_split_dialog, icon="call_split"),
                        self._button("Объединить со следующим", self.merge_current_with_next, icon="merge_type"),
                        self._button("Озвучить оригинал", self.play_current_tts, icon="volume_up"),
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.segment_tools_sheet)),
                    ],
                    spacing=9,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

        self.qa_summary_text = ft.Text("QA ещё не запускался", color=self.text_color, weight=ft.FontWeight.BOLD)
        self.qa_current_text = ft.Text("", color=self.muted_color, selectable=True)
        self.deep_qa_status = ft.Text("", color=self.muted_color, size=11)
        self.dictionary_word_input = ft.TextField(label="Добавить слово в словарь проекта", width=260)
        self.qa_filter = ft.Dropdown(
            label="Показывать сегменты",
            value="all",
            width=310,
            options=[
                ft.dropdown.Option("all", "Все сегменты"),
                ft.dropdown.Option("qa", "Только с QA-замечаниями"),
                ft.dropdown.Option("empty", "Только пустые"),
                ft.dropdown.Option("unconfirmed", "Только неподтверждённые"),
                ft.dropdown.Option("bookmarks", "Только закладки"),
            ],
            on_change=self.on_segment_filter_change,
        )
        self.qa_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="fact_check", color=self.accent), ft.Text("Проверка качества", weight=ft.FontWeight.BOLD, color=self.text_color)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        self.qa_summary_text,
                        self.qa_current_text,
                        self.qa_filter,
                        self._button("Следующая проблема", self.jump_next_qa, icon="skip_next"),
                        self._button("Исправить типографику текущего", self.apply_current_typography, icon="format_quote"),
                        self._button("Проверить орфографию текущего", self.start_deep_spellcheck, icon="spellcheck"),
                        self.deep_qa_status,
                        ft.Row(
                            [self.dictionary_word_input, self._button("Добавить", self.add_dictionary_word, icon="add")],
                            alignment=ft.MainAxisAlignment.CENTER,
                            wrap=True,
                        ),
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.qa_sheet)),
                    ],
                    spacing=10,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

        self.memory_summary_text = ft.Text("", color=self.muted_color, size=11)
        self.memory_results_column = ft.Column(spacing=8)
        self.memory_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="history", color=self.accent), ft.Text("Память переводов", weight=ft.FontWeight.BOLD, color=self.text_color)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        self.memory_summary_text,
                        self.memory_results_column,
                        ft.Text(
                            "Пары добавляются локально после подтверждения сегмента. Совпадения не отправляются во внешние сервисы.",
                            size=11,
                            color=self.muted_color,
                        ),
                        ft.Row(
                            [
                                self._button("Импорт TMX", self.import_tmx, icon="file_upload"),
                                self._button("Экспорт TMX", self.export_tmx, icon="file_download"),
                            ],
                            alignment=ft.MainAxisAlignment.CENTER,
                            wrap=True,
                        ),
                        self._button("Очистить память переводов", self.confirm_clear_translation_memory, icon="delete_sweep", danger=True),
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.memory_sheet)),
                    ],
                    scroll=ft.ScrollMode.AUTO,
                    spacing=10,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                height=620,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

        self.glossary_source_input = ft.TextField(label="Термин в оригинале", width=310)
        self.glossary_target_input = ft.TextField(label="Предпочтительный перевод", width=310)
        self.glossary_note_input = ft.TextField(label="Заметка · необязательно", width=310)
        self.glossary_case_switch = ft.Switch(label="Учитывать регистр", value=False)
        self.glossary_list_column = ft.Column(spacing=6)
        self.character_source_input = ft.TextField(label="Имя в оригинале", width=310)
        self.character_target_input = ft.TextField(label="Имя в переводе", width=310)
        self.character_role_input = ft.TextField(label="Роль / обращение", hint_text="Например: героиня · она · госпожа", width=310)
        self.character_aliases_input = ft.TextField(label="Псевдонимы в оригинале · через запятую", width=310)
        self.character_forms_input = ft.TextField(label="Склонения имени в переводе · через запятую", width=310)
        self.character_forms_button = self._button(
            "Подобрать формы офлайн",
            self.fill_character_forms,
            icon="spellcheck",
            tooltip="Склонить русское имя без отправки текста в интернет",
        )
        self.character_relationships_input = ft.TextField(label="Связи", hint_text="Сестра Акиры; наставница Рена", width=310)
        self.character_voice_input = ft.TextField(label="Голос персонажа", hint_text="Короткие фразы, ирония, архаизмы…", width=310)
        self.character_formality_input = ft.Dropdown(
            label="Манера обращения",
            value="",
            width=310,
            options=[
                ft.dropdown.Option("", "Не задана"),
                ft.dropdown.Option("ты", "Преимущественно на «ты»"),
                ft.dropdown.Option("вы", "Преимущественно на «вы»"),
                ft.dropdown.Option("context", "Зависит от собеседника"),
            ],
        )
        self.character_note_input = ft.TextField(label="Заметка · необязательно", width=310)
        self.character_list_column = ft.Column(spacing=6)
        self.morphology_status_text = ft.Text(
            "Русская морфология работает полностью офлайн."
            if HAS_PYMORPHY3 else
            "Морфологический модуль подключится после установки зависимостей проекта.",
            size=11,
            color=self.accent if HAS_PYMORPHY3 else self.muted_color,
        )
        self.morphology_lookup_input = ft.TextField(
            label="Русское слово",
            hint_text="Например: героинями",
            width=220,
            on_submit=self.lookup_morphology_word,
        )
        self.morphology_lookup_result = ft.Text(
            "Введите словоформу — разбор выполняется на устройстве.",
            size=11,
            color=self.muted_color,
            selectable=True,
        )
        self.morphology_lookup_tile = ft.ExpansionTile(
            title=ft.Text("Морфологический словарь", color=self.text_color, weight=ft.FontWeight.BOLD),
            subtitle=ft.Text("Лемма, часть речи и словоформы · офлайн", size=11, color=self.muted_color),
            initially_expanded=False,
            controls=[
                ft.Row(
                    [self.morphology_lookup_input, self._button("Разобрать", self.lookup_morphology_word, icon="manage_search")],
                    wrap=True,
                    alignment=ft.MainAxisAlignment.CENTER,
                ),
                self.morphology_lookup_result,
            ],
        )
        self.dual_raw_status_text = ft.Text("Дополнительный оригинал не подключён.", size=11, color=self.muted_color)
        self.dual_raw_tile = ft.ExpansionTile(
            title=ft.Text("Dual-RAW", color=self.text_color, weight=ft.FontWeight.BOLD),
            subtitle=ft.Text("Второй оригинал для сверки", size=11, color=self.muted_color),
            initially_expanded=False,
            controls=[
                self.dual_raw_status_text,
                ft.Row(
                    [
                        self._button("Подключить TXT/MD", self.open_dual_raw_picker, icon="add_link", primary=True),
                        self._button("Удалить", self.remove_dual_raw, icon="link_off", danger=True),
                    ],
                    wrap=True,
                    alignment=ft.MainAxisAlignment.CENTER,
                ),
                ft.Row(
                    [
                        self._button("Связь −1", lambda e: self.shift_dual_raw_alignment(-1)),
                        self._button("Добавить следующий", self.add_next_dual_raw_alignment),
                        self._button("Связь +1", lambda e: self.shift_dual_raw_alignment(1)),
                        self._button("Отвязать", self.unlink_current_dual_raw_alignment, danger=True),
                        self._button("Связать ближайший", self.link_nearest_dual_raw_alignment),
                    ],
                    wrap=True,
                    alignment=ft.MainAxisAlignment.CENTER,
                ),
            ],
        )
        self.honorific_source_input = ft.TextField(label="Обращение или суффикс", hint_text="-сан", width=220)
        self.honorific_target_input = ft.TextField(label="Замена", hint_text="сан", width=220)
        self.honorific_policy_input = ft.Dropdown(
            label="Политика",
            value="warn",
            width=220,
            options=[
                ft.dropdown.Option("warn", "Только предупреждать"),
                ft.dropdown.Option("keep", "Сохранять"),
                ft.dropdown.Option("transliterate", "Транслитерировать"),
                ft.dropdown.Option("replace", "Заменять"),
                ft.dropdown.Option("remove", "Удалять с предпросмотром"),
            ],
        )
        self.honorific_rules_column = ft.Column(spacing=4)
        self.honorific_tile = ft.ExpansionTile(
            title=ft.Text("Обращения и суффиксы", color=self.text_color, weight=ft.FontWeight.BOLD),
            subtitle=ft.Text("Правила проекта без скрытых автозамен", size=11, color=self.muted_color),
            initially_expanded=False,
            controls=[
                self.honorific_source_input,
                self.honorific_target_input,
                self.honorific_policy_input,
                self._button("Добавить правило", self.add_honorific_rule, icon="add"),
                self.honorific_rules_column,
            ],
        )
        self.reference_matches_text = ft.Text("", size=11, color=self.muted_color)
        self.reference_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="library_books", color=self.accent), ft.Text("Справочник проекта", weight=ft.FontWeight.BOLD, color=self.text_color)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        self.reference_matches_text,
                        ft.Text("Глоссарий", color=self.text_color, weight=ft.FontWeight.BOLD),
                        self.glossary_source_input,
                        self.glossary_target_input,
                        self.glossary_note_input,
                        self.glossary_case_switch,
                        self._button("Добавить термин", self.add_glossary_entry, icon="add", primary=True),
                        self.glossary_list_column,
                        ft.Divider(color=self.divider_color),
                        self.morphology_lookup_tile,
                        self.dual_raw_tile,
                        self.honorific_tile,
                        ft.Divider(color=self.divider_color),
                        ft.Text("Персонажи", color=self.text_color, weight=ft.FontWeight.BOLD),
                        self.morphology_status_text,
                        self.character_source_input,
                        self.character_target_input,
                        self.character_role_input,
                        self.character_aliases_input,
                        self.character_forms_input,
                        self.character_forms_button,
                        self.character_relationships_input,
                        self.character_voice_input,
                        self.character_formality_input,
                        self.character_note_input,
                        self._button("Добавить персонажа", self.add_character_entry, icon="person_add", primary=True),
                        self.character_list_column,
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.reference_sheet)),
                    ],
                    scroll=ft.ScrollMode.AUTO,
                    spacing=8,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                height=720,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

        self.history_summary_text = ft.Text("История пока пуста", size=11, color=self.muted_color)
        self.backup_list_column = ft.Column(spacing=6)
        self.history_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="restore", color=self.accent), ft.Text("История и версии", weight=ft.FontWeight.BOLD, color=self.text_color)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        self.history_summary_text,
                        ft.Row(
                            [
                                self._button("Отменить", self.undo_history, icon="undo"),
                                self._button("Вернуть", self.redo_history, icon="redo"),
                            ],
                            alignment=ft.MainAxisAlignment.CENTER,
                            wrap=True,
                        ),
                        self._button("Создать резервную версию", self.create_backup, icon="add_to_drive", primary=True),
                        ft.Text("Резервные версии", color=self.text_color, weight=ft.FontWeight.BOLD),
                        self.backup_list_column,
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.history_sheet)),
                    ],
                    scroll=ft.ScrollMode.AUTO,
                    spacing=10,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                height=650,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

        self.project_library_list = ft.Column(spacing=8)
        self.chapter_list = ft.Column(spacing=6)
        self.project_library_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [ft.Icon(name="collections_bookmark_outlined", color=self.accent), ft.Text("Книги и главы", weight=ft.FontWeight.BOLD, color=self.text_color)],
                            alignment=ft.MainAxisAlignment.CENTER,
                        ),
                        ft.Text("Последние проекты", color=self.text_color, weight=ft.FontWeight.BOLD),
                        self.project_library_list,
                        ft.Divider(color=self.divider_color),
                        ft.Text("Главы открытой книги", color=self.text_color, weight=ft.FontWeight.BOLD),
                        self.chapter_list,
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.project_library_sheet)),
                    ],
                    scroll=ft.ScrollMode.AUTO,
                    spacing=9,
                    horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                ),
                padding=20,
                height=700,
                bgcolor=self.card_bg,
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
                border=ft.border.all(1, self.border_color),
            ),
            dismissible=True,
        )

    def _build_mobile_controls(self) -> None:
        font_size = int(self.config.get("font_size", 14))
        self.mobile_segment_label = ft.Text("Сегмент —", weight=ft.FontWeight.BOLD, color=self.accent, size=14)
        self.mobile_status_dot = ft.Container(width=10, height=10, border_radius=5, bgcolor=STATUS_COLORS[STATUS_EMPTY])
        self.mobile_status_text = ft.Text("Откройте файл", size=11, color=self.muted_color)
        self.mobile_bookmark_button = ft.IconButton(
            icon="bookmark_border",
            icon_color=self.muted_color,
            tooltip="Закладка",
            on_click=lambda e: self.toggle_bookmark(self.current_index),
        )
        self.mobile_source_text = ft.Text(
            "Откройте файл новеллы на вкладке «Оригинал».",
            size=max(14, font_size),
            color=self.text_color,
            selectable=True,
        )
        self.mobile_source_gesture = ft.GestureDetector(
            content=ft.Container(
                content=self.mobile_source_text,
                bgcolor=self.editor_bg,
                border_radius=12,
                padding=14,
                border=ft.border.all(1, self.border_color),
            ),
            on_horizontal_drag_start=self.on_swipe_start,
            on_horizontal_drag_update=self.on_swipe_update,
            on_horizontal_drag_end=self.on_swipe_end,
        )
        self.mobile_dual_raw_text = ft.Text("", size=12, color=self.muted_color, selectable=True)
        self.mobile_dual_raw_card = ft.Container(
            content=ft.Column(
                [
                    ft.Text("Второй оригинал", size=10, color=self.accent, weight=ft.FontWeight.BOLD),
                    self.mobile_dual_raw_text,
                ],
                spacing=3,
            ),
            visible=False,
            bgcolor=self.editor_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=10,
            padding=10,
        )
        self.mobile_variant_buttons = {
            slot: self._button(
                TRANSLATION_VARIANT_LABELS[slot],
                lambda e, selected=slot: self.switch_translation_variant(selected),
            )
            for slot in TRANSLATION_VARIANT_SLOTS
        }
        self.mobile_variant_bar = ft.Row(
            list(self.mobile_variant_buttons.values()),
            spacing=4,
            scroll=ft.ScrollMode.AUTO,
        )
        self.mobile_glossary_chips = ft.Row([], spacing=4, scroll=ft.ScrollMode.AUTO)
        self.mobile_translation_field = ft.TextField(
            value="",
            multiline=True,
            min_lines=6,
            max_lines=14,
            expand=True,
            disabled=True,
            hint_text="Перевод текущего сегмента…",
            border_color=self.border_color,
            focused_border_color=self.accent,
            text_style=ft.TextStyle(color=self.text_color, size=font_size),
            on_change=self.on_mobile_translation_change,
            on_focus=lambda e: self.on_segment_focus(self.current_index),
        )
        symbols = self.config.get("mobile_symbol_order", DEFAULT_CONFIG["mobile_symbol_order"])
        self.mobile_symbol_bar = ft.Row(
            [
                ft.TextButton(
                    text="NBSP" if symbol == "\u00a0" else symbol,
                    height=44,
                    tooltip="Неразрывный пробел" if symbol == "\u00a0" else f"Вставить {symbol}",
                    on_click=lambda e, selected=symbol: self.insert_into_active_editor(selected),
                    style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=14, vertical=10)),
                )
                for symbol in symbols
                if isinstance(symbol, str) and symbol
            ],
            spacing=2,
            scroll=ft.ScrollMode.AUTO,
        )
        self.mobile_ai_button = ft.IconButton(
            icon="translate",
            icon_color=self.muted_color,
            tooltip="Перевести этот сегмент",
            on_click=self.translate_current,
        )
        self.mobile_undo_button = ft.IconButton(
            icon="undo",
            icon_color=self.muted_color,
            tooltip="Отменить",
            disabled=True,
            on_click=self.undo_history,
        )
        self.mobile_redo_button = ft.IconButton(
            icon="redo",
            icon_color=self.muted_color,
            tooltip="Вернуть",
            disabled=True,
            on_click=self.redo_history,
        )
        self.mobile_qa_text = ft.Text("", size=11, color=STATUS_COLORS[STATUS_DRAFT])
        self.mobile_done_button = self._button("Готово →", self.confirm_current, icon="check", primary=True)
        self.mobile_done_button.expand = True
        self.mobile_action_bar = ft.Container(
            content=ft.Row(
                [
                    ft.IconButton(icon="arrow_back", tooltip="Предыдущий", on_click=lambda e: self.move_segment(-1)),
                    self.mobile_undo_button,
                    self.mobile_done_button,
                    ft.IconButton(icon="arrow_forward", tooltip="Следующий", on_click=lambda e: self.move_segment(1)),
                    ft.IconButton(icon="more_horiz", tooltip="Другие инструменты", on_click=self.open_segment_tools),
                ],
                alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                vertical_alignment=ft.CrossAxisAlignment.CENTER,
                spacing=0,
            ),
            bgcolor=self.appbar_bg,
            border_radius=14,
            padding=ft.padding.symmetric(horizontal=4, vertical=4),
            border=ft.border.all(1, self.border_color),
        )
        self.mobile_editor_panel = ft.Container(
            content=ft.Column(
                [
                    ft.Row(
                        [
                            ft.Row([self.mobile_status_dot, self.mobile_segment_label], spacing=7),
                            self.mobile_bookmark_button,
                        ],
                        alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                    ),
                    self.mobile_status_text,
                    self.mobile_source_gesture,
                    self.mobile_dual_raw_card,
                    self.mobile_variant_bar,
                    self.mobile_glossary_chips,
                    self.mobile_translation_field,
                    self.mobile_symbol_bar,
                    self.mobile_qa_text,
                    self.mobile_action_bar,
                ],
                expand=True,
                spacing=8,
            ),
            expand=True,
            padding=2,
        )
        self.reader_title_text = ft.Text("Режим вычитки", color=self.text_color, weight=ft.FontWeight.BOLD, size=15)
        self.reader_summary_text = ft.Text("Откройте книгу", color=self.muted_color, size=11)
        self.reader_list = ft.ListView(expand=True, spacing=9)
        self.reader_sheet_list = ft.ListView(expand=True, spacing=9)
        self.reader_page_text = ft.Text("", color=self.muted_color, size=10)
        self.reader_sheet_page_text = ft.Text("", color=self.muted_color, size=10)
        self.reader_panel = ft.Container(
            content=ft.Column(
                [
                    ft.Row(
                        [
                            ft.IconButton(icon="chevron_left", tooltip="Предыдущая глава", on_click=lambda e: self.move_reader_chapter(-1)),
                            ft.Column([self.reader_title_text, self.reader_summary_text], spacing=1, expand=True),
                            ft.IconButton(icon="chevron_right", tooltip="Следующая глава", on_click=lambda e: self.move_reader_chapter(1)),
                        ],
                        vertical_alignment=ft.CrossAxisAlignment.CENTER,
                    ),
                    ft.Text(
                        "Нажмите на абзац, чтобы вернуться к его переводу.",
                        color=self.muted_color,
                        size=10,
                    ),
                    ft.Row(
                        [
                            ft.TextButton(text="Назад", icon="first_page", on_click=lambda e: self.move_reader_page(-1)),
                            self.reader_page_text,
                            ft.TextButton(text="Далее", icon="last_page", on_click=lambda e: self.move_reader_page(1)),
                        ],
                        alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                    ),
                    self.reader_list,
                ],
                expand=True,
                spacing=8,
            ),
            bgcolor=self.card_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=12,
            padding=10,
            expand=True,
        )
        self.reader_sheet_title = ft.Text("Режим вычитки", color=self.text_color, weight=ft.FontWeight.BOLD, size=17)
        self.reader_sheet_summary = ft.Text("", color=self.muted_color, size=11)
        self.reader_sheet = ft.BottomSheet(
            content=ft.Container(
                content=ft.Column(
                    [
                        ft.Row(
                            [
                                ft.IconButton(icon="chevron_left", on_click=lambda e: self.move_reader_chapter(-1)),
                                ft.Column([self.reader_sheet_title, self.reader_sheet_summary], spacing=1, expand=True),
                                ft.IconButton(icon="chevron_right", on_click=lambda e: self.move_reader_chapter(1)),
                            ]
                        ),
                        ft.Row(
                            [
                                ft.TextButton(text="Предыдущий фрагмент", icon="first_page", on_click=lambda e: self.move_reader_page(-1)),
                                self.reader_sheet_page_text,
                                ft.TextButton(text="Следующий фрагмент", icon="last_page", on_click=lambda e: self.move_reader_page(1)),
                            ],
                            alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                            wrap=True,
                        ),
                        self.reader_sheet_list,
                        ft.TextButton(text="Закрыть", on_click=lambda e: self._close(self.reader_sheet)),
                    ],
                    expand=True,
                    spacing=8,
                ),
                height=700,
                padding=16,
                bgcolor=self.card_bg,
                border=ft.border.all(1, self.border_color),
                border_radius=ft.border_radius.only(top_left=20, top_right=20),
            ),
            dismissible=True,
        )

    def _mount(self) -> None:
        self.page.on_resized = self.render_layout
        self.page.on_keyboard_event = self.on_keyboard
        if hasattr(self.page, "on_close"):
            self.page.on_close = self.on_page_close
        if hasattr(self.page, "on_disconnect"):
            self.page.on_disconnect = self.on_page_close
        self.page.add(self.content_column)
        self.update_recent_files_ui(update=False)
        self.refresh_reference_ui(update=False)
        self.refresh_backup_list(update=False)
        self.update_history_ui(update=False)
        self.render_layout(force=True)
        self.update_ui(update=True)

    def _open(self, control) -> None:
        try:
            self.page.open(control)
        except (AttributeError, RuntimeError):
            if control not in self.page.overlay:
                self.page.overlay.append(control)
            control.open = True
            self.page.update()

    def _close(self, control) -> None:
        try:
            self.page.close(control)
        except (AttributeError, RuntimeError):
            control.open = False
            self.page.update()

    def show_toast(self, text: str, *, error: bool = False, action_text: str = "", on_action=None) -> None:
        content = ft.Text(text)
        if action_text and on_action is not None:
            content = ft.Row(
                [
                    ft.Text(text, expand=True),
                    ft.TextButton(text=action_text, on_click=on_action),
                ],
                alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
            )
        snack = ft.SnackBar(
            content=content,
            bgcolor="#b3261e" if error else None,
        )
        self._open(snack)

    def open_help(self, e=None) -> None:
        self._open(self.help_dialog)

    def open_settings_sheet(self, e=None) -> None:
        self.fit_bottom_sheet(self.settings_sheet, 680, 300)
        self.update_recent_files_ui(update=False)
        self._open(self.settings_sheet)

    def fit_bottom_sheet(self, sheet, maximum: float, minimum: float = 280) -> None:
        try:
            available = float(self.page.height or 760) * 0.9
            sheet.content.height = max(minimum, min(maximum, available))
        except (AttributeError, TypeError, ValueError):
            pass

    def active_api_profile_data(self, profile_id: str | None = None) -> dict[str, str]:
        selected = profile_id if profile_id is not None else str(self.config.get("active_api_profile", "") or "")
        for profile in self.config.get("api_profiles", []):
            if isinstance(profile, dict) and profile.get("id") == selected:
                return profile
        return {}

    def _sync_api_profile_options(self) -> None:
        profiles = self.config.get("api_profiles", [])
        self.settings_api_profile.options = [ft.dropdown.Option(profile["id"], profile["name"]) for profile in profiles]
        selected = str(self.config.get("active_api_profile", "") or "")
        self.settings_api_profile.value = selected if any(profile["id"] == selected for profile in profiles) else ""

    def on_api_profile_change(self, e=None) -> None:
        previous = str(self.config.get("active_api_profile", "") or "")
        if previous:
            self.session_api_keys[previous] = (self.settings_custom_key.value or "").strip()
        selected = str(self.settings_api_profile.value or "")
        profile = self.active_api_profile_data(selected)
        if not profile:
            return
        self.config["active_api_profile"] = selected
        self.settings_custom_name.value = profile.get("name", "API-профиль")
        self.settings_custom_url.value = profile.get("url", "")
        self.settings_custom_model.value = profile.get("model", "")
        self.settings_custom_headers.value = profile.get("headers", "")
        self.settings_custom_key_header.value = profile.get("key_header", "Authorization")
        key = self.session_api_keys.get(selected)
        if key is None:
            key = self.secret_store.get(selected)
            if key:
                self.session_api_keys[selected] = key
        self.settings_custom_key.value = key or ""
        self.page.update()

    def new_api_profile(self, e=None) -> None:
        profile_id = uuid.uuid4().hex
        profile_number = len(self.config.get("api_profiles", [])) + 1
        self.config.setdefault("api_profiles", []).append(
            {"id": profile_id, "name": f"Новое подключение {profile_number}", "url": "", "model": "", "headers": "", "key_header": "Authorization"}
        )
        self.config["active_api_profile"] = profile_id
        self._sync_api_profile_options()
        self.settings_custom_name.value = self.active_api_profile_data().get("name", "Новое подключение")
        self.settings_custom_url.value = ""
        self.settings_custom_model.value = ""
        self.settings_custom_headers.value = ""
        self.settings_custom_key_header.value = "Authorization"
        self.settings_custom_key.value = ""
        self.settings_api_type.value = "custom"
        self.on_api_type_change()

    def delete_api_profile(self, e=None) -> None:
        profile_id = str(self.settings_api_profile.value or "")
        profile = self.active_api_profile_data(profile_id)
        if not profile:
            self.show_toast("Нет выбранного API-профиля.")
            return
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Удалить API-профиль?"),
            content=ft.Text(f"Подключение «{profile.get('name', 'API-профиль')}» и сохранённый ключ будут удалены."),
        )

        def confirm(_):
            self._close(dialog)
            self.config["api_profiles"] = [item for item in self.config.get("api_profiles", []) if item.get("id") != profile_id]
            self.secret_store.delete(profile_id)
            self.session_api_keys.pop(profile_id, None)
            profiles = self.config["api_profiles"]
            self.config["active_api_profile"] = profiles[0]["id"] if profiles else ""
            self._sync_api_profile_options()
            if profiles:
                self.on_api_profile_change()
            else:
                for control in (self.settings_custom_name, self.settings_custom_url, self.settings_custom_model, self.settings_custom_headers, self.settings_custom_key):
                    control.value = ""
                self.settings_custom_key_header.value = "Authorization"
                self.page.update()

        dialog.actions = [
            ft.TextButton(text="Удалить", on_click=confirm),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def _store_profile_from_controls(self) -> dict[str, str]:
        profile_id = str(self.settings_api_profile.value or self.config.get("active_api_profile", "") or uuid.uuid4().hex)
        profile = {
            "id": profile_id,
            "name": (self.settings_custom_name.value or "Мой API").strip(),
            "url": (self.settings_custom_url.value or "").strip(),
            "model": (self.settings_custom_model.value or "").strip(),
            "headers": (self.settings_custom_headers.value or "").strip(),
            "key_header": (self.settings_custom_key_header.value or "Authorization").strip(),
        }
        profiles = self.config.setdefault("api_profiles", [])
        existing = next((item for item in profiles if item.get("id") == profile_id), None)
        if existing is None:
            profiles.append(profile)
        else:
            existing.update(profile)
        self.config["active_api_profile"] = profile_id
        self._sync_api_profile_options()
        return profile

    def on_api_type_change(self, e=None) -> None:
        selected = self.settings_api_type.value or "google"
        self.custom_api_group.visible = selected == "custom"
        self.ollama_settings_group.visible = selected == "ollama" and bool(self.settings_show_local_ai.value)
        self.page.update()

    def on_local_ai_visibility_change(self, e=None) -> None:
        visible = bool(self.settings_show_local_ai.value)
        self.ollama_settings_group.visible = visible and self.settings_api_type.value == "ollama"
        options = [
            ft.dropdown.Option("google", "Google Translate · онлайн, без ключа"),
            ft.dropdown.Option("custom", "Свой API · OpenAI-совместимый"),
        ]
        if visible:
            options.append(ft.dropdown.Option("ollama", "Ollama · локальная модель"))
        elif self.settings_api_type.value == "ollama":
            self.settings_api_type.value = "google"
        self.settings_api_type.options = options
        self.on_api_type_change()

    def custom_api_config_from_controls(self) -> dict[str, Any]:
        config = dict(self.config)
        config.update(
            {
                "api_type": "custom",
                "custom_api_name": (self.settings_custom_name.value or "Мой API").strip(),
                "custom_api_url": normalise_openai_chat_url(self.settings_custom_url.value or ""),
                "custom_api_model": (self.settings_custom_model.value or "").strip(),
                "custom_api_key": (self.settings_custom_key.value or "").strip(),
                "custom_api_key_header": (self.settings_custom_key_header.value or "Authorization").strip(),
                "custom_api_headers": (self.settings_custom_headers.value or "").strip(),
                "translation_style": self.settings_style.value or "literary",
                "source_lang": self.settings_source_lang.value or "auto",
                "target_lang": self.settings_target_lang.value or "ru",
            }
        )
        if not config["custom_api_model"]:
            raise ValueError("укажите название модели")
        custom_api_headers(config)
        return config

    def start_custom_api_test(self, e=None) -> None:
        try:
            config = self.custom_api_config_from_controls()
        except (ValueError, TranslationError) as exc:
            self.custom_api_status.value = str(exc)
            self.custom_api_status.color = STATUS_COLORS[STATUS_EMPTY]
            self.page.update()
            return
        self.custom_api_status.value = "Проверяю коротким тестовым запросом…"
        self.custom_api_status.color = self.muted_color
        self.page.update()
        self.page.run_task(self._custom_api_test_task, config)

    async def _custom_api_test_task(self, config: dict[str, Any]) -> None:
        try:
            result = await asyncio.to_thread(translate_with_custom_api, "Hello, world.", config)
            self.custom_api_status.value = f"Подключение работает · ответ: {result[:80]}"
            self.custom_api_status.color = STATUS_COLORS[STATUS_CONFIRMED]
        except Exception as exc:
            self.custom_api_status.value = f"Ошибка: {exc}"
            self.custom_api_status.color = STATUS_COLORS[STATUS_EMPTY]
        self.page.update()

    def provider_description(self) -> str:
        fallback = " · резервный маршрут включён" if self.config.get("fallback_enabled") else ""
        if self.config.get("api_type") == "ollama":
            return f"Ollama · локальный режим{fallback}. Запрос отправляется только после вашего нажатия."
        if self.config.get("api_type") == "custom":
            name = self.config.get("custom_api_name") or "Пользовательский API"
            return f"{name}{fallback} · запрос отправляется только после вашего нажатия."
        return f"Google Translate · онлайн без ключа{fallback}. После нажатия отправляется только текущий сегмент."

    def open_ai_sheet(self, e=None) -> None:
        if hasattr(self, "segment_tools_sheet") and getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        self.ai_provider_text.value = self.provider_description()
        self._open(self.ai_sheet)

    def open_settings_from_ai(self, e=None) -> None:
        self._close(self.ai_sheet)
        self.open_settings_sheet()

    def save_settings(self, e=None) -> None:
        old_theme = self.config.get("theme")
        old_accent = self.config.get("accent_color_preset")
        old_segmentation = self.config.get("segmentation_method")
        old_font_size = self.config.get("font_size")
        old_target_lang = self.config.get("target_lang")

        show_local_ai = bool(self.settings_show_local_ai.value)
        selected_backend = self.settings_api_type.value or "google"
        if selected_backend == "ollama" and not show_local_ai:
            selected_backend = "google"
        if selected_backend == "ollama":
            try:
                ollama_url = normalise_ollama_generate_url(self.settings_ollama_url.value or "")
            except ValueError as exc:
                self.show_toast(f"Некорректный URL Ollama: {exc}", error=True)
                return
        else:
            ollama_url = self.settings_ollama_url.value or DEFAULT_CONFIG["ollama_url"]

        profile = self._store_profile_from_controls()
        if selected_backend == "custom":
            try:
                custom_config = self.custom_api_config_from_controls()
            except (ValueError, TranslationError) as exc:
                self.show_toast(f"Проверьте пользовательский API: {exc}", error=True)
                return
        else:
            custom_config = {
                "custom_api_name": (self.settings_custom_name.value or "Мой API").strip(),
                "custom_api_url": self.settings_custom_url.value or DEFAULT_CONFIG["custom_api_url"],
                "custom_api_model": (self.settings_custom_model.value or "").strip(),
                "custom_api_key": (self.settings_custom_key.value or "").strip(),
                "custom_api_key_header": (self.settings_custom_key_header.value or "Authorization").strip(),
                "custom_api_headers": (self.settings_custom_headers.value or "").strip(),
            }
            try:
                custom_api_headers(custom_config)
            except TranslationError as exc:
                self.show_toast(f"Проверьте пользовательский API: {exc}", error=True)
                return
        stored_profile = next((item for item in self.config.get("api_profiles", []) if item.get("id") == profile["id"]), None)
        if stored_profile is not None:
            stored_profile.update(
                {
                    "name": custom_config.get("custom_api_name", "Мой API"),
                    "url": custom_config.get("custom_api_url", ""),
                    "model": custom_config.get("custom_api_model", ""),
                    "headers": custom_config.get("custom_api_headers", ""),
                    "key_header": custom_config.get("custom_api_key_header", "Authorization"),
                }
            )
        self.session_api_key = str(custom_config.get("custom_api_key", ""))
        profile_id = profile["id"]
        self.session_api_keys[profile_id] = self.session_api_key
        remember_key = bool(self.settings_remember_api_key.value)
        if remember_key and self.session_api_key:
            if not self.secret_store.set(profile_id, self.session_api_key):
                remember_key = False
                self.show_toast("Защищённое хранилище недоступно: ключ оставлен только на эту сессию.", error=True)
        elif not remember_key:
            self.secret_store.delete(profile_id)

        self.config.update(
            {
                "config_version": DEFAULT_CONFIG["config_version"],
                "api_type": selected_backend or "google",
                "model": self.settings_model.value or DEFAULT_CONFIG["model"],
                "ollama_url": ollama_url,
                "show_local_ai": show_local_ai,
                "custom_api_name": custom_config.get("custom_api_name", "Мой API"),
                "custom_api_url": custom_config.get("custom_api_url", DEFAULT_CONFIG["custom_api_url"]),
                "custom_api_model": custom_config.get("custom_api_model", ""),
                "custom_api_key": self.session_api_key,
                "custom_api_key_header": custom_config.get("custom_api_key_header", "Authorization"),
                "custom_api_headers": custom_config.get("custom_api_headers", ""),
                "remember_api_key": remember_key,
                "fallback_enabled": bool(self.settings_fallback_enabled.value),
                "send_neighbor_context": bool(self.settings_send_neighbor_context.value),
                "google_request_interval": float(self.settings_google_interval.value or 1.0),
                "source_lang": self.settings_source_lang.value or "auto",
                "target_lang": self.settings_target_lang.value or "ru",
                "translation_style": self.settings_style.value or "literary",
                "accent_color_preset": self.settings_accent.value or "cyan",
                "auto_fetch": bool(self.settings_auto_fetch.value),
                "segmentation_method": self.settings_segmentation.value or "advanced",
                "spellcheck_mode": self.settings_spellcheck.value or "off",
                "short_word_nbsp": bool(self.settings_short_word_nbsp.value),
                "short_word_nbsp_words": (self.settings_short_word_nbsp_words.value or DEFAULT_CONFIG["short_word_nbsp_words"]).strip(),
                "theme": self.settings_theme.value or "dark",
                "font_size": int(self.settings_font_size.value or 14),
            }
        )
        try:
            save_config(self.config)
        except OSError as exc:
            self.show_toast(f"Не удалось сохранить настройки: {exc}", error=True)
            return

        if old_font_size != self.config["font_size"]:
            size = self.config["font_size"]
            for field in self.text_fields:
                if field is not None:
                    field.text_style = ft.TextStyle(color=self.text_color, size=size)
            for control in self.original_text_controls:
                if control is not None:
                    control.size = max(11, size - 2)
            for control in self.preview_text_controls:
                if control is not None:
                    control.size = max(13, size)
            self.mobile_source_text.size = max(14, size)
            self.mobile_translation_field.text_style = ft.TextStyle(color=self.text_color, size=size)

        self.ai_provider_text.value = self.provider_description()
        if self.file_loaded and old_target_lang != self.config["target_lang"]:
            self.refresh_qa()

        notes = ["Настройки сохранены"]
        if old_theme != self.config["theme"] or old_accent != self.config["accent_color_preset"]:
            notes.append("тема и акцент применятся после перезапуска")
        if self.file_loaded and old_segmentation != self.config["segmentation_method"]:
            notes.append("новая сегментация применится при следующем открытии файла")
        self._close(self.settings_sheet)
        self.show_toast("; ".join(notes) + ".")
        self.page.update()

    def start_loading_models(self, e=None) -> None:
        if self.models_status.value == "Проверяю соединение…":
            return
        self.models_status.value = "Проверяю соединение…"
        self.models_status.color = self.muted_color
        self.page.update()
        self.page.run_task(self._load_models_task)

    async def _load_models_task(self) -> None:
        try:
            models = await asyncio.to_thread(fetch_ollama_models, self.settings_ollama_url.value or "")
            if not models:
                raise TranslationError("сервер доступен, но список моделей пуст")
            current = self.settings_model.value
            self.settings_model.options = [ft.dropdown.Option(model) for model in models]
            self.settings_model.value = current if current in models else models[0]
            self.models_status.value = f"Ollama доступна · моделей: {len(models)}"
            self.models_status.color = STATUS_COLORS[STATUS_CONFIRMED]
        except Exception as exc:
            self.models_status.value = f"Ollama недоступна: {exc}"
            self.models_status.color = STATUS_COLORS[STATUS_EMPTY]
        self.page.update()

    def update_recent_files_ui(self, *, update: bool = True) -> None:
        self.recent_files_column.controls.clear()
        if hasattr(self, "welcome_recent_column"):
            self.welcome_recent_column.controls.clear()
        existing: list[str] = []
        for value in self.config.get("recent_files", []):
            if value and Path(value).is_file() and value not in existing:
                existing.append(value)
        if existing != self.config.get("recent_files", []):
            self.config["recent_files"] = existing[:5]
            try:
                save_config(self.config)
            except OSError:
                pass
        if existing:
            self.recent_files_column.controls.append(
                ft.Text("Недавние файлы", size=12, color=self.accent, weight=ft.FontWeight.BOLD)
            )
            for path in existing[:5]:
                self.recent_files_column.controls.append(
                    ft.TextButton(
                        text=Path(path).name,
                        tooltip=path,
                        on_click=lambda e, selected=path: self.load_recent_file(selected),
                    )
                )
        projects: list[dict[str, Any]] = []
        try:
            projects = self.project_store.list_projects(limit=5)
        except (OSError, sqlite3.Error):
            pass
        if hasattr(self, "welcome_continue_button"):
            candidate = next(
                (
                    project
                    for project in projects
                    if bool(project.get("has_source"))
                    or bool(str(project.get("source_path", "") or "") and Path(str(project.get("source_path", ""))).is_file())
                ),
                None,
            )
            last_file = str(self.config.get("last_file", "") or "")
            can_continue = bool((last_file and Path(last_file).is_file()) or candidate)
            self.welcome_continue_button.disabled = not can_continue
            if candidate:
                total = max(1, int(candidate.get("segment_count", 0) or 0))
                confirmed = int(candidate.get("confirmed_count", 0) or 0)
                self.welcome_continue_title.value = str(candidate.get("title") or candidate.get("source_name") or "Последняя книга")
                self.welcome_continue_details.value = (
                    f"Подтверждено {confirmed} из {total} · продолжить с сохранённого места"
                )
            elif last_file and Path(last_file).is_file():
                self.welcome_continue_title.value = Path(last_file).name
                self.welcome_continue_details.value = "Открыть последний файл и восстановить прогресс"
            else:
                self.welcome_continue_title.value = "Здесь появится последняя книга"
                self.welcome_continue_details.value = "Откройте рукопись — LiteraFlow запомнит прогресс локально."
        if hasattr(self, "welcome_recent_column") and (projects or existing):
            self.welcome_recent_column.controls.append(
                ft.Text("Недавние книги", color=self.text_color, weight=ft.FontWeight.BOLD, size=13)
            )
            seen: set[str] = set()
            for project in projects[:3]:
                project_id = str(project.get("project_id", ""))
                path = str(project.get("source_path", "") or "")
                if not project_id or project_id in seen:
                    continue
                seen.add(project_id)
                total = max(1, int(project.get("segment_count", 0) or 0))
                confirmed = int(project.get("confirmed_count", 0) or 0)
                self.welcome_recent_column.controls.append(
                    ft.Container(
                        content=ft.Row(
                            [
                                ft.Column(
                                    [
                                        ft.Text(str(project.get("title") or project.get("source_name") or "Книга"), color=self.text_color, size=12, weight=ft.FontWeight.BOLD),
                                        ft.Text(f"{round(confirmed / total * 100)}% готово", color=self.muted_color, size=10),
                                    ],
                                    spacing=1,
                                    expand=True,
                                ),
                                ft.IconButton(
                                    icon="arrow_forward",
                                    tooltip="Открыть проект",
                                    on_click=lambda e, selected_id=project_id, selected_path=path,
                                                    name=str(project.get("source_name", "novel.txt")):
                                        self.load_project_from_library(selected_id, selected_path, name),
                                ),
                            ]
                        ),
                        width=min(440, max(280, self._page_width() - 48)),
                        padding=ft.padding.symmetric(horizontal=10, vertical=5),
                        border=ft.border.all(1, self.border_color),
                        border_radius=10,
                        bgcolor=self.card_bg,
                    )
                )
        if update:
            self.page.update()

    def continue_last_project(self, e=None) -> None:
        try:
            projects = self.project_store.list_projects(limit=1)
        except (OSError, sqlite3.Error):
            projects = []
        project = next(
            (
                item
                for item in projects
                if bool(item.get("has_source"))
                or bool(str(item.get("source_path", "") or "") and Path(str(item.get("source_path", ""))).is_file())
            ),
            None,
        )
        if project:
            self.load_project_from_library(
                str(project.get("project_id", "")),
                str(project.get("source_path", "") or ""),
                str(project.get("source_name", "novel.txt")),
            )
            return
        last_file = str(self.config.get("last_file", "") or "")
        if last_file and Path(last_file).is_file():
            self.start_load_path(last_file)
            return
        self.show_toast("Нет сохранённого проекта. Откройте первую рукопись.")

    def load_recent_file(self, path: str) -> None:
        self._close(self.settings_sheet)
        self.start_load_path(path)

    def open_import_picker(self, e=None) -> None:
        try:
            self.import_picker.pick_files(
                dialog_title="Выберите файл новеллы",
                file_type=ft.FilePickerFileType.CUSTOM,
                allowed_extensions=["txt", "md", "docx", "epub", "fb2", "xlf", "xliff"],
                allow_multiple=False,
            )
        except Exception as exc:
            self.show_toast(f"Не удалось открыть выбор файла: {exc}", error=True)

    def on_zone_hover(self, e) -> None:
        hovered = str(e.data).lower() == "true"
        self.drop_zone.border = ft.border.all(2 if hovered else 1, self.accent if hovered else self.border_color)
        self.drop_zone.bgcolor = self.soft_accent if hovered else self.editor_bg
        self.drop_zone.update()

    def set_drop_zone_state(self, state: str) -> None:
        if state == "loading":
            self.drop_zone_icon.name = "hourglass_top"
            self.drop_zone_icon.color = self.muted_color
            self.drop_zone_text.value = "Читаю рукопись…"
        elif state == "loaded" and self.file_loaded:
            self.drop_zone_icon.name = "description_outlined"
            self.drop_zone_icon.color = self.accent
            self.drop_zone_text.value = f"{self.project_file_name}\n{len(self.sentences)} сегментов"
        else:
            self.drop_zone_icon.name = "note_add_outlined"
            self.drop_zone_icon.color = self.accent
            self.drop_zone_text.value = "Открыть рукопись\nTXT · MD · DOCX · EPUB · FB2 · XLIFF"

    def on_import_result(self, e) -> None:
        files = getattr(e, "files", None)
        if not files:
            return
        if self.loading_file:
            self.show_toast("Дождитесь завершения текущей загрузки.")
            return
        selected = files[0]
        path = getattr(selected, "path", None)
        if path:
            self.start_load_path(path)
            return
        raw = getattr(selected, "bytes", None)
        if isinstance(raw, (bytes, bytearray)):
            self.page.run_task(self._load_memory_task, bytes(raw), getattr(selected, "name", "novel.txt"))
            return
        self.show_toast(
            "Система не передала приложению содержимое файла. Попробуйте указать путь вручную.",
            error=True,
        )

    def start_load_path(self, path: str) -> None:
        if self.loading_file:
            self.show_toast("Дождитесь завершения текущей загрузки.")
            return
        if not path or not path.strip():
            self.show_toast("Укажите путь или выберите файл.", error=True)
            return
        value = os.path.abspath(os.path.expanduser(path.strip().strip('"')))
        self.page.run_task(self._load_path_task, value)

    async def _load_path_task(self, path: str) -> None:
        self.loading_file = True
        self.load_button.disabled = True
        self.set_drop_zone_state("loading")
        self.page.update()
        try:
            source = Path(path)
            if not source.is_file():
                raise ValueError(f"файл не найден: {path}")
            if source.suffix.lower() not in SUPPORTED_EXTENSIONS:
                raise ValueError(f"формат {source.suffix or 'без расширения'} не поддерживается")
            data = await asyncio.to_thread(source.read_bytes)
            await self._load_bytes_task(data, source.name, str(source))
        except Exception as exc:
            self.show_toast(f"Не удалось открыть файл: {exc}", error=True)
        finally:
            self.loading_file = False
            self.load_button.disabled = False
            self.set_drop_zone_state("loaded" if self.file_loaded else "empty")
            self.page.update()

    async def _load_memory_task(self, data: bytes, filename: str) -> None:
        self.loading_file = True
        self.load_button.disabled = True
        self.set_drop_zone_state("loading")
        self.page.update()
        try:
            await self._load_bytes_task(data, filename, "")
        except Exception as exc:
            self.show_toast(f"Не удалось открыть файл: {exc}", error=True)
        finally:
            self.loading_file = False
            self.load_button.disabled = False
            self.set_drop_zone_state("loaded" if self.file_loaded else "empty")
            self.page.update()

    async def _load_bytes_task(self, data: bytes, filename: str, path: str) -> None:
        extension = Path(filename).suffix.lower()
        if extension == ".epub":
            paragraphs, source_metadata = await asyncio.to_thread(read_epub_structured, data)
        elif extension == ".docx":
            paragraphs, source_metadata = await asyncio.to_thread(read_docx_structured, data)
        else:
            paragraphs = await asyncio.to_thread(read_source_bytes, data, filename)
            source_metadata = {"kind": extension.lstrip(".") or "text", "preservable": False}
        method = self.config.get("segmentation_method", "advanced")
        sentences, mapping = await asyncio.to_thread(segment_paragraphs, paragraphs, method)
        if not sentences:
            raise ValueError("после сегментации не осталось текста")

        if self.file_loaded:
            self.save_progress(update=False, force_json=True)
        self.project_generation += 1
        # Старые задачи остановятся по несовпадению generation; новый проект
        # не должен наследовать флаг отмены от предыдущего.
        self.batch_cancel_requested = False
        self.batch_job_id = ""
        self.busy_segments.clear()
        self.segment_lock_tokens.clear()
        self.navigation_generation += 1

        self.original_paragraphs = paragraphs
        self.sentences = sentences
        self.sentence_to_paragraph = mapping
        self.rebuild_paragraph_index()
        self.translations = [""] * len(sentences)
        self.statuses = [STATUS_EMPTY] * len(sentences)
        self.bookmarks = [False] * len(sentences)
        self.translation_variants = [self._empty_variant_bundle() for _ in sentences]
        self.active_variant_slots = ["literary"] * len(sentences)
        self.segment_notes = []
        self.secondary_sources = []
        self.honorific_rules = []
        self.glossary_entries = []
        self.character_entries = []
        self.custom_dictionary = []
        self.qa_issues = []
        self.qa_problem_count_cache = 0
        self.deep_qa_cache.clear()
        self.ai_drafts.clear()
        self.edit_examples = []
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.last_history_key = None
        self.current_index = 0
        self.file_loaded = True
        self.project_file_path = path
        self.project_file_name = filename
        self.source_hash = hashlib.sha256(data).hexdigest()
        self.source_document_bytes = bytes(data)
        self.source_document_metadata = source_metadata
        self.progress_path = ""
        self.last_saved_segment_states = []
        self.last_saved_reference_fingerprint = ""
        self.last_json_save_time = 0.0
        restored = self.load_database_project()
        if not restored:
            restored = self.load_progress_data()
        self._ensure_extended_state()
        self._load_project_extensions()
        self._recount_progress()
        self.dirty_segments.clear()
        self.dirty_variants.clear()
        self.dirty_references = False
        self.dirty_project_extensions = False
        self.chapters = detect_chapters(self.original_paragraphs, self.sentence_to_paragraph)
        self.undo_stack, self.redo_stack = self.project_store.load_history(self.source_hash)
        self.last_confirmation = None
        self.last_structure_snapshot = None

        self.search_matches = []
        self.search_position = -1
        self.last_search = ""
        self.rebuild_workspace()
        self.refresh_reference_ui(update=False)
        self.update_history_ui(update=False)
        self.file_path_input.value = path
        self.set_drop_zone_state("loaded")
        if extension == ".epub" and source_metadata.get("preservable"):
            self.export_format.value = "epub_preserve"
        elif extension == ".docx" and source_metadata.get("preservable"):
            self.export_format.value = "docx_preserve"
        elif self.export_format.value in {"epub_preserve", "docx_preserve"}:
            self.export_format.value = "txt"

        if path and Path(path).is_file():
            recent = [item for item in self.config.get("recent_files", []) if item != path]
            self.config["recent_files"] = [path, *recent][:5]
            self.config["last_file"] = path
        try:
            save_config(self.config)
        except OSError as exc:
            self.show_toast(f"Файл открыт, но настройки не сохранены: {exc}", error=True)
        self.update_recent_files_ui(update=False)
        await asyncio.to_thread(self.register_current_project, full=True)
        self.update_ui(update=False)
        self.highlight_current()
        self.render_layout(force=True)
        if self._page_width() < 900:
            self.switch_mobile_tab(1, update=False)
        self.page.update()
        if extension in {".epub", ".docx"} and source_metadata.get("preservable"):
            style_label = "CSS" if extension == ".epub" else "стилей"
            detail = (
                f" · иллюстраций {source_metadata.get('image_count', 0)} · "
                f"{style_label} {source_metadata.get('style_count', 0)}"
            )
        else:
            detail = ""
        self.show_toast("Прогресс восстановлен." if restored else f"Файл открыт: {len(self.sentences)} сегментов{detail}.")

    def rebuild_paragraph_index(self) -> None:
        self.paragraph_segments = [[] for _ in self.original_paragraphs]
        for sentence_index, paragraph_index in enumerate(self.sentence_to_paragraph):
            if 0 <= paragraph_index < len(self.paragraph_segments):
                self.paragraph_segments[paragraph_index].append(sentence_index)

    def _fallback_progress_path(self) -> Path:
        key = self.source_hash or hashlib.sha256(self.project_file_name.encode("utf-8")).hexdigest()
        return APP_DATA_DIR / "progress" / f"{key[:24]}.progress.json"

    def _progress_candidates(self) -> list[Path]:
        candidates: list[Path] = []
        if self.project_file_path and not self.project_file_path.startswith(("content://", "/document/")):
            candidates.append(Path(self.project_file_path + ".progress.json"))
        fallback = self._fallback_progress_path()
        if fallback not in candidates:
            candidates.append(fallback)
        return candidates

    def _normalise_loaded_list(self, value: Any, default: Any) -> list[Any]:
        items = value if isinstance(value, list) else []
        return [items[index] if index < len(items) else default for index in range(len(self.sentences))]

    def _normalise_reference_entries(self, value: Any, *, characters: bool = False) -> list[dict[str, Any]]:
        entries: list[dict[str, Any]] = []
        for raw in value if isinstance(value, list) else []:
            if not isinstance(raw, dict):
                continue
            source = str(raw.get("source", "")).strip()
            target = str(raw.get("target", "")).strip()
            if not source or not target:
                continue
            entry = {
                "source": source,
                "target": target,
                "note": str(raw.get("note", "")).strip(),
            }
            if characters:
                entry["role"] = str(raw.get("role", "")).strip()
                entry["aliases"] = [str(item).strip() for item in raw.get("aliases", []) if str(item).strip()] if isinstance(raw.get("aliases"), list) else []
                entry["target_forms"] = [str(item).strip() for item in raw.get("target_forms", []) if str(item).strip()] if isinstance(raw.get("target_forms"), list) else []
                entry["relationships"] = str(raw.get("relationships", "")).strip()
                entry["voice"] = str(raw.get("voice", "")).strip()
                entry["formality"] = str(raw.get("formality", "")).strip()
            else:
                entry["case_sensitive"] = bool(raw.get("case_sensitive", False))
            entries.append(entry)
        return entries

    @staticmethod
    def _empty_variant_bundle(text: str = "") -> dict[str, dict[str, str]]:
        now = datetime.now().isoformat(timespec="seconds")
        return {
            slot: {
                "label": TRANSLATION_VARIANT_LABELS[slot],
                "text": text if slot == "literary" else "",
                "provider": "",
                "raw_text": "",
                "updated_at": now,
            }
            for slot in TRANSLATION_VARIANT_SLOTS
        }

    def _ensure_extended_state(self) -> None:
        count = len(self.sentences)
        if len(self.translation_variants) != count:
            existing = list(self.translation_variants)
            self.translation_variants = []
            for index in range(count):
                bundle = self._empty_variant_bundle(self.translations[index] if index < len(self.translations) else "")
                if index < len(existing) and isinstance(existing[index], dict):
                    for slot in TRANSLATION_VARIANT_SLOTS:
                        raw = existing[index].get(slot)
                        if isinstance(raw, dict):
                            bundle[slot].update(
                                {key: str(value or "") for key, value in raw.items() if key in bundle[slot]}
                            )
                self.translation_variants.append(bundle)
        if len(self.active_variant_slots) != count:
            existing_slots = list(self.active_variant_slots)
            self.active_variant_slots = [
                existing_slots[index]
                if index < len(existing_slots) and existing_slots[index] in TRANSLATION_VARIANT_SLOTS
                else "literary"
                for index in range(count)
            ]
        for index in range(count):
            slot = self.active_variant_slots[index]
            self.translation_variants[index][slot]["text"] = self.translations[index]

    def _load_project_extensions(self) -> None:
        self._ensure_extended_state()
        if not self.source_hash:
            return
        try:
            stored_variants, stored_active = self.project_store.load_segment_variants(self.source_hash)
            for index in range(len(self.sentences)):
                bundle = self.translation_variants[index]
                for slot, value in stored_variants.get(index, {}).items():
                    if slot in TRANSLATION_VARIANT_SLOTS:
                        bundle[slot].update(value)
                active = stored_active.get(index, self.active_variant_slots[index])
                self.active_variant_slots[index] = active if active in TRANSLATION_VARIANT_SLOTS else "literary"
                bundle[self.active_variant_slots[index]]["text"] = self.translations[index]
            self.segment_notes = self.project_store.load_segment_notes(self.source_hash)
            self.secondary_sources = self.project_store.load_secondary_sources(self.source_hash)
            self.honorific_rules = self.project_store.load_honorific_rules(self.source_hash)
        except (OSError, sqlite3.Error, TypeError, ValueError, zlib.error):
            self.segment_notes = []
            self.secondary_sources = []
            self.honorific_rules = []

    def _recount_progress(self) -> None:
        self.translated_count_cache = sum(bool(value.strip()) for value in self.translations)
        self.confirmed_count_cache = sum(status == STATUS_CONFIRMED for status in self.statuses)
        self.qa_problem_count_cache = sum(bool(issues) for issues in self.qa_issues)

    def _mark_segment_changed(
        self,
        index: int,
        *,
        old_text: str | None = None,
        old_status: str | None = None,
        variant_changed: bool = True,
    ) -> None:
        if not 0 <= index < len(self.sentences):
            return
        if old_text is not None:
            self.translated_count_cache += int(bool(self.translations[index].strip())) - int(bool(old_text.strip()))
        if old_status is not None:
            self.confirmed_count_cache += int(self.statuses[index] == STATUS_CONFIRMED) - int(old_status == STATUS_CONFIRMED)
        self.dirty_segments.add(index)
        if variant_changed:
            self._ensure_extended_state()
            slot = self.active_variant_slots[index]
            record = self.translation_variants[index][slot]
            record["text"] = self.translations[index]
            record["updated_at"] = datetime.now().isoformat(timespec="seconds")
            self.dirty_variants.add(index)
            self._sync_inline_notes(index)
        self.content_revision += 1
        self.segment_lock_tokens.pop(index, None)

    def _sync_inline_notes(self, index: int) -> None:
        if not 0 <= index < len(self.translations):
            return
        _, parsed = parse_tl_notes(self.translations[index])
        previous = [
            note for note in self.segment_notes
            if int(note.get("segment_index", -1)) == index
        ]
        untouched = [
            note for note in self.segment_notes
            if int(note.get("segment_index", -1)) != index
        ]
        now = datetime.now().isoformat(timespec="seconds")
        rebuilt: list[dict[str, Any]] = []
        for position, note in enumerate(parsed):
            old = previous[position] if position < len(previous) else {}
            rebuilt.append(
                {
                    "note_id": str(old.get("note_id") or uuid.uuid4().hex),
                    "segment_index": index,
                    "position": int(note.get("position", 0)),
                    "text": str(note.get("text", "")),
                    "created_at": str(old.get("created_at") or now),
                    "updated_at": now,
                }
            )
        if rebuilt != previous:
            self.segment_notes = [*untouched, *rebuilt]
            self.dirty_project_extensions = True

    def _mark_all_dirty(self) -> None:
        self.dirty_segments = set(range(len(self.sentences)))
        self.dirty_variants = set(range(len(self.sentences)))
        self.dirty_references = True
        self.dirty_project_extensions = True
        self.content_revision += 1
        self._recount_progress()

    def _store_ai_variant(self, index: int, text: str, provider: str, raw_text: str = "") -> None:
        self._ensure_extended_state()
        old_text = self.translations[index]
        old_status = self.statuses[index]
        current_slot = self.active_variant_slots[index]
        self.translation_variants[index][current_slot]["text"] = old_text
        self.translation_variants[index]["machine"].update(
            {
                "text": text,
                "provider": provider,
                "raw_text": raw_text or text,
                "updated_at": datetime.now().isoformat(timespec="seconds"),
            }
        )
        self.active_variant_slots[index] = "machine"
        self.translations[index] = text
        self.statuses[index] = STATUS_DRAFT if text.strip() else STATUS_EMPTY
        self._mark_segment_changed(index, old_text=old_text, old_status=old_status)

    def switch_translation_variant(self, slot: str, e=None) -> None:
        if not self.sentences or slot not in TRANSLATION_VARIANT_SLOTS:
            return
        index = self.current_index
        self._ensure_extended_state()
        current_slot = self.active_variant_slots[index]
        if current_slot == slot:
            return
        self.push_history(f"Вариант перевода · сегмент {index + 1}", segment_indices=[index])
        old_text = self.translations[index]
        old_status = self.statuses[index]
        self.translation_variants[index][current_slot]["text"] = old_text
        self.active_variant_slots[index] = slot
        self.translations[index] = self.translation_variants[index][slot]["text"]
        self.statuses[index] = STATUS_DRAFT if self.translations[index].strip() else STATUS_EMPTY
        self._mark_segment_changed(index, old_text=old_text, old_status=old_status)
        self.update_qa_for_segment(index)
        self.update_preview_paragraph(self.sentence_to_paragraph[index], update=False)
        self.rebuild_variant_controls(update=False)
        self.sync_mobile_editor(update=False)
        field = self.text_fields[index] if index < len(self.text_fields) else None
        if field is not None:
            field.value = self.translations[index]
        self.schedule_autosave()
        self.update_ui(update=False)
        self.page.update()

    def cycle_translation_variant(self, e=None) -> None:
        if not self.sentences:
            return
        current = self.active_variant_slots[self.current_index] if self.active_variant_slots else "literary"
        position = TRANSLATION_VARIANT_SLOTS.index(current) if current in TRANSLATION_VARIANT_SLOTS else 0
        self.switch_translation_variant(TRANSLATION_VARIANT_SLOTS[(position + 1) % len(TRANSLATION_VARIANT_SLOTS)])

    def _segment_states(self) -> list[tuple[Any, ...]]:
        return [
            (
                self.sentences[index],
                int(self.sentence_to_paragraph[index]),
                self.translations[index],
                self.statuses[index],
                bool(self.bookmarks[index]),
            )
            for index in range(len(self.sentences))
        ]

    def _reference_fingerprint(self) -> str:
        payload = {
            "glossary": self.glossary_entries,
            "characters": self.character_entries,
            "dictionary": self.custom_dictionary,
            "examples": self.edit_examples[-100:],
        }
        raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(raw).hexdigest()

    def load_database_project(self) -> bool:
        if not self.source_hash:
            return False
        try:
            data = self.project_store.load_document(self.source_hash)
        except (OSError, sqlite3.Error, ValueError, TypeError):
            return False
        if not data or data.get("original_paragraphs") != self.original_paragraphs:
            return False
        sentences = data.get("sentences")
        mapping = data.get("sentence_to_paragraph")
        if not isinstance(sentences, list) or not isinstance(mapping, list) or len(sentences) != len(mapping):
            return False
        try:
            restored_mapping = [int(value) for value in mapping]
        except (TypeError, ValueError):
            return False
        if not restored_mapping or not all(0 <= value < len(self.original_paragraphs) for value in restored_mapping):
            return False
        self.sentences = [str(value) for value in sentences]
        self.sentence_to_paragraph = restored_mapping
        self.rebuild_paragraph_index()
        raw_translations = data.get("translations", [])
        self.translations = [str(raw_translations[index] or "") if index < len(raw_translations) else "" for index in range(len(self.sentences))]
        raw_statuses = data.get("statuses", [])
        self.statuses = []
        for index, translation in enumerate(self.translations):
            status = raw_statuses[index] if index < len(raw_statuses) else STATUS_DRAFT
            self.statuses.append(status if translation.strip() and status in {STATUS_DRAFT, STATUS_CONFIRMED} else STATUS_EMPTY)
        raw_bookmarks = data.get("bookmarks", [])
        self.bookmarks = [bool(raw_bookmarks[index]) if index < len(raw_bookmarks) else False for index in range(len(self.sentences))]
        self.glossary_entries = self._normalise_reference_entries(data.get("glossary"), characters=False)
        self.character_entries = self._normalise_reference_entries(data.get("characters"), characters=True)
        dictionary = data.get("custom_dictionary", [])
        self.custom_dictionary = sorted({str(word).strip() for word in dictionary if str(word).strip()}, key=str.casefold)
        examples = data.get("edit_examples", [])
        self.edit_examples = [dict(item) for item in examples if isinstance(item, dict) and item.get("source") and item.get("final")][-100:]
        try:
            self.current_index = max(0, min(int(data.get("current_index", 0)), len(self.sentences) - 1))
        except (TypeError, ValueError):
            self.current_index = 0
        self.last_saved_segment_states = [()] * len(self.sentences)
        self.last_saved_reference_fingerprint = self._reference_fingerprint()
        return True

    def save_database_project(self, *, full: bool = False) -> bool:
        if not self.file_loaded or not self.source_hash:
            return False
        self._ensure_extended_state()
        saved_revision = self.content_revision
        dirty_segments = set(range(len(self.sentences))) if full else set(self.dirty_segments)
        dirty_variants = set(range(len(self.sentences))) if full else set(self.dirty_variants)
        self.project_store.upsert_project(
            self.source_hash,
            title=Path(self.project_file_name or "Книга").stem,
            source_name=self.project_file_name,
            source_path=self.project_file_path,
            segment_count=len(self.sentences),
            translated_count=self.translated_count_cache,
            confirmed_count=self.confirmed_count_cache,
            current_index=self.current_index,
        )
        replace_all = full or not self.last_saved_segment_states
        if replace_all:
            self.project_store.replace_document(
                self.source_hash,
                paragraphs=self.original_paragraphs,
                sentences=self.sentences,
                sentence_to_paragraph=self.sentence_to_paragraph,
                translations=self.translations,
                statuses=self.statuses,
                bookmarks=self.bookmarks,
            )
            self.project_store.replace_chapters(self.source_hash, self.chapters)
        else:
            self.project_store.upsert_segments(
                self.source_hash,
                (
                    (
                        index,
                        self.sentence_to_paragraph[index],
                        self.sentences[index],
                        self.translations[index],
                        self.statuses[index],
                        self.bookmarks[index],
                    )
                    for index in sorted(dirty_segments)
                ),
            )
        if dirty_variants:
            self.project_store.upsert_segment_variants(
                self.source_hash,
                (
                    {
                        "segment_index": index,
                        "slot": slot,
                        **self.translation_variants[index][slot],
                    }
                    for index in sorted(dirty_variants)
                    for slot in TRANSLATION_VARIANT_SLOTS
                ),
            )
            self.project_store.upsert_variant_states(
                self.source_hash,
                ((index, self.active_variant_slots[index]) for index in sorted(dirty_variants)),
            )
        reference_fingerprint = self._reference_fingerprint()
        if full or self.dirty_references or reference_fingerprint != self.last_saved_reference_fingerprint:
            self.project_store.replace_references(
                self.source_hash,
                glossary=self.glossary_entries,
                characters=self.character_entries,
                dictionary=self.custom_dictionary,
                edit_examples=self.edit_examples[-100:],
            )
        if full or self.dirty_project_extensions:
            self.project_store.replace_segment_notes(self.source_hash, self.segment_notes)
            self.project_store.replace_honorific_rules(self.source_hash, self.honorific_rules)
            self.project_store.save_project_settings(
                self.source_hash,
                {
                    "content_revision": self.content_revision,
                    "format_version": 7,
                },
            )
        if full and self.source_document_bytes:
            self.project_store.save_source(
                self.source_hash,
                source_name=self.project_file_name,
                extension=Path(self.project_file_name).suffix.lower(),
                source_hash=self.source_hash,
                source_bytes=self.source_document_bytes,
                metadata=self.source_document_metadata,
            )
        # replace_document() пересоздаёт первичные сегменты и каскадно удаляет
        # их Dual-RAW связи. На полном сохранении восстанавливаем поток и карту.
        if full:
            for source in self.secondary_sources:
                source_id = str(source.get("source_id", ""))
                segment_rows = list(source.get("segments", []))
                if not source_id or not segment_rows:
                    continue
                source_bytes = bytes(source.get("source_bytes", b""))
                mapping = [int(item.get("paragraph_index", 0)) for item in segment_rows]
                secondary_segments = [str(item.get("source_text", "")) for item in segment_rows]
                self.project_store.save_secondary_source(
                    self.source_hash,
                    source_id=source_id,
                    name=str(source.get("name", "Второй оригинал")),
                    language=str(source.get("language", "auto")),
                    source_hash=str(source.get("source_hash", hashlib.sha256(source_bytes).hexdigest())),
                    source_bytes=source_bytes,
                    segments=secondary_segments,
                    mapping=mapping,
                    metadata=dict(source.get("metadata", {})),
                )
                self.project_store.replace_segment_alignments(
                    self.source_hash,
                    source_id,
                    (
                        (
                            int(item.get("primary", 0)),
                            int(item.get("secondary", 0)),
                            int(item.get("order", 0)),
                        )
                        for item in source.get("alignments", [])
                    ),
                )
        if replace_all:
            self.last_saved_segment_states = [()] * len(self.sentences)
        # Если пользователь успел отредактировать текст, пока SQLite записывался
        # в фоновом потоке, dirty-состояние не сбрасываем: следующий autosave
        # повторит запись и гарантированно подхватит свежую ревизию.
        if self.content_revision == saved_revision:
            self.last_saved_reference_fingerprint = reference_fingerprint
            self.dirty_segments.difference_update(dirty_segments)
            self.dirty_variants.difference_update(dirty_variants)
            self.dirty_references = False
            self.dirty_project_extensions = False
        return True

    def load_progress_data(self) -> bool:
        for candidate in self._progress_candidates():
            try:
                with candidate.open("r", encoding="utf-8") as stream:
                    data = json.load(stream)
            except (OSError, ValueError, TypeError):
                continue
            if not isinstance(data, dict):
                continue
            saved_hash = data.get("source_hash")
            if saved_hash and saved_hash != self.source_hash:
                continue
            if not saved_hash and data.get("sentences") != self.sentences:
                continue

            saved_sentences = data.get("sentences")
            saved_mapping = data.get("sentence_to_paragraph")
            if (
                saved_hash
                and isinstance(saved_sentences, list)
                and saved_sentences
                and isinstance(saved_mapping, list)
                and len(saved_sentences) == len(saved_mapping)
            ):
                try:
                    restored_mapping = [int(value) for value in saved_mapping]
                except (TypeError, ValueError):
                    restored_mapping = []
                if restored_mapping and all(0 <= value < len(self.original_paragraphs) for value in restored_mapping):
                    self.sentences = [str(value) for value in saved_sentences]
                    self.sentence_to_paragraph = restored_mapping
                    self.rebuild_paragraph_index()

            raw_translations = self._normalise_loaded_list(data.get("translations"), "")
            self.translations = [str(value or "") for value in raw_translations]
            raw_statuses = self._normalise_loaded_list(data.get("statuses"), "")
            self.statuses = []
            for index, status in enumerate(raw_statuses):
                if not self.translations[index].strip():
                    self.statuses.append(STATUS_EMPTY)
                elif status in {STATUS_DRAFT, STATUS_CONFIRMED}:
                    self.statuses.append(status)
                else:
                    self.statuses.append(STATUS_DRAFT)
            self.bookmarks = [bool(value) for value in self._normalise_loaded_list(data.get("bookmarks"), False)]
            raw_variants = data.get("translation_variants", [])
            self.translation_variants = [dict(item) if isinstance(item, dict) else {} for item in raw_variants] if isinstance(raw_variants, list) else []
            raw_active = data.get("active_variant_slots", [])
            self.active_variant_slots = [str(item) for item in raw_active] if isinstance(raw_active, list) else []
            raw_notes = data.get("segment_notes", [])
            self.segment_notes = [dict(item) for item in raw_notes if isinstance(item, dict)] if isinstance(raw_notes, list) else []
            raw_rules = data.get("honorific_rules", [])
            self.honorific_rules = [dict(item) for item in raw_rules if isinstance(item, dict)] if isinstance(raw_rules, list) else []
            self._ensure_extended_state()
            self.glossary_entries = self._normalise_reference_entries(data.get("glossary"), characters=False)
            self.character_entries = self._normalise_reference_entries(data.get("characters"), characters=True)
            dictionary = data.get("custom_dictionary", [])
            self.custom_dictionary = sorted({str(word).strip() for word in dictionary if str(word).strip()}, key=str.casefold) if isinstance(dictionary, list) else []
            examples = data.get("edit_examples", [])
            self.edit_examples = [
                {"source": str(item.get("source", "")), "draft": str(item.get("draft", "")), "final": str(item.get("final", ""))}
                for item in examples
                if isinstance(item, dict) and item.get("source") and item.get("final")
            ][-100:] if isinstance(examples, list) else []
            try:
                self.current_index = max(0, min(int(data.get("current_index", 0)), len(self.sentences) - 1))
            except (TypeError, ValueError):
                self.current_index = 0
            self.progress_path = str(candidate)
            return True
        return False

    def _progress_payload(self, *, reason: str = "autosave") -> dict[str, Any]:
        return {
            "version": 7,
            "source_file": self.project_file_name,
            "source_hash": self.source_hash,
            "source_document_metadata": self.source_document_metadata,
            "sentences": self.sentences,
            "sentence_to_paragraph": self.sentence_to_paragraph,
            "translations": self.translations,
            "statuses": self.statuses,
            "bookmarks": self.bookmarks,
            "translation_variants": self.translation_variants,
            "active_variant_slots": self.active_variant_slots,
            "segment_notes": self.segment_notes,
            "honorific_rules": self.honorific_rules,
            "glossary": self.glossary_entries,
            "characters": self.character_entries,
            "custom_dictionary": self.custom_dictionary,
            "chapters": self.chapters,
            "edit_examples": self.edit_examples[-100:],
            "current_index": self.current_index,
            "timestamp": datetime.now().isoformat(timespec="seconds"),
            "reason": reason,
        }

    def save_progress(self, *, update: bool = True, force_json: bool = False) -> bool:
        if not self.file_loaded or not self.sentences:
            return False
        database_saved = False
        database_error: Exception | None = None
        try:
            database_saved = self.save_database_project()
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            database_error = exc

        payload = self._progress_payload()
        candidates = [Path(self.progress_path)] if self.progress_path else []
        candidates.extend(path for path in self._progress_candidates() if path not in candidates)
        json_due = force_json or not database_saved or not self.last_json_save_time or time.monotonic() - self.last_json_save_time >= 30
        json_saved = False
        json_error: Exception | None = None
        if json_due:
            for candidate in candidates:
                try:
                    _atomic_write_json(candidate, payload)
                    self.progress_path = str(candidate)
                    self.last_json_save_time = time.monotonic()
                    json_saved = True
                    break
                except OSError as exc:
                    json_error = exc
        if database_saved or json_saved:
            suffix = " · резерв JSON" if json_saved else ""
            self.save_status_indicator.value = f"Сохранено в проект · {datetime.now().strftime('%H:%M:%S')}{suffix}"
            self.save_status_indicator.color = STATUS_COLORS[STATUS_CONFIRMED]
        else:
            self.save_status_indicator.value = f"Ошибка сохранения: {database_error or json_error or 'нет доступного пути'}"
            self.save_status_indicator.color = STATUS_COLORS[STATUS_EMPTY]
        if update:
            self.page.update()
        return database_saved or json_saved

    def project_snapshot(self) -> dict[str, Any]:
        return {
            "kind": "project",
            "sentences": list(self.sentences),
            "sentence_to_paragraph": list(self.sentence_to_paragraph),
            "translations": list(self.translations),
            "statuses": list(self.statuses),
            "bookmarks": list(self.bookmarks),
            "translation_variants": json.loads(json.dumps(self.translation_variants, ensure_ascii=False)),
            "active_variant_slots": list(self.active_variant_slots),
            "segment_notes": json.loads(json.dumps(self.segment_notes, ensure_ascii=False)),
            "secondary_sources": json.loads(
                json.dumps(
                    [{key: value for key, value in item.items() if key != "source_bytes"} for item in self.secondary_sources],
                    ensure_ascii=False,
                )
            ),
            "honorific_rules": json.loads(json.dumps(self.honorific_rules, ensure_ascii=False)),
            "glossary": json.loads(json.dumps(self.glossary_entries, ensure_ascii=False)),
            "characters": json.loads(json.dumps(self.character_entries, ensure_ascii=False)),
            "custom_dictionary": list(self.custom_dictionary),
            "edit_examples": json.loads(json.dumps(self.edit_examples[-100:], ensure_ascii=False)),
            "current_index": self.current_index,
        }

    def _segment_history_snapshot(self, indices: Iterable[int]) -> dict[str, Any]:
        self._ensure_extended_state()
        unique = sorted({int(index) for index in indices if 0 <= int(index) < len(self.sentences)})
        notes_by_segment: dict[int, list[dict[str, Any]]] = {}
        for note in self.segment_notes:
            try:
                note_index = int(note.get("segment_index", -1))
            except (TypeError, ValueError):
                continue
            if note_index in unique:
                notes_by_segment.setdefault(note_index, []).append(dict(note))
        return {
            "kind": "segments",
            "indices": unique,
            "items": {
                str(index): {
                    "translation": self.translations[index],
                    "status": self.statuses[index],
                    "bookmark": self.bookmarks[index],
                    "variants": json.loads(json.dumps(self.translation_variants[index], ensure_ascii=False)),
                    "active_slot": self.active_variant_slots[index],
                    "notes": notes_by_segment.get(index, []),
                }
                for index in unique
            },
            "current_index": self.current_index,
        }

    def _reference_history_snapshot(self) -> dict[str, Any]:
        return {
            "kind": "references",
            "glossary": json.loads(json.dumps(self.glossary_entries, ensure_ascii=False)),
            "characters": json.loads(json.dumps(self.character_entries, ensure_ascii=False)),
            "custom_dictionary": list(self.custom_dictionary),
            "honorific_rules": json.loads(json.dumps(self.honorific_rules, ensure_ascii=False)),
            "edit_examples": json.loads(json.dumps(self.edit_examples[-100:], ensure_ascii=False)),
            "current_index": self.current_index,
        }

    def _capture_like(self, snapshot: dict[str, Any]) -> dict[str, Any]:
        kind = snapshot.get("kind", "project")
        if kind == "segments":
            return self._segment_history_snapshot(snapshot.get("indices", []))
        if kind == "references":
            return self._reference_history_snapshot()
        return self.project_snapshot()

    def push_history(
        self,
        reason: str,
        *,
        coalesce_key: str | None = None,
        segment_indices: Iterable[int] | None = None,
        references: bool = False,
    ) -> None:
        if self.history_suspended or not self.file_loaded:
            return
        now = time.monotonic()
        if coalesce_key and self.last_history_key == coalesce_key and now - self.last_history_time < 2.5:
            self.last_history_time = now
            return
        if segment_indices is not None:
            snapshot = self._segment_history_snapshot(segment_indices)
        elif references:
            snapshot = self._reference_history_snapshot()
        else:
            snapshot = self.project_snapshot()
        self.undo_stack.append(
            {
                "reason": reason,
                "timestamp": datetime.now().isoformat(timespec="seconds"),
                "snapshot": snapshot,
            }
        )
        history_limit = 60
        del self.undo_stack[:-history_limit]
        self.redo_stack.clear()
        self.last_history_key = coalesce_key
        self.last_history_time = now
        self.update_history_ui(update=False)
        self.persist_history()

    def restore_project_snapshot(self, snapshot: dict[str, Any], *, save: bool = True) -> None:
        kind = snapshot.get("kind", "project")
        if kind == "segments":
            self.history_suspended = True
            try:
                items = snapshot.get("items", {})
                affected: set[int] = set()
                for raw_index, raw in items.items() if isinstance(items, dict) else []:
                    try:
                        index = int(raw_index)
                    except (TypeError, ValueError):
                        continue
                    if not 0 <= index < len(self.sentences) or not isinstance(raw, dict):
                        continue
                    self.translations[index] = str(raw.get("translation", ""))
                    status = str(raw.get("status", STATUS_DRAFT))
                    self.statuses[index] = status if self.translations[index].strip() and status in {STATUS_DRAFT, STATUS_CONFIRMED} else STATUS_EMPTY
                    self.bookmarks[index] = bool(raw.get("bookmark", False))
                    variants = raw.get("variants")
                    if isinstance(variants, dict):
                        self.translation_variants[index] = json.loads(json.dumps(variants, ensure_ascii=False))
                    active = str(raw.get("active_slot", "literary"))
                    self.active_variant_slots[index] = active if active in TRANSLATION_VARIANT_SLOTS else "literary"
                    self.segment_notes = [
                        note for note in self.segment_notes
                        if int(note.get("segment_index", -1)) != index
                    ]
                    self.segment_notes.extend(dict(note) for note in raw.get("notes", []) if isinstance(note, dict))
                    affected.add(index)
                self.current_index = max(0, min(int(snapshot.get("current_index", self.current_index)), len(self.sentences) - 1))
                self.dirty_segments.update(affected)
                self.dirty_variants.update(affected)
                self.dirty_project_extensions = True
                self.content_revision += 1
                self.segment_lock_tokens.clear()
                self.deep_qa_cache.clear()
                self._recount_progress()
                self.rebuild_workspace()
                self.update_ui(update=False)
                self.highlight_current(update=False)
                if save:
                    self.save_progress(update=False)
            finally:
                self.history_suspended = False
            self.update_history_ui(update=False)
            self.page.update()
            return
        if kind == "references":
            self.history_suspended = True
            try:
                self.glossary_entries = self._normalise_reference_entries(snapshot.get("glossary"), characters=False)
                self.character_entries = self._normalise_reference_entries(snapshot.get("characters"), characters=True)
                dictionary = snapshot.get("custom_dictionary", [])
                self.custom_dictionary = sorted({str(word).strip() for word in dictionary if str(word).strip()}, key=str.casefold)
                self.honorific_rules = [dict(item) for item in snapshot.get("honorific_rules", []) if isinstance(item, dict)]
                self.edit_examples = [dict(item) for item in snapshot.get("edit_examples", []) if isinstance(item, dict)][-100:]
                self.dirty_references = True
                self.dirty_project_extensions = True
                self.content_revision += 1
                self.deep_qa_cache.clear()
                self.refresh_qa()
                self.refresh_reference_ui(update=False)
                if save:
                    self.save_progress(update=False)
            finally:
                self.history_suspended = False
            self.update_history_ui(update=False)
            self.page.update()
            return
        sentences = snapshot.get("sentences")
        mapping = snapshot.get("sentence_to_paragraph")
        if not isinstance(sentences, list) or not isinstance(mapping, list) or len(sentences) != len(mapping):
            raise ValueError("резервная версия повреждена")
        try:
            restored_mapping = [int(value) for value in mapping]
        except (TypeError, ValueError) as exc:
            raise ValueError("резервная версия содержит неверную карту абзацев") from exc
        if not restored_mapping or not all(0 <= value < len(self.original_paragraphs) for value in restored_mapping):
            raise ValueError("резервная версия не соответствует структуре книги")
        self.history_suspended = True
        try:
            self.sentences = [str(value) for value in sentences]
            self.sentence_to_paragraph = restored_mapping
            self.translations = [str(value or "") for value in snapshot.get("translations", [])][:len(self.sentences)]
            self.translations.extend([""] * (len(self.sentences) - len(self.translations)))
            raw_statuses = list(snapshot.get("statuses", []))
            self.statuses = []
            for index, translation in enumerate(self.translations):
                status = raw_statuses[index] if index < len(raw_statuses) else STATUS_DRAFT
                self.statuses.append(status if translation.strip() and status in {STATUS_DRAFT, STATUS_CONFIRMED} else STATUS_EMPTY)
            raw_bookmarks = list(snapshot.get("bookmarks", []))
            self.bookmarks = [bool(raw_bookmarks[index]) if index < len(raw_bookmarks) else False for index in range(len(self.sentences))]
            raw_variants = snapshot.get("translation_variants", [])
            self.translation_variants = [dict(item) if isinstance(item, dict) else {} for item in raw_variants] if isinstance(raw_variants, list) else []
            raw_active = snapshot.get("active_variant_slots", [])
            self.active_variant_slots = [str(item) for item in raw_active] if isinstance(raw_active, list) else []
            self.segment_notes = [dict(item) for item in snapshot.get("segment_notes", []) if isinstance(item, dict)]
            restored_secondary = [dict(item) for item in snapshot.get("secondary_sources", []) if isinstance(item, dict)]
            current_secondary_bytes = {
                str(item.get("source_id", "")): item.get("source_bytes", b"") for item in self.secondary_sources
            }
            for item in restored_secondary:
                item["source_bytes"] = current_secondary_bytes.get(str(item.get("source_id", "")), b"")
            self.secondary_sources = restored_secondary
            self.honorific_rules = [dict(item) for item in snapshot.get("honorific_rules", []) if isinstance(item, dict)]
            self._ensure_extended_state()
            self.glossary_entries = self._normalise_reference_entries(snapshot.get("glossary"), characters=False)
            self.character_entries = self._normalise_reference_entries(snapshot.get("characters"), characters=True)
            dictionary = snapshot.get("custom_dictionary", [])
            self.custom_dictionary = sorted({str(word).strip() for word in dictionary if str(word).strip()}, key=str.casefold) if isinstance(dictionary, list) else []
            examples = snapshot.get("edit_examples", [])
            self.edit_examples = [dict(item) for item in examples if isinstance(item, dict) and item.get("source") and item.get("final")][-100:] if isinstance(examples, list) else []
            self.ai_drafts.clear()
            self.current_index = max(0, min(int(snapshot.get("current_index", 0)), max(0, len(self.sentences) - 1)))
            self.deep_qa_cache.clear()
            self.project_generation += 1
            self.rebuild_paragraph_index()
            self.chapters = detect_chapters(self.original_paragraphs, self.sentence_to_paragraph)
            self.last_saved_segment_states = []
            self._mark_all_dirty()
            self.rebuild_workspace()
            self.refresh_reference_ui(update=False)
            self.apply_segment_filter(update=False)
            self.update_ui(update=False)
            self.highlight_current(update=False)
            if save:
                self.save_progress(update=False)
        finally:
            self.history_suspended = False
        self.update_history_ui(update=False)
        self.persist_history()
        self.page.update()

    def undo_history(self, e=None) -> None:
        if not self.undo_stack:
            self.show_toast("Отменять больше нечего.")
            return
        action = self.undo_stack.pop()
        self.redo_stack.append(
            {"reason": action["reason"], "timestamp": datetime.now().isoformat(timespec="seconds"), "snapshot": self._capture_like(action["snapshot"])}
        )
        self.last_history_key = None
        self.restore_project_snapshot(action["snapshot"])
        self.persist_history()
        self.show_toast(f"Отменено: {action['reason']}.")

    def redo_history(self, e=None) -> None:
        if not self.redo_stack:
            self.show_toast("Возвращать больше нечего.")
            return
        action = self.redo_stack.pop()
        self.undo_stack.append(
            {"reason": action["reason"], "timestamp": datetime.now().isoformat(timespec="seconds"), "snapshot": self._capture_like(action["snapshot"])}
        )
        self.last_history_key = None
        self.restore_project_snapshot(action["snapshot"])
        self.persist_history()
        self.show_toast(f"Возвращено: {action['reason']}.")

    def update_history_ui(self, *, update: bool = True) -> None:
        for name, disabled in (
            ("undo_button", not self.undo_stack),
            ("mobile_undo_button", not self.undo_stack),
            ("redo_button", not self.redo_stack),
            ("mobile_redo_button", not self.redo_stack),
        ):
            control = getattr(self, name, None)
            if control is not None:
                control.disabled = disabled
        if hasattr(self, "history_summary_text"):
            last = self.undo_stack[-1]["reason"] if self.undo_stack else "история пока пуста"
            self.history_summary_text.value = f"Отмена: {len(self.undo_stack)} · возврат: {len(self.redo_stack)} · последнее: {last}"
        if update:
            self.page.update()

    def register_current_project(self, *, full: bool = False) -> None:
        if not self.file_loaded or not self.source_hash:
            return
        try:
            self.save_database_project(full=full)
        except (OSError, sqlite3.Error, TypeError, ValueError):
            # Переносимая JSON-копия остаётся независимым аварийным каналом.
            pass

    def persist_history(self) -> None:
        if not self.source_hash:
            return
        try:
            self.project_store.save_history(self.source_hash, self.undo_stack, self.redo_stack)
        except (OSError, sqlite3.Error, TypeError, ValueError):
            pass

    def open_project_library(self, e=None) -> None:
        self.register_current_project()
        self.refresh_project_library(update=False)
        self.fit_bottom_sheet(self.project_library_sheet, 700)
        self._open(self.project_library_sheet)

    def refresh_project_library(self, *, update: bool = True) -> None:
        if not hasattr(self, "project_library_list"):
            return
        self.project_library_list.controls.clear()
        self.chapter_list.controls.clear()
        try:
            projects = self.project_store.list_projects()
        except (OSError, sqlite3.Error):
            projects = []
        if not projects:
            self.project_library_list.controls.append(ft.Text("Каталог пока пуст.", color=self.muted_color, size=12))
        for project in projects:
            count = max(1, int(project.get("segment_count", 0) or 0))
            confirmed = int(project.get("confirmed_count", 0) or 0)
            path = str(project.get("source_path", "") or "")
            has_external = bool(path and Path(path).is_file())
            has_source = bool(project.get("has_source", False))
            open_button = ft.TextButton(
                text="Открыть",
                disabled=not has_external and not has_source,
                on_click=lambda e, project_id=str(project.get("project_id", "")), selected=path,
                                name=str(project.get("source_name", "novel.txt")):
                    self.load_project_from_library(project_id, selected, name),
            )
            storage_note = "исходник внутри проекта" if has_source else "нужен исходный файл"
            self.project_library_list.controls.append(
                ft.Container(
                    content=ft.Row(
                        [
                            ft.Column(
                                [
                                    ft.Text(str(project.get("title", "Книга")), color=self.text_color, weight=ft.FontWeight.BOLD),
                                    ft.Text(
                                        f"{confirmed}/{count} подтверждено · {storage_note} · {project.get('updated_at', '')}",
                                        color=self.muted_color,
                                        size=11,
                                    ),
                                ],
                                spacing=2,
                                expand=True,
                            ),
                            open_button,
                        ]
                    ),
                    padding=8,
                    border=ft.border.all(1, self.border_color),
                    border_radius=8,
                )
            )
        if not self.chapters:
            self.chapter_list.controls.append(ft.Text("Откройте книгу, чтобы увидеть главы.", color=self.muted_color, size=12))
        for index, chapter in enumerate(self.chapters):
            start = int(chapter.get("start", 0))
            end = int(chapter.get("end", start))
            stats = chapter_progress_statistics(
                start,
                end,
                self.translations,
                self.statuses,
                self.bookmarks,
                self.qa_issues,
            )
            progress = float(stats["progress"])
            progress_color = (
                STATUS_COLORS[STATUS_CONFIRMED]
                if progress >= 1
                else STATUS_COLORS[STATUS_DRAFT]
                if progress > 0
                else STATUS_COLORS[STATUS_EMPTY]
            )
            self.chapter_list.controls.append(
                ft.Container(
                    content=ft.Column(
                        [
                            ft.Row(
                                [
                                    ft.Column(
                                        [
                                            ft.Text(
                                                str(chapter.get("title", f"Глава {index + 1}")),
                                                color=self.text_color,
                                                size=12,
                                                weight=ft.FontWeight.BOLD,
                                            ),
                                            ft.Text(
                                                f"{round(progress * 100)}% · готово {stats['confirmed']}/{max(1, int(stats['total']))} · "
                                                f"пусто {stats['empty']} · QA {stats['qa']}",
                                                color=self.muted_color,
                                                size=10,
                                            ),
                                        ],
                                        spacing=2,
                                        expand=True,
                                    ),
                                    ft.IconButton(
                                        icon="arrow_forward",
                                        tooltip="Открыть главу",
                                        on_click=lambda e, selected=start: self.jump_to_chapter(selected),
                                    ),
                                ]
                            ),
                            ft.ProgressBar(
                                value=progress,
                                bar_height=4,
                                color=progress_color,
                                bgcolor=self.progress_track_color,
                            ),
                        ],
                        spacing=6,
                    ),
                    padding=9,
                    border=ft.border.all(1, self.border_color),
                    border_radius=10,
                    bgcolor=self.editor_bg,
                )
            )
        if update:
            self.page.update()

    def load_project_from_library(self, project_id: str, path: str, source_name: str) -> None:
        self._close(self.project_library_sheet)
        if path and Path(path).is_file():
            self.start_load_path(path)
            return
        try:
            stored = self.project_store.load_source(project_id)
        except (OSError, sqlite3.Error, ValueError) as exc:
            self.show_toast(f"Не удалось открыть встроенный исходник: {exc}", error=True)
            return
        if stored is None:
            self.show_toast("Исходный файл проекта больше недоступен.", error=True)
            return
        data, stored_name, _ = stored
        self.page.run_task(self._load_memory_task, data, stored_name or source_name)

    def jump_to_chapter(self, index: int) -> None:
        self._close(self.project_library_sheet)
        self.focus_segment(index)

    def backup_directory(self) -> Path:
        if self.project_file_path and not self.project_file_path.startswith(("content://", "/document/")):
            return Path(self.project_file_path + ".literaflow-backups")
        key = self.source_hash or hashlib.sha256(self.project_file_name.encode("utf-8")).hexdigest()
        return APP_DATA_DIR / "backups" / key[:24]

    def backup_files(self) -> list[Path]:
        try:
            return sorted(self.backup_directory().glob("*.json"), reverse=True)
        except OSError:
            return []

    def create_backup(self, e=None, *, reason: str = "manual") -> Path | None:
        if not self.file_loaded:
            self.show_toast("Сначала загрузите файл.")
            return None
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S-%f")
        path = self.backup_directory() / f"{stamp}.json"
        try:
            _atomic_write_json(path, self._progress_payload(reason=reason))
            for obsolete in self.backup_files()[20:]:
                try:
                    obsolete.unlink()
                except OSError:
                    pass
            self.refresh_backup_list(update=False)
            self.page.update()
            if e is not None:
                self.show_toast(f"Резервная версия создана: {path.name}")
            return path
        except OSError as exc:
            self.show_toast(f"Не удалось создать резервную версию: {exc}", error=True)
            return None

    def schedule_autosave(self) -> None:
        self.autosave_revision += 1
        revision = self.autosave_revision
        self.page.run_task(self._autosave_after_delay, revision, self.project_generation)

    async def _autosave_after_delay(self, revision: int, generation: int) -> None:
        await asyncio.sleep(0.7)
        if revision == self.autosave_revision and generation == self.project_generation:
            self.save_progress(update=True)

    def on_page_close(self, e=None) -> None:
        self.batch_cancel_requested = True
        if self.file_loaded:
            self.save_progress(update=False, force_json=True)

    def rebuild_workspace(self) -> None:
        self.workspace_list.controls.clear()
        self.left_list.controls.clear()
        self.preview_list.controls.clear()
        count = len(self.sentences)
        paragraph_count = len(self.original_paragraphs)
        self.text_fields = [None] * count
        self.status_indicators = [None] * count
        self.ai_buttons = [None] * count
        self.bookmark_buttons = [None] * count
        self.original_views = [None] * count
        self.original_text_controls = [None] * count
        self.segment_views = [None] * count
        self.preview_boxes = [None] * paragraph_count
        self.preview_text_controls = [None] * paragraph_count
        self.qa_labels = [None] * count
        self.highlighted_index = -1
        self.highlighted_paragraph = -1
        if len(self.qa_issues) != count:
            self.qa_issues = [[] for _ in range(count)]
            self.qa_problem_count_cache = 0

        self.large_document_mode = count > LARGE_DOCUMENT_THRESHOLD
        if self.large_document_mode:
            half = LARGE_DOCUMENT_WINDOW // 2
            start = max(0, min(max(0, count - LARGE_DOCUMENT_WINDOW), self.current_index - half))
            end = min(count, start + LARGE_DOCUMENT_WINDOW)
            render_indices = list(range(start, end))
        else:
            render_indices = list(range(count))
        self.rendered_indices = set(render_indices)
        self.rendered_paragraphs = {self.sentence_to_paragraph[index] for index in render_indices}
        for index in render_indices:
            old_problem = bool(self.qa_issues[index])
            self.qa_issues[index] = qa_issues_for_segment(
                self.sentences[index],
                self.translations[index],
                self.config.get("target_lang", "ru"),
                self.glossary_entries,
                self.character_entries,
                self.honorific_rules,
            )
            self.qa_problem_count_cache += int(bool(self.qa_issues[index])) - int(old_problem)

        font_size = int(self.config.get("font_size", 14))
        for index in render_indices:
            source = self.sentences[index]
            source_text = ft.Text(
                source,
                size=max(11, font_size - 2),
                color=self.text_color,
                selectable=True,
                expand=True,
            )
            self.original_text_controls[index] = source_text
            left_inner = ft.Container(
                key=f"source-{index}",
                content=ft.Row(
                    [
                        ft.Text(f"{index + 1}", size=10, color=self.muted_color, width=32),
                        source_text,
                    ],
                    vertical_alignment=ft.CrossAxisAlignment.START,
                ),
                padding=8,
                border_radius=6,
                on_click=lambda e, selected=index: self.focus_segment(selected),
            )
            self.original_views[index] = left_inner
            self.left_list.controls.append(left_inner)

            status = self.statuses[index]
            status_indicator = ft.Container(
                width=10,
                height=10,
                bgcolor=STATUS_COLORS[status],
                border_radius=5,
                tooltip=STATUS_TITLES[status],
            )
            self.status_indicators[index] = status_indicator
            qa_label = ft.Text(
                f"⚠ {len(self.qa_issues[index])}" if self.qa_issues[index] else "",
                size=10,
                color=(
                    STATUS_COLORS[STATUS_EMPTY]
                    if any(qa_issue_severity(issue) == "error" for issue in self.qa_issues[index])
                    else STATUS_COLORS[STATUS_DRAFT]
                ),
                tooltip=" · ".join(self.qa_issues[index]),
            )
            self.qa_labels[index] = qa_label

            bookmark_button = ft.IconButton(
                icon="bookmark" if self.bookmarks[index] else "bookmark_border",
                icon_size=17,
                icon_color=self.accent if self.bookmarks[index] else self.muted_color,
                tooltip="Убрать закладку" if self.bookmarks[index] else "Добавить закладку",
                on_click=lambda e, selected=index: self.toggle_bookmark(selected),
            )
            self.bookmark_buttons[index] = bookmark_button
            tts_button = ft.IconButton(
                icon="volume_up",
                icon_size=17,
                icon_color=self.muted_color,
                tooltip="Озвучить оригинал",
                on_click=lambda e, selected=index: self.play_tts(self.sentences[selected]),
            )
            ai_button = ft.IconButton(
                icon="translate",
                icon_size=17,
                icon_color=self.muted_color,
                tooltip="Предложить перевод",
                on_click=lambda e, selected=index: self.start_segment_translation(selected),
            )
            self.ai_buttons[index] = ai_button

            field = ft.TextField(
                value=self.translations[index],
                multiline=True,
                min_lines=2,
                max_lines=8,
                expand=True,
                border_color=self.border_color,
                focused_border_color=self.accent,
                bgcolor=self.editor_bg,
                text_style=ft.TextStyle(color=self.text_color, size=font_size),
                hint_text="Введите или исправьте перевод…",
                on_change=lambda e, selected=index: self.on_segment_change(selected, e.control.value),
                on_focus=lambda e, selected=index: self.on_segment_focus(selected),
            )
            self.text_fields[index] = field
            confirm_button = ft.IconButton(
                icon="check_circle",
                icon_color=STATUS_COLORS[STATUS_CONFIRMED],
                tooltip="Подтвердить и перейти дальше",
                on_click=lambda e, selected=index: self.confirm_segment(selected),
            )
            segment_header = ft.Row(
                [
                    ft.Row(
                        [
                            status_indicator,
                            ft.Text(f"Сегмент {index + 1}", size=11, weight=ft.FontWeight.BOLD, color=self.text_color),
                            qa_label,
                        ],
                        spacing=6,
                    ),
                    ft.Row([bookmark_button, tts_button, ai_button], spacing=0),
                ],
                alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
            )
            segment_box = ft.Container(
                key=f"segment-{index}",
                content=ft.Column(
                    [
                        segment_header,
                        ft.Text(source, size=max(11, font_size - 2), color=self.muted_color, italic=True, selectable=True),
                        ft.Row([field, confirm_button], vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ],
                    spacing=6,
                ),
                bgcolor=self.editor_bg,
                padding=12,
                border_radius=10,
                border=ft.border.all(1, self.border_color),
            )
            self.workspace_list.controls.append(segment_box)
            self.segment_views[index] = segment_box

        for paragraph_index in sorted(self.rendered_paragraphs):
            preview_text = ft.Text("", size=max(13, font_size), color=self.text_color, selectable=True)
            preview_box = ft.Container(
                key=f"preview-{paragraph_index}",
                content=preview_text,
                padding=ft.padding.symmetric(vertical=9, horizontal=10),
                border_radius=8,
            )
            self.preview_text_controls[paragraph_index] = preview_text
            self.preview_boxes[paragraph_index] = preview_box
            self.preview_list.controls.append(preview_box)
        self.update_all_previews(update=False)
        self.sync_mobile_editor(update=False)
        self.apply_segment_filter(update=False)

    def apply_status_visual(self, index: int) -> None:
        if not 0 <= index < len(self.status_indicators):
            return
        status = self.statuses[index]
        indicator = self.status_indicators[index]
        if indicator is not None:
            indicator.bgcolor = STATUS_COLORS[status]
            indicator.tooltip = STATUS_TITLES[status]
        if index == self.current_index:
            self.mobile_status_dot.bgcolor = STATUS_COLORS[status]
            self.mobile_status_text.value = STATUS_TITLES[status] + " · свайп по оригиналу — навигация"

    def update_qa_for_segment(self, index: int) -> list[str]:
        if not 0 <= index < len(self.sentences):
            return []
        while len(self.qa_issues) < len(self.sentences):
            self.qa_issues.append([])
        old_problem = bool(self.qa_issues[index])
        issues = qa_issues_for_segment(
            self.sentences[index],
            self.translations[index],
            self.config.get("target_lang", "ru"),
            self.glossary_entries,
            self.character_entries,
            self.honorific_rules,
        )
        dictionary = {word.casefold() for word in self.custom_dictionary}
        for match in self.deep_qa_cache.get(index, []):
            word = str(match.get("word", "")).strip()
            if word and word.casefold() in dictionary:
                continue
            suggestions = ", ".join(match.get("suggestions", [])[:3])
            detail = f"; варианты: {suggestions}" if suggestions else ""
            issues.append(f"Орфография: {match.get('message', 'проверьте написание')}{detail}")
        self.qa_issues[index] = issues
        self.qa_problem_count_cache += int(bool(issues)) - int(old_problem)
        label = self.qa_labels[index] if index < len(self.qa_labels) else None
        if label is not None:
            label.value = f"⚠ {len(issues)}" if issues else ""
            label.tooltip = " · ".join(issues)
            label.color = (
                STATUS_COLORS[STATUS_EMPTY]
                if any(qa_issue_severity(issue) == "error" for issue in issues)
                else STATUS_COLORS[STATUS_DRAFT]
            )
        if index == self.current_index:
            self.mobile_qa_text.value = "⚠ " + " · ".join(issues) if issues else "✓ Локальных замечаний нет"
            self.mobile_qa_text.color = (
                STATUS_COLORS[STATUS_EMPTY]
                if any(qa_issue_severity(issue) == "error" for issue in issues)
                else STATUS_COLORS[STATUS_DRAFT] if issues else STATUS_COLORS[STATUS_CONFIRMED]
            )
        return issues

    def current_secondary_text(self, index: int) -> str:
        if not 0 <= index < len(self.sentences):
            return ""
        chunks: list[str] = []
        for source in self.secondary_sources:
            source_id = str(source.get("source_id", ""))
            aligned = sorted(
                (
                    item for item in source.get("alignments", [])
                    if int(item.get("primary", -1)) == index
                ),
                key=lambda item: int(item.get("order", 0)),
            )
            segment_map = {
                int(item.get("segment_index", -1)): str(item.get("source_text", ""))
                for item in source.get("segments", [])
            }
            values = [segment_map.get(int(item.get("secondary", -1)), "") for item in aligned]
            text = " ".join(value.strip() for value in values if value.strip())
            if text:
                chunks.append(f"{source.get('name', source_id)}: {text}")
        return "\n".join(chunks)

    def rebuild_variant_controls(self, *, update: bool = True) -> None:
        available = bool(self.sentences)
        active = self.active_variant_slots[self.current_index] if available and self.active_variant_slots else "literary"
        bundle = self.translation_variants[self.current_index] if available and self.translation_variants else {}
        for mapping in (getattr(self, "desktop_variant_buttons", {}), getattr(self, "mobile_variant_buttons", {})):
            for slot, button in mapping.items():
                has_text = bool(str(bundle.get(slot, {}).get("text", "")).strip())
                button.text = ("● " if slot == active else "") + TRANSLATION_VARIANT_LABELS[slot] + ("" if has_text else " · пусто")
                button.bgcolor = self.accent if slot == active else self.control_bg
                button.color = self.button_text if slot == active else self.text_color
                button.disabled = not available
        if update:
            self.page.update()

    def rebuild_inline_context(self, *, update: bool = True) -> None:
        if not self.sentences:
            return
        glossary, characters = self.current_reference_matches()
        matches = [*glossary, *characters]
        for row in (self.desktop_glossary_chips, self.mobile_glossary_chips):
            row.controls.clear()
            for entry in matches[:10]:
                target = str(entry.get("target", ""))
                if not target:
                    continue
                present = _term_present(self.translations[self.current_index], target)
                row.controls.append(
                    ft.TextButton(
                        text=("✓ " if present else "+ ") + target,
                        tooltip=f"{entry.get('source', '')} → {target}" + (f" · {entry.get('note')}" if entry.get("note") else ""),
                        on_click=lambda e, selected=dict(entry): self.insert_reference_entry(selected),
                    )
                )
            _, current_notes = parse_tl_notes(self.translations[self.current_index])
            for note_index, note in enumerate(current_notes):
                row.controls.append(
                    ft.TextButton(
                        text=f"📝 TL {note_index + 1}",
                        tooltip=str(note.get("text", "")),
                        on_click=lambda e, selected=note_index: self.open_existing_tl_note_dialog(selected),
                    )
                )
            row.visible = bool(row.controls)
        secondary = self.current_secondary_text(self.current_index)
        self.desktop_dual_raw_text.value = secondary
        self.desktop_dual_raw_card.visible = bool(secondary)
        self.mobile_dual_raw_text.value = secondary
        self.mobile_dual_raw_card.visible = bool(secondary)
        self.rebuild_variant_controls(update=False)
        if update:
            self.page.update()

    def insert_reference_entry(self, entry: dict[str, Any]) -> None:
        target = str(entry.get("target", "")).strip()
        forms = list(
            dict.fromkeys(
                value for value in [target, *[str(item).strip() for item in (entry.get("target_forms") or [])]]
                if value
            )
        )
        if len(forms) <= 1:
            if target:
                self.insert_into_active_editor(target, smart_spacing=True)
            return
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Выберите форму имени"),
            content=ft.Column(
                [
                    ft.TextButton(
                        text=value,
                        on_click=lambda e, selected=value: (
                            self._close(dialog),
                            self.insert_into_active_editor(selected, smart_spacing=True),
                        ),
                    )
                    for value in forms[:12]
                ],
                tight=True,
                scroll=ft.ScrollMode.AUTO,
            ),
        )
        dialog.actions = [ft.TextButton(text="Отмена", on_click=lambda e: self._close(dialog))]
        self._open(dialog)

    def insert_into_active_editor(self, value: str, *, smart_spacing: bool = False) -> None:
        if not self.sentences:
            return
        index = self.current_index
        mobile = self._page_width() < 900
        field = self.mobile_translation_field if mobile else (
            self.text_fields[index] if index < len(self.text_fields) else None
        )
        current = self.translations[index]
        start = end = len(current)
        selection = getattr(field, "selection", None) if field is not None else None
        if selection is not None:
            raw_start = getattr(selection, "start", getattr(selection, "base_offset", start))
            raw_end = getattr(selection, "end", getattr(selection, "extent_offset", raw_start))
            try:
                start, end = sorted((max(0, int(raw_start)), max(0, int(raw_end))))
                start = min(start, len(current))
                end = min(end, len(current))
            except (TypeError, ValueError):
                start = end = len(current)
        elif field is not None and current and not self.cursor_fallback_notified:
            self.cursor_fallback_notified = True
            self.show_toast("Эта сборка Flet не передаёт позицию курсора — символ вставлен в конец. Подсказка больше не появится.")
        inserted = value
        if smart_spacing and start == end:
            left_space = "" if start == 0 or current[start - 1].isspace() else " "
            right_space = "" if end >= len(current) or current[end].isspace() or current[end] in ",.!?:;»”" else " "
            inserted = left_space + value + right_space
        new_value = current[:start] + inserted + current[end:]
        self.on_segment_change(index, new_value, sync_mobile=not mobile)
        if field is not None:
            field.value = new_value
            try:
                field.focus()
            except (AttributeError, RuntimeError, AssertionError):
                pass

    def sync_mobile_editor(self, *, update: bool = True) -> None:
        self.mobile_field_syncing = True
        try:
            if not self.sentences:
                self.mobile_segment_label.value = "Сегмент —"
                self.mobile_status_dot.bgcolor = STATUS_COLORS[STATUS_EMPTY]
                self.mobile_status_text.value = "Откройте файл"
                self.mobile_source_text.value = "Откройте файл новеллы на вкладке «Оригинал»."
                self.mobile_translation_field.value = ""
                self.mobile_translation_field.disabled = True
                self.mobile_bookmark_button.icon = "bookmark_border"
                self.mobile_qa_text.value = ""
                return
            index = max(0, min(self.current_index, len(self.sentences) - 1))
            self.current_index = index
            status = self.statuses[index]
            self.mobile_segment_label.value = f"Сегмент {index + 1} из {len(self.sentences)}"
            self.mobile_status_dot.bgcolor = STATUS_COLORS[status]
            self.mobile_status_text.value = STATUS_TITLES[status] + " · свайп по оригиналу — навигация"
            self.mobile_source_text.value = self.sentences[index]
            self.mobile_translation_field.value = self.translations[index]
            self.mobile_translation_field.disabled = False
            self.mobile_bookmark_button.icon = "bookmark" if self.bookmarks[index] else "bookmark_border"
            self.mobile_bookmark_button.icon_color = self.accent if self.bookmarks[index] else self.muted_color
            self.mobile_ai_button.disabled = self.batch_running or index in self.busy_segments
            self.mobile_ai_button.icon = "hourglass_top" if index in self.busy_segments else "translate"
            self.rebuild_inline_context(update=False)
            self.update_qa_for_segment(index)
        finally:
            self.mobile_field_syncing = False
            if update:
                self.page.update()

    def on_mobile_translation_change(self, e) -> None:
        if self.mobile_field_syncing or not self.sentences:
            return
        self.on_segment_change(self.current_index, e.control.value, sync_mobile=False)

    def confirm_current(self, e=None) -> None:
        self.confirm_segment(self.current_index)

    def translate_current(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        if getattr(self.ai_sheet, "open", False):
            self._close(self.ai_sheet)
        self.start_segment_translation(self.current_index)

    def play_current_tts(self, e=None) -> None:
        self._close(self.segment_tools_sheet)
        if self.sentences:
            self.play_tts(self.sentences[self.current_index])

    def _preview_text(self, paragraph_index: int) -> str:
        parts: list[str] = []
        if not 0 <= paragraph_index < len(self.paragraph_segments):
            return ""
        for index in self.paragraph_segments[paragraph_index]:
            translation = self.translations[index].strip()
            parts.append(translation if translation else f"[{self.sentences[index]}]")
        return " ".join(parts)

    def _chapter_for_segment(self, segment_index: int) -> int:
        for chapter_index, chapter in enumerate(self.chapters):
            if int(chapter.get("start", 0)) <= segment_index <= int(chapter.get("end", -1)):
                return chapter_index
        return 0

    def _reader_paragraph_card(self, paragraph_index: int) -> ft.Container:
        segment_indices = self.paragraph_segments[paragraph_index] if 0 <= paragraph_index < len(self.paragraph_segments) else []
        first_segment = segment_indices[0] if segment_indices else 0
        all_confirmed = bool(segment_indices) and all(
            index < len(self.statuses) and self.statuses[index] == STATUS_CONFIRMED
            for index in segment_indices
        )
        has_empty = any(index >= len(self.translations) or not self.translations[index].strip() for index in segment_indices)
        marker_color = (
            STATUS_COLORS[STATUS_CONFIRMED]
            if all_confirmed
            else STATUS_COLORS[STATUS_EMPTY]
            if has_empty
            else STATUS_COLORS[STATUS_DRAFT]
        )
        return ft.Container(
            content=ft.Row(
                [
                    ft.Container(width=4, bgcolor=marker_color, border_radius=3),
                    ft.Text(
                        self._preview_text(paragraph_index),
                        color=self.text_color,
                        size=max(13, int(self.config.get("font_size", 14))),
                        selectable=True,
                        expand=True,
                    ),
                ],
                spacing=10,
                vertical_alignment=ft.CrossAxisAlignment.STRETCH,
            ),
            padding=ft.padding.symmetric(horizontal=10, vertical=12),
            bgcolor=self.editor_bg,
            border=ft.border.all(1, self.border_color),
            border_radius=10,
            on_click=lambda e, selected=first_segment: self.jump_from_reader(selected),
            tooltip=f"Перейти к сегменту {first_segment + 1}",
        )

    def refresh_reader_mode(self, *, follow_current: bool = False, update: bool = True) -> None:
        if not hasattr(self, "reader_list"):
            return
        self.reader_list.controls.clear()
        self.reader_sheet_list.controls.clear()
        if not self.sentences or not self.chapters:
            empty_message = ft.Text("Откройте книгу, чтобы начать вычитку.", color=self.muted_color)
            self.reader_list.controls.append(empty_message)
            self.reader_sheet_list.controls.append(ft.Text("Откройте книгу, чтобы начать вычитку.", color=self.muted_color))
            return
        if follow_current:
            self.reader_chapter_index = self._chapter_for_segment(self.current_index)
        self.reader_chapter_index = max(0, min(self.reader_chapter_index, len(self.chapters) - 1))
        chapter = self.chapters[self.reader_chapter_index]
        start = max(0, int(chapter.get("start", 0)))
        end = min(len(self.sentences) - 1, int(chapter.get("end", start)))
        stats = chapter_progress_statistics(start, end, self.translations, self.statuses, self.bookmarks, self.qa_issues)
        title = str(chapter.get("title", f"Глава {self.reader_chapter_index + 1}"))
        summary = (
            f"{self.reader_chapter_index + 1}/{len(self.chapters)} · "
            f"{round(float(stats['progress']) * 100)}% подтверждено · пусто {stats['empty']} · QA {stats['qa']}"
        )
        self.reader_title_text.value = title
        self.reader_sheet_title.value = title
        self.reader_summary_text.value = summary
        self.reader_sheet_summary.value = summary
        paragraph_indices: list[int] = []
        for segment_index in range(start, end + 1):
            paragraph_index = self.sentence_to_paragraph[segment_index]
            if not paragraph_indices or paragraph_indices[-1] != paragraph_index:
                paragraph_indices.append(paragraph_index)
        page_count = max(1, (len(paragraph_indices) + READER_PAGE_SIZE - 1) // READER_PAGE_SIZE)
        if follow_current and paragraph_indices:
            current_paragraph = self.sentence_to_paragraph[self.current_index]
            try:
                self.reader_page_index = paragraph_indices.index(current_paragraph) // READER_PAGE_SIZE
            except ValueError:
                self.reader_page_index = 0
        self.reader_page_index = max(0, min(self.reader_page_index, page_count - 1))
        page_start = self.reader_page_index * READER_PAGE_SIZE
        visible_paragraphs = paragraph_indices[page_start:page_start + READER_PAGE_SIZE]
        page_label = f"Фрагмент {self.reader_page_index + 1} из {page_count}"
        self.reader_page_text.value = page_label
        self.reader_sheet_page_text.value = page_label
        for paragraph_index in visible_paragraphs:
            self.reader_list.controls.append(self._reader_paragraph_card(paragraph_index))
            self.reader_sheet_list.controls.append(self._reader_paragraph_card(paragraph_index))
        if update:
            self.page.update()

    def move_reader_chapter(self, delta: int) -> None:
        if not self.chapters:
            return
        target = max(0, min(self.reader_chapter_index + int(delta), len(self.chapters) - 1))
        if target == self.reader_chapter_index:
            self.show_toast("Это крайняя глава.")
            return
        self.reader_chapter_index = target
        self.reader_page_index = 0
        self.refresh_reader_mode(update=True)

    def move_reader_page(self, delta: int) -> None:
        if not self.sentences or not self.chapters:
            return
        chapter = self.chapters[self.reader_chapter_index]
        start = max(0, int(chapter.get("start", 0)))
        end = min(len(self.sentences) - 1, int(chapter.get("end", start)))
        paragraph_count = len({self.sentence_to_paragraph[index] for index in range(start, end + 1)})
        page_count = max(1, (paragraph_count + READER_PAGE_SIZE - 1) // READER_PAGE_SIZE)
        target = max(0, min(self.reader_page_index + int(delta), page_count - 1))
        if target == self.reader_page_index:
            self.show_toast("Это крайний фрагмент главы.")
            return
        self.reader_page_index = target
        self.refresh_reader_mode(update=True)

    def open_reader_mode(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        self.refresh_reader_mode(follow_current=True, update=False)
        if self._page_width() < 900:
            self.switch_mobile_tab(2)
        else:
            self.fit_bottom_sheet(self.reader_sheet, 760, 420)
            self._open(self.reader_sheet)

    def jump_from_reader(self, segment_index: int) -> None:
        if getattr(self.reader_sheet, "open", False):
            self._close(self.reader_sheet)
        if self._page_width() < 900:
            self.switch_mobile_tab(1, update=False)
        self.focus_segment(segment_index)

    def update_preview_paragraph(self, paragraph_index: int, *, update: bool = True) -> None:
        control = self.preview_text_controls[paragraph_index] if 0 <= paragraph_index < len(self.preview_text_controls) else None
        if control is not None:
            control.value = self._preview_text(paragraph_index)
        reader_visible = (
            hasattr(self, "mobile_navbar")
            and self._page_width() < 900
            and self.mobile_navbar.selected_index == 2
        ) or (hasattr(self, "reader_sheet") and getattr(self.reader_sheet, "open", False))
        if reader_visible:
            self.refresh_reader_mode(update=False)
        if update:
            self.page.update()

    def update_all_previews(self, *, update: bool = True) -> None:
        for paragraph_index, control in enumerate(self.preview_text_controls):
            if control is not None:
                control.value = self._preview_text(paragraph_index)
        if update:
            self.page.update()

    def update_ui(self, *, update: bool = True) -> None:
        if not self.file_loaded or not self.sentences:
            self.file_info_text.value = "Файл не загружен"
            self.progress_bar.visible = False
            self.editor_position_text.value = "Сегмент —"
            self.export_note.value = "Сначала откройте файл новеллы."
            self.fidelity_card.visible = False
        else:
            translated = self.translated_count_cache
            confirmed = self.confirmed_count_cache
            qa_count = self.qa_problem_count_cache
            total = len(self.sentences)
            document_note = ""
            source_kind = self.source_document_metadata.get("kind")
            if source_kind in {"epub", "docx"}:
                source_label = str(source_kind).upper()
                document_note = (
                    f" · оформление {source_label} сохранится"
                    if self.source_document_metadata.get("preservable")
                    else f" · только чистый {source_label}"
                )
            self.file_info_text.value = (
                f"{self.project_file_name} · заполнено {translated}/{total} · "
                f"подтверждено {confirmed}/{total}{document_note}"
            )
            self.progress_bar.visible = True
            self.progress_bar.value = confirmed / total
            self.progress_bar.tooltip = f"Подтверждено {confirmed} из {total}; заполнено {translated}"
            mode = f" · окно {len(self.rendered_indices)}" if self.large_document_mode else ""
            self.editor_position_text.value = f"Сегмент {self.current_index + 1} из {total}{mode}"
            self.fidelity_card.visible = source_kind in {"epub", "docx"}
            if self.fidelity_card.visible:
                if self.source_document_metadata.get("preservable"):
                    self.fidelity_title.value = "Оформление под защитой"
                    self.fidelity_title.color = self.text_color
                    if source_kind == "epub":
                        self.fidelity_details.value = (
                            f"Глав: {len(self.source_document_metadata.get('spine_files', []))} · "
                            f"иллюстраций: {self.source_document_metadata.get('image_count', 0)} · "
                            f"CSS: {self.source_document_metadata.get('style_count', 0)}"
                        )
                    else:
                        self.fidelity_details.value = (
                            f"Абзацев: {self.source_document_metadata.get('block_count', 0)} · "
                            f"иллюстраций: {self.source_document_metadata.get('image_count', 0)} · "
                            f"таблицы и стили сохраняются"
                        )
                else:
                    self.fidelity_title.value = "Нужен чистый EPUB"
                    self.fidelity_title.color = STATUS_COLORS[STATUS_DRAFT]
                    self.fidelity_details.value = "Исходная HTML-разметка нестандартна; содержимое доступно, но безопасная подмена оформления отключена."
            missing = total - translated
            quality_note = (
                f"Все сегменты заполнены. QA-замечаний: {qa_count}."
                if missing == 0
                else f"Пустых сегментов: {missing}. QA-замечаний: {qa_count}."
            )
            self.export_complex_policy.visible = self._export_kind() in {"epub_preserve", "docx_preserve"}
            if self._export_kind() in {"epub_preserve", "docx_preserve"}:
                if self.source_document_metadata.get("preservable"):
                    resource_note = (
                        f" Структура и {self.source_document_metadata.get('image_count', 0)} иллюстраций будут сохранены."
                    )
                else:
                    resource_note = " Бережный режим недоступен для этого источника; выберите чистый EPUB."
            else:
                resource_note = ""
            self.export_note.value = quality_note + resource_note
        if update:
            self.page.update()

    def highlight_current(self, *, update: bool = False) -> None:
        if not self.sentences:
            return
        active_paragraph = self.sentence_to_paragraph[self.current_index]
        if 0 <= self.highlighted_index < len(self.original_views):
            previous_view = self.original_views[self.highlighted_index]
            previous_segment = self.segment_views[self.highlighted_index]
            if previous_view is not None:
                previous_view.bgcolor = None
                previous_view.border = None
            if previous_segment is not None:
                previous_segment.border = ft.border.all(1, self.border_color)
        if 0 <= self.highlighted_paragraph < len(self.preview_boxes):
            previous_preview = self.preview_boxes[self.highlighted_paragraph]
            if previous_preview is not None:
                previous_preview.bgcolor = None
                previous_preview.border = None

        current_view = self.original_views[self.current_index]
        current_segment = self.segment_views[self.current_index]
        if current_view is not None:
            current_view.bgcolor = self.soft_accent
            current_view.border = ft.border.all(1, self.accent)
        if current_segment is not None:
            current_segment.border = ft.border.all(1, self.accent)
        current_preview = self.preview_boxes[active_paragraph]
        if current_preview is not None:
            current_preview.bgcolor = self.soft_accent
            current_preview.border = ft.border.all(1, self.accent)
        self.highlighted_index = self.current_index
        self.highlighted_paragraph = active_paragraph
        mode = f" · окно {len(self.rendered_indices)}" if self.large_document_mode else ""
        self.editor_position_text.value = f"Сегмент {self.current_index + 1} из {len(self.sentences)}{mode}"
        self.update_memory_hint()
        if hasattr(self, "reference_sheet") and getattr(self.reference_sheet, "open", False):
            self.refresh_reference_ui(update=False)
        self.sync_mobile_editor(update=False)
        if update:
            self.page.update()

    def on_segment_focus(self, index: int) -> None:
        if not 0 <= index < len(self.sentences):
            return
        self.current_index = index
        self.highlight_current(update=True)
        self.schedule_autosave()
        if self.config.get("auto_fetch") and not self.translations[index].strip():
            self.start_segment_translation(index, quiet=True)

    def focus_segment(self, index: int) -> None:
        if not self.sentences:
            return
        index = max(0, min(index, len(self.sentences) - 1))
        self.navigation_generation += 1
        request_id = self.navigation_generation
        try:
            self.page.run_task(self.focus_segment_safe, index, request_id)
        except Exception:
            # Безопасный синхронный fallback: меняем состояние, но не вызываем
            # scroll/focus для ещё не смонтированного контрола.
            self.current_index = index
            if self.large_document_mode and index not in self.rendered_indices:
                self.rebuild_workspace()
            self.highlight_current(update=True)
            self.schedule_autosave()

    async def focus_segment_safe(self, index: int, request_id: int | None = None) -> None:
        if not self.sentences:
            return
        index = max(0, min(index, len(self.sentences) - 1))
        if request_id is None:
            self.navigation_generation += 1
            request_id = self.navigation_generation
        if not self.segment_visible_for_filter(index):
            self.segment_filter = "all"
            self.apply_segment_filter(update=False)
        self.current_index = index
        if self.large_document_mode and index not in self.rendered_indices:
            self.rebuild_workspace()
            self.page.update()
            await asyncio.sleep(0)
            if request_id != self.navigation_generation:
                return
            field = self.text_fields[index] if index < len(self.text_fields) else None
            if self._page_width() >= 900 and field is None:
                await asyncio.sleep(0.016)
                if request_id != self.navigation_generation:
                    return
        try:
            if request_id != self.navigation_generation:
                return
            if self._page_width() < 900:
                if self.mobile_navbar.selected_index != 1:
                    self.switch_mobile_tab(1, update=False)
                self.sync_mobile_editor(update=False)
                self.mobile_translation_field.focus()
            else:
                self.workspace_list.scroll_to(key=f"segment-{index}", duration=250)
                field = self.text_fields[index] if index < len(self.text_fields) else None
                if field is not None:
                    field.focus()
        except (AttributeError, RuntimeError, AssertionError):
            pass
        if request_id != self.navigation_generation:
            return
        self.highlight_current(update=True)
        self.schedule_autosave()

    def move_segment(self, delta: int) -> None:
        if not self.file_loaded:
            self.show_toast("Сначала загрузите файл.")
            return
        target = self.current_index + delta
        while 0 <= target < len(self.sentences) and not self.segment_visible_for_filter(target):
            target += delta
        if target < 0:
            self.show_toast("Это первый доступный сегмент.")
        elif target >= len(self.sentences):
            self.show_toast("Это последний доступный сегмент.")
        else:
            self.focus_segment(target)

    def on_segment_change(self, index: int, value: str, *, sync_mobile: bool = True) -> None:
        if not 0 <= index < len(self.translations):
            return
        new_value = value or ""
        if self.translations[index] == new_value:
            return
        old_text = self.translations[index]
        old_status = self.statuses[index]
        self.push_history(
            f"Текст сегмента {index + 1}",
            coalesce_key=f"translation:{index}",
            segment_indices=[index],
        )
        self.translations[index] = new_value
        self.deep_qa_cache.pop(index, None)
        field = self.text_fields[index] if index < len(self.text_fields) else None
        if field is not None and field.value != self.translations[index]:
            field.value = self.translations[index]
        self.statuses[index] = STATUS_DRAFT if self.translations[index].strip() else STATUS_EMPTY
        self._mark_segment_changed(index, old_text=old_text, old_status=old_status)
        self.apply_status_visual(index)
        self.update_qa_for_segment(index)
        self.update_preview_paragraph(self.sentence_to_paragraph[index], update=False)
        self.update_ui(update=False)
        self.apply_segment_filter(update=False)
        if sync_mobile and index == self.current_index:
            self.sync_mobile_editor(update=False)
        self.schedule_autosave()
        self.page.update()

    def confirm_segment(self, index: int) -> None:
        if not 0 <= index < len(self.translations):
            return
        raw_value = self.translations[index]
        if index == self.current_index and self._page_width() < 900:
            raw_value = self.mobile_translation_field.value or ""
        elif index < len(self.text_fields) and self.text_fields[index] is not None:
            raw_value = self.text_fields[index].value or ""
        value = raw_value.strip()
        if not value:
            self.show_toast("Нельзя подтвердить пустой сегмент.", error=True)
            return
        old_text = self.translations[index]
        old_status = self.statuses[index]
        self.push_history(f"Подтверждение сегмента {index + 1}", segment_indices=[index])
        previous_status = self.statuses[index] if self.statuses[index] != STATUS_CONFIRMED else STATUS_DRAFT
        confirmation_snapshot = (self.project_generation, index, previous_status)
        self.last_confirmation = confirmation_snapshot
        self.translations[index] = raw_value
        if self.text_fields[index] is not None:
            self.text_fields[index].value = raw_value
        self.statuses[index] = STATUS_CONFIRMED
        self._mark_segment_changed(index, old_text=old_text, old_status=old_status)
        ai_draft = self.ai_drafts.pop(index, "")
        if ai_draft and _memory_key(ai_draft) != _memory_key(raw_value):
            self.edit_examples.append({"source": self.sentences[index], "draft": ai_draft, "final": raw_value.strip()})
            self.edit_examples = self.edit_examples[-100:]
        self.remember_confirmed_translation(index)
        self.apply_status_visual(index)
        self.update_qa_for_segment(index)
        self.update_preview_paragraph(self.sentence_to_paragraph[index], update=False)
        self.update_ui(update=False)
        self.apply_segment_filter(update=False)
        self.save_progress(update=False)
        next_index = index + 1
        while next_index < len(self.sentences) and not self.segment_visible_for_filter(next_index):
            next_index += 1
        if next_index < len(self.sentences):
            self.focus_segment(next_index)
        else:
            self.page.update()
        message = "Перевод завершён: последний сегмент подтверждён." if index + 1 == len(self.sentences) else f"Сегмент {index + 1} подтверждён."
        self.show_toast(
            message,
            action_text="ОТМЕНИТЬ",
            on_action=self.undo_history,
        )

    def undo_last_confirmation(self, e=None, snapshot: tuple[int, int, str] | None = None) -> None:
        snapshot = snapshot or self.last_confirmation
        if not snapshot:
            return
        generation, index, previous_status = snapshot
        if self.last_confirmation == snapshot:
            self.last_confirmation = None
        if generation != self.project_generation or not 0 <= index < len(self.sentences):
            self.show_toast("Этот шаг уже нельзя отменить.")
            return
        self.statuses[index] = previous_status if self.translations[index].strip() else STATUS_EMPTY
        self.current_index = index
        if self.large_document_mode and index not in self.rendered_indices:
            self.rebuild_workspace()
        self.apply_status_visual(index)
        self.update_qa_for_segment(index)
        self.update_ui(update=False)
        self.highlight_current(update=False)
        self.save_progress(update=False)
        self.page.update()
        self.show_toast("Подтверждение отменено, текст сохранён.")

    def jump_next_untranslated(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        order = list(range(self.current_index + 1, len(self.sentences))) + list(range(0, self.current_index + 1))
        for index in order:
            if not self.translations[index].strip():
                self.focus_segment(index)
                self.show_toast(f"Непереведённый сегмент {index + 1}.")
                return
        self.show_toast("Все сегменты заполнены.")

    def jump_next_bookmark(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        order = list(range(self.current_index + 1, len(self.sentences))) + list(range(0, self.current_index + 1))
        for index in order:
            if self.bookmarks[index]:
                self.focus_segment(index)
                self.show_toast(f"Закладка: сегмент {index + 1}.")
                return
        self.show_toast("В этом файле нет закладок.")

    def toggle_bookmark(self, index: int) -> None:
        if not 0 <= index < len(self.bookmarks):
            return
        self.push_history(f"Закладка сегмента {index + 1}", segment_indices=[index])
        self.bookmarks[index] = not self.bookmarks[index]
        self._mark_segment_changed(index, variant_changed=False)
        button = self.bookmark_buttons[index]
        if button is not None:
            button.icon = "bookmark" if self.bookmarks[index] else "bookmark_border"
            button.icon_color = self.accent if self.bookmarks[index] else self.muted_color
            button.tooltip = "Убрать закладку" if self.bookmarks[index] else "Добавить закладку"
        if index == self.current_index:
            self.sync_mobile_editor(update=False)
        self.apply_segment_filter(update=False)
        self.schedule_autosave()
        self.page.update()

    def search_in_text(self, query: str) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        normalised = (query or "").strip().casefold()
        if not normalised:
            self.show_toast("Введите слово или фразу.")
            return
        if normalised != self.last_search:
            self.last_search = normalised
            self.search_matches = [
                index
                for index, source in enumerate(self.sentences)
                if normalised in source.casefold() or normalised in self.translations[index].casefold()
            ]
            self.search_position = -1
        if not self.search_matches:
            self.show_toast(f"«{query}» не найдено.")
            return
        self.search_position = (self.search_position + 1) % len(self.search_matches)
        target = self.search_matches[self.search_position]
        self.focus_segment(target)
        self.show_toast(f"Совпадение {self.search_position + 1} из {len(self.search_matches)} · сегмент {target + 1}.")

    def memory_matches_for_current(self) -> list[tuple[float, dict[str, Any]]]:
        if not self.sentences:
            return []
        return find_translation_memory_matches(
            self.translation_memory,
            self.sentences[self.current_index],
            self.config.get("source_lang", "auto"),
            self.config.get("target_lang", "ru"),
        )

    def update_memory_hint(self) -> None:
        matches = self.memory_matches_for_current()
        self.memory_hint_text.value = f"TM {round(matches[0][0] * 100)}%" if matches else ""
        self.memory_hint_text.visible = bool(matches)

    def refresh_memory_sheet(self, *, update: bool = True) -> None:
        self.memory_results_column.controls.clear()
        matches = self.memory_matches_for_current()
        self.update_memory_hint()
        self.memory_summary_text.value = (
            f"Сегмент {self.current_index + 1} · найдено вариантов: {len(matches)} · всего в памяти: {len(self.translation_memory)}"
            if self.sentences
            else f"Всего в памяти: {len(self.translation_memory)}"
        )
        if not matches:
            self.memory_results_column.controls.append(
                ft.Text("Похожих подтверждённых переводов пока нет.", color=self.muted_color, size=12)
            )
        for score, entry in matches:
            target = str(entry.get("target", ""))
            self.memory_results_column.controls.append(
                ft.Container(
                    content=ft.Column(
                        [
                            ft.Row(
                                [
                                    ft.Text(f"Совпадение {round(score * 100)}%", color=self.accent, weight=ft.FontWeight.BOLD, size=11),
                                    ft.Text(f"использований: {entry.get('uses', 1)}", color=self.muted_color, size=10),
                                ],
                                alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                            ),
                            ft.Text(str(entry.get("source", "")), color=self.muted_color, size=11, selectable=True),
                            ft.Text(target, color=self.text_color, size=13, selectable=True),
                            self._button(
                                "Подставить в сегмент",
                                lambda e, value=target: self.apply_memory_match(value),
                                icon="north_west",
                                primary=score >= 0.999,
                            ),
                        ],
                        spacing=6,
                    ),
                    padding=10,
                    bgcolor=self.editor_bg,
                    border=ft.border.all(1, self.border_color),
                    border_radius=10,
                )
            )
        if update:
            self.page.update()

    def open_memory_sheet(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        if getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        self.fit_bottom_sheet(self.memory_sheet, 620)
        self.refresh_memory_sheet(update=False)
        self._open(self.memory_sheet)

    def apply_memory_match(self, value: str) -> None:
        self._close(self.memory_sheet)
        self.on_segment_change(self.current_index, value)
        self.focus_segment(self.current_index)
        self.show_toast("Вариант из памяти вставлен как черновик.")

    def remember_confirmed_translation(self, index: int) -> None:
        remember_translation_pair(
            self.translation_memory,
            self.sentences[index],
            self.translations[index],
            self.config.get("source_lang", "auto"),
            self.config.get("target_lang", "ru"),
        )
        try:
            save_translation_memory(self.translation_memory)
        except OSError as exc:
            self.show_toast(f"Перевод подтверждён, но память не сохранена: {exc}", error=True)

    def import_tmx(self, e=None) -> None:
        try:
            self.tmx_import_picker.pick_files(
                dialog_title="Импорт памяти переводов TMX",
                file_type=ft.FilePickerFileType.CUSTOM,
                allowed_extensions=["tmx"],
                allow_multiple=False,
            )
        except Exception as exc:
            self.show_toast(f"Не удалось открыть TMX: {exc}", error=True)

    def on_tmx_import_result(self, e) -> None:
        files = getattr(e, "files", None)
        if not files:
            return
        selected = files[0]
        try:
            path = getattr(selected, "path", None)
            raw = Path(path).read_bytes() if path else getattr(selected, "bytes", None)
            if not isinstance(raw, (bytes, bytearray)):
                raise ValueError("система не передала содержимое TMX")
            imported = read_tmx_entries(bytes(raw), self.config.get("target_lang", "ru"))
            before = len(self.translation_memory)
            for entry in imported:
                remember_translation_pair(
                    self.translation_memory,
                    entry["source"],
                    entry["target"],
                    entry.get("source_lang", "auto"),
                    entry.get("target_lang", self.config.get("target_lang", "ru")),
                )
            save_translation_memory(self.translation_memory)
            self.refresh_memory_sheet(update=False)
            self.page.update()
            self.show_toast(f"TMX импортирован: {len(imported)} пар · новых {max(0, len(self.translation_memory) - before)}.")
        except (OSError, ValueError, TypeError) as exc:
            self.show_toast(f"Не удалось импортировать TMX: {exc}", error=True)

    def export_tmx(self, e=None) -> None:
        if not self.translation_memory:
            self.show_toast("Память переводов пока пуста.")
            return
        data = make_tmx_bytes(
            self.translation_memory,
            self.config.get("source_lang", "en"),
            self.config.get("target_lang", "ru"),
        )
        name = f"literaflow-memory-{datetime.now().strftime('%Y%m%d')}.tmx"
        self.pending_tmx_export = (name, data)
        try:
            self.tmx_export_picker.save_file(
                dialog_title="Экспорт памяти переводов",
                file_name=name,
                file_type=ft.FilePickerFileType.CUSTOM,
                allowed_extensions=["tmx"],
            )
        except Exception as exc:
            self.pending_tmx_export = None
            self._save_export_fallback(name, data, reason=str(exc))

    def on_tmx_export_result(self, e) -> None:
        pending = self.pending_tmx_export
        self.pending_tmx_export = None
        if not pending or not getattr(e, "path", None):
            return
        name, data = pending
        try:
            path = Path(str(e.path))
            if path.suffix.lower() != ".tmx":
                path = path.with_suffix(".tmx")
            _atomic_write_bytes(path, data)
            self.show_toast(f"Память экспортирована: {path.name}")
        except OSError as exc:
            self._save_export_fallback(name, data, reason=str(exc))

    def confirm_clear_translation_memory(self, e=None) -> None:
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Очистить память переводов?"),
            content=ft.Text("Будут удалены все накопленные пары оригинал → перевод. Проекты и текущие переводы не изменятся."),
        )

        def confirm(_):
            self._close(dialog)
            self.translation_memory.clear()
            try:
                save_translation_memory(self.translation_memory)
                self.refresh_memory_sheet(update=False)
                self.page.update()
                self.show_toast("Память переводов очищена.")
            except OSError as exc:
                self.show_toast(f"Не удалось очистить память: {exc}", error=True)

        dialog.actions = [
            ft.TextButton(text="Очистить", on_click=confirm),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def current_reference_matches(self) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        if not self.sentences:
            return [], []
        secondary = self.current_secondary_text(self.current_index)
        source = self.sentences[self.current_index] + ("\n" + secondary if secondary else "")
        glossary = [
            entry for entry in self.glossary_entries
            if _term_present(source, str(entry.get("source", "")), case_sensitive=bool(entry.get("case_sensitive", False)))
        ]
        characters = [
            entry
            for entry in self.character_entries
            if any(
                _term_present(source, value)
                for value in [str(entry.get("source", "")), *[str(item) for item in entry.get("aliases", [])]]
                if value
            )
        ]
        return glossary, characters

    def refresh_reference_ui(self, *, update: bool = True) -> None:
        if not hasattr(self, "glossary_list_column"):
            return
        self.glossary_list_column.controls.clear()
        self.character_list_column.controls.clear()
        self.honorific_rules_column.controls.clear()
        for index, entry in enumerate(self.glossary_entries):
            note = f" · {entry['note']}" if entry.get("note") else ""
            self.glossary_list_column.controls.append(
                ft.Container(
                    content=ft.Row(
                        [
                            ft.Text(f"{entry['source']} → {entry['target']}{note}", expand=True, color=self.text_color, size=12),
                            ft.IconButton(icon="delete_outline", icon_color=self.muted_color, tooltip="Удалить термин", on_click=lambda e, selected=index: self.delete_glossary_entry(selected)),
                        ],
                        alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                    ),
                    padding=ft.padding.symmetric(horizontal=8, vertical=4),
                    bgcolor=self.editor_bg,
                    border_radius=8,
                    border=ft.border.all(1, self.border_color),
                )
            )
        for index, entry in enumerate(self.character_entries):
            aliases = f"псевдонимы: {', '.join(entry.get('aliases', []))}" if entry.get("aliases") else ""
            forms = f"формы: {', '.join(entry.get('target_forms', []))}" if entry.get("target_forms") else ""
            details = " · ".join(
                value
                for value in (
                    entry.get("role", ""),
                    aliases,
                    forms,
                    entry.get("formality", ""),
                    entry.get("voice", ""),
                    entry.get("relationships", ""),
                    entry.get("note", ""),
                )
                if value
            )
            suffix = f" · {details}" if details else ""
            self.character_list_column.controls.append(
                ft.Container(
                    content=ft.Row(
                        [
                            ft.Text(f"{entry['source']} → {entry['target']}{suffix}", expand=True, color=self.text_color, size=12),
                            ft.IconButton(icon="delete_outline", icon_color=self.muted_color, tooltip="Удалить персонажа", on_click=lambda e, selected=index: self.delete_character_entry(selected)),
                        ],
                        alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                    ),
                    padding=ft.padding.symmetric(horizontal=8, vertical=4),
                    bgcolor=self.editor_bg,
                    border_radius=8,
                    border=ft.border.all(1, self.border_color),
                )
            )
        glossary_matches, character_matches = self.current_reference_matches()
        matched = [f"{entry['source']} → {entry['target']}" for entry in [*glossary_matches, *character_matches]]
        self.reference_matches_text.value = (
            "В текущем сегменте: " + " · ".join(matched)
            if matched
            else "В текущем сегменте совпадений со справочником нет."
        )
        for index, rule in enumerate(self.honorific_rules):
            policy_titles = {
                "warn": "предупреждать",
                "keep": "сохранять",
                "transliterate": "транслитерировать",
                "replace": "заменять",
                "remove": "удалять с предпросмотром",
            }
            target = f" → {rule.get('target')}" if rule.get("target") else ""
            self.honorific_rules_column.controls.append(
                ft.Row(
                    [
                        ft.Text(
                            f"{rule.get('source', '')}{target} · {policy_titles.get(rule.get('policy'), rule.get('policy', 'warn'))}",
                            color=self.text_color,
                            size=12,
                            expand=True,
                        ),
                        ft.IconButton(
                            icon="delete_outline",
                            tooltip="Удалить правило",
                            on_click=lambda e, selected=index: self.delete_honorific_rule(selected),
                        ),
                    ]
                )
            )
        if self.secondary_sources:
            source = self.secondary_sources[0]
            self.dual_raw_status_text.value = (
                f"{source.get('name', 'Второй оригинал')} · сегментов {len(source.get('segments', []))} · "
                f"связей {len(source.get('alignments', []))}"
            )
            self.dual_raw_status_text.color = self.accent
        else:
            self.dual_raw_status_text.value = "Дополнительный оригинал не подключён."
            self.dual_raw_status_text.color = self.muted_color
        self.rebuild_inline_context(update=False)
        if update:
            self.page.update()

    def open_reference_sheet(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        if getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        self.fit_bottom_sheet(self.reference_sheet, 720)
        self.refresh_reference_ui(update=False)
        self._open(self.reference_sheet)

    def open_dual_raw_picker(self, e=None) -> None:
        if not self.file_loaded:
            self.show_toast("Сначала откройте основной оригинал.")
            return
        try:
            self.dual_raw_picker.pick_files(
                dialog_title="Выберите второй оригинал",
                file_type=ft.FilePickerFileType.CUSTOM,
                allowed_extensions=["txt", "md"],
                allow_multiple=False,
            )
        except Exception as exc:
            self.show_toast(f"Не удалось открыть Dual-RAW: {exc}", error=True)

    def on_dual_raw_result(self, e) -> None:
        files = getattr(e, "files", None)
        if not files:
            return
        selected = files[0]
        path = getattr(selected, "path", None)
        raw = getattr(selected, "bytes", None)
        name = str(getattr(selected, "name", "secondary.txt") or "secondary.txt")
        if path:
            self.page.run_task(self._load_dual_raw_path, str(path), name)
        elif isinstance(raw, (bytes, bytearray)):
            self.page.run_task(self._load_dual_raw_bytes, bytes(raw), name)
        else:
            self.show_toast("Система не передала содержимое второго оригинала.", error=True)

    async def _load_dual_raw_path(self, path: str, name: str) -> None:
        try:
            data = await asyncio.to_thread(Path(path).read_bytes)
            await self._load_dual_raw_bytes(data, name or Path(path).name)
        except Exception as exc:
            self.show_toast(f"Dual-RAW не загружен: {exc}", error=True)

    async def _load_dual_raw_bytes(self, data: bytes, name: str) -> None:
        try:
            extension = Path(name).suffix.lower()
            if extension not in {".txt", ".md"}:
                raise ValueError("в этой версии второй оригинал поддерживает TXT и MD")
            paragraphs = await asyncio.to_thread(plain_text_paragraphs, data)
            segments, mapping = await asyncio.to_thread(
                segment_paragraphs,
                paragraphs,
                self.config.get("segmentation_method", "advanced"),
            )
            if not segments:
                raise ValueError("во втором оригинале не найден текст")
            source_id = uuid.uuid4().hex
            alignments = proportional_segment_alignments(len(self.sentences), len(segments))
            source = {
                "source_id": source_id,
                "name": name,
                "language": "auto",
                "source_hash": hashlib.sha256(data).hexdigest(),
                "source_bytes": bytes(data),
                "metadata": {"paragraph_count": len(paragraphs), "kind": extension.lstrip(".")},
                "segments": [
                    {
                        "source_id": source_id,
                        "segment_index": index,
                        "paragraph_index": mapping[index],
                        "source_text": text,
                    }
                    for index, text in enumerate(segments)
                ],
                "alignments": [
                    {"primary": primary, "secondary": secondary, "order": order}
                    for primary, secondary, order in alignments
                ],
            }
            # Сначала надёжно записываем новый поток: при ошибке пользователь
            # не теряет уже настроенный дополнительный оригинал.
            await asyncio.to_thread(
                self.project_store.save_secondary_source,
                self.source_hash,
                source_id=source_id,
                name=name,
                language="auto",
                source_hash=source["source_hash"],
                source_bytes=data,
                segments=segments,
                mapping=mapping,
                metadata=source["metadata"],
            )
            await asyncio.to_thread(self.project_store.replace_segment_alignments, self.source_hash, source_id, alignments)
            previous_sources = list(self.secondary_sources)
            for existing in previous_sources:
                existing_id = str(existing.get("source_id", ""))
                if existing_id and existing_id != source_id:
                    await asyncio.to_thread(self.project_store.delete_secondary_source, self.source_hash, existing_id)
            self.secondary_sources = [source]
            self.dirty_project_extensions = True
            self.content_revision += 1
            self.refresh_reference_ui(update=False)
            self.rebuild_inline_context(update=False)
            self.page.update()
            self.show_toast(f"Dual-RAW подключён: {len(segments)} сегментов. Связи можно поправлять вручную.")
        except Exception as exc:
            self.show_toast(f"Dual-RAW не загружен: {exc}", error=True)

    def _save_current_dual_alignments(self) -> bool:
        if not self.secondary_sources:
            return False
        source = self.secondary_sources[0]
        rows = [
            (int(item.get("primary", 0)), int(item.get("secondary", 0)), int(item.get("order", 0)))
            for item in source.get("alignments", [])
        ]
        try:
            self.project_store.replace_segment_alignments(self.source_hash, str(source.get("source_id", "")), rows)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            self.show_toast(f"Не удалось сохранить связи Dual-RAW: {exc}", error=True)
            return False
        self.rebuild_inline_context(update=False)
        self.refresh_reference_ui(update=False)
        self.page.update()
        return True

    def shift_dual_raw_alignment(self, delta: int) -> None:
        if not self.secondary_sources:
            self.show_toast("Сначала подключите второй оригинал.")
            return
        source = self.secondary_sources[0]
        maximum = len(source.get("segments", [])) - 1
        current = [item for item in source.get("alignments", []) if int(item.get("primary", -1)) == self.current_index]
        if not current:
            self.show_toast("У текущего сегмента нет связи Dual-RAW.")
            return
        previous = [int(item.get("secondary", 0)) for item in current]
        for item in current:
            item["secondary"] = max(0, min(maximum, int(item.get("secondary", 0)) + int(delta)))
        self.content_revision += 1
        if not self._save_current_dual_alignments():
            for item, old_value in zip(current, previous):
                item["secondary"] = old_value

    def add_next_dual_raw_alignment(self, e=None) -> None:
        if not self.secondary_sources:
            self.show_toast("Сначала подключите второй оригинал.")
            return
        source = self.secondary_sources[0]
        current = [item for item in source.get("alignments", []) if int(item.get("primary", -1)) == self.current_index]
        if not current:
            return
        candidate = max(int(item.get("secondary", 0)) for item in current) + 1
        if candidate >= len(source.get("segments", [])):
            self.show_toast("Следующего сегмента во втором оригинале нет.")
            return
        if any(int(item.get("secondary", -1)) == candidate for item in current):
            return
        added = {"primary": self.current_index, "secondary": candidate, "order": len(current)}
        source.setdefault("alignments", []).append(
            added
        )
        self.content_revision += 1
        if not self._save_current_dual_alignments():
            source["alignments"].remove(added)

    def unlink_current_dual_raw_alignment(self, e=None) -> None:
        if not self.secondary_sources:
            return
        source = self.secondary_sources[0]
        original = list(source.get("alignments", []))
        source["alignments"] = [
            item for item in original if int(item.get("primary", -1)) != self.current_index
        ]
        if len(source["alignments"]) == len(original):
            self.show_toast("У текущего сегмента уже нет связи Dual-RAW.")
            return
        self.content_revision += 1
        if not self._save_current_dual_alignments():
            source["alignments"] = original

    def link_nearest_dual_raw_alignment(self, e=None) -> None:
        if not self.secondary_sources:
            return
        source = self.secondary_sources[0]
        segments = list(source.get("segments", []))
        if not segments:
            return
        if any(
            int(item.get("primary", -1)) == self.current_index
            for item in source.get("alignments", [])
        ):
            self.show_toast("Текущий сегмент уже связан; используйте ±1 или «Добавить следующий».")
            return
        ratio = self.current_index / max(1, len(self.sentences) - 1)
        nearest = round(ratio * max(0, len(segments) - 1))
        added = {"primary": self.current_index, "secondary": nearest, "order": 0}
        source.setdefault("alignments", []).append(added)
        self.content_revision += 1
        if not self._save_current_dual_alignments():
            source["alignments"].remove(added)

    def remove_dual_raw(self, e=None) -> None:
        if not self.secondary_sources:
            return
        source = self.secondary_sources[0]
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Удалить второй оригинал?"),
            content=ft.Text("Основной текст и перевод не изменятся."),
        )

        def confirm(_):
            self._close(dialog)
            try:
                self.project_store.delete_secondary_source(self.source_hash, str(source.get("source_id", "")))
                self.secondary_sources.clear()
                self.refresh_reference_ui(update=False)
                self.rebuild_inline_context(update=False)
                self.page.update()
            except (OSError, sqlite3.Error) as exc:
                self.show_toast(f"Не удалось удалить Dual-RAW: {exc}", error=True)

        dialog.actions = [
            ft.TextButton(text="Удалить", on_click=confirm),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def add_honorific_rule(self, e=None) -> None:
        source = (self.honorific_source_input.value or "").strip()
        if not source:
            self.show_toast("Введите обращение или суффикс.")
            return
        self.push_history("Правило обращения", references=True)
        self.honorific_rules.append(
            {
                "rule_id": uuid.uuid4().hex,
                "source": source,
                "language": self.config.get("source_lang", "auto"),
                "category": "address",
                "policy": self.honorific_policy_input.value or "warn",
                "target": (self.honorific_target_input.value or "").strip(),
                "priority": len(self.honorific_rules),
                "conditions": {},
            }
        )
        self.dirty_project_extensions = True
        self.content_revision += 1
        self.honorific_source_input.value = ""
        self.honorific_target_input.value = ""
        self.refresh_reference_ui(update=False)
        self.save_progress(update=False)
        self.page.update()

    def delete_honorific_rule(self, index: int) -> None:
        if not 0 <= index < len(self.honorific_rules):
            return
        self.push_history("Удаление правила обращения", references=True)
        del self.honorific_rules[index]
        self.dirty_project_extensions = True
        self.content_revision += 1
        self.refresh_reference_ui(update=False)
        self.save_progress(update=False)
        self.page.update()

    def add_glossary_entry(self, e=None) -> None:
        source = (self.glossary_source_input.value or "").strip()
        target = (self.glossary_target_input.value or "").strip()
        if not source or not target:
            self.show_toast("Для термина заполните оригинал и перевод.", error=True)
            return
        self.push_history("Добавление термина", references=True)
        existing = next((entry for entry in self.glossary_entries if _memory_key(entry.get("source", "")) == _memory_key(source)), None)
        entry = {
            "source": source,
            "target": target,
            "note": (self.glossary_note_input.value or "").strip(),
            "case_sensitive": bool(self.glossary_case_switch.value),
        }
        if existing is None:
            self.glossary_entries.append(entry)
        else:
            existing.update(entry)
        self.dirty_references = True
        self.content_revision += 1
        self.glossary_source_input.value = ""
        self.glossary_target_input.value = ""
        self.glossary_note_input.value = ""
        self.refresh_qa()
        self.refresh_reference_ui(update=False)
        self.save_progress(update=False)
        self.page.update()

    def lookup_morphology_word(self, e=None) -> None:
        value = (self.morphology_lookup_input.value or "").strip()
        if not value:
            self.morphology_lookup_result.value = "Введите одно русское слово."
            self.page.update()
            return
        if not HAS_PYMORPHY3 or _morph_analyzer() is None:
            self.morphology_lookup_result.value = "Модуль офлайн-морфологии не установлен. Запустите установку зависимостей проекта."
            self.morphology_lookup_result.color = STATUS_COLORS[STATUS_EMPTY]
            self.page.update()
            return
        try:
            info = self.project_store.load_morphology_cache(value) or {}
        except (OSError, sqlite3.Error, TypeError, ValueError):
            info = {}
        if not info:
            info = russian_morphology_info(value)
            if info:
                try:
                    self.project_store.save_morphology_cache(value, info)
                except (OSError, sqlite3.Error, TypeError, ValueError):
                    pass
        if not info:
            self.morphology_lookup_result.value = "Не удалось разобрать слово."
            self.morphology_lookup_result.color = STATUS_COLORS[STATUS_DRAFT]
        else:
            status = "словарное слово" if info.get("known") else "в словаре не найдено"
            properties = ", ".join(info.get("properties", [])) or "часть речи не определена"
            forms = ", ".join(info.get("forms", [])) or "неизменяемое"
            self.morphology_lookup_result.value = (
                f"Лемма: {info.get('lemma') or '—'} · {properties} · {status}\n"
                f"Формы: {forms}"
            )
            self.morphology_lookup_result.color = self.text_color
        self.page.update()

    def fill_character_forms(self, e=None) -> None:
        target = (self.character_target_input.value or "").strip()
        if not target:
            self.show_toast("Сначала укажите имя в переводе.")
            return
        if not HAS_PYMORPHY3 or _morph_analyzer() is None:
            self.show_toast("Офлайн-морфология не установлена. Установите зависимости проекта.", error=True)
            return
        forms = russian_word_forms(target)
        if not forms:
            self.show_toast("Для этого имени словарь не нашёл изменяемых форм.")
            return
        self.character_forms_input.value = ", ".join(forms)
        self.page.update()
        self.show_toast(f"Подобрано форм: {len(forms)}. Их можно поправить перед сохранением.")

    def add_character_entry(self, e=None) -> None:
        source = (self.character_source_input.value or "").strip()
        target = (self.character_target_input.value or "").strip()
        if not source or not target:
            self.show_toast("Для персонажа заполните оба варианта имени.", error=True)
            return
        self.push_history("Добавление персонажа", references=True)
        existing = next((entry for entry in self.character_entries if _memory_key(entry.get("source", "")) == _memory_key(source)), None)
        entry = {
            "source": source,
            "target": target,
            "role": (self.character_role_input.value or "").strip(),
            "aliases": [value.strip() for value in (self.character_aliases_input.value or "").split(",") if value.strip()],
            "target_forms": [value.strip() for value in (self.character_forms_input.value or "").split(",") if value.strip()],
            "relationships": (self.character_relationships_input.value or "").strip(),
            "voice": (self.character_voice_input.value or "").strip(),
            "formality": self.character_formality_input.value or "",
            "note": (self.character_note_input.value or "").strip(),
        }
        if existing is None:
            self.character_entries.append(entry)
        else:
            existing.update(entry)
        self.dirty_references = True
        self.content_revision += 1
        for control in (
            self.character_source_input,
            self.character_target_input,
            self.character_role_input,
            self.character_aliases_input,
            self.character_forms_input,
            self.character_relationships_input,
            self.character_voice_input,
            self.character_note_input,
        ):
            control.value = ""
        self.character_formality_input.value = ""
        self.refresh_qa()
        self.refresh_reference_ui(update=False)
        self.save_progress(update=False)
        self.page.update()

    def delete_glossary_entry(self, index: int) -> None:
        if not 0 <= index < len(self.glossary_entries):
            return
        self.push_history("Удаление термина", references=True)
        del self.glossary_entries[index]
        self.dirty_references = True
        self.content_revision += 1
        self.refresh_qa()
        self.refresh_reference_ui(update=False)
        self.save_progress(update=False)
        self.page.update()

    def delete_character_entry(self, index: int) -> None:
        if not 0 <= index < len(self.character_entries):
            return
        self.push_history("Удаление персонажа", references=True)
        del self.character_entries[index]
        self.dirty_references = True
        self.content_revision += 1
        self.refresh_qa()
        self.refresh_reference_ui(update=False)
        self.save_progress(update=False)
        self.page.update()

    def on_segment_filter_change(self, e=None) -> None:
        self.segment_filter = self.qa_filter.value or "all"
        self.apply_segment_filter(update=True)

    def segment_visible_for_filter(self, index: int) -> bool:
        if self.segment_filter == "qa":
            return bool(index < len(self.qa_issues) and self.qa_issues[index])
        if self.segment_filter == "empty":
            return not self.translations[index].strip()
        if self.segment_filter == "unconfirmed":
            return self.statuses[index] != STATUS_CONFIRMED
        if self.segment_filter == "bookmarks":
            return self.bookmarks[index]
        return True

    def apply_segment_filter(self, *, update: bool = True) -> None:
        mounted = self.rendered_indices if self.large_document_mode else range(len(self.sentences))
        for index in mounted:
            visible = self.segment_visible_for_filter(index)
            original_view = self.original_views[index] if index < len(self.original_views) else None
            segment_view = self.segment_views[index] if index < len(self.segment_views) else None
            if original_view is not None:
                original_view.visible = visible
            if segment_view is not None:
                segment_view.visible = visible
        if hasattr(self, "qa_filter"):
            self.qa_filter.value = self.segment_filter
        if update:
            visible_count = sum(self.segment_visible_for_filter(index) for index in range(len(self.sentences)))
            self.page.update()
            self.show_toast(f"Фильтр: показано сегментов {visible_count} из {len(self.sentences)}.")

    def open_history_sheet(self, e=None) -> None:
        if not self.file_loaded:
            self.show_toast("Сначала загрузите файл.")
            return
        if getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        self.fit_bottom_sheet(self.history_sheet, 650)
        self.update_history_ui(update=False)
        self.refresh_backup_list(update=False)
        self._open(self.history_sheet)

    def refresh_backup_list(self, *, update: bool = True) -> None:
        if not hasattr(self, "backup_list_column"):
            return
        self.backup_list_column.controls.clear()
        files = self.backup_files()[:10] if self.file_loaded else []
        if not files:
            self.backup_list_column.controls.append(ft.Text("Резервных версий пока нет.", color=self.muted_color, size=12))
        for path in files:
            try:
                label = datetime.strptime(path.stem, "%Y%m%d-%H%M%S-%f").strftime("%d.%m.%Y · %H:%M:%S")
            except ValueError:
                label = path.stem
            self.backup_list_column.controls.append(
                ft.Row(
                    [
                        ft.Text(label, color=self.text_color, size=12, expand=True),
                        ft.TextButton(text="Восстановить", on_click=lambda e, selected=path: self.confirm_restore_backup(selected)),
                    ],
                    alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                )
            )
        if update:
            self.page.update()

    def confirm_restore_backup(self, path: Path) -> None:
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Восстановить резервную версию?"),
            content=ft.Text("Текущее состояние останется доступно через Undo."),
        )

        def confirm(_):
            self._close(dialog)
            self.restore_backup(path)

        dialog.actions = [
            ft.TextButton(text="Восстановить", on_click=confirm),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def restore_backup(self, path: Path) -> None:
        try:
            with path.open("r", encoding="utf-8") as stream:
                data = json.load(stream)
            if not isinstance(data, dict) or data.get("source_hash") != self.source_hash:
                raise ValueError("версия относится к другому исходному файлу")
            snapshot = {
                "sentences": data.get("sentences"),
                "sentence_to_paragraph": data.get("sentence_to_paragraph"),
                "translations": data.get("translations", []),
                "statuses": data.get("statuses", []),
                "bookmarks": data.get("bookmarks", []),
                "glossary": data.get("glossary", []),
                "characters": data.get("characters", []),
                "current_index": data.get("current_index", 0),
            }
            self.push_history("Восстановление резервной версии")
            self.restore_project_snapshot(snapshot)
            self._close(self.history_sheet)
            self.show_toast("Резервная версия восстановлена.")
        except (OSError, ValueError, TypeError) as exc:
            self.show_toast(f"Не удалось восстановить версию: {exc}", error=True)

    def open_segment_tools(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        self.segment_tools_title.value = f"Инструменты · сегмент {self.current_index + 1}"
        self._open(self.segment_tools_sheet)

    def open_tl_note_dialog(self, e=None) -> None:
        if not self.sentences:
            return
        self._close(self.segment_tools_sheet)
        note_input = ft.TextField(
            label="Текст примечания переводчика",
            multiline=True,
            min_lines=3,
            max_lines=7,
            width=360,
        )
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("TL-Note"),
            content=note_input,
        )

        def add_note(_):
            value = (note_input.value or "").strip()
            if not value:
                self.show_toast("Введите текст сноски.")
                return
            escaped = value.replace("]", "\\]")
            self._close(dialog)
            self.insert_into_active_editor(f"[note: {escaped}]", smart_spacing=True)

        dialog.actions = [
            ft.TextButton(text="Добавить", on_click=add_note),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def open_existing_tl_note_dialog(self, note_index: int) -> None:
        if not self.sentences:
            return
        _, notes = parse_tl_notes(self.translations[self.current_index])
        if not 0 <= note_index < len(notes):
            return
        note = notes[note_index]
        note_input = ft.TextField(
            label="Текст примечания переводчика",
            value=str(note.get("text", "")),
            multiline=True,
            min_lines=3,
            max_lines=7,
            width=360,
        )
        dialog = ft.AlertDialog(modal=True, title=ft.Text(f"TL-Note {note_index + 1}"), content=note_input)

        def replace_marker(value: str) -> None:
            raw = self.translations[self.current_index]
            start = int(note.get("source_start", len(raw)))
            end = int(note.get("source_end", start))
            escaped_value = value.replace("]", "\\]")
            marker = f"[note: {escaped_value}]" if value else ""
            self.on_segment_change(self.current_index, raw[:start] + marker + raw[end:])

        def save_note(_):
            value = (note_input.value or "").strip()
            if not value:
                self.show_toast("Введите текст сноски или нажмите «Удалить».")
                return
            self._close(dialog)
            replace_marker(value)

        def delete_note(_):
            self._close(dialog)
            replace_marker("")

        dialog.actions = [
            ft.TextButton(text="Сохранить", on_click=save_note),
            ft.TextButton(text="Удалить", on_click=delete_note),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def apply_current_typography(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        if getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        if getattr(self.qa_sheet, "open", False):
            self._close(self.qa_sheet)
        index = self.current_index
        current = self.translations[index]
        words = [word.strip() for word in str(self.config.get("short_word_nbsp_words", "")).split(",") if word.strip()]
        formatted = apply_russian_typography(
            current,
            use_short_nbsp=bool(self.config.get("short_word_nbsp", True)),
            short_words=words or DEFAULT_SHORT_NBSP_WORDS,
        )
        if not formatted:
            self.show_toast("В текущем сегменте пока нет перевода.")
            return
        if formatted == current:
            self.show_toast("Типографика уже в порядке.")
            return
        self.on_segment_change(index, formatted)
        self.show_toast(
            "Русская типографика применена.",
            action_text="ОТМЕНИТЬ",
            on_action=self.undo_history,
        )

    def restore_segment_text(self, index: int, value: str, generation: int | None = None) -> None:
        if generation is not None and generation != self.project_generation:
            self.show_toast("Этот шаг уже нельзя отменить.")
            return
        if not 0 <= index < len(self.sentences):
            return
        self.current_index = index
        self.on_segment_change(index, value)
        self.focus_segment(index)

    def open_split_dialog(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        if getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        index = self.current_index
        split_input = ft.TextField(
            value=self.sentences[index],
            multiline=True,
            min_lines=4,
            max_lines=10,
            border_color=self.border_color,
            focused_border_color=self.accent,
            text_style=ft.TextStyle(color=self.text_color, size=int(self.config.get("font_size", 14))),
        )
        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text(f"Разделить сегмент {index + 1}"),
            content=ft.Column(
                [
                    ft.Text("Поставьте перенос строки в каждом месте разделения. Перевод останется у первой части и станет черновиком."),
                    split_input,
                ],
                tight=True,
                spacing=10,
            ),
        )

        def confirm_split(_):
            parts = [_normalise_spaces(part) for part in (split_input.value or "").splitlines() if part.strip()]
            if len(parts) < 2:
                self.show_toast("Нужно добавить хотя бы один перенос строки.", error=True)
                return
            self._close(dialog)
            self.split_segment(index, parts)

        dialog.actions = [
            ft.TextButton(text="Разделить", on_click=confirm_split),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def split_segment(self, index: int, parts: list[str]) -> None:
        cleaned = [_normalise_spaces(part) for part in parts if part.strip()]
        if not 0 <= index < len(self.sentences) or len(cleaned) < 2:
            return
        paragraph_index = self.sentence_to_paragraph[index]
        translation = self.translations[index]
        bookmark = self.bookmarks[index]
        self._ensure_extended_state()
        original_variant = json.loads(json.dumps(self.translation_variants[index], ensure_ascii=False))
        original_slot = self.active_variant_slots[index]
        self.capture_structure_snapshot("Разделение сегмента")
        self.sentences[index:index + 1] = cleaned
        self.sentence_to_paragraph[index:index + 1] = [paragraph_index] * len(cleaned)
        self.translations[index:index + 1] = [translation, *([""] * (len(cleaned) - 1))]
        first_status = STATUS_DRAFT if translation.strip() else STATUS_EMPTY
        self.statuses[index:index + 1] = [first_status, *([STATUS_EMPTY] * (len(cleaned) - 1))]
        self.bookmarks[index:index + 1] = [bookmark, *([False] * (len(cleaned) - 1))]
        self.translation_variants[index:index + 1] = [
            original_variant,
            *[self._empty_variant_bundle() for _ in range(len(cleaned) - 1)],
        ]
        self.active_variant_slots[index:index + 1] = [original_slot, *(["literary"] * (len(cleaned) - 1))]
        shift = len(cleaned) - 1
        for note in self.segment_notes:
            note_index = int(note.get("segment_index", -1))
            if note_index > index:
                note["segment_index"] = note_index + shift
        for secondary in self.secondary_sources:
            for alignment in secondary.get("alignments", []):
                if int(alignment.get("primary", -1)) > index:
                    alignment["primary"] = int(alignment["primary"]) + shift
        self.current_index = index
        self.finish_segmentation_change()
        self.show_toast(
            f"Сегмент разделён на {len(cleaned)} части.",
            action_text="ОТМЕНИТЬ",
            on_action=self.undo_history,
        )

    def merge_current_with_next(self, e=None) -> None:
        if getattr(self.segment_tools_sheet, "open", False):
            self._close(self.segment_tools_sheet)
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        index = self.current_index
        if index + 1 >= len(self.sentences):
            self.show_toast("После текущего сегмента больше ничего нет.")
            return
        if self.sentence_to_paragraph[index] != self.sentence_to_paragraph[index + 1]:
            self.show_toast("Нельзя объединять сегменты из разных абзацев.", error=True)
            return
        source = " ".join(part.strip() for part in self.sentences[index:index + 2] if part.strip())
        translation = " ".join(part.strip() for part in self.translations[index:index + 2] if part.strip())
        self._ensure_extended_state()
        self.capture_structure_snapshot("Объединение сегментов")
        self.sentences[index:index + 2] = [source]
        del self.sentence_to_paragraph[index + 1]
        self.translations[index:index + 2] = [translation]
        self.statuses[index:index + 2] = [STATUS_DRAFT if translation else STATUS_EMPTY]
        self.bookmarks[index:index + 2] = [self.bookmarks[index] or self.bookmarks[index + 1]]
        merged_bundle = self.translation_variants[index]
        merged_slot = self.active_variant_slots[index]
        merged_bundle[merged_slot]["text"] = translation
        self.translation_variants[index:index + 2] = [merged_bundle]
        self.active_variant_slots[index:index + 2] = [merged_slot]
        for note in self.segment_notes:
            note_index = int(note.get("segment_index", -1))
            if note_index == index + 1:
                note["segment_index"] = index
            elif note_index > index + 1:
                note["segment_index"] = note_index - 1
        for secondary in self.secondary_sources:
            for alignment in secondary.get("alignments", []):
                primary = int(alignment.get("primary", -1))
                if primary == index + 1:
                    alignment["primary"] = index
                elif primary > index + 1:
                    alignment["primary"] = primary - 1
        self.current_index = index
        self.finish_segmentation_change()
        self.show_toast(
            "Сегменты объединены.",
            action_text="ОТМЕНИТЬ",
            on_action=self.undo_history,
        )

    def capture_structure_snapshot(self, reason: str = "Изменение структуры") -> None:
        self.create_backup(reason=f"before-{reason}")
        self.push_history(reason)
        self.last_structure_snapshot = self.project_snapshot()

    def undo_structure_change(self, e=None, snapshot: dict[str, Any] | None = None) -> None:
        snapshot = snapshot or self.last_structure_snapshot
        self.last_structure_snapshot = None
        if not snapshot:
            return
        self.sentences = list(snapshot["sentences"])
        self.sentence_to_paragraph = list(snapshot["sentence_to_paragraph"])
        self.translations = list(snapshot["translations"])
        self.statuses = list(snapshot["statuses"])
        self.bookmarks = list(snapshot["bookmarks"])
        self.current_index = int(snapshot["current_index"])
        self.finish_segmentation_change()
        self.show_toast("Структура сегментов восстановлена.")

    def finish_segmentation_change(self) -> None:
        self.project_generation += 1
        self.batch_cancel_requested = False
        self.busy_segments.clear()
        self.last_confirmation = None
        self.search_matches = []
        self.search_position = -1
        self.last_search = ""
        self.deep_qa_cache.clear()
        self.rebuild_paragraph_index()
        self.chapters = detect_chapters(self.original_paragraphs, self.sentence_to_paragraph)
        self.last_saved_segment_states = []
        self._ensure_extended_state()
        self._mark_all_dirty()
        self.rebuild_workspace()
        self.update_ui(update=False)
        self.highlight_current(update=False)
        self.save_progress(update=False)
        self.page.update()

    def start_deep_spellcheck(self, e=None) -> None:
        if not self.sentences or not self.translations[self.current_index].strip():
            self.show_toast("Сначала добавьте перевод текущего сегмента.")
            return
        if self.config.get("spellcheck_mode") == "off":
            self.show_toast("Выберите офлайн-морфологию или LanguageTool в настройках.")
            return
        index = self.current_index
        self.deep_qa_status.value = "Офлайн-морфология проверяет перевод…" if self.config.get("spellcheck_mode") == "local" else "LanguageTool проверяет текущий перевод…"
        self.deep_qa_status.color = self.muted_color
        self.page.update()
        self.page.run_task(self._deep_spellcheck_task, index, self.project_generation, self.translations[index])

    async def _deep_spellcheck_task(self, index: int, generation: int, text: str) -> None:
        try:
            if self.config.get("spellcheck_mode") == "local":
                matches = await asyncio.to_thread(
                    check_with_local_dictionary,
                    text,
                    self.config.get("target_lang", "ru"),
                    self.custom_dictionary,
                )
            else:
                matches = await asyncio.to_thread(
                    check_with_languagetool,
                    text,
                    self.config.get("target_lang", "ru"),
                    self.config.get("languagetool_url", DEFAULT_CONFIG["languagetool_url"]),
                )
            if generation != self.project_generation or index >= len(self.translations) or self.translations[index] != text:
                self.deep_qa_status.value = "Результат устарел: текст изменился во время проверки."
                return
            self.deep_qa_cache[index] = matches
            issues = self.update_qa_for_segment(index)
            self.deep_qa_status.value = f"Глубокая проверка завершена · найдено {len(matches)}."
            self.deep_qa_status.color = STATUS_COLORS[STATUS_CONFIRMED] if not matches else STATUS_COLORS[STATUS_DRAFT]
            self.qa_current_text.value = (
                "Текущий сегмент:\n• " + "\n• ".join(issues)
                if issues
                else "В текущем сегменте замечаний нет."
            )
        except Exception as exc:
            self.deep_qa_status.value = f"Проверка не выполнена: {exc}"
            self.deep_qa_status.color = STATUS_COLORS[STATUS_EMPTY]
        finally:
            self.page.update()

    def add_dictionary_word(self, e=None) -> None:
        word = (self.dictionary_word_input.value or "").strip()
        if not word:
            self.show_toast("Введите слово.")
            return
        if word.casefold() not in {value.casefold() for value in self.custom_dictionary}:
            self.push_history("Словарь проекта", references=True)
            self.custom_dictionary.append(word)
            self.custom_dictionary.sort(key=str.casefold)
            self.dirty_references = True
            self.content_revision += 1
            self.save_progress(update=False)
        self.dictionary_word_input.value = ""
        self.update_qa_for_segment(self.current_index)
        self.deep_qa_status.value = f"«{word}» добавлено в словарь проекта."
        self.page.update()

    def refresh_qa(self) -> list[int]:
        problem_indices: list[int] = []
        for index in range(len(self.sentences)):
            if self.update_qa_for_segment(index):
                problem_indices.append(index)
        self.update_ui(update=False)
        self.apply_segment_filter(update=False)
        return problem_indices

    def open_qa_sheet(self, e=None) -> None:
        if not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        problems = self.refresh_qa()
        current_issues = self.qa_issues[self.current_index]
        severity_counts = Counter(
            qa_issue_severity(issue)
            for issues in self.qa_issues
            for issue in issues
        )
        self.qa_summary_text.value = (
            f"Проблемные сегменты: {len(problems)}/{len(self.sentences)} · "
            f"ошибки {severity_counts['error']} · предупреждения {severity_counts['warning']} · стиль {severity_counts['style']}"
        )
        self.qa_current_text.value = (
            f"Текущий сегмент: {chr(10)}• " + f"{chr(10)}• ".join(
                f"[{qa_issue_severity_title(issue)}] {issue}" for issue in current_issues
            )
            if current_issues
            else "В текущем сегменте локальных замечаний нет."
        )
        self._open(self.qa_sheet)

    def jump_next_qa(self, e=None) -> None:
        if not self.sentences:
            return
        problems = self.refresh_qa()
        if not problems:
            self.show_toast("QA не нашёл замечаний.")
            return
        ordered = [index for index in problems if index > self.current_index] + [index for index in problems if index <= self.current_index]
        self._close(self.qa_sheet)
        self.focus_segment(ordered[0])
        self.show_toast(f"QA: сегмент {ordered[0] + 1} · " + " · ".join(self.qa_issues[ordered[0]]))

    def reset_progress(self, e=None) -> None:
        if not self.file_loaded:
            self.show_toast("Сначала загрузите файл.")
            return

        dialog = ft.AlertDialog(
            modal=True,
            title=ft.Text("Сбросить прогресс?"),
            content=ft.Text("Все переводы, статусы и закладки текущего файла будут удалены."),
        )

        def confirm(_):
            self._close(dialog)
            self._close(self.settings_sheet)
            self.create_backup(reason="before-reset")
            self.push_history("Сброс прогресса", segment_indices=range(len(self.sentences)))
            self.translations = [""] * len(self.sentences)
            self.statuses = [STATUS_EMPTY] * len(self.sentences)
            self.bookmarks = [False] * len(self.sentences)
            self.translation_variants = [self._empty_variant_bundle() for _ in self.sentences]
            self.active_variant_slots = ["literary"] * len(self.sentences)
            self.segment_notes = []
            self._mark_all_dirty()
            self.qa_issues = [[] for _ in self.sentences]
            self.qa_problem_count_cache = 0
            self.current_index = 0
            self.last_confirmation = None
            self.last_structure_snapshot = None
            self.ai_drafts.clear()
            self.deep_qa_cache.clear()
            for path in self._progress_candidates():
                try:
                    path.unlink(missing_ok=True)
                except OSError:
                    pass
            self.progress_path = ""
            if self.large_document_mode and 0 not in self.rendered_indices:
                self.rebuild_workspace()
            for index, field in enumerate(self.text_fields):
                if field is not None:
                    field.value = ""
                self.apply_status_visual(index)
                button = self.bookmark_buttons[index]
                if button is not None:
                    button.icon = "bookmark_border"
                    button.icon_color = self.muted_color
                    button.tooltip = "Добавить закладку"
                self.update_qa_for_segment(index)
            self.update_all_previews(update=False)
            self.update_ui(update=False)
            self.apply_segment_filter(update=False)
            self.highlight_current(update=False)
            self.sync_mobile_editor(update=False)
            self.save_progress(update=False)
            self.page.update()
            self.show_toast("Прогресс текущего файла сброшен.")

        dialog.actions = [
            ft.TextButton(text="Сбросить", on_click=confirm),
            ft.TextButton(text="Отмена", on_click=lambda event: self._close(dialog)),
        ]
        self._open(dialog)

    def play_tts(self, text: str) -> None:
        if not text:
            return
        if not HAS_FLET_AUDIO or ft_audio is None:
            self.show_toast("Для озвучки установите flet-audio и добавьте его в зависимости сборки.", error=True)
            return
        language = source_language_for_tts(self.config.get("source_lang", "auto"), text)
        spoken = text[:240]
        url = f"https://translate.google.com/translate_tts?ie=UTF-8&tl={quote(language)}&client=tw-ob&q={quote(spoken)}"
        try:
            if self.audio_player is not None and self.audio_player in self.page.overlay:
                self.page.overlay.remove(self.audio_player)
            self.audio_player = ft_audio.Audio(src=url, autoplay=True)
            self.page.overlay.append(self.audio_player)
            self.page.update()
            if len(text) > len(spoken):
                self.show_toast("Озвучены первые 240 символов сегмента.")
        except Exception as exc:
            self.show_toast(f"Не удалось запустить озвучку: {exc}", error=True)

    def translation_config_for_index(self, index: int) -> dict[str, Any]:
        config = dict(self.config)
        if not 0 <= index < len(self.sentences):
            return config
        source = self.sentences[index]
        terminology: list[str] = []
        for entry in self.glossary_entries:
            if _term_present(source, str(entry.get("source", "")), case_sensitive=bool(entry.get("case_sensitive", False))):
                terminology.append(f"{entry['source']} → {entry['target']}")
        for entry in self.character_entries:
            source_variants = [str(entry.get("source", "")), *[str(value) for value in entry.get("aliases", [])]]
            if any(_term_present(source, value) for value in source_variants if value):
                details = [str(entry.get("role", "")).strip(), str(entry.get("voice", "")).strip(), str(entry.get("formality", "")).strip()]
                extra = f" ({'; '.join(value for value in details if value)})" if any(details) else ""
                saved_forms = [str(value) for value in entry.get("target_forms", []) if value]
                target_forms = ", ".join(saved_forms or russian_word_forms(str(entry.get("target", ""))))
                forms = f"; формы: {target_forms}" if target_forms else ""
                terminology.append(f"{entry['source']} / {', '.join(entry.get('aliases', []))} → {entry['target']}{forms}{extra}")
        for rule in self.honorific_rules:
            marker = str(rule.get("source", "")).strip()
            if not marker or not _term_present(source, marker):
                continue
            policy = str(rule.get("policy", "warn"))
            target = str(rule.get("target", "")).strip()
            if policy in {"replace", "transliterate"} and target:
                terminology.append(f"обращение {marker} → {target}")
            elif policy == "keep":
                terminology.append(f"сохраняй обращение {marker}")
            elif policy == "remove":
                terminology.append(f"адаптируй тональность без буквального {marker}")
        config["terminology"] = terminology
        chapter = next(
            (item for item in self.chapters if int(item.get("start", 0)) <= index <= int(item.get("end", -1))),
            None,
        )
        config["scene_context"] = str(chapter.get("title", "")) if chapter else ""
        query = _memory_key(source)
        ranked_examples = sorted(
            (
                (SequenceMatcher(None, query, _memory_key(str(item.get("source", "")))).ratio(), item)
                for item in self.edit_examples
                if item.get("source") and item.get("final")
            ),
            key=lambda pair: pair[0],
            reverse=True,
        )
        config["edit_examples"] = [item for score, item in ranked_examples[:3] if score >= 0.35]
        runtime_profiles: list[dict[str, Any]] = []
        for profile in self.config.get("api_profiles", []):
            profile_id = str(profile.get("id", ""))
            runtime = dict(config)
            runtime.update(
                {
                    "_profile_id": profile_id,
                    "api_type": "custom",
                    "custom_api_name": profile.get("name", "API-профиль"),
                    "custom_api_url": profile.get("url", ""),
                    "custom_api_model": profile.get("model", ""),
                    "custom_api_headers": profile.get("headers", ""),
                    "custom_api_key_header": profile.get("key_header", "Authorization"),
                    "custom_api_key": self.session_api_keys.get(profile_id, "") or self.secret_store.get(profile_id),
                }
            )
            runtime_profiles.append(runtime)
        config["api_profiles_runtime"] = runtime_profiles
        active_id = str(self.config.get("active_api_profile", ""))
        active = next((item for item in runtime_profiles if item.get("_profile_id") == active_id), None)
        if active:
            config.update({key: value for key, value in active.items() if key.startswith("custom_api_")})
        return config

    def start_segment_translation(self, index: int, *, quiet: bool = False) -> None:
        if not 0 <= index < len(self.sentences):
            return
        if self.batch_running:
            if quiet:
                return
            # Явный запрос пользователя важнее фонового пакета. Текущий
            # пакетный token станет недействительным и его поздний ответ
            # будет отброшен до записи.
            self.batch_cancel_requested = True
            self.batch_job_id = ""
            self.show_toast("Автопилот останавливается; запускаю ручной запрос для текущего сегмента.")
        if index in self.busy_segments:
            return
        if not self.translations[index].strip():
            exact = find_translation_memory_matches(
                self.translation_memory,
                self.sentences[index],
                self.config.get("source_lang", "auto"),
                self.config.get("target_lang", "ru"),
                limit=1,
                threshold=0.995,
            )
            if exact and exact[0][0] >= 0.995:
                self.push_history(f"Черновик из памяти · сегмент {index + 1}", segment_indices=[index])
                result = str(exact[0][1].get("target", ""))
                self._store_ai_variant(index, result, "memory")
                if self.text_fields[index] is not None:
                    self.text_fields[index].value = result
                self.apply_status_visual(index)
                self.update_qa_for_segment(index)
                self.update_preview_paragraph(self.sentence_to_paragraph[index], update=False)
                self.sync_mobile_editor(update=False)
                self.save_progress(update=False)
                self.page.update()
                if not quiet:
                    self.show_toast("Точный перевод взят из локальной памяти — сетевой запрос не понадобился.")
                return
        generation = self.project_generation
        token = uuid.uuid4().hex
        self.segment_lock_tokens[index] = token
        self.busy_segments.add(index)
        self._set_segment_busy(index, True)
        self.page.update()
        try:
            self.page.run_task(self._translate_one_task, index, generation, self.translations[index], token, quiet)
        except Exception as exc:
            self.busy_segments.discard(index)
            self._set_segment_busy(index, False)
            if not quiet:
                self.show_toast(f"Не удалось запустить перевод: {exc}", error=True)

    def _set_segment_busy(self, index: int, busy: bool) -> None:
        if not 0 <= index < len(self.ai_buttons):
            return
        button = self.ai_buttons[index]
        if button is not None:
            button.disabled = busy
            button.icon = "hourglass_top" if busy else "translate"
        if index == self.current_index:
            self.mobile_ai_button.disabled = busy or self.batch_running
            self.mobile_ai_button.icon = "hourglass_top" if busy else "translate"

    async def _translate_one_task(
        self,
        index: int,
        generation: int,
        original_value: str,
        token: str,
        quiet: bool,
    ) -> None:
        if generation != self.project_generation or not 0 <= index < len(self.sentences):
            return
        try:
            use_context = bool(self.config.get("send_neighbor_context", True))
            previous = self.sentences[index - 1] if use_context and index else ""
            following = self.sentences[index + 1] if use_context and index + 1 < len(self.sentences) else ""
            result = await asyncio.to_thread(
                translate_segment_sync,
                self.sentences[index],
                self.translation_config_for_index(index),
                previous,
                following,
            )
            if generation != self.project_generation or self.segment_lock_tokens.get(index) != token:
                return
            if self.translations[index] != original_value:
                if not quiet:
                    self.show_toast("Черновик не вставлен: сегмент был изменён во время запроса.")
                return
            self.push_history(f"AI-черновик сегмента {index + 1}", segment_indices=[index])
            self._store_ai_variant(index, result.text, result.provider, result.raw_text)
            self.ai_drafts[index] = result.text
            if self.text_fields[index] is not None:
                self.text_fields[index].value = result.text
            self.apply_status_visual(index)
            self.update_qa_for_segment(index)
            self.update_preview_paragraph(self.sentence_to_paragraph[index], update=False)
            self.update_ui(update=False)
            self.apply_segment_filter(update=False)
            if index == self.current_index:
                self.sync_mobile_editor(update=False)
            self.save_progress(update=False)
            self.page.update()
        except Exception as exc:
            if not quiet:
                self.show_toast(f"Ошибка переводчика: {exc}", error=True)
        finally:
            if generation == self.project_generation:
                if self.segment_lock_tokens.get(index) == token:
                    self.segment_lock_tokens.pop(index, None)
                self.busy_segments.discard(index)
                self._set_segment_busy(index, False)
                self.page.update()

    def toggle_batch_translation(self, e=None) -> None:
        if not self.file_loaded:
            self.show_toast("Сначала загрузите файл.")
            return
        if self.batch_running:
            self.batch_cancel_requested = True
            self.batch_job_id = ""
            self.set_batch_progress("Останавливаю…")
            self.page.update()
            return
        self.batch_cancel_requested = False
        self.batch_job_id = uuid.uuid4().hex
        self.page.run_task(self._batch_translation_task, self.project_generation)

    def _set_batch_ui(self, running: bool) -> None:
        self.batch_button.text = "Остановить автопилот" if running else "Автопилот пустых сегментов"
        self.batch_button.bgcolor = self.danger_bg if running else self.control_bg
        self.batch_button.color = self.danger_text if running else self.text_color
        for index, button in enumerate(self.ai_buttons):
            if button is not None:
                button.disabled = running or index in self.busy_segments
        self.mobile_ai_button.disabled = running or self.current_index in self.busy_segments

    def set_batch_progress(self, value: str) -> None:
        self.batch_progress_text.value = value
        self.ai_sheet_progress_text.value = value

    async def _batch_translation_task(self, generation: int) -> None:
        if self.batch_running:
            return
        self.batch_running = True
        job_id = self.batch_job_id or uuid.uuid4().hex
        self.batch_job_id = job_id
        self._set_batch_ui(True)
        empty_indices = [index for index, value in enumerate(self.translations) if not value.strip()]
        if not empty_indices:
            self.batch_running = False
            self._set_batch_ui(False)
            self.set_batch_progress("")
            self.page.update()
            self.show_toast("Все сегменты уже заполнены.")
            return

        self.push_history("Автопилот главы", segment_indices=empty_indices)

        completed = 0
        errors = 0
        consecutive_errors = 0
        self.set_batch_progress(f"0/{len(empty_indices)}")
        self.page.update()
        try:
            for index in empty_indices:
                if self.batch_cancel_requested or generation != self.project_generation or self.batch_job_id != job_id:
                    break
                if self.translations[index].strip():
                    continue
                use_context = bool(self.config.get("send_neighbor_context", True))
                previous = self.sentences[index - 1] if use_context and index else ""
                following = self.sentences[index + 1] if use_context and index + 1 < len(self.sentences) else ""
                from_memory = False
                token = uuid.uuid4().hex
                self.segment_lock_tokens[index] = token
                try:
                    exact = find_translation_memory_matches(
                        self.translation_memory,
                        self.sentences[index],
                        self.config.get("source_lang", "auto"),
                        self.config.get("target_lang", "ru"),
                        limit=1,
                        threshold=0.995,
                    )
                    from_memory = bool(exact and exact[0][0] >= 0.995)
                    result = (
                        TranslationResult(
                            text=str(exact[0][1].get("target", "")),
                            provider="memory",
                            request_id=token,
                            latency_ms=0,
                            from_memory=True,
                        )
                        if from_memory
                        else await asyncio.to_thread(
                            translate_segment_sync,
                            self.sentences[index],
                            self.translation_config_for_index(index),
                            previous,
                            following,
                        )
                    )
                    if (
                        self.batch_cancel_requested
                        or generation != self.project_generation
                        or self.batch_job_id != job_id
                        or self.segment_lock_tokens.get(index) != token
                    ):
                        break
                    if self.translations[index].strip():
                        continue
                    self._store_ai_variant(index, result.text, result.provider, result.raw_text)
                    if not from_memory:
                        self.ai_drafts[index] = result.text
                    if self.text_fields[index] is not None:
                        self.text_fields[index].value = result.text
                    self.apply_status_visual(index)
                    self.update_qa_for_segment(index)
                    self.update_preview_paragraph(self.sentence_to_paragraph[index], update=False)
                    completed += 1
                    consecutive_errors = 0
                    self.save_progress(update=False)
                except Exception as exc:
                    errors += 1
                    consecutive_errors += 1
                    self.set_batch_progress(f"Ошибка на сегменте {index + 1}: {exc}")
                    self.page.update()
                    if consecutive_errors >= 3:
                        self.show_toast(f"Автопилот остановлен после трёх ошибок подряд: {exc}", error=True)
                        break
                finally:
                    if self.segment_lock_tokens.get(index) == token:
                        self.segment_lock_tokens.pop(index, None)
                self.set_batch_progress(f"Готово {completed}/{len(empty_indices)} · ошибок {errors}")
                self.update_ui(update=False)
                self.page.update()
                # Сетевую частоту ограничивает ProviderRateLimiter по фактически
                # использованному провайдеру; здесь лишь отдаём управление UI.
                await asyncio.sleep(0)
        finally:
            self.batch_running = False
            was_cancelled = self.batch_cancel_requested or generation != self.project_generation or self.batch_job_id != job_id
            self.batch_cancel_requested = False
            if self.batch_job_id == job_id:
                self.batch_job_id = ""
            self._set_batch_ui(False)
            if generation == self.project_generation:
                self.update_ui(update=False)
                self.apply_segment_filter(update=False)
                self.sync_mobile_editor(update=False)
                self.set_batch_progress("")
                self.page.update()
                if was_cancelled:
                    self.show_toast(f"Автопилот остановлен · добавлено сегментов: {completed}.")
                elif consecutive_errors < 3:
                    self.show_toast(f"Автопилот завершён · добавлено {completed}, ошибок {errors}.")

    def _export_kind(self) -> str:
        return self.export_format.value or "txt"

    def _export_extension(self) -> str:
        return {
            "txt": ".txt",
            "docx": ".docx",
            "docx_preserve": ".docx",
            "docx_bilingual": ".docx",
            "epub_preserve": ".epub",
            "epub": ".epub",
            "fb2": ".fb2",
            "xliff": ".xliff",
        }.get(self._export_kind(), ".txt")

    def _suggested_export_name(self) -> str:
        stem = Path(self.project_file_name or "novel").stem
        target = self.config.get("target_lang", "ru")
        if self._export_kind() == "docx_bilingual":
            suffix = "_original_translation"
        elif self._export_kind() in {"epub_preserve", "docx_preserve"}:
            suffix = f"_{target}_preserved"
        else:
            suffix = f"_{target}"
        return f"{stem}{suffix}{self._export_extension()}"

    def _normalise_export_path(self, value: str) -> Path:
        raw = os.path.expanduser((value or "").strip().strip('"'))
        if not raw:
            raise ValueError("путь не указан")
        path = Path(raw)
        if path.exists() and path.is_dir():
            path = path / self._suggested_export_name()
        expected = self._export_extension()
        if path.suffix.lower() != expected:
            path = path.with_suffix(expected)
        return path.absolute()

    def _build_export_payload(self) -> tuple[str, bytes]:
        if not self.file_loaded or not self.sentences:
            raise ValueError("нет открытого файла")
        include_original = bool(self.export_include_original.value)
        translated = assemble_paragraphs(
            self.sentences,
            self.translations,
            self.sentence_to_paragraph,
            original_for_empty=include_original,
        )
        kind = self._export_kind()
        if kind == "txt":
            data = ("\n\n".join(translated).rstrip() + "\n").encode("utf-8")
        elif kind == "docx_bilingual":
            data = make_docx_bytes(translated, self.original_paragraphs)
        elif kind == "docx":
            data = make_docx_bytes(translated)
        elif kind == "docx_preserve":
            if Path(self.project_file_name).suffix.lower() != ".docx" or not self.source_document_bytes:
                raise ValueError("бережный экспорт доступен только для исходного DOCX")
            data = make_preserved_docx_bytes(
                self.source_document_bytes,
                translated,
                complex_policy=self.export_complex_policy.value or "error",
            )
        elif kind == "epub_preserve":
            if Path(self.project_file_name).suffix.lower() != ".epub" or not self.source_document_bytes:
                raise ValueError("бережный экспорт доступен только для исходного EPUB")
            if not self.source_document_metadata.get("preservable", False):
                raise ValueError("разметка этого EPUB несовместима; выберите «новая чистая книга»")
            data = make_preserved_epub_bytes(
                self.source_document_bytes,
                translated,
                self.config.get("target_lang", "ru"),
                complex_policy=self.export_complex_policy.value or "error",
            )
        elif kind == "epub":
            data = make_epub_bytes(translated, Path(self.project_file_name).stem, self.config.get("target_lang", "ru"))
        elif kind == "fb2":
            data = make_fb2_bytes(translated, Path(self.project_file_name).stem, self.config.get("target_lang", "ru"))
        elif kind == "xliff":
            data = make_xliff_bytes(
                self.sentences,
                self.translations,
                self.config.get("source_lang", "en"),
                self.config.get("target_lang", "ru"),
            )
        else:
            raise ValueError("неизвестный формат экспорта")
        return self._suggested_export_name(), data

    def on_export_format_change(self, e=None) -> None:
        self.export_complex_policy.visible = self._export_kind() in {"epub_preserve", "docx_preserve"}
        self.config["complex_format_policy"] = self.export_complex_policy.value or "error"
        current = (self.export_path_input.value or "").strip()
        if current:
            try:
                self.export_path_input.value = str(Path(current).with_suffix(self._export_extension()))
            except ValueError:
                pass
        self.update_ui(update=True)

    def _export_preflight(self, *, choose_path: bool) -> None:
        if not self.file_loaded or not self.sentences:
            self.show_toast("Сначала загрузите файл.")
            return
        self.pending_export_choose_path = choose_path
        problems = self.refresh_qa()
        summary = summarize_export_readiness(self.translations, self.statuses, self.qa_issues)
        format_label = {
            "txt": "TXT — готовый перевод",
            "docx": "DOCX — готовый перевод",
            "docx_preserve": "DOCX — сохранить оформление исходника",
            "docx_bilingual": "DOCX — оригинал | перевод",
            "epub_preserve": "EPUB — сохранить оформление исходника",
            "epub": "EPUB — новая чистая книга",
            "fb2": "FB2 — электронная книга",
            "xliff": "XLIFF 2.0 — обмен с CAT",
        }.get(self._export_kind(), self._export_kind())
        self.export_preflight_summary.value = (
            f"{format_label}\n"
            f"Готово {summary['confirmed']} из {summary['total']} · "
            f"черновиков {summary['draft']} · пустых {summary['empty']}"
        )
        self.export_preflight_details.controls.clear()
        checks: list[tuple[str, str, str]] = []
        checks.append(
            (
                "check_circle" if summary["empty"] == 0 else "warning_amber",
                "Все сегменты заполнены" if summary["empty"] == 0 else f"Пустых сегментов: {summary['empty']}",
                STATUS_COLORS[STATUS_CONFIRMED] if summary["empty"] == 0 else STATUS_COLORS[STATUS_DRAFT],
            )
        )
        qa_total = summary["qa_errors"] + summary["qa_warnings"] + summary["qa_style"]
        checks.append(
            (
                "verified" if qa_total == 0 else "fact_check",
                "Локальный QA пройден" if qa_total == 0 else (
                    f"QA: ошибок {summary['qa_errors']} · предупреждений {summary['qa_warnings']} · стиль {summary['qa_style']}"
                ),
                STATUS_COLORS[STATUS_CONFIRMED] if qa_total == 0 else STATUS_COLORS[STATUS_DRAFT],
            )
        )
        kind = self._export_kind()
        if kind in {"epub_preserve", "docx_preserve"}:
            preservable = bool(self.source_document_metadata.get("preservable"))
            checks.append(
                (
                    "layers" if preservable else "report_problem",
                    "Оформление и иллюстрации будут перенесены" if preservable else "Безопасное сохранение оформления недоступно",
                    STATUS_COLORS[STATUS_CONFIRMED] if preservable else STATUS_COLORS[STATUS_EMPTY],
                )
            )
        for icon, label, color in checks:
            self.export_preflight_details.controls.append(
                ft.Row([ft.Icon(name=icon, color=color, size=18), ft.Text(label, color=self.text_color, size=12, expand=True)], spacing=8)
            )
        self.export_preflight_go_to_issue.visible = bool(problems or summary["empty"])
        self._open(self.export_preflight_dialog)

    def jump_from_export_preflight(self, e=None) -> None:
        self._close(self.export_preflight_dialog)
        target = next((index for index, value in enumerate(self.translations) if not value.strip()), None)
        if target is None:
            target = next((index for index, issues in enumerate(self.qa_issues) if issues), None)
        if target is None:
            return
        if self._page_width() < 900:
            self.switch_mobile_tab(1, update=False)
        self.focus_segment(target)

    def confirm_export_preflight(self, e=None) -> None:
        choose_path = self.pending_export_choose_path
        self._close(self.export_preflight_dialog)
        self._perform_export_now(choose_path=choose_path)

    def _perform_export_now(self, *, choose_path: bool = False) -> None:
        try:
            suggested_name, data = self._build_export_payload()
        except Exception as exc:
            self.show_toast(f"Экспорт невозможен: {exc}", error=True)
            return
        if choose_path:
            self._open_export_picker(suggested_name, data)
            return
        path_value = (self.export_path_input.value or "").strip()
        if not path_value:
            self._open_export_picker(suggested_name, data)
            return
        try:
            path = self._normalise_export_path(path_value)
            self._write_export(path, data)
        except Exception as exc:
            self.show_toast(f"Ошибка экспорта: {exc}", error=True)

    def export_now(self, e=None) -> None:
        self._export_preflight(choose_path=False)

    def choose_export_path(self, e=None) -> None:
        self._export_preflight(choose_path=True)

    def _open_export_picker(self, suggested_name: str, data: bytes) -> None:
        self.pending_export = (suggested_name, data)
        try:
            self.export_picker.save_file(
                dialog_title="Сохранить перевод",
                file_name=suggested_name,
                file_type=ft.FilePickerFileType.CUSTOM,
                allowed_extensions=[self._export_extension().lstrip(".")],
            )
        except Exception as exc:
            self.pending_export = None
            self._save_export_fallback(suggested_name, data, reason=str(exc))

    def on_export_result(self, e) -> None:
        pending = self.pending_export
        self.pending_export = None
        if not pending:
            return
        suggested_name, data = pending
        selected_path = getattr(e, "path", None)
        if not selected_path:
            return
        try:
            path = self._normalise_export_path(selected_path)
            self._write_export(path, data)
        except Exception as exc:
            self._save_export_fallback(suggested_name, data, reason=str(exc))

    def _write_export(self, path: Path, data: bytes) -> None:
        _atomic_write_bytes(path, data)
        self.export_path_input.value = str(path)
        self.config["last_export"] = str(path)
        try:
            save_config(self.config)
        except OSError:
            pass
        self.page.update()
        self.show_toast(f"Экспортировано: {path.name}")

    def _save_export_fallback(self, suggested_name: str, data: bytes, *, reason: str) -> None:
        fallback = APP_DATA_DIR / "exports" / suggested_name
        try:
            _atomic_write_bytes(fallback, data)
            self.export_path_input.value = str(fallback)
            self.config["last_export"] = str(fallback)
            try:
                save_config(self.config)
            except OSError:
                pass
            self.page.update()
            self.show_toast(
                f"Выбранный путь недоступен ({reason}). Файл сохранён во внутреннюю папку: {fallback}",
                error=True,
            )
        except OSError as exc:
            self.show_toast(f"Не удалось сохранить экспорт: {exc}", error=True)

    def copy_all_translation(self, e=None) -> None:
        if not self.file_loaded:
            self.show_toast("Сначала загрузите файл.")
            return
        paragraphs = assemble_paragraphs(
            self.sentences,
            self.translations,
            self.sentence_to_paragraph,
            original_for_empty=bool(self.export_include_original.value),
        )
        text = "\n\n".join(paragraphs)
        try:
            self.page.set_clipboard(text)
            self.show_toast(f"Скопировано: {len(text)} символов.")
        except Exception as exc:
            self.show_toast(f"Буфер обмена недоступен: {exc}", error=True)

    def on_keyboard(self, e) -> None:
        key = str(getattr(e, "key", "")).lower()
        ctrl = bool(getattr(e, "ctrl", False) or getattr(e, "meta", False))
        alt = bool(getattr(e, "alt", False))
        shift = bool(getattr(e, "shift", False))
        if ctrl and key in {"enter", "numpad enter"}:
            if self.file_loaded:
                self.confirm_segment(self.current_index)
        elif ctrl and key == "z":
            self.undo_history()
        elif ctrl and key == "y":
            self.redo_history()
        elif ctrl and key == "s":
            if self.file_loaded and self.save_progress(update=True, force_json=True):
                self.show_toast("Прогресс сохранён.")
        elif ctrl and shift and key in {" ", "space", "spacebar"}:
            self.cycle_translation_variant()
        elif alt and key in {"arrow up", "up"}:
            self.move_segment(-1)
        elif alt and key in {"arrow down", "down"}:
            self.move_segment(1)

    def toggle_zen_mode(self, e=None) -> None:
        self.zen_mode = not self.zen_mode
        self.render_layout(force=True)
        self.show_toast("Режим Дзен включён." if self.zen_mode else "Режим Дзен выключен.")

    def _detach(self, control) -> None:
        for controls in (self.content_column.controls, self.desktop_row.controls, self.header_tile.controls):
            while control in controls:
                controls.remove(control)
        if self.mobile_holder.content is control:
            self.mobile_holder.content = None

    def _page_width(self) -> float:
        width = getattr(self.page, "width", None)
        if isinstance(width, (int, float)) and width > 0:
            return float(width)
        try:
            window_width = self.page.window.width
            if isinstance(window_width, (int, float)) and window_width > 0:
                return float(window_width)
        except AttributeError:
            pass
        return 1300.0

    def render_layout(self, e=None, *, force: bool = False) -> None:
        narrow = self._page_width() < 900
        state = (narrow, self.zen_mode, self.file_loaded)
        if not force and self.layout_state == state:
            return
        self.layout_state = state
        self.page.padding = 4 if self.zen_mode else (6 if narrow else 12)
        self.app_title_text.value = f"{APP_TITLE} · Дзен" if self.zen_mode else APP_TITLE
        self.app_title_text.size = 16 if narrow else 17
        self.app_tagline_text.value = "Только текст и текущая задача" if self.zen_mode else APP_TAGLINE
        self.app_tagline_text.size = 9 if narrow else 10
        self.app_tagline_text.visible = not (self.zen_mode and narrow)
        self.drop_zone.width = 300 if narrow else 360
        self.header_actions.width = 300 if narrow else 440
        self.file_path_input.width = 300 if narrow else 330
        self.search_input.width = 300
        self.header_panel.padding = 8 if narrow else 12
        self.welcome_continue_card.width = min(440, max(280, self._page_width() - 48))

        for control in [
            self.welcome_panel,
            self.header_panel,
            self.left_column,
            self.workspace_column,
            self.mobile_editor_panel,
            self.reader_panel,
            self.right_column,
            self.export_panel,
        ]:
            self._detach(control)
        self._detach(self.mobile_box)
        self._detach(self.desktop_row)
        self._detach(self.header_tile)
        self.header_tile.controls.clear()

        if not self.file_loaded:
            self.status_row.visible = False
            self.file_info_banner.visible = False
            self.header_tile.visible = False
            self.content_column.controls[:] = [self.welcome_panel]
        elif self.zen_mode:
            self.status_row.visible = True
            editor = self.mobile_editor_panel if narrow else self.workspace_column
            editor.expand = True
            self.content_column.controls[:] = [self.status_row, self.progress_bar, editor]
        elif narrow:
            self.left_column.expand = True
            self.workspace_column.expand = True
            self.right_column.expand = True
            self.header_tile.controls.append(self.header_panel)
            self.content_column.controls[:] = [
                self.status_row,
                self.progress_bar,
                self.file_info_banner,
                self.header_tile,
                self.mobile_box,
            ]
            self.switch_mobile_tab(self.mobile_navbar.selected_index or 0, update=False)
        else:
            self.status_row.visible = True
            self.file_info_banner.visible = True
            self.header_tile.visible = True
            self.left_column.expand = 2
            self.workspace_column.expand = 5
            self.right_column.expand = 3
            self.desktop_row.controls[:] = [self.left_column, self.workspace_column, self.right_column]
            self.content_column.controls[:] = [
                self.status_row,
                self.progress_bar,
                self.file_info_banner,
                self.header_panel,
                self.desktop_row,
                self.divider,
                self.export_panel,
            ]
        self.page.update()

    def switch_mobile_tab(self, index: int, *, update: bool = True) -> None:
        index = max(0, min(int(index), len(self.mobile_panes) - 1))
        self.mobile_navbar.selected_index = index
        target = self.mobile_panes[index]
        self._detach(target)
        self.mobile_holder.content = target
        compact_editor = index == 1
        self.status_row.visible = not compact_editor
        self.file_info_banner.visible = not compact_editor
        self.header_tile.visible = not compact_editor
        if compact_editor:
            self.sync_mobile_editor(update=False)
        elif index == 2:
            self.refresh_reader_mode(follow_current=True, update=False)
        if update:
            self.page.update()

    def on_mobile_nav_change(self, e) -> None:
        self.switch_mobile_tab(e.control.selected_index)

    def on_swipe_start(self, e) -> None:
        self.swipe_dx = 0.0

    def on_swipe_update(self, e) -> None:
        try:
            self.swipe_dx += float(getattr(e, "delta_x", 0) or 0)
        except (TypeError, ValueError):
            pass

    def on_swipe_end(self, e) -> None:
        delta = self.swipe_dx
        self.swipe_dx = 0.0
        if delta > 80:
            self.move_segment(-1)
        elif delta < -80:
            self.move_segment(1)


def main(page: ft.Page) -> None:
    LiteraFlowApp(page)


if __name__ == "__main__":
    ft.app(target=main)
