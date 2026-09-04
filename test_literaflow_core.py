from __future__ import annotations

import hashlib
import io
import os
from pathlib import Path
import sqlite3
import sys
import tempfile
import threading
import time
import types
import unittest
import xml.etree.ElementTree as ET
import zipfile
import asyncio


# Контейнер проверки не содержит Flutter/Flet. Для тестов чистого ядра хватает
# модуля-заглушки: UI-классы не создаются при импорте main.
flet_stub = types.ModuleType("flet")
flet_stub.__getattr__ = lambda name: type(name, (), {})
sys.modules.setdefault("flet", flet_stub)

import main as lf  # noqa: E402


def rewrite_zip(data: bytes, replacements: dict[str, bytes], additions: dict[str, bytes] | None = None) -> bytes:
    output = io.BytesIO()
    with zipfile.ZipFile(io.BytesIO(data), "r") as source, zipfile.ZipFile(output, "w") as target:
        for info in source.infolist():
            target.writestr(info, replacements.get(info.filename, source.read(info.filename)))
        for name, value in (additions or {}).items():
            target.writestr(name, value)
    return output.getvalue()


class TypographyTests(unittest.TestCase):
    def test_nested_quotes_nbsp_and_ellipsis(self):
        value = 'В дом и на улицу... Он сказал: "Она ответила: "да"."'
        self.assertEqual(
            lf.apply_russian_typography(value),
            "В\u00a0дом и\u00a0на\u00a0улицу… Он сказал: «Она ответила: „да“.»",
        )

    def test_existing_quotes_code_and_tags_are_preserved(self):
        value = '`"code"` <span title="x"> «Уже „верно“». '
        result = lf.apply_russian_typography(value)
        self.assertIn('`"code"`', result)
        self.assertIn('<span title="x">', result)
        self.assertIn("«Уже „верно“»", result)

    def test_nbsp_can_be_disabled(self):
        self.assertEqual(lf.apply_russian_typography("в дом", use_short_nbsp=False), "в дом")


class NoteAndAiTests(unittest.TestCase):
    def test_note_parser_escape_and_unclosed_marker(self):
        clean, notes = lf.parse_tl_notes(r"Текст[note: a\] b] конец")
        self.assertEqual(clean, "Текст конец")
        self.assertEqual(notes[0]["text"], "a] b")
        self.assertEqual(clean[notes[0]["position"]:], " конец")
        raw = "Текст[note: незакрыто"
        self.assertEqual(lf.parse_tl_notes(raw), (raw, []))

    def test_ai_prefix_and_obvious_loop_are_removed(self):
        result = lf.clean_ai_translation("Конечно! Вот перевод: Привет. Привет. Привет. Привет.")
        self.assertFalse(result.casefold().startswith("конечно"))
        self.assertLess(result.count("Привет"), 4)

    def test_fallback_returns_actual_provider_and_uses_its_limiter(self):
        original_custom = lf.translate_with_custom_api
        original_google = lf.translate_with_google
        original_limiter = lf.PROVIDER_RATE_LIMITER

        class FakeLimiter:
            def __init__(self):
                self.waits = []

            def is_open(self, provider):
                return False

            def acquire(self, provider):
                pass

            def release(self, provider):
                pass

            def wait(self, provider, interval):
                self.waits.append((provider, interval))

            def success(self, provider):
                pass

            def failure(self, provider, error):
                pass

        fake = FakeLimiter()
        try:
            lf.PROVIDER_RATE_LIMITER = fake
            lf.translate_with_custom_api = lambda *args, **kwargs: (_ for _ in ()).throw(lf.TranslationError("offline"))
            lf.translate_with_google = lambda *args, **kwargs: "Вот перевод: Готово"
            result = lf.translate_segment_sync(
                "Done",
                {
                    **lf.DEFAULT_CONFIG,
                    "api_type": "custom",
                    "fallback_enabled": True,
                    "fallback_order": ["google"],
                    "google_request_interval": 0.8,
                },
            )
            self.assertEqual(result.provider, "google")
            self.assertEqual(result.text, "Готово")
            google_wait = next(interval for provider, interval in fake.waits if provider == "google")
            self.assertGreaterEqual(google_wait, 0.8)
        finally:
            lf.translate_with_custom_api = original_custom
            lf.translate_with_google = original_google
            lf.PROVIDER_RATE_LIMITER = original_limiter

    def test_provider_slot_serializes_parallel_requests(self):
        limiter = lf.ProviderRateLimiter()
        active = 0
        maximum = 0
        state_lock = threading.Lock()

        def worker():
            nonlocal active, maximum
            limiter.acquire("google")
            try:
                with state_lock:
                    active += 1
                    maximum = max(maximum, active)
                time.sleep(0.01)
                with state_lock:
                    active -= 1
            finally:
                limiter.release("google")

        threads = [threading.Thread(target=worker) for _ in range(8)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        self.assertEqual(maximum, 1)


class AsyncSafetyTests(unittest.TestCase):
    def test_late_ai_result_cannot_overwrite_manual_edit(self):
        app = lf.LiteraFlowApp.__new__(lf.LiteraFlowApp)
        app.sentences = ["Source"]
        app.translations = [""]
        app.config = {"send_neighbor_context": False}
        app.project_generation = 7
        app.segment_lock_tokens = {0: "request"}
        app.busy_segments = {0}
        app.text_fields = [None]
        app.translation_config_for_index = lambda index: dict(lf.DEFAULT_CONFIG)
        app._set_segment_busy = lambda index, busy: None
        app.show_toast = lambda *args, **kwargs: None
        app.page = types.SimpleNamespace(update=lambda: None)

        original_translate = lf.translate_segment_sync

        def delayed(*args, **kwargs):
            time.sleep(0.03)
            return lf.TranslationResult("Поздний ответ", "fake", "request", 30, raw_text="Поздний ответ")

        async def scenario():
            task = asyncio.create_task(app._translate_one_task(0, 7, "", "request", True))
            await asyncio.sleep(0.005)
            app.translations[0] = "Ручная правка"
            app.segment_lock_tokens.pop(0, None)
            await task

        try:
            lf.translate_segment_sync = delayed
            asyncio.run(scenario())
        finally:
            lf.translate_segment_sync = original_translate
        self.assertEqual(app.translations[0], "Ручная правка")

    def test_focus_waits_for_mount_and_ignores_stale_request(self):
        events = []

        class Field:
            def focus(self):
                events.append("focus")

        class Workspace:
            def scroll_to(self, **kwargs):
                events.append("scroll")

        app = lf.LiteraFlowApp.__new__(lf.LiteraFlowApp)
        app.sentences = [str(index) for index in range(20)]
        app.translations = [""] * 20
        app.navigation_generation = 4
        app.large_document_mode = True
        app.rendered_indices = set()
        app.current_index = 0
        app.segment_filter = "all"
        app.workspace_list = Workspace()
        app.page = types.SimpleNamespace(update=lambda: events.append("update"))
        app.segment_visible_for_filter = lambda index: True
        app.apply_segment_filter = lambda update=False: None
        app._page_width = lambda: 1200
        app.highlight_current = lambda update=False: events.append("highlight")
        app.schedule_autosave = lambda: None

        def rebuild():
            events.append("rebuild")
            app.rendered_indices = {10}
            app.text_fields = [None] * 20
            app.text_fields[10] = Field()

        app.rebuild_workspace = rebuild
        asyncio.run(app.focus_segment_safe(10, 4))
        self.assertLess(events.index("update"), events.index("scroll"))
        self.assertLess(events.index("scroll"), events.index("focus"))

        events.clear()
        app.navigation_generation = 6
        asyncio.run(app.focus_segment_safe(11, 5))
        self.assertNotIn("scroll", events)
        self.assertNotIn("focus", events)


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.path = Path(self.temp.name) / "project.db"
        self.store = lf.ProjectStore(self.path)

    def tearDown(self):
        self.temp.cleanup()

    def seed_project(self, count: int = 3):
        project_id = "project"
        self.store.upsert_project(
            project_id,
            title="Test",
            source_name="test.txt",
            source_path="",
            segment_count=count,
            translated_count=0,
            confirmed_count=0,
            current_index=0,
        )
        self.store.replace_document(
            project_id,
            paragraphs=[f"Paragraph {i}" for i in range(count)],
            sentences=[f"Sentence {i}" for i in range(count)],
            sentence_to_paragraph=list(range(count)),
            translations=[""] * count,
            statuses=[lf.STATUS_EMPTY] * count,
            bookmarks=[False] * count,
        )
        return project_id

    def test_schema_session_close_and_rollback(self):
        with self.store._session() as connection:
            version = connection.execute("PRAGMA user_version").fetchone()[0]
            journal = connection.execute("PRAGMA journal_mode").fetchone()[0]
        self.assertEqual(version, lf.DATABASE_SCHEMA_VERSION)
        self.assertEqual(str(journal).casefold(), "wal")
        with self.assertRaises(sqlite3.ProgrammingError):
            connection.execute("SELECT 1")
        with self.assertRaises(RuntimeError):
            with self.store._session() as failing:
                failing.execute(
                    "INSERT INTO projects(project_id,title,source_name,updated_at) VALUES('rollback','x','x','x')"
                )
                raise RuntimeError("rollback")
        with self.store._session() as check:
            self.assertIsNone(check.execute("SELECT 1 FROM projects WHERE project_id='rollback'").fetchone())

    def test_variants_notes_dual_raw_and_morph_cache_roundtrip(self):
        project_id = self.seed_project()
        self.store.upsert_segment_variants(
            project_id,
            [
                {
                    "segment_index": 0,
                    "slot": "machine",
                    "label": "Машинный",
                    "text": "Перевод",
                    "provider": "fake",
                    "raw_text": "Вот перевод: Перевод",
                }
            ],
        )
        self.store.upsert_variant_states(project_id, [(0, "machine")])
        self.store.replace_segment_notes(
            project_id,
            [{"note_id": "n1", "segment_index": 0, "position": 3, "text": "Пояснение"}],
        )
        raw = "Другой оригинал".encode()
        self.store.save_secondary_source(
            project_id,
            source_id="raw1",
            name="raw.txt",
            language="ja",
            source_hash=hashlib.sha256(raw).hexdigest(),
            source_bytes=raw,
            segments=["A", "B"],
            mapping=[0, 0],
        )
        self.store.replace_segment_alignments(project_id, "raw1", [(0, 0, 0), (0, 1, 1)])
        self.store.save_morphology_cache("Героинями", {"lemma": "героиня", "forms": ["героини"]})
        variants, active = self.store.load_segment_variants(project_id)
        self.assertEqual(active[0], "machine")
        self.assertEqual(variants[0]["machine"]["raw_text"], "Вот перевод: Перевод")
        self.assertEqual(self.store.load_segment_notes(project_id)[0]["text"], "Пояснение")
        sources = self.store.load_secondary_sources(project_id)
        self.assertEqual(sources[0]["source_bytes"], raw)
        self.assertEqual(len(sources[0]["alignments"]), 2)
        self.assertEqual(self.store.load_morphology_cache("героинями")["lemma"], "героиня")

    def test_many_short_sessions_do_not_leak_descriptors(self):
        self.seed_project()
        before = len(os.listdir("/proc/self/fd")) if Path("/proc/self/fd").exists() else 0
        for _ in range(5000):
            self.store.list_projects()
        after = len(os.listdir("/proc/self/fd")) if before else 0
        if before:
            self.assertLessEqual(after, before + 2)


class FormatTests(unittest.TestCase):
    def test_docx_footnote_package(self):
        data = lf.make_docx_bytes(["До[note: пояснение] после"])
        with zipfile.ZipFile(io.BytesIO(data), "r") as archive:
            self.assertIsNone(archive.testzip())
            self.assertIn("word/footnotes.xml", archive.namelist())
            document = ET.fromstring(archive.read("word/document.xml"))
            notes = ET.fromstring(archive.read("word/footnotes.xml"))
            self.assertTrue(any(lf._xml_local(node.tag) == "footnoteReference" for node in document.iter()))
            self.assertIn("пояснение", "".join(notes.itertext()))

    def test_clean_epub_contains_accessible_note(self):
        data = lf.make_epub_bytes(["Текст[note: справка] дальше"], "Book")
        with zipfile.ZipFile(io.BytesIO(data), "r") as archive:
            content = ET.fromstring(archive.read("EPUB/text.xhtml"))
            self.assertTrue(any(lf._xml_local(node.tag) == "aside" for node in content.iter()))
            self.assertIn("справка", "".join(content.itertext()))

    def test_epub_preserve_rejects_complex_by_default_and_keeps_resources(self):
        base = lf.make_epub_bytes(["First paragraph", "Second paragraph"], "Book")
        with zipfile.ZipFile(io.BytesIO(base), "r") as archive:
            xhtml = archive.read("EPUB/text.xhtml").replace(
                b"<p>First paragraph</p>", b"<p>First <em>paragraph</em></p>"
            )
        image = b"\x89PNG\r\n\x1a\nfixture"
        source = rewrite_zip(base, {"EPUB/text.xhtml": xhtml}, {"EPUB/image.png": image})
        paragraphs, metadata = lf.read_epub_structured(source)
        self.assertTrue(metadata["preservable"])
        translations = [f"Перевод {i}" for i in range(len(paragraphs))]
        with self.assertRaisesRegex(ValueError, "inline-разметку"):
            lf.make_preserved_epub_bytes(source, translations)
        result = lf.make_preserved_epub_bytes(source, translations, complex_policy="clean")
        with zipfile.ZipFile(io.BytesIO(result), "r") as archive:
            self.assertEqual(archive.read("EPUB/image.png"), image)
            self.assertIsNone(archive.testzip())
            ET.fromstring(archive.read("EPUB/text.xhtml"))

    def test_docx_preserve_rejects_complex_and_keeps_binary_resources(self):
        base = lf.make_docx_bytes(["First", "Second"])
        with zipfile.ZipFile(io.BytesIO(base), "r") as archive:
            root = ET.fromstring(archive.read("word/document.xml"))
        first = next(node for node in root.iter() if lf._xml_local(node.tag) == "p")
        run = ET.SubElement(first, f"{{{lf.W_NS}}}r")
        ET.SubElement(run, f"{{{lf.W_NS}}}t").text = " decorated"
        document = ET.tostring(root, encoding="utf-8", xml_declaration=True)
        media = b"binary-image"
        source = rewrite_zip(base, {"word/document.xml": document}, {"word/media/image1.png": media})
        paragraphs, metadata = lf.read_docx_structured(source)
        self.assertTrue(metadata["preservable"])
        with self.assertRaisesRegex(ValueError, "несколько форматированных"):
            lf.make_preserved_docx_bytes(source, ["Один", "Два"])
        result = lf.make_preserved_docx_bytes(source, ["Один", "Два"], complex_policy="clean")
        with zipfile.ZipFile(io.BytesIO(result), "r") as archive:
            self.assertEqual(archive.read("word/media/image1.png"), media)
            self.assertIsNone(archive.testzip())
            ET.fromstring(archive.read("word/document.xml"))


class ScaleTests(unittest.TestCase):
    def test_20k_segmentation_alignment_and_assembly(self):
        paragraphs = [f"Chapter line {index}. Second sentence {index}!" for index in range(10000)]
        sentences, mapping = lf.segment_paragraphs(paragraphs, "advanced")
        self.assertEqual(len(sentences), 20000)
        self.assertEqual(len(mapping), 20000)
        translations = [f"Перевод {index}." for index in range(20000)]
        assembled = lf.assemble_paragraphs(sentences, translations, mapping, original_for_empty=False)
        self.assertEqual(len(assembled), 10000)
        alignment = lf.proportional_segment_alignments(20000, 15000)
        self.assertEqual(len(alignment), 20000)
        self.assertTrue(all(0 <= secondary < 15000 for _, secondary, _ in alignment))


class UxSummaryTests(unittest.TestCase):
    def test_export_readiness_summary(self):
        summary = lf.summarize_export_readiness(
            ["Готово", "Черновик", ""],
            [lf.STATUS_CONFIRMED, lf.STATUS_DRAFT, lf.STATUS_EMPTY],
            [[], ["Проверьте числа", "Двойные пробелы"], []],
        )
        self.assertEqual(summary["total"], 3)
        self.assertEqual(summary["empty"], 1)
        self.assertEqual(summary["confirmed"], 1)
        self.assertEqual(summary["qa_errors"], 1)
        self.assertEqual(summary["qa_warnings"], 1)

    def test_chapter_progress_summary(self):
        summary = lf.chapter_progress_statistics(
            1,
            3,
            ["", "Один", "", "Три", ""],
            [lf.STATUS_EMPTY, lf.STATUS_CONFIRMED, lf.STATUS_EMPTY, lf.STATUS_DRAFT, lf.STATUS_EMPTY],
            [False, True, False, False, False],
            [[], [], ["Двойные пробелы"], [], []],
        )
        self.assertEqual(summary["total"], 3)
        self.assertEqual(summary["confirmed"], 1)
        self.assertEqual(summary["empty"], 1)
        self.assertEqual(summary["qa"], 1)
        self.assertEqual(summary["bookmarks"], 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
