"""Tests for the review exchange helper (v3). Run: python3 -m unittest discover -s tools/review-exchange/tests"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from importlib import util as importlib_util
from io import StringIO
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
TOOL = HERE.parent / "exchange.py"
MODULE_SPEC = importlib_util.spec_from_file_location("review_exchange", TOOL)
EXCHANGE = importlib_util.module_from_spec(MODULE_SPEC)
assert MODULE_SPEC.loader is not None
MODULE_SPEC.loader.exec_module(EXCHANGE)

REGISTRY = """
protocol = "smusni-review-mail/v3"
spool = "review/exchange"
generation = 1
[models.codex]
active = true
display_name = "Codex"
client = "codex"
model = "m1"
broadcast_recipient = true
[models.fable]
active = true
display_name = "Fable"
client = "claude"
model = "m2"
broadcast_recipient = true
[models.kimi]
active = true
display_name = "Kimi"
client = "kimi"
model = "m3"
broadcast_recipient = true
[models.inactive]
active = false
display_name = "Inactive"
client = "x"
model = "m4"
broadcast_recipient = true
[models.human]
active = true
display_name = "human partner"
client = "none"
model = "human"
sessions = false
broadcast_recipient = false
acknowledges = false
"""

V1_MSG = """---
protocol: smusni-review-mail/v1
id: 20260823T173125Z-codex-handshake
from: codex
to: fable
created_utc: 2026-08-23T17:31:25Z
kind: request
in_reply_to: none
supersedes: none
github_issues: #1
---

# Handshake
"""

V2_MSG = """---
protocol: smusni-review-mail/v2
id: 20260825T120000Z-codex-legacy-note
from: codex
to: fable,kimi
audience: all
created_utc: 2026-08-25T12:00:00Z
kind: handoff
model: m1
client: codex
ack_required: true
in_reply_to: none
supersedes: none
github_issues: none
---

# A v2 broadcast

Real content here.
"""

V2_ACK_BY_FABLE = """---
protocol: smusni-review-mail/v2
acknowledges: 20260825T120000Z-codex-legacy-note
by: fable
created_utc: 2026-08-25T12:30:00Z
---

Read and disposition captured in: legacy reply.
"""


class FakeClock:
    """Monotonic clock whose sleep advances immediately and runs timed events."""

    def __init__(self):
        self.now = 0.0
        self.events = []

    def monotonic(self):
        return self.now

    def schedule(self, when, callback):
        self.events.append((when, callback))
        self.events.sort(key=lambda event: event[0])

    def sleep(self, duration):
        target = self.now + duration
        while self.events and self.events[0][0] <= target:
            when, callback = self.events.pop(0)
            self.now = when
            callback()
        self.now = target


class ExchangeTest(unittest.TestCase):
    def setUp(self):
        self.outer_binding = os.environ.pop("SMUSNI_EXCHANGE_ACTOR", None)
        if self.outer_binding is not None:
            self.addCleanup(os.environ.__setitem__, "SMUSNI_EXCHANGE_ACTOR", self.outer_binding)
        self.tmp = Path(tempfile.mkdtemp())
        (self.tmp / "tools" / "review-exchange").mkdir(parents=True)
        (self.tmp / "tools" / "review-exchange" / "participants.toml").write_text(REGISTRY)
        for name in ("MESSAGE_TEMPLATE.md", "ACK_TEMPLATE.md"):
            (self.tmp / "tools" / "review-exchange" / name).write_text((HERE.parent / name).read_text())
        (self.tmp / "tools" / "review-exchange" / "exchange.py").write_text(TOOL.read_text())
        self.spool = self.tmp / "review" / "exchange"
        self.spool.mkdir(parents=True)

    def run_tool(self, *args, env=None, expect=0):
        e = dict(os.environ)
        e.pop("SMUSNI_EXCHANGE_ACTOR", None)
        if env:
            e.update(env)
        r = subprocess.run([sys.executable, str(self.tmp / "tools" / "review-exchange" / "exchange.py"), *args],
                           capture_output=True, text=True, env=e)
        if expect is not None:
            self.assertEqual(r.returncode, expect, f"{args}\nstdout: {r.stdout}\nstderr: {r.stderr}")
        return r

    def join(self, model, **kw):
        return self.run_tool("join", "--model", model).stdout.strip()

    def fill(self, draft: str, body: str = "\n# Title\n\nReal content.\n"):
        p = Path(draft)
        text = p.read_text()
        head, _, _ = text.partition("\n---\n")
        p.write_text(head + "\n---\n" + body)

    def new(self, actor, to, slug="note", **kw):
        args = ["new", "--actor", actor, "--to", to, "--kind", "handoff", "--slug", slug]
        for k, v in kw.items():
            args += [f"--{k.replace('_', '-')}", v]
        return self.run_tool(*args).stdout.strip()

    def publish_message(self, actor, to, slug="note", *, no_ack=False):
        args = ["new", "--actor", actor, "--to", to, "--kind", "handoff", "--slug", slug]
        if no_ack:
            args.append("--no-ack")
        draft = self.run_tool(*args).stdout.strip()
        self.fill(draft)
        path = self.run_tool("publish", "--actor", actor, draft).stdout.strip()
        return Path(path).stem

    def registry(self):
        return EXCHANGE.Registry(self.tmp)

    def wait(self, actor, clock, *, idle=5, debounce=5, broadcasts=False, scan=None):
        reg = self.registry()
        return EXCHANGE.wait_for_batch(
            reg,
            actor,
            idle_timeout=idle,
            debounce=debounce,
            include_broadcasts=broadcasts,
            initial_spool=EXCHANGE.Spool(reg),
            scan=scan or (lambda: EXCHANGE.Spool(reg)),
            monotonic=clock.monotonic,
            sleep=clock.sleep,
            poll_interval=1,
        )

    # ---- sessions

    def test_join_assigns_generation_ids_and_increments(self):
        self.assertEqual(self.join("fable"), "fable_1")
        self.assertEqual(self.join("fable"), "fable_1.1")
        self.assertEqual(self.join("fable"), "fable_1.2")
        self.assertEqual(self.join("codex"), "codex_1")
        out = self.run_tool("sessions").stdout
        self.assertIn("fable_1.2 model=fable", out)
        self.assertIn("generation=1", out)

    def test_join_refuses_fixed_inactive_and_unknown_models(self):
        self.run_tool("join", "--model", "human", expect=1)
        self.run_tool("join", "--model", "inactive", expect=3)
        self.run_tool("join", "--model", "nobody", expect=1)

    def test_bare_model_slug_is_not_an_actor(self):
        r = self.run_tool("status", "--actor", "fable", expect=3)
        self.assertIn("join --model fable", r.stderr)

    def test_generation_bump_changes_new_ids_but_keeps_old_sessions(self):
        self.assertEqual(self.join("fable"), "fable_1")
        reg = self.tmp / "tools" / "review-exchange" / "participants.toml"
        reg.write_text(reg.read_text().replace("generation = 1", "generation = 2"))
        self.assertEqual(self.join("fable"), "fable_2")
        self.assertEqual(self.join("fable"), "fable_2.1")
        self.run_tool("status", "--actor", "fable_1")  # still addressable

    def test_retire_leaves_broadcast_but_stays_addressable(self):
        f1, c1, k1 = self.join("fable"), self.join("codex"), self.join("kimi")
        self.run_tool("retire", "--actor", k1, "--note", "handed off")
        self.run_tool("retire", "--actor", k1, expect=4)  # twice is a collision
        d = self.new(f1, "all")
        self.fill(d)
        pub = self.run_tool("publish", "--actor", f1, d).stdout.strip()
        text = Path(pub).read_text()
        self.assertIn("to: codex_1\n", text)
        self.assertNotIn("kimi_1", text.split("\n---\n")[0])
        d2 = self.new(f1, k1, slug="direct")
        self.fill(d2)
        self.run_tool("publish", "--actor", f1, d2)
        self.assertIn("pending_for_kimi_1=1", self.run_tool("status", "--actor", k1).stdout)

    # ---- messages

    def test_direct_round_trip_with_generation_field(self):
        f1, c1 = self.join("fable"), self.join("codex")
        d = self.new(f1, c1)
        self.assertIn("generation: 1\n", Path(d).read_text())
        self.fill(d)
        pub = self.run_tool("publish", "--actor", f1, d).stdout.strip()
        self.assertTrue(Path(pub).exists() and not Path(d).exists())
        self.assertIn("pending_for_codex_1=1", self.run_tool("status", "--actor", c1).stdout)
        mid = Path(pub).stem
        self.run_tool("ack", "--actor", c1, mid, "--disposition", "done")
        self.assertIn("pending_for_codex_1=0", self.run_tool("status", "--actor", c1).stdout)
        self.run_tool("ack", "--actor", c1, mid, "--disposition", "again", expect=4)
        self.run_tool("ack", "--actor", f1, mid, "--disposition", "not mine", expect=3)

    def test_broadcast_excludes_sender_inactive_model_and_unjoined(self):
        f1, c1 = self.join("fable"), self.join("codex")
        d = self.new(f1, "all")
        self.fill(d)
        pub = self.run_tool("publish", "--actor", f1, d).stdout.strip()
        head = Path(pub).read_text().split("\n---\n")[0]
        self.assertIn("to: codex_1\n", head)
        self.assertIn("audience: all", head)
        self.assertNotIn("fable_1", head.split("to:")[1].split("\n")[0])

    def test_broadcast_with_no_active_sessions_is_refused(self):
        f1 = self.join("fable")
        d = self.new(f1, "all")
        self.fill(d)
        self.run_tool("publish", "--actor", f1, d, expect=1)

    def test_human_is_addressed_but_never_pending(self):
        f1 = self.join("fable")
        d = self.new(f1, "human", slug="ask")
        self.fill(d)
        self.run_tool("publish", "--actor", f1, d)
        out = self.run_tool("status", "--actor", "human").stdout
        self.assertIn("pending_for_human=0", out)
        self.assertIn("ADDRESSED", out)

    def test_fyi_is_not_pending(self):
        f1, c1 = self.join("fable"), self.join("codex")
        d = self.new(f1, c1, slug="fyi", no_ack=None) if False else self.run_tool(
            "new", "--actor", f1, "--to", c1, "--kind", "handoff", "--slug", "fyi", "--no-ack").stdout.strip()
        self.fill(d)
        self.run_tool("publish", "--actor", f1, d)
        self.assertIn("pending_for_codex_1=0", self.run_tool("status", "--actor", c1).stdout)

    def test_foreign_draft_unknown_target_and_bare_id_publish(self):
        f1, c1 = self.join("fable"), self.join("codex")
        d = self.new(f1, c1)
        self.fill(d)
        self.run_tool("publish", "--actor", c1, d, expect=3)
        d2 = self.new(f1, c1, slug="reply", reply_to="20260101T000000Z-fable_1-nothing")
        self.fill(d2)
        self.run_tool("publish", "--actor", f1, d2, expect=5)
        self.run_tool("publish", "--actor", f1, Path(d).stem)  # bare id works

    def test_actor_binding(self):
        f1, c1 = self.join("fable"), self.join("codex")
        env = {"SMUSNI_EXCHANGE_ACTOR": f1}
        self.run_tool("new", "--actor", c1, "--to", f1, "--kind", "handoff", "--slug", "x", env=env, expect=3)
        d = self.run_tool("new", "--to", c1, "--kind", "handoff", "--slug", "y", env=env).stdout.strip()
        self.assertIn(f"/drafts/{f1}/", d)
        self.run_tool("new", "--to", c1, "--kind", "handoff", "--slug", "z",
                      env={"SMUSNI_EXCHANGE_ACTOR": "fable"}, expect=3)

    def test_tmp_files_are_invisible_and_ids_never_collide(self):
        f1, c1 = self.join("fable"), self.join("codex")
        (self.spool / "messages").mkdir(exist_ok=True)
        (self.spool / "messages" / "garbage.md.123.tmp").write_text("junk")
        self.run_tool("validate")
        a = self.new(f1, c1, slug="same")
        b = self.new(f1, c1, slug="same")
        self.assertNotEqual(a, b)

    # ---- blocking wait

    def test_wait_batches_direct_messages_and_resets_trailing_edge(self):
        f1, c1 = self.join("fable"), self.join("codex")
        clock = FakeClock()
        clock.schedule(1, lambda: self.publish_message(f1, c1, "first"))
        clock.schedule(3, lambda: self.publish_message(f1, c1, "second"))

        result = self.wait(c1, clock, idle=10, debounce=3)

        self.assertEqual(result.outcome, "batch")
        self.assertEqual([message.id.split("-", 2)[2] for message in result.messages], ["first", "second"])
        self.assertEqual(clock.now, 6)

    def test_wait_uses_set_difference_not_lexicographic_high_water(self):
        f1, c1 = self.join("fable"), self.join("codex")
        older_draft = self.new(f1, c1, slug="a-older-draft")
        self.fill(older_draft)
        older_id = Path(older_draft).stem
        baseline_id = self.publish_message(f1, c1, "z-baseline")
        self.assertLess(older_id, baseline_id)
        clock = FakeClock()
        clock.schedule(1, lambda: self.run_tool("publish", "--actor", f1, older_draft))

        result = self.wait(c1, clock, idle=4, debounce=2)

        self.assertEqual([message.id for message in result.messages], [older_id])

    def test_wait_ignores_unrelated_and_default_broadcast_traffic(self):
        f1, c1, k1 = self.join("fable"), self.join("codex"), self.join("kimi")
        clock = FakeClock()
        clock.schedule(1, lambda: self.publish_message(f1, k1, "unrelated"))
        clock.schedule(2, lambda: self.publish_message(f1, "all", "broadcast"))

        result = self.wait(c1, clock, idle=4, debounce=3)

        self.assertEqual(result.outcome, "empty")
        self.assertEqual(result.messages, [])
        self.assertEqual(clock.now, 4)

    def test_wait_unrelated_traffic_does_not_extend_active_batch(self):
        f1, c1, k1 = self.join("fable"), self.join("codex"), self.join("kimi")
        clock = FakeClock()
        qualifying = []
        clock.schedule(1, lambda: qualifying.append(self.publish_message(f1, c1, "qualifying")))
        clock.schedule(2, lambda: self.publish_message(f1, k1, "other-actor"))
        clock.schedule(3, lambda: self.publish_message(f1, "all", "excluded-broadcast"))

        result = self.wait(c1, clock, idle=10, debounce=3)

        self.assertEqual([message.id for message in result.messages], qualifying)
        self.assertEqual(clock.now, 4)

    def test_wait_can_include_broadcasts(self):
        f1, c1 = self.join("fable"), self.join("codex")
        clock = FakeClock()
        clock.schedule(1, lambda: self.publish_message(f1, "all", "broadcast"))

        result = self.wait(c1, clock, idle=4, debounce=2, broadcasts=True)

        self.assertEqual(result.outcome, "batch")
        self.assertEqual([message.id.split("-", 2)[2] for message in result.messages], ["broadcast"])
        self.assertEqual(clock.now, 3)

    def test_wait_includes_new_no_ack_direct_mail(self):
        f1, c1 = self.join("fable"), self.join("codex")
        clock = FakeClock()
        clock.schedule(1, lambda: self.publish_message(f1, c1, "fyi", no_ack=True))

        result = self.wait(c1, clock, idle=4, debounce=2)

        self.assertEqual(result.outcome, "batch")
        self.assertFalse(result.messages[0].ack_required)
        direct, broadcast = result.spool.pending_for(c1)
        self.assertEqual((direct, broadcast), ([], []))

    def test_wait_first_snapshot_is_baseline_and_next_scan_catches_startup_race(self):
        f1, c1 = self.join("fable"), self.join("codex")
        old = self.publish_message(f1, c1, "already-seen")
        clock = FakeClock()
        published = []
        calls = 0

        def scan():
            nonlocal calls
            calls += 1
            if calls == 1:
                published.append(self.publish_message(f1, c1, "racing"))
            return EXCHANGE.Spool(self.registry())

        result = self.wait(c1, clock, idle=4, debounce=2, scan=scan)

        self.assertEqual([message.id for message in result.messages], published)
        self.assertNotIn(old, [message.id for message in result.messages])

    def test_wait_final_scan_catches_quiet_boundary_race(self):
        f1, c1 = self.join("fable"), self.join("codex")
        clock = FakeClock()
        published = []
        calls = 0

        def scan():
            nonlocal calls
            calls += 1
            if calls == 3:  # t=2 boundary's second, race-closing scan
                published.append(self.publish_message(f1, c1, "at-boundary"))
            return EXCHANGE.Spool(self.registry())

        result = self.wait(c1, clock, idle=2, debounce=2, scan=scan)

        self.assertEqual([message.id for message in result.messages], published)
        self.assertEqual(clock.now, 4)

    def test_wait_rejects_validation_error_unknown_bound_and_retired_actor(self):
        f1, c1 = self.join("fable"), self.join("codex")
        reg = self.registry()
        with self.assertRaisesRegex(EXCHANGE.ExchangeError, "unknown actor") as unknown:
            EXCHANGE.cmd_wait(reg, "nobody_1", idle_timeout=1, debounce=1, include_broadcasts=False)
        self.assertEqual(unknown.exception.code, EXCHANGE.EXIT_OWNERSHIP)

        with mock.patch.dict(os.environ, {EXCHANGE.BINDING_ENV: f1}):
            with self.assertRaisesRegex(EXCHANGE.ExchangeError, "bound to actor") as bound:
                EXCHANGE.cmd_wait(reg, c1, idle_timeout=1, debounce=1, include_broadcasts=False)
        self.assertEqual(bound.exception.code, EXCHANGE.EXIT_OWNERSHIP)

        self.run_tool("retire", "--actor", c1)
        with self.assertRaisesRegex(EXCHANGE.ExchangeError, "retired session") as retired:
            EXCHANGE.cmd_wait(self.registry(), c1, idle_timeout=1, debounce=1, include_broadcasts=False)
        self.assertEqual(retired.exception.code, EXCHANGE.EXIT_OWNERSHIP)

        messages = self.spool / "messages"
        messages.mkdir(exist_ok=True)
        (messages / "broken.md").write_text("not front matter")
        with self.assertRaisesRegex(EXCHANGE.ExchangeError, "validation errors") as invalid:
            EXCHANGE.cmd_wait(self.registry(), f1, idle_timeout=1, debounce=1, include_broadcasts=False)
        self.assertEqual(invalid.exception.code, EXCHANGE.EXIT_VALIDATION)

    def test_wait_aborts_on_validation_error_after_baseline(self):
        c1 = self.join("codex")
        clock = FakeClock()
        messages = self.spool / "messages"

        def introduce_error():
            messages.mkdir(exist_ok=True)
            (messages / "broken.md").write_text("not front matter")

        clock.schedule(1, introduce_error)

        with self.assertRaisesRegex(EXCHANGE.ExchangeError, "validation errors") as invalid:
            self.wait(c1, clock, idle=4, debounce=2)
        self.assertEqual(invalid.exception.code, EXCHANGE.EXIT_VALIDATION)
        self.assertEqual(clock.now, 1)

    def test_wait_output_is_stable_and_reuses_status_view(self):
        f1, c1 = self.join("fable"), self.join("codex")
        clock = FakeClock()
        clock.schedule(1, lambda: self.publish_message(f1, c1, "z-last"))
        clock.schedule(1, lambda: self.publish_message(f1, c1, "a-first"))
        reg = self.registry()
        output = StringIO()

        with redirect_stdout(output):
            EXCHANGE.cmd_wait(
                reg,
                c1,
                idle_timeout=4,
                debounce=2,
                include_broadcasts=False,
                monotonic=clock.monotonic,
                sleep=clock.sleep,
                scan=lambda: EXCHANGE.Spool(reg),
                poll_interval=1,
            )

        lines = output.getvalue().splitlines()
        self.assertEqual(lines[0], f"WAIT_BATCH actor={c1} new=2")
        new_lines = [line for line in lines if line.startswith("NEW ")]
        self.assertEqual(new_lines, sorted(new_lines))
        status = EXCHANGE.status_lines(EXCHANGE.Spool(reg), c1)
        self.assertEqual(lines[-len(status):], status)

    def test_wait_empty_output_and_duration_parser(self):
        c1 = self.join("codex")
        clock = FakeClock()
        reg = self.registry()
        output = StringIO()

        with mock.patch.dict(os.environ, {EXCHANGE.BINDING_ENV: c1}), redirect_stdout(output):
            EXCHANGE.cmd_wait(
                reg,
                None,
                idle_timeout=2,
                debounce=3,
                include_broadcasts=False,
                monotonic=clock.monotonic,
                sleep=clock.sleep,
                scan=lambda: EXCHANGE.Spool(reg),
                poll_interval=1,
            )

        self.assertTrue(output.getvalue().startswith(f"WAIT_EMPTY actor={c1}\n"))
        self.assertEqual(EXCHANGE.parse_duration("500ms"), 0.5)
        self.assertEqual(EXCHANGE.parse_duration("5m"), 300)
        for bad in ("0s", "5", "1 minute", "-2s", "infs"):
            with self.assertRaises(EXCHANGE.argparse.ArgumentTypeError):
                EXCHANGE.parse_duration(bad)

    def test_wait_interruption_is_clean_and_explicit(self):
        c1 = self.join("codex")
        output = StringIO()

        with mock.patch.object(EXCHANGE, "cmd_wait", side_effect=KeyboardInterrupt), redirect_stdout(output):
            code = EXCHANGE.main(["--root", str(self.tmp), "wait", "--actor", c1])

        self.assertEqual(code, 130)
        self.assertEqual(output.getvalue(), f"WAIT_INTERRUPTED actor={c1}\n")

        with mock.patch.object(EXCHANGE, "cmd_status", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                EXCHANGE.main(["--root", str(self.tmp), "status", "--actor", c1])

    # ---- legacy history

    def test_v1_and_v2_history_validate_and_are_inherited_by_first_session(self):
        (self.spool / "inbox" / "fable").mkdir(parents=True)
        (self.spool / "inbox" / "fable" / "20260823T173125Z-codex-handshake.md").write_text(V1_MSG)
        (self.spool / "messages").mkdir()
        (self.spool / "messages" / "20260825T120000Z-codex-legacy-note.md").write_text(V2_MSG)
        self.run_tool("validate")
        f1, k1 = self.join("fable"), self.join("kimi")
        out = self.run_tool("status", "--actor", f1).stdout
        self.assertIn("pending_for_fable_1=2", out)  # v1 direct + v2 broadcast
        self.assertIn("pending_for_kimi_1=1", self.run_tool("status", "--actor", k1).stdout)
        f11 = self.join("fable")  # a second session does not inherit
        self.assertIn("pending_for_fable_1.1=0", self.run_tool("status", "--actor", f11).stdout)
        # a legacy ack directory (by the bare model) still discharges the message
        (self.spool / "acks" / "fable").mkdir(parents=True)
        (self.spool / "acks" / "fable" / "20260825T120000Z-codex-legacy-note.ack.md").write_text(V2_ACK_BY_FABLE)
        self.assertIn("pending_for_fable_1=1", self.run_tool("status", "--actor", f1).stdout)
        # and the session can acknowledge the remaining v1 message itself
        self.run_tool("ack", "--actor", f1, "20260823T173125Z-codex-handshake", "--disposition", "read")
        self.assertIn("pending_for_fable_1=0", self.run_tool("status", "--actor", f1).stdout)
        self.run_tool("validate")

    def test_v3_message_cannot_name_bare_model(self):
        f1 = self.join("fable")
        self.run_tool("new", "--actor", f1, "--to", "codex", "--kind", "handoff", "--slug", "x", expect=3)

    def test_markdown_links_resolve_relative_to_their_file(self):
        root = HERE.parent.parent.parent
        link = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
        for md in [HERE.parent / "PROTOCOL.md", HERE.parent / "LAUNCH.md", root / "AGENTS.md"]:
            for target in link.findall(md.read_text()):
                t = target.split("#", 1)[0]
                if not t or "://" in t:
                    continue
                resolved = (md.parent / t).resolve()
                if resolved == (root / "review").resolve() or (root / "review").resolve() in resolved.parents:
                    continue  # the review/ tree is gitignored by design; absent in clean checkouts
                self.assertTrue(resolved.exists(), f"{md.name}: {target}")


if __name__ == "__main__":
    unittest.main()
