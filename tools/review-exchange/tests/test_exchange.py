"""Tests for the review exchange helper. Run: python3 -m unittest discover -s tools/review-exchange/tests"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOL = HERE.parent / "exchange.py"

REGISTRY = """
protocol = "smusni-review-mail/v2"
spool = "review/exchange"
[actors.codex]
active = true
display_name = "Codex"
client = "codex"
model = "m1"
broadcast_recipient = true
[actors.fable]
active = true
display_name = "Fable"
client = "claude"
model = "m2"
broadcast_recipient = true
[actors.kimi]
active = true
display_name = "Kimi"
client = "kimi"
model = "m3"
broadcast_recipient = true
[actors.retired]
active = false
display_name = "Retired"
client = "x"
model = "m4"
broadcast_recipient = true
[actors.human]
active = true
display_name = "human partner"
client = "none"
model = "human"
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

V1_ACK = """---
protocol: smusni-review-mail/v1
acknowledges: 20260823T173125Z-codex-handshake
by: fable
created_utc: 2026-08-23T19:31:14Z
---

Read and disposition captured in: reply.
"""


class ExchangeTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        (self.tmp / "tools" / "review-exchange").mkdir(parents=True)
        (self.tmp / "tools" / "review-exchange" / "participants.toml").write_text(REGISTRY)
        for f in ("MESSAGE_TEMPLATE.md", "ACK_TEMPLATE.md"):
            shutil.copy(HERE.parent / f, self.tmp / "tools" / "review-exchange" / f)
        shutil.copy(TOOL, self.tmp / "tools" / "review-exchange" / "exchange.py")
        self.spool = self.tmp / "review" / "exchange"
        for d in ("inbox/codex", "inbox/fable", "messages"):
            (self.spool / d).mkdir(parents=True)
        for a in ("codex", "fable", "kimi", "retired", "human"):
            (self.spool / "drafts" / a).mkdir(parents=True)
            (self.spool / "acks" / a).mkdir(parents=True)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def run_tool(self, *args, expect=0, env=None):
        e = dict(os.environ); e.pop("SMUSNI_EXCHANGE_ACTOR", None); e.update(env or {})
        r = subprocess.run([sys.executable, str(self.tmp / "tools/review-exchange/exchange.py"),
                            "--root", str(self.tmp), *args], capture_output=True, text=True, env=e)
        self.assertEqual(r.returncode, expect, f"args={args}\nstdout={r.stdout}\nstderr={r.stderr}")
        return r.stdout

    def fill(self, draft: Path, body="\n# Subject\n\nbody\n"):
        text = draft.read_text()
        head, _, _ = text.partition("\n---\n")
        draft.write_text(head + "\n---\n" + body)

    # ---- v1 compatibility -------------------------------------------------
    def test_v1_history_validates_and_is_pending_until_acked(self):
        (self.spool / "inbox/fable/20260823T173125Z-codex-handshake.md").write_text(V1_MSG)
        out = self.run_tool("status", "--actor", "fable")
        self.assertIn("pending_for_fable=1 direct=1 broadcast=0", out)
        (self.spool / "acks/fable/20260823T173125Z-codex-handshake.ack.md").write_text(V1_ACK)
        out = self.run_tool("status", "--actor", "fable")
        self.assertIn("pending_for_fable=0", out)
        self.assertIn("messages=1 drafts=0 acknowledgements=1 errors=0", out)

    def test_v1_wrong_recipient_ack_fails(self):
        (self.spool / "inbox/fable/20260823T173125Z-codex-handshake.md").write_text(V1_MSG)
        (self.spool / "acks/codex/20260823T173125Z-codex-handshake.ack.md").write_text(
            V1_ACK.replace("by: fable", "by: codex"))
        out = self.run_tool("validate", expect=2)
        self.assertIn("not a recipient", out)

    def test_v1_cannot_be_published_via_helper(self):
        d = self.spool / "drafts/codex/20260823T173125Z-codex-handshake.md"
        d.write_text(V1_MSG)
        self.run_tool("publish", "--actor", "codex", str(d), expect=2)

    # ---- v2 direct / subset / broadcast -----------------------------------
    def test_direct_message_round_trip(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "probe", "--issues", "#24").strip())
        self.assertTrue(d.exists()); self.fill(d)
        pub = Path(self.run_tool("publish", "--actor", "codex", str(d)).strip())
        self.assertFalse(d.exists()); self.assertTrue(pub.exists())
        self.assertIn("audience: direct", pub.read_text())
        self.assertIn("model: m1", pub.read_text())
        out = self.run_tool("status", "--actor", "fable")
        self.assertIn("direct=1 broadcast=0", out)
        self.assertIn("pending_for_kimi=0", self.run_tool("status", "--actor", "kimi"))
        mid = pub.stem
        self.run_tool("ack", "--actor", "fable", mid, "--disposition", "captured")
        self.assertIn("pending_for_fable=0", self.run_tool("status", "--actor", "fable"))

    def test_broadcast_expands_at_publication_and_excludes_sender_and_inactive(self):
        d = Path(self.run_tool("new", "--actor", "fable", "--to", "all", "--kind", "finding",
                               "--slug", "b").strip()); self.fill(d)
        pub = Path(self.run_tool("publish", "--actor", "fable", str(d)).strip())
        text = pub.read_text()
        self.assertIn("to: codex,kimi\n", text)          # retired, human, sender excluded
        self.assertIn("audience: all", text)
        for a, n in (("codex", 1), ("kimi", 1), ("fable", 0), ("human", 0)):
            self.assertIn(f"pending_for_{a}={n}", self.run_tool("status", "--actor", a))
        self.assertIn("broadcast=1", self.run_tool("status", "--actor", "kimi"))
        # a later registry change does not alter the published audience
        reg = self.tmp / "tools/review-exchange/participants.toml"
        reg.write_text(reg.read_text().replace('[actors.retired]\nactive = false', '[actors.retired]\nactive = true'))
        self.assertIn("pending_for_retired=0", self.run_tool("status", "--actor", "retired"))

    def test_subset_recipients(self):
        d = Path(self.run_tool("new", "--actor", "kimi", "--to", "codex,fable", "--kind", "proposal",
                               "--slug", "s").strip()); self.fill(d)
        self.run_tool("publish", "--actor", "kimi", str(d))
        self.assertIn("pending_for_codex=1", self.run_tool("status", "--actor", "codex"))
        self.assertIn("pending_for_kimi=0", self.run_tool("status", "--actor", "kimi"))

    def test_fyi_is_not_pending(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "all", "--kind", "handoff",
                               "--slug", "fyi", "--no-ack").strip()); self.fill(d)
        self.run_tool("publish", "--actor", "codex", str(d))
        self.assertIn("pending_for_fable=0", self.run_tool("status", "--actor", "fable"))

    # ---- ownership, collisions, references --------------------------------
    def test_non_recipient_cannot_ack_and_no_double_ack(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "x").strip()); self.fill(d)
        mid = Path(self.run_tool("publish", "--actor", "codex", str(d)).strip()).stem
        self.run_tool("ack", "--actor", "kimi", mid, "--disposition", "no", expect=3)
        self.run_tool("ack", "--actor", "fable", mid, "--disposition", "yes")
        self.run_tool("ack", "--actor", "fable", mid, "--disposition", "again", expect=4)

    def test_publish_refuses_foreign_draft_and_unknown_reply_target(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "y").strip()); self.fill(d)
        self.run_tool("publish", "--actor", "fable", str(d), expect=3)
        d2 = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "response",
                                "--slug", "z", "--reply-to", "20260101T000000Z-fable-nothing").strip()); self.fill(d2)
        out = self.run_tool("status", "--actor", "codex")      # own draft: warning, spool still clean
        self.assertIn("WARNING", out); self.assertIn("errors=0", out)
        self.assertIn("errors=0", self.run_tool("status", "--actor", "fable"))  # not even a warning for others
        self.run_tool("publish", "--actor", "codex", str(d2), expect=5)

    def test_duplicate_id_collision_is_refused(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "dup").strip()); self.fill(d)
        text = d.read_text()
        pub = Path(self.run_tool("publish", "--actor", "codex", str(d)).strip())
        # re-create an identical draft and try to publish it again
        d.write_text(text)
        self.run_tool("publish", "--actor", "codex", str(d), expect=4)  # documented collision code

    def test_tmp_and_partial_files_are_invisible(self):
        (self.spool / "messages" / "20260825T000000Z-codex-partial.md.tmp").write_text("garbage")
        (self.spool / "acks" / "fable" / "junk.ack.md.tmp").write_text("garbage")
        self.assertIn("errors=0", self.run_tool("validate"))

    def test_same_second_ids_do_not_collide(self):
        a = self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request", "--slug", "t").strip()
        b = self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request", "--slug", "t").strip()
        self.assertNotEqual(a, b)

    def test_unknown_actor_rejected(self):
        self.run_tool("status", "--actor", "gemini", expect=3)
        self.run_tool("new", "--actor", "codex", "--to", "gemini", "--kind", "request", "--slug", "g", expect=3)


    # ---- concurrency and atomicity ------------------------------------------
    def test_half_written_foreign_draft_never_blocks_others(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "ok").strip()); self.fill(d)
        (self.spool / "drafts/kimi/20260825T000000Z-kimi-partial.md").write_text("---\nprotocol: smusni-review-mail/v2\nid: 2026")
        self.assertIn("errors=0", self.run_tool("status", "--actor", "fable"))
        mid = Path(self.run_tool("publish", "--actor", "codex", str(d)).strip()).stem   # publish unaffected
        self.run_tool("ack", "--actor", "fable", mid, "--disposition", "ok")             # ack unaffected
        self.assertIn("WARNING", self.run_tool("status", "--actor", "kimi"))              # owner is warned

    def test_partial_ack_tmp_is_invisible_and_ack_is_atomic(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "a").strip()); self.fill(d)
        mid = Path(self.run_tool("publish", "--actor", "codex", str(d)).strip()).stem
        (self.spool / "acks/fable" / f"{mid}.ack.md.tmp").write_text("---\nprotocol: smusni-review-mail/v2\nackno")
        self.assertIn("errors=0", self.run_tool("status", "--actor", "codex"))
        self.run_tool("ack", "--actor", "fable", mid, "--disposition", "done")
        self.assertTrue((self.spool / "acks/fable" / f"{mid}.ack.md").exists())
        leftovers = [p.name for p in (self.spool / "acks/fable").glob("*.tmp")]
        self.assertEqual(leftovers, [f"{mid}.ack.md.tmp"])   # only the planted stale file; the helper's own temp is gone
        self.assertIn("errors=0", self.run_tool("validate"))   # and it never blocks anything

    def test_concurrent_new_allocates_distinct_ids(self):
        e = dict(os.environ); e.pop("SMUSNI_EXCHANGE_ACTOR", None)
        cmd = [sys.executable, str(self.tmp / "tools/review-exchange/exchange.py"), "--root", str(self.tmp),
               "new", "--actor", "codex", "--to", "fable", "--kind", "request", "--slug", "race"]
        procs = [subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True, env=e) for _ in range(4)]
        outs = [p.communicate()[0].strip() for p in procs]
        self.assertTrue(all(p.returncode == 0 for p in procs))
        self.assertEqual(len(set(outs)), 4)

    def test_invalid_materialization_never_publishes(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "empty").strip())      # body left as the template
        self.run_tool("publish", "--actor", "codex", str(d), expect=2)
        self.assertFalse(list((self.spool / "messages").glob("*")))
        self.assertTrue(d.exists())                              # draft retained for editing

    # ---- human semantics and actor binding ---------------------------------
    def test_human_recipient_is_addressed_but_never_pending(self):
        d = Path(self.run_tool("new", "--actor", "fable", "--to", "human", "--kind", "decision-query",
                               "--slug", "q").strip()); self.fill(d)
        mid = Path(self.run_tool("publish", "--actor", "fable", str(d)).strip()).stem
        out = self.run_tool("status", "--actor", "human")
        self.assertIn("pending_for_human=0", out); self.assertIn(f"ADDRESSED {mid}", out)
        self.assertIn("errors=0", self.run_tool("validate"))    # no ack expected, none owed
        self.run_tool("ack", "--actor", "human", mid, "--disposition", "seen")  # optional, still allowed
        self.assertNotIn("ADDRESSED", self.run_tool("status", "--actor", "human"))

    def test_actor_binding_refuses_mismatch_and_supplies_default(self):
        env = {"SMUSNI_EXCHANGE_ACTOR": "qwen"}
        (self.spool / "drafts/qwen").mkdir(exist_ok=True); (self.spool / "acks/qwen").mkdir(exist_ok=True)
        reg = self.tmp / "tools/review-exchange/participants.toml"
        reg.write_text(reg.read_text() + '\n[actors.qwen]\nactive = true\ndisplay_name = "Qwen"\nclient = "qwen"\nmodel = "m5"\nbroadcast_recipient = true\n')
        self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request", "--slug", "x", expect=3, env=env)
        d = Path(self.run_tool("new", "--to", "fable", "--kind", "request", "--slug", "x", env=env).strip())
        self.assertIn("/drafts/qwen/", str(d)); self.fill(d)
        self.run_tool("publish", "--actor", "codex", str(d), expect=3, env=env)
        mid = Path(self.run_tool("publish", str(d), env=env).strip()).stem
        self.run_tool("ack", "--actor", "fable", mid, "--disposition", "no", expect=3, env=env)
        self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request", "--slug", "y")  # unbound driver ok

    def test_empty_recipient_list_rejected_at_creation(self):
        self.run_tool("new", "--actor", "codex", "--to", ",", "--kind", "request", "--slug", "e", expect=1)


    def test_publish_accepts_bare_id_or_filename(self):
        d = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                               "--slug", "byid").strip()); self.fill(d)
        pub = Path(self.run_tool("publish", "--actor", "codex", d.stem).strip())     # bare id
        self.assertTrue(pub.exists())
        d2 = Path(self.run_tool("new", "--actor", "codex", "--to", "fable", "--kind", "request",
                                "--slug", "byname").strip()); self.fill(d2)
        self.assertTrue(Path(self.run_tool("publish", "--actor", "codex", d2.name).strip()).exists())
        self.run_tool("publish", "--actor", "codex", "20260101T000000Z-codex-nothing", expect=1)

    # ---- documentation hygiene ----------------------------------------------
    def test_markdown_links_resolve_relative_to_their_file(self):
        import re
        docs = list(HERE.parent.glob("*.md"))
        self.assertTrue(docs)
        broken = []
        for doc in docs:
            for m in re.finditer(r"\]\(([^)]+)\)", doc.read_text()):
                target = m.group(1).split("#")[0]
                if not target or target.startswith(("http://", "https://")):
                    continue
                if not (doc.parent / target).exists():
                    broken.append(f"{doc.name}: {target}")
        self.assertEqual(broken, [])


if __name__ == "__main__":
    unittest.main()
