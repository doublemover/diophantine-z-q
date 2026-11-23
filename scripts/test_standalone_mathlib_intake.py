#!/usr/bin/env python3
"""Exact Mathlib admission and dependency-reader fixtures. No tools are installed."""
from copy import deepcopy
import json
import hashlib
import re
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_standalone_intake as runner


GRAM = "pel-original-order-gram-r2"
DLOG = "finite-height-dlog-mapped-trait-r1"
LENSTRA = "same-j-direct-lenstra-clear-r2"
CRT = "pel-actual-marking-crt-r3"
TRACE = "same-j-crt-trace-r2"
DIFFERENT = "same-j-crt-different-r1"
TWIST = "forward-detached-twist-point-r3"
STRUCTURAL = "same-j-structural-normalization-r3"
DYADIC = "finite-plus11-dyadic-vertical-r4"
DJ = "same-j-integral-trace-diagonal-r5"
REFLECT = "raw318-input-reflection-r4"
OBSERVED = "linear-a4-signed-observed-r1"
ARITH = "arithmetic-three-adic-nonroot-r4"
PERIOD = "period-original-elliptic-sections-r1"
FLAT = "original-elliptic-lattice-descent-r1"
DIRECT = "direct-literal-reflection-r3"
ORDINARY = "same-j-ordinary-diagonal-equation-r1"
MU = "original-mu-intertwiner-r1"
EXPECTED = {ORDINARY: 7, MU: 5, FLAT: 1, DIRECT: 5, ARITH: 8, PERIOD: 4, GRAM: 9, DLOG: 7, LENSTRA: 5, CRT: 6, TRACE: 5, DIFFERENT: 10, TWIST: 4, STRUCTURAL: 3, DJ: 4, DYADIC: 12, REFLECT: 4, OBSERVED: 3}
FRESH = {ORDINARY: 3, MU: 1, FLAT: 1, DIRECT: 10, ARITH: 2, PERIOD: 1, GRAM: 3, DLOG: 4, LENSTRA: 1, CRT: 1, TRACE: 1, DIFFERENT: 3, TWIST: 2, STRUCTURAL: 1, DJ: 4, DYADIC: 5, REFLECT: 7, OBSERVED: 5}


def packets():
    requested = os.environ.get("PACKET")
    if requested is None:
        return tuple(EXPECTED)
    if requested not in EXPECTED:
        raise ValueError("Expected one of the eighteen reviewed Mathlib rows")
    return (requested,)


def receipts(config):
    identity = runner.LAKE_LOCKS | {"protocol": 1, "helper_sha256": runner.DEPENDENCY_HELPER_SHA}
    good = {"status": "PASS", "proof_check_run": False, "identity": identity}
    return (
        "".join(root + "\n" for root in config["artifact_roots"]).encode("ascii"),
        dict(good, mode="sources", packages=[
            {"name": n, "rev": rev} for n, rev in runner.PACKAGE_REVISIONS.items()
        ]),
        dict(good, mode="artifacts", attempts=[{"label": "upstream-artifacts", "exit_code": 0}]),
    )


class MathlibIntakeTests(unittest.TestCase):
    def test_exact_modes_roots_and_stock_admission(self):
        self.assertEqual(set(runner.ALLOWLIST), set(EXPECTED) | {runner.CORE_PACKET})
        head = runner.git_at(runner.ROOT, "rev-parse", "HEAD").decode().strip()
        for packet in packets():
            config = runner.ALLOWLIST[packet]
            with self.subTest(packet=packet):
                with runner.admitted(runner.ROOT, head, packet, config) as (folder, data, audit):
                    self.assertEqual(data["order"], [n for n, _, _ in config["modules"]])
                    self.assertEqual(len(data["order"]), FRESH[packet])
                    self.assertEqual(len(config["artifact_roots"]), EXPECTED[packet])
                    self.assertEqual(set(p.name for p in folder.iterdir()),
                                     {"intake.json", *(n + ".lean" for n in data["order"])})
                    self.assertEqual(runner.digest(audit), config["audit_sha256"])
                    if packet in (CRT, TRACE):
                        module = {CRT: b"SelectedPELMarkingCRT318", TRACE: b"SelectedJOneCRTTrace318"}[packet]
                        self.assertEqual(audit.splitlines()[1:5], [
                            b"import all " + module,
                            b"public meta import Lean", b"public meta import Lean.Elab.Command",
                            b"public meta import Lean.Util.CollectAxioms",
                        ])
                    elif packet == TWIST:
                        self.assertEqual(data["order"], [
                            "CheckedHomogeneousTwistPoint318", "CheckedHomogeneousTwistPoint937Smoke318",
                        ])
                        self.assertEqual(config["source_paths"], {
                            "CheckedHomogeneousTwistPoint318": runner.INTAKES +
                            "/forward-detached-twist-point-r2/CheckedHomogeneousTwistPoint318.lean",
                        })
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == REFLECT:
                        self.assertEqual(data["order"][-1], "Raw318InputReflection318")
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                        donors = {n: runner.INTAKES + "/raw318-input-reflection-r1/" + n + ".lean"
                                  for n in data["order"] if n not in {"AffineAnchor", "AnchorValueShear", "Raw318InputReflection318"}}
                        donors["AnchorValueShear"] = runner.INTAKES + "/raw318-input-reflection-r3/AnchorValueShear.lean"
                        donors["AffineAnchor"] = runner.INTAKES + "/raw318-input-reflection-r2/AffineAnchor.lean"
                        self.assertEqual(config["source_paths"], donors)
                        # The original progress sources are frozen in the historical commit;
                        # none are updated for this validation job. Reconstruct the exact
                        # pre-lint-repair blob for the two strict-copy exceptions.
                        for name in data["order"][:-1]:
                            source = (folder / (name + ".lean")).read_bytes()
                            if name == "AffineAnchor":
                                old = b"forward, backward, huv, huz, hvz, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring"
                                for new in (b"forward, backward, Ne.symm huv, Ne.symm huz, Ne.symm hvz]; ring",
                                            b"forward, backward, Ne.symm huv]; ring",
                                            b"forward, backward, Ne.symm huz, Ne.symm hvz]; ring"):
                                    self.assertEqual(source.count(new), 2)
                                    source = source.replace(new, old)
                                self.assertEqual(runner.digest(source),
                                                 "6463cbe1e71a9359c3c8bee3a436f8cbc760df57c5401ce47f9edbd390b20cfc")
                            elif name == "AnchorValueShear":
                                simp = b"simp [forward,backward,hun,Ne.symm hun]"
                                for stem, tail, count in [(b"  \xc2\xb7 subst i; ", b"; ring", 2),
                                                          (b"    \xc2\xb7 subst i; ", b"; ring", 1),
                                                          (b"    \xc2\xb7 subst i; ", b"", 1)]:
                                    current = b"\n" + stem + simp + tail + b"\n"
                                    old = b"\n" + stem + simp + b"<;> ring\n"
                                    self.assertEqual(source.count(current), count)
                                    source = source.replace(current, old)
                                self.assertEqual(runner.digest(source),
                                                 "d0e4cb0ae948ae86dfc36d97892ee8f7600bf5241aca577b4dca87fc0e159138")
                            path = runner.PROGRESS + "/" + name + ".lean"
                            historical = runner.tree_entries(runner.ROOT, head, path)[path]
                            self.assertEqual(historical, ("100644", "blob", hashlib.sha1(
                                b"blob " + str(len(source)).encode("ascii") + b"\x00" + source).hexdigest()))
                    elif packet == DJ:
                        self.assertEqual(data["order"][-1], "SelectedJDifferentAnnihilates318")
                        self.assertEqual(config["source_paths"], {
                            n: runner.INTAKES + "/same-j-integral-trace-diagonal-r4/" + n + ".lean"
                            for n in ("SelectedJIntegralScaledTraceDual318", "SelectedJDifferentAnnihilates318")
                        } | {"SelectedJTraceDiagonalDerivation318": runner.INTAKES +
                             "/same-j-integral-trace-diagonal-r3/SelectedJTraceDiagonalDerivation318.lean"})
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == DIRECT:
                        self.assertEqual(len(runner.DIRECT_ORIGINAL_BLOBS), 5)
                        self.assertEqual(len(config["source_paths"]), 9)
                        self.assertEqual(data["order"][-1], "DirectLiteralReflection318326")
                        name = "Current326CoefficientBindingNormalize.lean"
                        path = runner.PROGRESS + "/" + name
                        expected = ("100644", "blob", "b8e2395c443f575ee6079bc6194866b2b52ccf03")
                        self.assertEqual(runner.tree_entries(runner.ROOT, head, path)[path], expected)
                        source = (folder / name).read_bytes()
                        for new, old in [(b"ite_eq_left", b"if_pos"), (b"ite_eq_right", b"if_neg")]:
                            self.assertEqual(source.count(new), 1)
                            source = source.replace(new, old)
                        self.assertEqual(source, runner.checked_blob(runner.ROOT, head, path, expected))
                        self.assertEqual(runner.digest(source),
                                         "c872b83c5c188e385f276b36dea74a1925479eff63038612a4dc5dfa46997724")
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == ORDINARY:
                        self.assertEqual(data["order"], ["OpenJModel318", "SelectedJAbsoluteStructuralKernel318",
                                                        "SelectedJOrdinaryDiagonalRegular318"])
                        self.assertEqual(config["source_paths"], {"OpenJModel318": runner.PROGRESS + "/OpenJModel318.lean"})
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == MU:
                        self.assertEqual(data["order"], ["OriginalYuanMuIntertwiner318"])
                        self.assertFalse(config.get("source_paths"))
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == FLAT:
                        self.assertEqual(data["order"], ["OriginalEllipticHalfLatticeDescent318"])
                        self.assertFalse(config.get("source_paths"))
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet in (ARITH, PERIOD):
                        expected = (["SelectedThreeAdicEscape318", "SelectedThreeAdicNonroot318"]
                                    if packet == ARITH else ["OriginalEllipticPairSections318"])
                        self.assertEqual(data["order"], expected)
                        donors = ({"SelectedThreeAdicEscape318": runner.INTAKES +
                                   "/arithmetic-three-adic-nonroot-r3/SelectedThreeAdicEscape318.lean"}
                                  if packet == ARITH else {})
                        self.assertEqual(config.get("source_paths", {}), donors)
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    elif packet == STRUCTURAL:
                        self.assertEqual(data["order"], ["SelectedJStructuralNormalization318"])
                        self.assertFalse(config.get("source_paths"))
                        self.assertIn(b"public meta import Lean.Elab.Command", audit)
                    else:
                        self.assertNotIn(b"import Lean.Elab.Command\n", audit)
                    if packet in (LENSTRA, CRT, TRACE):
                        self.assertFalse(config.get("source_paths"))
                        self.assertEqual(len(data["order"]), 1)
                    self.assertIn(b"collectAxioms name", audit)
                    if packet == DIFFERENT:
                        self.assertEqual(data["order"], [
                            "SelectedJOneDirectLenstraClear318", "SelectedJOneCRTTrace318",
                            "SelectedJOneCRTDifferent318",
                        ])
                        self.assertEqual(config["source_paths"], {
                            "SelectedJOneDirectLenstraClear318": runner.INTAKES + "/" + LENSTRA +
                                "/SelectedJOneDirectLenstraClear318.lean",
                            "SelectedJOneCRTTrace318": runner.INTAKES + "/" + TRACE +
                                "/SelectedJOneCRTTrace318.lean",
                        })
                    if packet == DYADIC:
                        self.assertEqual(data["order"][-2:], ["FractionDerivation318", "SelectedSameADyadicVerticalD2_318"])
                        donors = {n: runner.INTAKES + "/finite-height-dlog-rows-r4/" + n + ".lean"
                                  for n in data["order"][:3]}
                        donors["FractionDerivation318"] = (
                            runner.INTAKES + "/finite-plus11-dyadic-vertical-r2/FractionDerivation318.lean")
                        self.assertEqual(config["source_paths"], donors)
                        # The repaired copy differs from the historical progress blob by
                        # exactly one audited line; neither input is a project artifact.
                        src = runner.PROGRESS + "/FractionDerivation318.lean"
                        self.assertEqual(runner.tree_entries(runner.ROOT, head, src)[src],
                                         ("100644", "blob", "31e417380682bd958d1ce1be568831cc2899e96a"))
                        revised = (folder / "FractionDerivation318.lean").read_bytes()
                        prefix = b"  apply isUnit_iff_ne_zero.mpr\n"
                        good = prefix + b"  simp [jet]\n"
                        before = prefix + (b"  simpa [jet] using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors "
                                  b"(S := K) s.property)\n")
                        self.assertEqual(revised.count(good), 1)
                        self.assertEqual(runner.digest(revised.replace(good, before, 1)),
                                         "79514f79cc4ff0bfc5a13b5a67214c838f3477f1a356b3eb71c380fdb6b67a42")
                    if packet == DLOG:
                        self.assertNotIn("packet", data)
                        self.assertEqual(set(config["source_paths"]), set(data["order"][:-1]))
                        owner = runner.INTAKES + "/finite-height-dlog-rows-r4/"
                        for module, path in config["source_paths"].items():
                            self.assertEqual(path, owner + module + ".lean")

    def test_four_native_matrix_fail_closed_elsewhere(self):
        # Parse the actual finite subset of GHA expressions emitted here; do
        # not infer a decision from the packet name or merely count strings.
        wf = (runner.ROOT / ".github/workflows/progress-standalone-intake.yml").read_text()
        # The hosted checkout is intentionally sparse; this control reads the
        # actual checked-out workflow rather than silently skipping the fixture.
        self.assertIn("            /.github/workflows/progress-standalone-intake.yml\n", wf)
        # Freeze repaired reflection and prior kernel-verified signed contracts separately.
        self.assertEqual(runner.ALLOWLIST[REFLECT]["manifest_sha256"],
                         "fc5e0159632f390d304c02a666287bff008abf4200807f451fa80cf35814e77b")
        self.assertEqual(runner.ALLOWLIST[OBSERVED]["manifest_sha256"],
                         "dc14c02c15ddfd937786e4cfa98b93c0c5615c8263eba1e0986fef70791849bd")
        self.assertEqual(runner.ALLOWLIST[DYADIC]["manifest_sha256"],
                         "bc7962e57b141eb75929509a90eccdf4e0cf34938a3d75e3eeca2b75b6075a50")
        self.assertEqual(runner.ALLOWLIST[FLAT]["manifest_sha256"],
                         "d8e046d9dcb908d2da3ff6374d8a5666e9dc60ededc4166e5bc1ef25f938ec41")
        self.assertEqual(runner.ALLOWLIST[DJ]["manifest_sha256"],
                         "6377b4f845404e1048cdbdef0f3371d923186d308899b616ca92b98608fbe24d")
        cuts = re.findall(r"^          - packet: ([a-z][a-z0-9-]*)\n"
                          r"            profile: [^\n]+\n            root_count: [0-9]+\n"
                          r"            verification: (kernel check|>-\n(?: {14,}[^\n]+\n?)+)", wf, re.M)
        self.assertEqual([k for k, _ in cuts], list(runner.ALLOWLIST))
        base = 'a83a08472ea5496a98f5c9bcf86a7a02f7689c36'
        newest = {ORDINARY, MU, ARITH, DIRECT}
        narrow = ("${{ github.event.before == '"+base+"' && join(github.event.commits.*.id, ',') "
                  "== github.sha && !github.event.forced && 'source admission only' || 'kernel check' }}")
        def rows(event_before, commits, head, forced):
            result = {}
            for key, raw in cuts:
                if raw == "kernel check":
                    self.assertIn(key, newest)
                    result[key] = "native"
                else:
                    self.assertNotIn(key, newest)
                    self.assertEqual(" ".join(raw.removeprefix(">-").split()), narrow)
                    reduced = event_before == base and ",".join(commits) == head and not forced
                    result[key] = "source" if reduced else "native"
            return result
        head = "f" * 40
        selected = rows(base, [head], head, False)
        self.assertEqual({k for k, v in selected.items() if v == "native"}, newest)
        self.assertEqual(list(selected.values()).count("source"), 15)
        for ev in [("a"*40, [head], False), (base, [], False),
                   (base, ["a"*40, head], False), (base, [head], True), (None, [], False)]:
            self.assertEqual(set(rows(ev[0], ev[1], head, ev[2]).values()), {"native"})

    def test_static_external_donors_are_canonical_and_named(self):
        config = runner.ALLOWLIST[GRAM]
        files = runner.source_paths(GRAM, config)
        self.assertEqual(len(config["source_paths"]), 2)
        for name, source in config["source_paths"].items():
            self.assertEqual(files[name + ".lean"], source)
            for wrong in (source.replace("/intake/", "/intake/../intake/"), source + "/../",
                          source.replace(name + ".lean", "NotTheDonor.lean"), source[1:]):
                broken = deepcopy(config)
                broken["source_paths"][name] = wrong
                with self.subTest(wrong=wrong), self.assertRaisesRegex(ValueError, "donor path"):
                    runner.source_paths(GRAM, broken)
        broken = deepcopy(config)
        broken["source_paths"]["Unlisted"] = "arbitrary.lean"
        with self.assertRaisesRegex(ValueError, "unlisted module"):
            runner.source_paths(GRAM, broken)

    def test_exact_original_donor_rejections(self):
        cfg = runner.ALLOWLIST[DIRECT]
        head = runner.git_at(runner.ROOT, "rev-parse", "HEAD").decode().strip()
        name = "Current326CoefficientBinding"
        path = runner.PROGRESS + "/" + name + ".lean"
        ordinary = runner.ALLOWLIST[ORDINARY]
        self.assertEqual(runner.PINNED_ORIGINALS[ORDINARY],
                         {"OpenJModel318": "068898a89b9c35cddbe1ce76d997303e2c077323"})
        with self.assertRaisesRegex(ValueError, "donor path"):
            runner.source_paths(DIRECT, ordinary)
        self.assertEqual(cfg["source_paths"][name], path)
        with self.assertRaisesRegex(ValueError, "donor path"):
            runner.source_paths("another-reflection", cfg)
        for wrong in (runner.INTAKES + "/direct-old/" + name + ".lean",
                      path.replace("/progress/", "/progress/../progress/")):
            with self.subTest(path=wrong), self.assertRaisesRegex(ValueError, "donor path"):
                runner.source_paths(DIRECT, {**cfg, "source_paths": cfg["source_paths"] | {name: wrong}})
        lookup = runner.tree_entries
        oid = runner.DIRECT_ORIGINAL_BLOBS[name]
        for invalid in (("120000", "blob", oid), ("100755", "blob", oid),
                        ("100644", "blob", "0"*40)):
            def mutated(root, commit, target):
                return {path: invalid} if target == path else lookup(root, commit, target)
            with self.subTest(invalid=invalid), patch.object(runner, "tree_entries", side_effect=mutated):
                with self.assertRaisesRegex(ValueError, "Changed original donor identity"):
                    runner.read_payload(runner.ROOT, head, DIRECT, cfg)
        payload = runner.read_payload(runner.ROOT, head, DIRECT, cfg)
        payload[name + ".lean"] += b"\n"
        with self.assertRaisesRegex(ValueError, "Changed exact source"):
            runner.validate_payload(cfg, payload)

    def test_mismatched_roots_rejected(self):
        cfg = runner.ALLOWLIST[DLOG]
        with self.assertRaisesRegex(ValueError, "differ from admitted"):
            runner.profile_contract({**cfg, "artifact_roots": cfg["artifact_roots"][:-1]})
        with self.assertRaisesRegex(ValueError, "sorted unique"):
            runner.profile_contract({**cfg, "source_roots": (*cfg["source_roots"], cfg["source_roots"][-1])})

    def test_receipt_stage_and_exact_targets(self):
        for packet in packets():
            cfg = runner.ALLOWLIST[packet]
            targets, sources, artifacts = receipts(cfg)
            runner.validate_setup_receipts(cfg, targets, sources, artifacts)
            for bad_targets in (targets + b"Mathlib\n", b""):
                with self.assertRaisesRegex(ValueError, "target file differs"):
                    runner.validate_setup_receipts(cfg, bad_targets, sources, artifacts)
            for key, value in (("status", "FAIL"), ("mode", "sources"),
                               ("proof_check_run", True), ("identity", {})):
                with self.assertRaisesRegex(ValueError, "setup receipt"):
                    runner.validate_setup_receipts(cfg, targets, sources, {**artifacts, key: value})
            with self.assertRaisesRegex(ValueError, "package revisions"):
                runner.validate_setup_receipts(cfg, targets, {**sources, "packages": []}, artifacts)
            with self.assertRaisesRegex(ValueError, "No successful"):
                runner.validate_setup_receipts(cfg, targets, sources, {**artifacts, "attempts": []})

    def test_only_fresh_and_locked_libraries_pass_to_native_environment(self):
        packet = packets()[0]
        cfg = runner.ALLOWLIST[packet]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            project = root / runner.PROGRESS
            project.mkdir(parents=True)
            for name in runner.LAKE_LOCKS:
                (project / name).write_bytes((runner.ROOT / runner.PROGRESS / name).read_bytes())
            lock = json.loads((project / "lake-manifest.json").read_bytes())
            fake_rows = {p["name"]: p for p in lock["packages"]}
            setup = root / runner.DEP_OUTPUT
            setup.mkdir(parents=True)
            targets, sources, artifacts = receipts(cfg)
            (setup / (packet + ".targets.txt")).write_bytes(targets)
            (setup / "sources.json").write_text(json.dumps(sources))
            (setup / (packet + ".artifacts.json")).write_text(json.dumps(artifacts))
            packages = project / ".lake/packages"
            for p in fake_rows:
                (packages / p / ".git").mkdir(parents=True)
            mathlib = packages / "mathlib/.lake/build/lib/lean"
            for r in cfg["artifact_roots"]:
                target = mathlib / (r.replace(".", "/") + ".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(b"fixture-only, never a real Lean input")
            progress_lib = project / ".lake/build/lib/lean"
            progress_lib.mkdir(parents=True)
            fresh = root / "fresh"

            def git_fixture(path, *args):
                self.assertEqual(path.parent, packages)
                p = fake_rows[path.name]
                if args == ("rev-parse", "HEAD"):
                    return (p["rev"] + "\n").encode()
                if args == ("remote", "get-url", "origin"):
                    return (p["url"] + "\n").encode()
                self.assertEqual(args, ("diff", "--quiet", "HEAD", "--"))
                return b""

            with patch.object(runner, "git_at", side_effect=git_fixture):
                libs, receipt = runner.mathlib_setup(root, packet, cfg)
                self.assertEqual(libs, (mathlib,))
                self.assertEqual(receipt["dependency_revisions"], runner.PACKAGE_REVISIONS)
                env = runner.profile_environment(cfg, fresh, {"LEAN_PATH": str(progress_lib)}, libs)
                self.assertEqual(env["LEAN_PATH"].split(os.pathsep), [str(fresh), str(mathlib)])
                target.unlink()
                with self.assertRaisesRegex(ValueError, "Missing pinned upstream artifact"):
                    runner.mathlib_setup(root, packet, cfg)


if __name__ == "__main__":
    unittest.main()
