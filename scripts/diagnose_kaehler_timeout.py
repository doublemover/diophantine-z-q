#!/usr/bin/env python3
"""Hosted-only, exact-source Kaehler timeout diagnostic. Never a repair or acceptance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import re
import diagnose_diagonal_identity as runner
ci = runner.ci
PACKET = 'pel-original-cotangent-hzero-forty-r69'
MODULE = 'FourRootActualBranchKaehler318'
DEPENDENCIES = {'FourRootActualBranchLocalization318','ActualEtaleFrameNormalization318','SquareCoordinateDifferential318','ActualRootPivotCoordinates318'}
BASELINE_SOURCES = {'SquareCoordinateDifferential318': 'dc7711a87960735b1682f8ccfa9275be60b5bce135ab5386b36d12f06a2e908b'}
SOURCE_SHA = '26e84b6a6e5f1d14263d71673cdfbbc520964630179cf9732fb2616b471d0b32'
CONTROL_SCRATCH_SHAS = {'imports_only':'f1897fcc4789b38cf94da1e8ce4cbf9876709002c2d54252ba63ae7f6f4dbb59','command_trace':'fb4b98362750454ca0d65c7591b58312657fa8ee194b52479617674dc994a483'}
INTAKE_SHA = '6e0afdf648f8afae6195ad8ac836ac706f8e804a3bdf2572ce15f292d435f442'
APPLICATION_SHA = 'bb069d50852d17b665734340b9ded0e32d373aadef7685c13e854998ee8b8128'
RUNNER_SHA = 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2'
RUNNER_LIMITS_SHA = '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00'
SECONDS = 90
MAX_BYTES = 2 * 1024 * 1024
EXPECTED_FLAGS = ('-j1', '-M', '6144', '-Ddebug.skipKernelTC=false')
COMPILED_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir')
LABEL = 'scratch-kaehler-timeout'

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

def no_compiled(root, module=None):
    bad = sorted(str(p.relative_to(root)) for ext in COMPILED_SUFFIXES
                 for p in root.rglob((module or '*') + ext))
    require(not bad, 'Unexpected compiled artifacts: ' + ', '.join(bad))

OLD_FINAL_TACTICS = '  rw [regroup_root,AlgHom.commutes,\n    IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)\n      (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]\n  rfl\n'
SUBSTEP_FINAL_TACTICS = '  kaehler_final\n    (rw [regroup_root,AlgHom.commutes,\n      IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)\n        (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes])\n    (rfl)\n'
SUBSTEP_TACTIC_DECL = 'syntax "kaehler_final " "(" tactic ")" "(" tactic ")" : tactic\nelab_rules : tactic\n  | `(tactic| kaehler_final ($rwTac:tactic) ($rflTac:tactic)) => do\n    let emit : String → Lean.Elab.Tactic.TacticM Unit := fun label => do\n      let out ← IO.getStderr\n      out.putStrLn ("KAEHLER_SUBSTEP_" ++ label)\n      out.flush\n    emit "BEFORE_FINAL_RW"\n    Lean.Elab.Tactic.evalTactic rwTac\n    emit "AFTER_FINAL_RW"\n    emit "BEFORE_FINAL_RFL"\n    Lean.Elab.Tactic.evalTactic rflTac\n    emit "AFTER_FINAL_RFL"\n\n'
SUBSTEP_SCOPE = 'set_option trace.Elab.definition.header true in\nset_option trace.Elab.definition.value true in\n'

def substep_specimen(text):
    """Trace exact call-site tactic syntax with a predeclared elaborator wrapper.

    Markers execute inside one predeclared elaborator, including after rfl
    closes the last goal. Captured syntax preserves call-site identifier scopes.
    The local run_tac compilation path is not used. No result is admitted.
    """
    target = 'lemma source_coordinate_original:'
    require(text.count(target) == 1, 'Target declaration boundary changed')
    start = text.index(target)
    end = text.index('\nrun_cmd ', start)
    declaration = text[start:end]
    before = OLD_FINAL_TACTICS
    require(declaration.count(before.rstrip('\n')) == 1, 'Final tactic sequence changed')
    after = declaration.replace(before.rstrip('\n'), SUBSTEP_FINAL_TACTICS.rstrip('\n'), 1)
    return text[:start] + SUBSTEP_TACTIC_DECL + SUBSTEP_SCOPE + after + text[end:]

def control_specimens(source):
    """Frozen historical specimens. Only imports_only is executed; command_trace
    retains diagnosed syntax defects for provenance, never as a clean control.
    """
    require(digest(source) == SOURCE_SHA, 'Frozen target source changed')
    pattern = r'#eval \(do\n  let out ← IO.getStdout\n  out.putStrLn "PEL_KAEHLER_CHECKPOINT ([^"]+)"\n  out.flush : IO Unit\)'
    require(len(re.findall(pattern,source)) == 21, 'Checkpoint count changed')
    def marker(label):
        return 'run_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n  out.putStrLn "KAEHLER_COMMAND_'+label+'"\n  out.flush'
    imports = source[:source.index('#eval')]
    text = re.sub(pattern, lambda m: marker(m[1]), source)
    text = text.replace(imports,imports+'set_option stderrAsMessages false\n',1)
    text = text.replace('public section\n','public section\nset_option profiler true\nset_option profiler.threshold 10\n',1)
    text = substep_specimen(text)
    result = {'imports_only':imports+'set_option stderrAsMessages false\n'+marker('IMPORTS_ONLY_COMPLETE')+'\n','command_trace':text}
    require({k:digest(v) for k,v in result.items()} == CONTROL_SCRATCH_SHAS, 'Reviewed specimen changed')
    return result

# Reviewed candidate is scratch-only. Original packet/timeout/prefix/baseline
# authentication remains unchanged; only the second bounded specimen differs.
CANDIDATE_SOURCE_SHA = '22bc3db3670727d3209fca63b4f54316ea43dfbd0f2957b0a9545c8323376066'
CANDIDATE_FIXTURE = Path(__file__).resolve().parent/'diagnostic_evidence/kaehler_generic_scalar_candidate.lean.txt'
GENERIC_HELPER = '/-- Scalar coherence for the same tensor inclusion and algebra equivalence,\nproved over abstract dictionaries before specializing the original chart. -/\nprivate theorem tensorScalarImage\n    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]\n    [Algebra R A] [Algebra R B] [Algebra A C]\n    (e : TensorProduct R A B ≃ₐ[A] C) (x : R) :\n    e (Algebra.TensorProduct.includeRight (algebraMap R B x)) =\n      algebraMap A C (algebraMap R A x) := by\n  rw [AlgHom.commutes,\n    IsScalarTower.algebraMap_apply R A (TensorProduct R A B), AlgEquiv.commutes]\n\n'
ORIGINAL_TARGET_PROOF = '  apply (sourceLocalizationEquiv b i).injective\n  rw [sourceCoordinate,AlgEquiv.apply_symm_apply,sourceLocalizationEquiv_on_source]\n  change orderCoordinate b i=localizedSourceEquiv b i\n    (Algebra.TensorProduct.includeRight (sourceRegroup b i\n      (FourRootAffineCoordinateRing318.coordinate b (some i))))\n  rw [regroup_root,AlgHom.commutes,\n    IsScalarTower.algebraMap_apply (BranchBase b i) (OpenBase b i)\n      (OpenBase b i⊗[BranchBase b i]RegroupedOrder b i),AlgEquiv.commutes]\n  rfl\n'
CANDIDATE_TARGET_PROOF = '  exact (sourceLocalizationEquiv b i).symm_apply_eq.mpr\n    ((tensorScalarImage (localizedSourceEquiv b i) (baseCoordinate b i)).symm.trans\n      ((congrArg (fun z : RegroupedOrder b i =>\n        localizedSourceEquiv b i (Algebra.TensorProduct.includeRight z))\n        (regroup_root b i)).symm.trans\n        (sourceLocalizationEquiv_on_source b i\n          (FourRootAffineCoordinateRing318.coordinate b (some i))).symm))\n'
SQUARE_HELPER = '/-- Transport the original square relation through the same scalar tower. -/\nprivate theorem mappedSquare\n    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]\n    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]\n    (x y : A) (r : R) (h : y ^ 2 = x - algebraMap R A r) :\n    algebraMap A B x - algebraMap R B r = (algebraMap A B y) ^ 2 := by\n  have hm := congrArg (algebraMap A B) h\n  simpa only [map_pow, map_sub, ← IsScalarTower.algebraMap_apply] using hm.symm\n\n'
ORIGINAL_SQUARE_PROOF = '  apply (sourceLocalizationEquiv b i).injective\n  rw [map_sub,map_pow,AlgEquiv.commutes,sourceCoordinate,AlgEquiv.apply_symm_apply]\n  rw [sourceParameter,sourceLocalizationEquiv_on_source]\n  change sourceMap b i (algebraMap ℂ[X] (FourRootActualFractionField318.A b) X)-_=_\n  rw [sourceMap_on_polynomial]\n  have h:=congrArg (algebraMap (OpenBase b i) (OpenOrder b i))\n    (FourRootActualFiniteBranchChart318.exact_square b i)\n  have hC(q:ℂ):algebraMap ℂ[X] (OpenOrder b i) (C q)=algebraMap ℂ (OpenOrder b i) q:=\n    (IsScalarTower.algebraMap_apply ℂ ℂ[X] (OpenOrder b i) q).symm\n  simpa only [map_sub,map_pow,orderCoordinate,baseCoordinate_root,\n    FourRootActualFiniteBranchChart318.root,FiniteBranchChart318.openRoot,\n    ←IsScalarTower.algebraMap_apply,hC] using h\n'
CANDIDATE_SQUARE_PROOF = '  exact (mappedSquare (R := ℂ) (A := FourRootActualFractionField318.A b)\n    (B := SourceRing b i) (FourRootAffineCoordinateRing318.coordinate b none)\n    (FourRootAffineCoordinateRing318.coordinate b (some i)) (b i)\n    (FourRootAffineCoordinateRing318.relation b i)).trans\n      (congrArg (fun z : SourceRing b i => z ^ 2) (source_coordinate_original b i).symm)\n'
ORIGINAL_REGROUP_PROOF = '  rw [baseCoordinate_root]\n  change _ (FourRootAffineTensorPresentation318.toTensor b\n    (FourRootAffineCoordinateRing318.coordinate b (some i)))=_\n  rw [FourRootAffineTensorPresentation318.toTensor_root]\n  simpa only [FourRootAffineTensorPresentation318.radicand,FourRootPivot318.indices_zero,\n    LinearRootCoordinate318.parameter,Units.val_one,map_one,one_mul] using\n    ActualRootPivotCoordinates318.regroup_generator (FourRootAffineTensorPresentation318.radicand b) i\n'
TRANSPORT_HELPER = '/-- Predicate transport across the same two index equalities, proved\nbefore specializing any algebraic carrier or dictionary. -/\nprivate theorem transportProperty\n    {α β : Type*} (F : α → β → Type*) (P : ∀ p q, F p q → Prop)\n    {p p₀ : α} {q q₀ : β} (hp : p = p₀) (hq : q = q₀)\n    (x : F p₀ q₀) (hx : P p₀ q₀ x) :\n    P p q (Eq.mpr (congrArg (fun z => F z q) hp)\n      (Eq.mpr (congrArg (fun z => F p₀ z) hq) x)) := by\n  cases hp\n  cases hq\n  exact hx\n\n/-- The exact sourceRegroup parameter transport, named separately so its\ncomplete declaration can be checked before the root-compatibility theorem. -/\nprivate def transportedRegroup\n    {R : Type*} [CommRing R] (a : Fin 4 → R) (i : Fin 4)\n    (p : R) (q : Fin 3 → R)\n    (hp : p = a (FourRootPivot318.indices i 0))\n    (hq : q = fun j => a (FourRootPivot318.indices i j.succ)) :\n    FourRootOrder318.Order a ≃ₐ[R]\n      TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q) := by\n  rw [hp,hq]\n  exact FourRootPivot318.regroup a i\n\n/-- Diagnostic only: the exact compatibility proposition as a type-valued\nconstruction. This definition does not assert or prove compatibility. -/\nprivate def transportedRegroupRootStatement\n    {R : Type*} [CommRing R] (a : Fin 4 → R) (i : Fin 4)\n    (p : R) (q : Fin 3 → R)\n    (hp : p = a (FourRootPivot318.indices i 0))\n    (hq : q = fun j => a (FourRootPivot318.indices i j.succ)) : Prop :=\n    (transportedRegroup a i p q hp hq)\n        (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing p)\n        (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q)))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial p))\n\n/-- Diagnostic only: the exact compatibility proposition as a type-valued\nconstruction. This definition does not assert or prove compatibility. -/\nprivate def explicitCastRegroupRootStatement\n    {R : Type*} [CommRing R] (a : Fin 4 → R) (i : Fin 4)\n    (p : R) (q : Fin 3 → R)\n    (hp : p = a (FourRootPivot318.indices i 0))\n    (hq : q = fun j => a (FourRootPivot318.indices i j.succ)) : Prop :=\n    (Eq.mpr\n      (congrArg (fun r : R => FourRootOrder318.Order a ≃ₐ[R]\n        TensorProduct R (QuadraticPresentation318.RootRing r) (ThreeRootOrder318.Order q)) hp)\n      (Eq.mpr\n        (congrArg (fun v : Fin 3 → R => FourRootOrder318.Order a ≃ₐ[R]\n          TensorProduct R\n            (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0)))\n            (ThreeRootOrder318.Order v)) hq)\n        (FourRootPivot318.regroup a i)))\n        (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing p)\n        (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q)))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial p))\n\n/-- Diagnostic native-law specialization at the exact parameter values\nused by transportProperty, without applying either equality transport. -/\nprivate theorem nativeRegroupRootSpecialization\n    {R : Type*} [CommRing R] (a : Fin 4 → R) (i : Fin 4) :\n    (FourRootPivot318.regroup a i)\n        (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0)))\n        (TensorProduct R (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0))) (ThreeRootOrder318.Order (fun j => a (FourRootPivot318.indices i j.succ))))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0))))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0))) (ThreeRootOrder318.Order (fun j => a (FourRootPivot318.indices i j.succ)))))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial (a (FourRootPivot318.indices i 0)))) := by\n  exact ActualRootPivotCoordinates318.regroup_generator a i\n\n/-- Diagnostic proof partition: native root compatibility for the explicit\nnested casts returned by transportProperty. Equality with the separately\nrw-generated transportedRegroup is not asserted here. -/\nprivate theorem explicitCastRegroupRoot\n    {R : Type*} [CommRing R] (a : Fin 4 → R) (i : Fin 4)\n    (p : R) (q : Fin 3 → R)\n    (hp : p = a (FourRootPivot318.indices i 0))\n    (hq : q = fun j => a (FourRootPivot318.indices i j.succ)) :\n    (Eq.mpr\n      (congrArg (fun r : R => FourRootOrder318.Order a ≃ₐ[R]\n        TensorProduct R (QuadraticPresentation318.RootRing r) (ThreeRootOrder318.Order q)) hp)\n      (Eq.mpr\n        (congrArg (fun v : Fin 3 → R => FourRootOrder318.Order a ≃ₐ[R]\n          TensorProduct R\n            (QuadraticPresentation318.RootRing (a (FourRootPivot318.indices i 0)))\n            (ThreeRootOrder318.Order v)) hq)\n        (FourRootPivot318.regroup a i)))\n        (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing p)\n        (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q)))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial p)) := by\n  exact transportProperty\n    (fun p q => FourRootOrder318.Order a ≃ₐ[R]\n      TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n    (fun p q e => e (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing p)\n        (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q)))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial p)))\n    hp hq (FourRootPivot318.regroup a i)\n    (ActualRootPivotCoordinates318.regroup_generator a i)\n\n/-- Root compatibility for the same regrouping equivalence transported\nalong the two parameter equalities used in sourceRegroup. -/\nprivate theorem transportedRegroupRoot\n    {R : Type*} [CommRing R] (a : Fin 4 → R) (i : Fin 4)\n    (p : R) (q : Fin 3 → R)\n    (hp : p = a (FourRootPivot318.indices i 0))\n    (hq : q = fun j => a (FourRootPivot318.indices i j.succ)) :\n    (transportedRegroup a i p q hp hq)\n        (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing p)\n        (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q)))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial p)) := by\n  exact transportProperty\n    (fun p q => FourRootOrder318.Order a ≃ₐ[R]\n      TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n    (fun p q e => e (FourRootOrderSigns318.generator a i) =\n      (@algebraMap (QuadraticPresentation318.RootRing p)\n        (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q))\n        (inferInstance : CommSemiring (QuadraticPresentation318.RootRing p))\n        (inferInstance : Semiring\n          (TensorProduct R (QuadraticPresentation318.RootRing p) (ThreeRootOrder318.Order q)))\n        inferInstance)\n        (AdjoinRoot.root (QuadraticPresentation318.polynomial p)))\n    hp hq (FourRootPivot318.regroup a i)\n    (ActualRootPivotCoordinates318.regroup_generator a i)\n\n'
CANDIDATE_REGROUP_PROOF = '  rw [baseCoordinate_root]\n  have ht : FourRootActualFractionField318.polynomialEquivalence b\n      (FourRootAffineCoordinateRing318.coordinate b (some i)) =\n      FourRootAffineTensorPresentation318.toTensor b\n        (FourRootAffineCoordinateRing318.coordinate b (some i)) := rfl\n  rw [sourceRegroup, AlgEquiv.trans_apply, ht,\n    FourRootAffineTensorPresentation318.toTensor_root]\n  have h0 : LinearRootCoordinate318.parameter (1:ℂˣ) (b i) =\n      FourRootAffineTensorPresentation318.radicand b (FourRootPivot318.indices i 0) := by\n    change (Polynomial.C (1:ℂ):ℂ[X]) * (X-C (b i)) =\n      X-C (b (FourRootPivot318.indices i 0))\n    rw [Polynomial.C_1,one_mul,FourRootPivot318.indices_zero]\n  have hother : FiniteBranchChart318.other twists (otherBranch b i) =\n      (fun j => FourRootAffineTensorPresentation318.radicand b (FourRootPivot318.indices i j.succ)) := by\n    funext j\n    change (Polynomial.C (1:ℂ):ℂ[X]) * (X-C (b (FourRootPivot318.indices i j.succ))) =\n      X-C (b (FourRootPivot318.indices i j.succ))\n    rw [Polynomial.C_1,one_mul]\n  exact transportedRegroupRoot (FourRootAffineTensorPresentation318.radicand b) i\n    (LinearRootCoordinate318.parameter (1:ℂˣ) (b i))\n    (FiniteBranchChart318.other twists (otherBranch b i)) h0 hother\n'
SCRATCH_SHAS = {'imports_only': 'f1897fcc4789b38cf94da1e8ce4cbf9876709002c2d54252ba63ae7f6f4dbb59', 'complete_candidate_prefix': '3dda693c2bb1bcc570de65db7d27662b219a66c0a6b7aababd85137c823729c7'}

def frozen_candidate(source):
    require(digest(source) == SOURCE_SHA, 'Frozen original source changed')
    candidate = CANDIDATE_FIXTURE.read_text()
    require(digest(candidate) == CANDIDATE_SOURCE_SHA, 'Reviewed candidate changed')
    require(candidate.count(GENERIC_HELPER) == 1 and
            candidate.count(CANDIDATE_TARGET_PROOF) == 1 and
            candidate.count(SQUARE_HELPER) == 1 and
            candidate.count(TRANSPORT_HELPER) == 1 and
            candidate.count(CANDIDATE_SQUARE_PROOF) == 1 and
            candidate.count(CANDIDATE_REGROUP_PROOF) == 1, 'Candidate boundaries changed')
    restored = candidate.replace(GENERIC_HELPER, '', 1).replace(SQUARE_HELPER, '', 1).replace(TRANSPORT_HELPER, '', 1).replace(
        CANDIDATE_TARGET_PROOF, ORIGINAL_TARGET_PROOF, 1).replace(
        CANDIDATE_SQUARE_PROOF, ORIGINAL_SQUARE_PROOF, 1).replace(
        CANDIDATE_REGROUP_PROOF, ORIGINAL_REGROUP_PROOF, 1)
    require(restored == source, 'Candidate changes exceed reviewed helper/proof substitution')
    return candidate

def scope_declaration(text, target):
    """Put scoped options before an attached doc comment, not between it and the declaration."""
    require(text.count(target) == 1, 'Candidate target declaration boundary changed')
    start = text.index(target)
    doc = re.search(r'(?m)^/--(?:(?!-/)[\s\S])*-/\s*\Z', text[:start])
    if doc is not None:
        start = doc.start()
    return text[:start] + SUBSTEP_SCOPE + text[start:]

def compiler_outcome(row):
    """Process outcome only: checkpoints and exit zero do not establish audited acceptance."""
    if row.get('limit'):
        return 'LIMIT_REACHED_NO_ACCEPTANCE'
    if row['exit_code'] == 0:
        return 'EXIT_ZERO_NO_AUDIT_OR_ADMISSION'
    return 'COMPILER_FAILURE_NO_ACCEPTANCE'

def candidate_specimen(candidate):
    require(digest(candidate) == CANDIDATE_SOURCE_SHA, 'Reviewed candidate changed')
    pattern = r'#eval \(do\n  let out ← IO.getStdout\n  out.putStrLn "PEL_KAEHLER_CHECKPOINT ([^"]+)"\n  out.flush : IO Unit\)'
    require(len(re.findall(pattern, candidate)) == 21, 'Candidate checkpoint count changed')
    def marker(label):
        return 'run_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n  out.putStrLn "KAEHLER_CANDIDATE_'+label+'"\n  out.flush'
    imports = candidate[:candidate.index('#eval')]
    text = re.sub(pattern, lambda m: marker(m[1]), candidate)
    text = text.replace(imports, imports+'set_option stderrAsMessages false\n', 1)
    text = text.replace('public section\n', 'public section\nset_option profiler true\nset_option profiler.threshold 10\n', 1)
    text = text.replace(GENERIC_HELPER, marker('BEFORE_GENERIC_HELPER')+'\n'+
        SUBSTEP_SCOPE+GENERIC_HELPER+marker('AFTER_GENERIC_HELPER')+'\n', 1)
    text = text.replace(SQUARE_HELPER, marker('BEFORE_MAPPED_SQUARE')+'\n'+
        SUBSTEP_SCOPE+SQUARE_HELPER+marker('AFTER_MAPPED_SQUARE')+'\n', 1)
    text = text.replace(TRANSPORT_HELPER, marker('BEFORE_TRANSPORT_HELPER')+'\n'+
        SUBSTEP_SCOPE+TRANSPORT_HELPER+marker('AFTER_TRANSPORT_HELPER')+'\n', 1)
    for target in ['lemma source_coordinate_original:', 'lemma exact_square:']:
        text = scope_declaration(text, target)
    return text

PREFIX_RAW_SHA = '10af81b32380b134441d57f1b6b176bcdd93d2bc788a860ef50c9e62e7560363'
PREFIX_END = 'end FourRootActualBranchKaehler318\n'
PREFIX_CHECKPOINT = '/-- Diagnostic proof partition: native root compatibility'
PREFIX_MARKER = '/-- Diagnostic proof partition: native root compatibility'

def prefix_specimen(candidate):
    """Complete native-root specialization prefix, not original production.

    Cut after the native root-law specialization; both transported proof theorems excluded.
    Close only the named namespace; normal process exit must classify the prefix.
    Full candidate reversal remains checked by frozen_candidate in specimens.
    """
    require(digest(candidate) == CANDIDATE_SOURCE_SHA, 'Reviewed candidate changed')
    require(candidate.count(PREFIX_CHECKPOINT) == 1, 'Prefix checkpoint boundary changed')
    raw_prefix = candidate[:candidate.index(PREFIX_CHECKPOINT)]
    require(digest(raw_prefix) == PREFIX_RAW_SHA, 'Reviewed raw prefix changed')
    require('private def transportedRegroup' in raw_prefix and
            'private theorem nativeRegroupRootSpecialization' in raw_prefix and
            'private theorem explicitCastRegroupRoot' not in raw_prefix and
            'private theorem transportedRegroupRoot' not in raw_prefix and
            'variable (b:Fin 4' not in raw_prefix,
            'Prefix declaration scope changed')
    text = candidate_specimen(candidate)
    require(text.count(PREFIX_MARKER) == 1, 'Instrumented prefix boundary changed')
    return text[:text.index(PREFIX_MARKER)] + PREFIX_END

def specimens(source):
    control = control_specimens(source)
    result = {'imports_only': control['imports_only'],
        'complete_candidate_prefix': prefix_specimen(frozen_candidate(source))}
    require({k:digest(v) for k,v in result.items()} == SCRATCH_SHAS,
        'Reviewed candidate specimen changed')
    return result


def baseline_dependency_evidence(output, result, successful_prefix):
    """Read-only authentication of the one direct import from the audited baseline.

    This repeats cache provenance checks against the same job's copied library;
    it does not compile, copy, repair, or promote any artifact.
    """
    missing = DEPENDENCIES - set(successful_prefix)
    require(missing == set(BASELINE_SOURCES), 'Unexpected dependency outside successful prefix')
    plan = ci.derive_plan()
    require(result.get('baseline_snapshot') == plan['snapshot'] and
            result.get('baseline_modules') == len(plan['module_order']),
            'Own normal baseline identity changed')
    require(missing <= set(plan['module_keys']), 'Required import is not an accepted baseline module')
    source_bindings = {}
    for name, expected in BASELINE_SOURCES.items():
        source = ci.PROJECT / (name + '.lean')
        require(sha(source) == expected, 'Frozen baseline source changed: ' + name)
        source_bindings[name] = expected
    cache = ci.ROOT / '.cache/progress-ci'
    receipt_path = cache / 'receipt.json'
    receipt = json.loads(receipt_path.read_text())
    expected_receipt = {'schema': ci.SCHEMA, 'status': 'PASS', 'base': plan['base'],
        'snapshot': plan['snapshot'], 'scope': 'Complete source coverage and recursive axiom audit'}
    require(all(receipt.get(k) == v for k, v in expected_receipt.items()),
            'Audited baseline receipt identity changed')
    require(isinstance(receipt.get('audit_result_sha256'), str) and
            re.fullmatch(r'[0-9a-f]{64}', receipt['audit_result_sha256']),
            'Audited baseline result reference missing')
    needed = set()
    def visit(name):
        if name in needed:
            return
        for dependency in plan['dependencies'][name]:
            visit(dependency)
        needed.add(name)
    for name in sorted(missing):
        visit(name)
    built, artifacts = {}, {}
    for name in plan['module_order']:
        if name not in needed:
            continue
        entry = receipt.get('modules', {}).get(name)
        require(ci.reusable(entry, name, plan, cache / 'lib', built),
                'Missing, stale or corrupt audited baseline artifact: ' + name)
        require(ci.artifact_hashes(output / 'lib', name) == entry['files'],
                'Same-run copied baseline artifact differs: ' + name)
        built[name] = entry
        for suffix, value in entry['files'].items():
            artifacts['lib/' + name.replace('.', '/') + suffix] = value
    return {'scope': 'AUTHENTICATED_REUSED_BASELINE_NOT_FRESH_COMPILATION',
        'receipt_sha256': sha(receipt_path), 'audit_result_sha256': receipt['audit_result_sha256'],
        'snapshot': plan['snapshot'], 'base': plan['base'], 'source_bindings': source_bindings,
        'required_modules': [n for n in plan['module_order'] if n in needed],
        'module_keys': {n: plan['module_keys'][n] for n in plan['module_order'] if n in needed},
        'same_run_artifacts': artifacts}

def validate(packet, output, hosted=True):
    if hosted:
        require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
                'Hosted Actions only')
    require(sha(Path(runner.__file__)) == RUNNER_SHA and
            sha(Path(runner.original.__file__)) == RUNNER_LIMITS_SHA, 'Bounded runner changed')
    require(tuple(ci.FLAGS) == EXPECTED_FLAGS, 'Strict compiler flags changed')
    require(runner.original.SECONDS == SECONDS and runner.original.MAX_BYTES == MAX_BYTES,
            'Existing scratch caps changed')
    require(packet.name == PACKET, 'Wrong activation packet')
    require(sha(packet/'intake.json') == INTAKE_SHA and sha(packet/'APPLICATION.json') == APPLICATION_SHA,
            'Frozen packet metadata changed')
    intake = json.loads((packet/'intake.json').read_text())
    for name, item in intake['files'].items():
        require(sha(packet/name) == item['sha256'], 'Source binding changed: ' + name)
    rp = output/'RESULT.json'
    require(rp.is_file(), 'Fresh own normal result unavailable')
    result = json.loads(rp.read_text())
    require(result.get('packet') == PACKET and result.get('packet_sha256') == INTAKE_SHA,
            'Own normal result identity changed')
    require(result.get('status') == 'FAILED', 'Own normal result is not the expected failure')
    index = intake['order'].index(MODULE)
    rows = result.get('commands', [])
    require([x.get('module') for x in rows] == intake['order'][:index+1], 'Own normal frontier changed')
    require(all(x.get('exit_code') == 0 for x in rows[:-1]) and rows[-1].get('exit_code') == 124,
            'Own normal outcomes changed')
    baseline_evidence = baseline_dependency_evidence(output, result, intake['order'][:index])
    lp = output/'logs'/(MODULE+'.log')
    require(lp.is_file() and 'WALL_CLOCK_LIMIT_EXCEEDED' in lp.read_text(), 'Exact own timeout absent')
    no_compiled(output/'lib', MODULE)
    artifacts = dict(baseline_evidence['same_run_artifacts'])
    for row in rows[:-1]:
        name = row['module']
        require((output/'lib'/(name+'.olean')).is_file(), 'Own normally compiled predecessor missing: '+name)
        for suffix in COMPILED_SUFFIXES:
            p = output/'lib'/(name+suffix)
            if p.is_file():
                artifacts[str(p.relative_to(output))] = sha(p)
    return specimens((packet/(MODULE+'.lean')).read_text()), {
        'normal_result_sha256':sha(rp), 'normal_failure_log_sha256':sha(lp),
        'successful_prefix_modules':[r['module'] for r in rows[:-1]],
        'same_run_predecessor_artifacts':artifacts,
        'authenticated_reused_baseline':baseline_evidence}

def main():
    p = argparse.ArgumentParser();p.add_argument('packet', choices=[PACKET]);a = p.parse_args()
    # The hosted guard precedes all writes, even a diagnostic SKIP receipt.
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and bool(os.environ.get('RUNNER_TEMP')),
            'Hosted Actions only')
    packet = ci.ROOT/'quartics/quartic-318-326/proof/experiments'/a.packet
    output = ci.ROOT/'build/progress-experiments'/a.packet
    logs = output/LABEL;logs.mkdir(parents=True, exist_ok=False)
    base = {'scope':'NON_ADMITTED_KAEHLER_NATIVE_ROOT_SPECIALIZATION_PREFIX_DIFFERENTIAL',
            'packet':PACKET,'packet_intake_sha256':INTAKE_SHA,'packet_application_sha256':APPLICATION_SHA,
            'original_source_sha256':SOURCE_SHA,'candidate_source_sha256':CANDIDATE_SOURCE_SHA,
            'scratch_source_sha256':SCRATCH_SHAS,
            'prefix_raw_sha256':PREFIX_RAW_SHA,'prefix_of':'named transport-definition candidate, not original production',
            'prefix_last_declaration':'nativeRegroupRootSpecialization','target_declaration_included':False,
            'actual_head':os.environ.get('GITHUB_SHA'),'actual_run':os.environ.get('GITHUB_RUN_ID'),
            'production_source_changed':False,'production_limits_changed':False,
            'checkpoints_are_traversal_only':True,'timeouts_may_hide_deferred_errors':True,
            'full_packet_accepted':False,'proof_acceptance':False,'writes_olean':False}
    try:
        text, evidence = validate(packet, output)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        ci.write_json(logs/'DIAGNOSTIC.json', dict(base,status='SKIPPED',reason=str(exc),probe_executed=False))
        print('Kaehler diagnostic skipped: '+str(exc),flush=True)
        return
    env, version = ci.environment(ci.PROJECT, output/'lib')
    rows = []
    with tempfile.TemporaryDirectory(prefix='kaehler-timeout-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as t:
        root=Path(t);no_compiled(root);no_compiled(output/'lib', MODULE)
        for name, specimen in text.items():
            source=root/(name+'.lean');source.write_text(specimen)
            (logs/(name+'.lean.txt')).write_text(specimen)
            row=runner.bounded_memory(source,root,env,logs/(name+'.log'))
            row['compiler_outcome']=compiler_outcome(row); rows.append(row)
            no_compiled(root);no_compiled(output/'lib', MODULE)
            if name == 'imports_only' and (row['exit_code'] != 0 or row.get('limit') or
                'KAEHLER_COMMAND_IMPORTS_ONLY_COMPLETE' not in (logs/(name+'.log')).read_text()):
                break
        require(sha(output/'RESULT.json') == evidence['normal_result_sha256'], 'Production result changed')
        require(sha(output/'logs'/(MODULE+'.log')) == evidence['normal_failure_log_sha256'], 'Production log changed')
        require(sha(packet/(MODULE+'.lean')) == SOURCE_SHA, 'Production source changed')
        require(baseline_dependency_evidence(output, json.loads((output/'RESULT.json').read_text()),
                evidence['successful_prefix_modules']) == evidence['authenticated_reused_baseline'],
                'Audited baseline provenance changed during probe')
        for name, expected in evidence['same_run_predecessor_artifacts'].items():
            require(sha(output/name) == expected, 'Compiled predecessor changed: '+name)
    ci.write_json(logs/'DIAGNOSTIC.json',dict(base,status='RECORDED',probe_executed=True,
        toolchain=version,seconds_per_probe=SECONDS,probe_wall_cap_sum_seconds=2*SECONDS,
        bytes_per_probe=MAX_BYTES,strict_flags=list(EXPECTED_FLAGS),evidence=evidence,variants=rows,
        interpretation='Fresh original timeout and own prefix plus the unchanged imports-only control precede a declaration-complete native-root specialization prefix of the candidate, not original production. The second probe ends after nativeRegroupRootSpecialization and closes its namespace; both transported proof theorems and every concrete b/i declaration are excluded. Only the native root-law specialization is included, not a transported compatibility theorem or bridge equality. This replaces the full-candidate second probe, never adds a third probe. Only full process exit and output can establish this prefix compile outcome. Checkpoints and profiles are traversal-only, including recovery; timeouts may hide deferred errors. Even prefix exit zero establishes neither the target/full candidate nor production audit, admission or proof acceptance. Same strict kernel/no-olean controls and two-probe budget; instrumentation may affect timing.'))

if __name__ == '__main__':
    main()
