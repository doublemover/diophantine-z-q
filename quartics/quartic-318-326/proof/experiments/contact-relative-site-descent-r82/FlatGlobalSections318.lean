module
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public section
noncomputable section
namespace FlatGlobalSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S T : Scheme.{u}} (p : X ⟶ S) (b : T ⟶ S)

lemma appLE_top (f : X ⟶ S) : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
  simp [Scheme.Hom.appLE]

/-- Actual flat base change of global functions for a proper source over
an affine base is the canonical pushout square, by the library's finite
open-cover equalizer theorem. -/
lemma global_pushout [IsAffine S] [IsAffine T] [IsProper p] [Flat b] :
    IsPushout p.appTop b.appTop (pullback.fst p b).appTop (pullback.snd p b).appTop := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback p b) (US := ⊤) (UT := ⊤) (UX := ⊤)
    (UY := ⊤) (by simp) (by simp) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T) isCompact_univ isQuasiSeparated_univ
  have hh := (isIso_pushoutSection_iff (IsPullback.of_hasPullback p b)
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)).mp h
  simpa only [appLE_top] using hh

/-- If the original structural global-section map is an isomorphism, so
is the actual structural map after any flat affine base change. -/
lemma baseChange_appTop_isIso [IsAffine S] [IsAffine T] [IsProper p] [Flat b]
    [IsIso p.appTop] : IsIso (pullback.snd p b).appTop :=
  (global_pushout p b).isIso_inr_of_isIso
/-- The same canonical comparison on every affine open of an arbitrary
base test, retaining the entire inverse-image open on the source. -/
lemma baseChange_app_isIso [IsAffine S] [IsProper p] [Flat b] [IsIso p.appTop]
    (U : T.Opens) (hU : IsAffineOpen U) : IsIso ((pullback.snd p b).app U) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback p b) (US := ⊤) (UT := U) (UX := ⊤)
    (UY := (pullback.snd p b) ⁻¹ᵁ U) (by simp) (by simp) (by simp)
    (isAffineOpen_top S) hU isCompact_univ isQuasiSeparated_univ
  have hh := (isIso_pushoutSection_iff (IsPullback.of_hasPullback p b)
    (US := ⊤) (UT := U) (UX := ⊤) (UY := (pullback.snd p b) ⁻¹ᵁ U)
    (by simp) (by simp) (by simp)).mp h
  let : IsIso (p.appLE ⊤ ⊤ (by simp)) := by rw [appLE_top]; infer_instance
  have hi := hh.isIso_inr_of_isIso
  simpa only [Scheme.Hom.appLE_eq_app] using hi
end FlatGlobalSections318
