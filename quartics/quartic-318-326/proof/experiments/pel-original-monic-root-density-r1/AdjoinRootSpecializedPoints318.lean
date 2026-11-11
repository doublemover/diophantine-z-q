module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace AdjoinRootSpecializedPoints318
open Polynomial AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] (Q : Polynomial R) (v : R →+* ℂ)

/-- All evaluations of the entire monogenic order over the SPECIFIED
base evaluation, not just evaluations chosen from one field component. -/
abbrev Points := {e : AdjoinRoot Q →+* ℂ // e.comp (AdjoinRoot.of Q) = v}
abbrev Roots := {z : ℂ // (Q.map v).eval z = 0}

lemma point_root (e : Points Q v) : (Q.map v).eval (e.1 (AdjoinRoot.root Q)) = 0 := by
  have h := congrArg e.1 (AdjoinRoot.eval₂_root Q)
  rw [Polynomial.hom_eval₂,e.2,map_zero] at h
  simpa only [Polynomial.eval_map] using h

/-- The genuine AdjoinRoot universal property gives BOTH inverse maps,
with the original primitive generator as the exact root coordinate. -/
@[expose] def rootEquiv : Points Q v ≃ Roots Q v where
  toFun e := ⟨e.1 (AdjoinRoot.root Q),point_root Q v e⟩
  invFun z := ⟨AdjoinRoot.lift v z.1 (by simpa only [Polynomial.eval_map] using z.2),
    AdjoinRoot.lift_comp_of _⟩
  left_inv e := by
    apply Subtype.ext
    apply AdjoinRoot.ringHom_ext
    · rw [AdjoinRoot.lift_comp_of,e.2]
    · exact AdjoinRoot.lift_root
        (by simpa only [Polynomial.eval_map] using point_root Q v e)
  right_inv z := Subtype.ext (AdjoinRoot.lift_root _)

abbrev SchemePoints :=
  {q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (AdjoinRoot Q)) //
    q ≫ Spec.map (CommRingCat.ofHom (AdjoinRoot.of Q)) =
      Spec.map (CommRingCat.ofHom v)}

@[expose] def toScheme (e : Points Q v) : SchemePoints Q v :=
  ⟨Spec.map (CommRingCat.ofHom e.1),by
    rw [←Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) e.2⟩

/-- These are exactly the actual Scheme-valued points over the fixed
base point, using Spec full faithfulness rather than point-set analogy. -/
theorem toScheme_bijective : Function.Bijective (toScheme Q v) := by
  constructor
  · intro e f h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact congrArg (fun φ => φ.hom) (Spec.map_injective hh)
  · rintro ⟨q,hq⟩
    obtain ⟨φ,rfl⟩ := Spec.map_surjective q
    have hφ : φ.hom.comp (AdjoinRoot.of Q) = v := by
      rw [←Spec.map_comp] at hq
      exact congrArg (fun f => f.hom) (Spec.map_injective hq)
    exact ⟨⟨φ.hom,hφ⟩,Subtype.ext rfl⟩

@[expose] def schemeEquiv : Points Q v ≃ SchemePoints Q v :=
  Equiv.ofBijective (toScheme Q v) (toScheme_bijective Q v)

@[expose] def schemeRootEquiv : SchemePoints Q v ≃ Roots Q v :=
  (schemeEquiv Q v).symm.trans (rootEquiv Q v)
@[simp] theorem schemeRootEquiv_toScheme (e : Points Q v) :
    (schemeRootEquiv Q v (toScheme Q v e)).1 = e.1 (AdjoinRoot.root Q) := by
  change ((rootEquiv Q v) ((schemeEquiv Q v).symm ((schemeEquiv Q v) e))).1 = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- When the specified base evaluation fixes C, every one of these
actual Scheme points fixes the SAME original complex scalar structure. -/
@[reassoc] theorem over_complex [Algebra ℂ R]
    (hc : ∀ c : ℂ, v (algebraMap ℂ R c) = c) (q : SchemePoints Q v) :
    q.1 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjoinRoot Q))) = 𝟙 _ := by
  have hs : Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjoinRoot Q))) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of Q)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) := by
    rw [←Spec.map_comp]
    rfl
  rw [hs,←Category.assoc,q.2,←Spec.map_comp,←Spec.map_id]
  congr 1
  ext c
  exact hc c
end AdjoinRootSpecializedPoints318
