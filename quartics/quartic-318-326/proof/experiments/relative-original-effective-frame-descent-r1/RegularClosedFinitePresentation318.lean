module
public import OriginalRegularClosedCharts318
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public section
noncomputable section
namespace RegularClosedFinitePresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) (h : OriginalRegularClosedCharts318.Property p)
/-- Full Cartier charts imply finite presentation of the actual closed
map over arbitrary rings. No Noetherian hypothesis is inserted. -/
lemma finitePresentation : LocallyOfFinitePresentation p := by
  classical
  choose A j hj hx c z hs hr using h
  letI : ∀ x, IsOpenImmersion (j x) := hj
  let U : X.OpenCover :=
    { I₀ := X
      X := fun x => Spec (A x)
      f := j
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => ⟨x,hx x⟩,fun x => inferInstance⟩ }
  apply IsZariskiLocalAtTarget.of_openCover U
  intro x
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c x})))
  letI : LocallyOfFinitePresentation q := by
    apply LocallyOfFinitePresentation.SpecMap_iff.mpr
    apply RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact ⟨{c x},by simp only [Finset.coe_singleton]⟩
  have hf : LocallyOfFinitePresentation ((hs x).flip.isoPullback.inv ≫ q) := inferInstance
  simpa only [(hs x).flip.isoPullback_inv_snd] using hf
end RegularClosedFinitePresentation318
