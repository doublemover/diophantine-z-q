module
public import ContactOriginalLinearOpenChart318
public section
noncomputable section
namespace ContactLinearFiberDisjoint318
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev linearForm := ContactOriginalLinearOpenChart318.linearForm
@[expose] def locus (a : ℚ) : (ProjectiveJLine318.scheme ℚ).Opens :=
  Proj.basicOpen (ProjectiveJLine318.grading ℚ) (linearForm a)
/-- Distinct rational linear forms have disjoint vanishing fibers on the
actual projective line. No geometric-point labels or chart shortcuts. -/
lemma pair_cover (a b : ℚ) (hab : a≠b) : locus a⊔locus b=⊤ := by
  classical
  ext p
  change (p∈locus a ∨ p∈locus b) ↔ True
  apply iff_true_intro
  by_contra h
  have ha : linearForm a∈p.asHomogeneousIdeal := by
    by_contra ha
    exact h (Or.inl ha)
  have hb : linearForm b∈p.asHomogeneousIdeal := by
    by_contra hb
    exact h (Or.inr hb)
  let L : Submodule ℚ (MvPolynomial (Fin 2) ℚ) := p.asHomogeneousIdeal.toIdeal.restrictScalars ℚ
  have hd : (b-a) • (X 1 : MvPolynomial (Fin 2) ℚ)∈L := by
    have he : (b-a) • (X 1 : MvPolynomial (Fin 2) ℚ)=linearForm a-linearForm b := by
      dsimp only [linearForm,ContactOriginalLinearOpenChart318.linearForm]
      module
    rw [he]
    exact L.sub_mem ha hb
  have hx1 : (X 1 : MvPolynomial (Fin 2) ℚ)∈L := by
    have hba : b-a≠0 := sub_ne_zero.mpr hab.symm
    have hm := L.smul_mem (b-a)⁻¹ hd
    simpa only [smul_smul,inv_mul_cancel₀ hba,one_smul] using hm
  have hx0 : (X 0 : MvPolynomial (Fin 2) ℚ)∈L := by
    have hm := L.add_mem ha (L.smul_mem a hx1)
    simpa only [linearForm,ContactOriginalLinearOpenChart318.linearForm,sub_add_cancel] using hm
  have hp : p∈⨆ i : Fin 2, Proj.basicOpen (ProjectiveJLine318.grading ℚ) (X i) := by
    rw [JLineAtlas318.standard_opens_cover]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  fin_cases i
  · exact hi hx0
  · exact hi hx1
lemma at_most_one (p : ProjectiveJLine318.scheme ℚ) {a b : ℚ}
    (ha : p∉locus a) (hb : p∉locus b) : a=b := by
  by_contra hab
  have hp : p∈locus a⊔locus b := by rw [pair_cover a b hab]; trivial
  exact hp.elim ha hb
end ContactLinearFiberDisjoint318
