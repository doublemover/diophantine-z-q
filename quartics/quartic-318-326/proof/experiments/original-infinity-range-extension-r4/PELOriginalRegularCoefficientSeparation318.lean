module
public import FourRootSignCoefficientExtraction318
public section
noncomputable section
namespace PELOriginalRegularCoefficientSeparation318
open scoped BigOperators
open FourRootSignCoefficientExtraction318
open PELOriginalRegularCoordinateAlgebra318
open PELOriginalContactRootFunctions318 PELOriginalCommonContactBase318

/-- Literal polynomial coefficients of the sixteen squarefree-root
monomials are determined by values on the actual original regular source.
This does not assume a function field, scheme algebraization, or degree. -/
theorem coefficients_zero (c : Mask → Polynomial ℂ)
    (h : ∀ x : OriginalRegular,
      (∑ m : Mask, (c m).eval (base x.val) * monomial (roots x.val) m) = 0) :
    ∀ m, c m = 0 := by
  intro m
  apply polynomial_zero branches (c m)
  intro t ht
  let z : Fin 4 → ℂ := fun i => Complex.sqrt (t - branches i)
  have hzsq : ∀ i, z i ^ 2 = t - branches i := by
    intro i
    exact Complex.sq_sqrt _
  have hz : ∀ i, z i ≠ 0 := by
    intro i hi
    have hzi := hzsq i
    rw [hi,zero_pow (by decide : (2:ℕ) ≠ 0)] at hzi
    exact ht i (sub_eq_zero.mp hzi.symm)
  have hD : FourCharacterRootRecombination318.denominator branches t ≠ 0 := by
    simp only [FourCharacterRootRecombination318.denominator,
      FourCharacterRootRecombination318.product,FourCharacterRootRecombination318.linear,
      mul_ne_zero_iff,sub_ne_zero]
    exact ⟨⟨⟨ht 0,ht 1⟩,ht 2⟩,ht 3⟩
  apply FourRootSignCoefficientExtraction318.coefficients_zero
    (fun n => (c n).eval t) z hz _ m
  intro s
  have hs : ∀ i, signed z s i ^ 2 = t - branches i := by
    intro i
    cases hi : s i <;> simp [signed,hi,hzsq]
  obtain ⟨x,hx,hbase,hroots⟩ := all_roots t hD (signed z s) hs
  have hactual := h ⟨x,hx⟩
  rw [hbase] at hactual
  have hr : roots x = signed z s := funext hroots
  rw [hr] at hactual
  exact hactual
end PELOriginalRegularCoefficientSeparation318
