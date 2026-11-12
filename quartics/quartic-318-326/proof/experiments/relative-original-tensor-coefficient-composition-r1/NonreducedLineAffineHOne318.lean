module
public import NonreducedLineOpenLifting318
public section
noncomputable section
namespace NonreducedLineAffineHOne318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open LineSheafClass318 LocalSheafCohomologySections318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} (L : Line X)

/-- Actual local Ext-defined H1 of the original GLOBAL line vanishes on
every actual affine open of the original arbitrary scheme, including nonreduced schemes. It is not defined
as the cohomology of an independently chosen affine replacement. -/
theorem eq_zero (U : X.Opens) (hU : IsAffineOpen U)
    (x : (NonreducedLineRestriction318.additive L).H' 1 U) : x = 0 := by
  let F := NonreducedLineRestriction318.additive L
  let i := Injective.ι F
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ (generator U) hS x
    (Ext.eq_zero_of_injective _) (n₀:=0) rfl
  obtain ⟨s,hs⟩ := NonreducedLineOpenLifting318.surjective_affine L S hS (Iso.refl _) U hU
    (zeroEquiv S.X₃ U y)
  let z : S.X₂.H' 0 U := (zeroEquiv S.X₂ U).symm s
  have hz : z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
    apply (zeroEquiv S.X₃ U).injective
    rw [zeroEquiv_naturality]
    simpa only [z,Equiv.apply_symm_apply] using hs
  rw [← hy,← hz,Ext.comp_assoc_of_second_deg_zero,hS.comp_extClass,Ext.comp_zero]
end NonreducedLineAffineHOne318
