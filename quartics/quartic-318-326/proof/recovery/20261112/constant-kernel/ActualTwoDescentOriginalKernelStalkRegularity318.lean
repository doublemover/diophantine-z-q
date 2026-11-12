module
public import ActualTwoDescentProperClosedFieldConstants318
public section
noncomputable section
namespace ActualTwoDescentOriginalKernelStalkRegularity318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalCommonPolarizationLattices318
open ActualTwoDescentOriginalDoublePolePointLattices318 ActualTwoDescentOriginalSchemeInfinityPole318
variable {K : Type*} [Field K] [CharZero K]
local instance (n : K) : Nonempty (⊤ : (originalCubicScheme n).Opens) := ⟨⟨genericPoint _,trivial⟩⟩
lemma weight_ne (n : K) (x : originalCubicScheme n) : weight n x≠0 := by
  classical
  unfold weight
  split_ifs
  · exact pow_ne_zero 2 (inv_ne_zero (actual_scheme_origin_parameter_nonzero n))
  · exact one_ne_zero
/-- Both coefficient and inverse are regular at EVERY actual scheme
point, including O, all three root points, and the generic point. -/
lemma regular (n : K) (a : (SchemeFunctionField n)ˣ)
    (ha : ∀ x f,f∈pointImage n x ↔ (a:SchemeFunctionField n)*f∈pointImage n x)
    (x : originalCubicScheme n) :
    (∃ r : (originalCubicScheme n).presheaf.stalk x,
      algebraMap _ (SchemeFunctionField n) r=(a:SchemeFunctionField n)) ∧
    (∃ r : (originalCubicScheme n).presheaf.stalk x,
      algebraMap _ (SchemeFunctionField n) r=(↑a⁻¹:SchemeFunctionField n)) := by
  apply ActualTwoDescentFractionalLineStabilizerRegularity318.regular (weight n x) (weight_ne n x) a
  intro f
  simpa only [actual_image,lattice] using ha x f
/-- Actual global regular UNIT, not only an everywhere integral value. -/
lemma global_unit (n : K) (a : (SchemeFunctionField n)ˣ)
    (ha : ∀ x f,f∈pointImage n x ↔ (a:SchemeFunctionField n)*f∈pointImage n x) :
    ∃ s : Γ(originalCubicScheme n,⊤)ˣ,
      (originalCubicScheme n).germToFunctionField ⊤ (s:Γ(originalCubicScheme n,⊤))=
        (a:SchemeFunctionField n) :=
  ActualTwoDescentIntegralRationalRegularSections318.global_unit (originalCubicScheme n) a
    (regular n a ha)

end ActualTwoDescentOriginalKernelStalkRegularity318
