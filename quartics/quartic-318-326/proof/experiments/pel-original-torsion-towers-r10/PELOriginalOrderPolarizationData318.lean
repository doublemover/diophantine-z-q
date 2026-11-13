module
public import PELOriginalOrderPowerCoefficients318
public import PELOriginalBalancedLineSquare318
public import PELOriginalOrderSchemeMorphism318
public section
noncomputable section
namespace PELOriginalOrderPolarizationData318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELPrincipalOrderCoordinates318 PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev I := NonemptyIndex τ hτ
abbrev O := opens τ hτ
abbrev act (a : order) := PELOriginalOrderSchemeMorphism318.morphism τ hτ a
lemma act_point (a : order) (z : ComplexVectors) :
    PELOriginalCandidateComplexPoints318.candidateComplexPoint τ hτ (projection (P τ) z)≫act τ hτ a=
      PELOriginalCandidateComplexPoints318.candidateComplexPoint τ hτ (projection (P τ) (linear a z)) :=
  PELOriginalOrderSchemeMorphism318.original_point_action τ hτ a z

/-- Independently regular coefficients for actual order/complement
pullbacks. No line comparison, dual endomorphism or Rosati identification
is part of the input. -/
structure Data where
  lineData : PELOriginalBalancedLineData318.Data τ hτ
  coefficient : ∀ (a : order) (i j k : I τ hτ),Γ(candidate τ hτ,O τ hτ k)
  coefficient_value : ∀ a i j k z,z∈domain τ hτ (O τ hτ k) →
    value τ hτ (O τ hτ k) (coefficient a i j k) z=
      (lineData.g i (linear a z)^2*lineData.g j (linear (complement a) z)^2)/
        lineData.g k z^(2*degree a)
variable (D : Data τ hτ) (a : order)
abbrev Index := I τ hτ × I τ hτ × I τ hτ
@[expose] def chart (b : Index τ hτ) : (candidate τ hτ).Opens :=
  O τ hτ b.1 ⊓ (act τ hτ a ⁻¹ᵁ O τ hτ b.2.1) ⊓
    (act τ hτ (complement a) ⁻¹ᵁ O τ hτ b.2.2)
lemma covers : (⊤ : (candidate τ hτ).Opens)≤⨆ b,chart τ hτ a b := by
  intro x hx
  obtain ⟨k,hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (coversTop τ hτ (show x∈⊤ from trivial))
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (coversTop τ hτ (show act τ hτ a x∈⊤ from trivial))
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (coversTop τ hτ (show act τ hτ (complement a) x∈⊤ from trivial))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(k,i,j),⟨⟨hk,hi⟩,hj⟩⟩
lemma domain_iff (b : Index τ hτ) (z : ComplexVectors) :
    z∈domain τ hτ (chart τ hτ a b) ↔
      z∈domain τ hτ (O τ hτ b.1) ∧
      linear a z∈domain τ hτ (O τ hτ b.2.1) ∧
      linear (complement a) z∈domain τ hτ (O τ hτ b.2.2) := by
  change ((_∈O τ hτ b.1 ∧ act τ hτ a _∈O τ hτ b.2.1) ∧
    act τ hτ (complement a) _∈O τ hτ b.2.2) ↔ _
  rw [←Scheme.Hom.comp_apply,act_point,←Scheme.Hom.comp_apply,act_point]
  exact and_assoc
@[expose] def regular (b : Index τ hτ) : Γ(candidate τ hτ,chart τ hτ a b) :=
  (candidate τ hτ).presheaf.map (homOfLE
    (show chart τ hτ a b≤O τ hτ b.1 from inf_le_left.trans inf_le_left)).op
      (D.coefficient a b.2.1 b.2.2 b.1)
lemma regular_value (b : Index τ hτ) (z : ComplexVectors)
    (hz : z∈domain τ hτ (chart τ hτ a b)) :
    value τ hτ (chart τ hτ a b) (regular τ hτ D a b) z=
      (D.lineData.g b.2.1 (linear a z)^2*D.lineData.g b.2.2 (linear (complement a) z)^2)/
        D.lineData.g b.1 z^(2*degree a) := by
  rw [regular,value_restrict]
  exact D.coefficient_value a _ _ _ z ((domain_iff τ hτ a b z).mp hz).1
lemma regular_isUnit (b : Index τ hτ) : IsUnit (regular τ hτ D a b) := by
  let U := chart τ hτ a b
  let π := U.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  have hu : IsUnit ((LineFrameTopScalar318.ringTop U).inv (regular τ hτ D a b)) := by
    apply ReducedSchemeGlobalFunctionSeparation318.isUnit π
    intro p hp
    obtain ⟨z,hz,he⟩ := PELOriginalOpenFunctionSeparation318.point_representation τ hτ U p hp
    have hv := regular_value τ hτ D a b z hz
    rw [value_at_point τ hτ U _ z p he] at hv
    have hh := (domain_iff τ hτ a b z).mp hz
    have hn : (D.lineData.g b.2.1 (linear a z)^2*D.lineData.g b.2.2 (linear (complement a) z)^2)/
        D.lineData.g b.1 z^(2*degree a)≠0 :=
      div_ne_zero (mul_ne_zero (pow_ne_zero _ (D.lineData.nonzero _ _ hh.2.1))
        (pow_ne_zero _ (D.lineData.nonzero _ _ hh.2.2)))
        (pow_ne_zero _ (D.lineData.nonzero _ _ hh.1))
    have heU : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (p.appTop ((LineFrameTopScalar318.ringTop U).inv (regular τ hτ D a b)))) := by
      rw [hv]; exact isUnit_iff_ne_zero.mpr hn
    simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
      heU.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
  simpa only [Iso.inv_hom_id_apply] using hu.map (LineFrameTopScalar318.ringTop U).hom
@[expose] def unit (b : Index τ hτ) : Γ(candidate τ hτ,chart τ hτ a b)ˣ :=
  (regular_isUnit τ hτ D a b).unit
lemma unit_value (b : Index τ hτ) : (unit τ hτ D a b).val=regular τ hτ D a b :=
  (regular_isUnit τ hτ D a b).unit_spec
end PELOriginalOrderPolarizationData318
