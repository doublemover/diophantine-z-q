module
public import PELOriginalRosatiTestPairing318
public import PELOriginalRelativePolarizationHom318
public section
noncomputable section
namespace PELOriginalRelativeRosatiAction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalPolarizationBicharacter318 PELOriginalNormalizedPolarizationFamily318
open PELOriginalRelativePolarizationHom318 PELOriginalOrderHermitianAdjoint318
open RelativeLineClassQuotient318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ))
/-- Actual order map on the original factor, leaving the complete
parameter test scheme unchanged, including its nilpotents. -/
@[expose] def totalAction : Total τ hτ ρ⟶Total τ hτ ρ :=
  pullback.lift (pullback.fst (π τ hτ) ρ≫PELOriginalOrderSchemeMorphism318.morphism τ hτ a)
    (pullback.snd (π τ hτ) ρ) (by
      rw [Category.assoc,PELOriginalOrderSchemeMorphism318.over_complex]
      exact pullback.condition)
@[reassoc] lemma parameter_square : totalAction τ hτ a ρ≫parameterMap τ hτ ρ=parameterMap τ hτ ρ :=
  pullback.lift_snd _ _ _
lemma base_square : totalAction τ hτ a ρ≫totalBase τ hτ ρ=totalBase τ hτ ρ := by
  rw [totalBase,←Category.assoc,totalAction,pullback.lift_fst,Category.assoc,
    PELOriginalOrderSchemeMorphism318.over_complex]
lemma pull_original :
    pull τ hτ (totalBase τ hτ ρ) (totalAction τ hτ a ρ) (base_square τ hτ a ρ)
      (original τ hτ ρ)=
    PELOriginalUniversalOrderAction318.endomorphism τ hτ (totalBase τ hτ ρ) a (original τ hτ ρ) := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _
lemma pull_parameter (x : Points τ hτ T ρ) :
    pull τ hτ (totalBase τ hτ ρ) (totalAction τ hτ a ρ) (base_square τ hτ a ρ)
      (parameter τ hτ ρ x)=parameter τ hτ ρ x := by
  apply Subtype.ext
  change totalAction τ hτ a ρ≫(parameterMap τ hτ ρ≫x.val)=parameterMap τ hτ ρ≫x.val
  rw [←Category.assoc,parameter_square]
lemma parameter_action (x : Points τ hτ T ρ) :
    PELOriginalUniversalOrderAction318.endomorphism τ hτ (totalBase τ hτ ρ) a (parameter τ hτ ρ x)=
      parameter τ hτ ρ (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a x) := by
  have he := congrArg (fun f => f x)
    (PELOriginalUniversalOrderAction318.naturality τ hτ ρ (parameterMap τ hτ ρ)
      pullback.condition.symm a)
  exact he.symm

/-- Genuine pullback homomorphism on the naive relative line quotient.
The commuting parameter square, not a represented dual, constructs it. -/
@[expose] def action : RelativeClass (parameterMap τ hτ ρ) →* RelativeClass (parameterMap τ hτ ρ) :=
  RelativeLineClassQuotient318.map (parameterMap τ hτ ρ) (parameterMap τ hτ ρ)
    (totalAction τ hτ a ρ) (𝟙 T) (by rw [Category.comp_id,parameter_square])
lemma action_class (c : Class (Total τ hτ ρ)) :
    action τ hτ a ρ (quotient τ hτ ρ c)=
      quotient τ hτ ρ (LineClassPullbackHom318.pullback (totalAction τ hτ a ρ) c) := rfl
lemma relative_pairing (x : Points τ hτ T ρ) :
    relativeValue τ hτ ρ x=
      quotient τ hτ ρ (pairing τ hτ (totalBase τ hτ ρ) (original τ hτ ρ) (parameter τ hτ ρ x)) := by
  simp only [relativeValue,pairing,map_mul,map_inv,parameter_trivial,zero_trivial,inv_one,mul_one]

/-- Exact all-test Rosati compatibility of the ACTUAL original relative
polarization. The equality is established before sheafification and
retains the original parameter-line quotient. No dual representability,
flatness or reducedness assumption is inserted. -/
lemma polarization_equivariance (x : Points τ hτ T ρ) :
    action τ hτ a ρ (relativeValue τ hτ ρ x)=
      relativeValue τ hτ ρ (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ (adjoint a) x) := by
  rw [relative_pairing,action_class,
    pairing_pull τ hτ (totalBase τ hτ ρ) (totalAction τ hτ a ρ) (base_square τ hτ a ρ),
    pull_original,pull_parameter,PELOriginalRosatiTestPairing318.pairing_adjoint,
    parameter_action,←relative_pairing]
end PELOriginalRelativeRosatiAction318
