module
public import ThreeJGlobalKernelChart318
public section
noncomputable section
namespace ThreeJLocalAnnihilators318
open Polynomial
open ThreeProjectiveJCertificates318 ThreeJCuspDifferentialCharts318
open ThreeJRamificationIdealCharts318 ThreeJRelativeDifferentials318
open LocalizedRationalDifferentials318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A cyclic quotient presentation identifies the entire annihilator,
not merely one scalar that kills a chosen differential generator. -/
theorem annihilates_iff_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (e : (A ⧸ I) ≃ₗ[A] M) (a : A) :
    (∀ w : M, a • w=0) ↔ a ∈ I := by
  constructor
  · intro h
    have he : e (a • (1:A ⧸ I))=e 0 := by rw [map_smul,map_zero];exact h _
    have hq := e.injective he
    change Ideal.Quotient.mk I a * 1=0 at hq
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [mul_one] using hq)
  · intro ha w
    obtain ⟨q,rfl⟩ := e.surjective w
    rw [←map_smul]
    have hq : a • q=0 := by
      obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective q
      change Ideal.Quotient.mk I (a*b)=0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right b ha)
    rw [hq,map_zero]

/-- Whole finite-cusp relative-module annihilator, with the actual 1/j
scalar action and the complete nonreduced degree-six equation. -/
theorem finite_annihilator (a : FiniteRing) :
    letI := targetAlgebra finiteDenominator finiteNumerator finiteInverse
    (∀ w : KaehlerDifferential ℚ[X] FiniteRing, a • w=0) ↔
      a ∈ Ideal.map (value finiteNumerator).toRingHom (Ideal.span {finiteEquation}) := by
  letI := targetAlgebra finiteDenominator finiteNumerator finiteInverse
  rw [←finite_jacobian_ideal]
  exact annihilates_iff_mem _ finitePresentation a

/-- Whole reciprocal source chart, including its origin. The action is
again the literal 1/j target coordinate, not the finite-chart j action. -/
theorem infinity_annihilator (a : InfinityRing) :
    letI := targetAlgebra reciprocalDenominator reciprocalNumerator infinityInverse
    (∀ w : KaehlerDifferential ℚ[X] InfinityRing, a • w=0) ↔
      a ∈ Ideal.map (value reciprocalNumerator).toRingHom (Ideal.span {infinityEquation}) := by
  letI := targetAlgebra reciprocalDenominator reciprocalNumerator infinityInverse
  rw [←infinity_jacobian_ideal]
  exact annihilates_iff_mem _ infinityPresentation a

/-- The Laurent statement uses the actual global j pullback algebra. -/
theorem laurent_annihilator (a : ThreeJLaurentEquiv318.Laurent) :
    letI := ThreeJFiniteLaurentMap318.jAlgebra
    (∀ w : KaehlerDifferential ThreeJMonicAlgebra318.Base ThreeJLaurentEquiv318.Laurent,
      a • w=0) ↔ a ∈ originalDifferentialIdeal := by
  letI := ThreeJFiniteLaurentMap318.jAlgebra
  exact annihilates_iff_mem _ ThreeJLaurentDifferentialJoin318.literalLaurentPresentation a
end ThreeJLocalAnnihilators318
