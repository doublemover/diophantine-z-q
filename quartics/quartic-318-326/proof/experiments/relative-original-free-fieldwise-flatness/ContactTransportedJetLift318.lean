module
public import ContactFiniteComplexCoefficient318
public section
noncomputable section
namespace ContactTransportedJetLift318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeFiniteCohomologyModel318 ContactRelativeFiniteCechComparison318
open ContactFiniteComplexCoefficient318
open scoped TensorProduct
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (b : ℕ)
local instance : Algebra R S := f.toAlgebra
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _

/-- Transport the ORIGINAL chosen jet lift through the ACTUAL original
infinity section and jet quotient coefficient comparisons. -/
@[expose] def lift : termOne S c (L' R S f c L) b →ₗ[S] infinitySections S c (L' R S f c L) :=
  (infinityEquivalence R S f c L).toLinearMap.comp
    (((jetLift R c L b).baseChange S).comp (oneEquivalence R S f c L b).symm.toLinearMap)

lemma pure_tensor (s : S) (q : termOne R c L b) :
    lift R S f c L b (oneEquivalence R S f c L b (s ⊗ₜ[R] q))=
      infinityEquivalence R S f c L (s ⊗ₜ[R] jetLift R c L b q) := by
  change infinityEquivalence R S f c L
    ((jetLift R c L b).baseChange S ((oneEquivalence R S f c L b).symm
      (oneEquivalence R S f c L b (s ⊗ₜ[R] q))))=_
  rw [LinearEquiv.symm_apply_apply,LinearMap.baseChange_tmul]

/-- This transported map really splits the original S-jet projection;
it is not an arbitrary chosen map to the infinity chart. -/
lemma specification : (ContactRelativeInfinityJet318.power S c (L' R S f c L) b).range.mkQ.comp
    (lift R S f c L b)=LinearMap.id := by
  ext q
  obtain ⟨z,rfl⟩ := (oneEquivalence R S f c L b).surjective q
  induction z using TensorProduct.inductionOn with
  | tmul s q =>
      change (ContactRelativeInfinityJet318.power S c (L' R S f c L) b).range.mkQ
        (lift R S f c L b (oneEquivalence R S f c L b (s ⊗ₜ[R] q)))=oneEquivalence R S f c L b (s ⊗ₜ[R] q)
      rw [pure_tensor,← one_pure]
      have hq := LinearMap.congr_fun (jetLift_spec R c L b) q
      change (ContactRelativeInfinityJet318.power R c L b).range.mkQ (jetLift R c L b q)=q at hq
      rw [hq]
  | add x y hx hy => simpa only [map_add,hx,hy]
end ContactTransportedJetLift318
