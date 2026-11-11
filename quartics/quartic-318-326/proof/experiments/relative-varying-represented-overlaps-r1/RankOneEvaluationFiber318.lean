module
public import AffineSectionQuotientFlat318
public import SectionZeroRegularCoordinate318
public section
noncomputable section
namespace RankOneEvaluationFiber318
universe u
open TensorProduct
open scoped BigOperators
variable (R S P : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
  (K : Type u) [CommRing K] [Algebra R K]
local notation "D" => Module.Dual S P

@[expose] def section (s : P) : S →ₗ[R] P :=
  (SectionZeroRegularCoordinate318.sectionMap S P s).restrictScalars R

local notation "ev" => AffineSectionQuotientFlat318.evaluation R S P

/-- The finite dual-frame identity survives arbitrary coefficient change.
The coefficients and all evaluation maps are the original ones. -/
lemma reconstruct (F : FiniteProjectiveEvaluationFrame318.Frame S P)
    (z : K ⊗[R] D) :
    ∑ i, ((LinearMap.toSpanSingleton S D (F.coordinate i)).restrictScalars R).baseChange K
      ((ev (F.vector i)).baseChange K z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul k φ =>
    simp only [LinearMap.baseChange_tmul]
    change (∑ i, k ⊗ₜ[R] (φ (F.vector i) • F.coordinate i)) = k ⊗ₜ[R] φ
    rw [← TensorProduct.tmul_sum, F.dual_reconstruct]
  | add x y hx hy =>
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

/-- Intrinsic regularity of the coefficient-extended section implies
injectivity of the coefficient-extended dual evaluation, provided the
actual rank-one commutation identity holds. No dual-base-change
isomorphism or hidden injectivity hypothesis is assumed. -/
lemma evaluation_injective (F : FiniteProjectiveEvaluationFrame318.Frame S P) (s : P)
    (hline : ∀ (φ : D) (x : P), φ s • x = φ x • s)
    (hs : Function.Injective ((section R S P s).baseChange K)) :
    Function.Injective ((ev s).baseChange K) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro z hz
  change z=0
  have hz0 : (ev s).baseChange K z=0 := hz
  have hpair (x : P) : (ev x).baseChange K z=0 := by
    have hcross : (section R S P s).comp (ev x) =
        (section R S P x).comp (ev s) := by
      apply LinearMap.ext
      intro φ
      exact (hline φ x).symm
    apply hs
    rw [map_zero]
    calc
      (section R S P s).baseChange K ((ev x).baseChange K z) =
          (section R S P x).baseChange K ((ev s).baseChange K z) := by
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcross,
          LinearMap.baseChange_comp, LinearMap.comp_apply]
      _ = 0 := by rw [hz0, map_zero]
  rw [← reconstruct R S P K F z]
  simp only [hpair, map_zero, Finset.sum_const_zero]
end RankOneEvaluationFiber318
