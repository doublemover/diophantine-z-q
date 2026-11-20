module
public import SelectedGammaOneEllipticGerm318
public import SelectedLocalDVRCanonical318
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public section
noncomputable section

open scoped MatrixGroups Topology

namespace SelectedTrueBranchDivisor318

/-- Tag the actual geometric fibers of a single compact map. A cusp
stores its actual SL₂ lift, not an integer claimed to be its width. -/
inductive Branch where
  | zero
  | elliptic
  | cusp (g : SL(2, ℤ))
  | ordinary (a : ℂ)

@[expose] def ramification (N : ℕ) : Branch → ℕ
  | .zero => 3
  | .elliptic => 2
  | .cusp g => N/N.gcd ((g 1 0:ZMod N).val)
  | .ordinary _ => 1

@[expose] def differentialOrder (N : ℕ) : Branch → ℤ
  | .zero => 2
  | .elliptic => 1
  | .cusp g => -(ramification N (.cusp g):ℤ)-1
  | .ordinary _ => 0

theorem ramification_positive (N : ℕ) [NeZero N] (hN : 4 < N) (b : Branch) :
    0 < ramification N b := by
  cases b with
  | zero =>
      change 0 < (3 : ℕ)
      decide
  | elliptic =>
      change 0 < (2 : ℕ)
      decide
  | cusp g => exact (SelectedGammaOneCuspWidth318.least_positive N hN g).1
  | ordinary a =>
      change 0 < (1 : ℕ)
      decide

/-- The function measured at each place of the SAME literal J.
In particular the analytic pole test uses 1/J but dJ below is not
replaced by d(1/J). -/
@[expose] def probe {K : Type*} [Field K] [Algebra ℂ K] (J : K) : Branch → K
  | .zero => J-algebraMap ℂ K 0
  | .elliptic => J-algebraMap ℂ K 1728
  | .cusp _ => J⁻¹
  | .ordinary a => J-algebraMap ℂ K a

section Local
variable {B K : Type*}
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    [Algebra ℂ B] [Algebra B K] [Algebra ℂ K] [IsScalarTower ℂ B K] [IsFractionRing B K]

local notation "ν" => ValuationRing.valuation B K
local notation "t" => algebraMap B K

/-- A genuine irreducible uniformizer has a unique signed valuation
exponent. This identifies the actual divisor coefficient rather
than choosing one of possibly many representations. -/
theorem exponent_injective (z : B) (hz : Irreducible z) :
    Function.Injective (fun n : ℤ => (ν (t z))^n) := by
  have ht : t z ≠ 0 :=
    fun h => hz.ne_zero ((IsFractionRing.injective B K) (h.trans (map_zero t).symm))
  have h₀ : 0 < ν (t z) := (Valuation.pos_iff ν).mpr ht
  have h₁ : ν (t z) < 1 := (ValuationRing.integers B K).valuation_irreducible_lt_one hz
  exact (zpow_right_strictAnti₀ h₀ h₁).injective

theorem local_differential (N : ℕ) [NeZero N] (hN : 4 < N) (b : Branch)
    (J : K) (z : B) (hz : Irreducible z)
    (frame : KaehlerDifferential ℂ B ≃ₗ[B] B)
    (dz : frame (KaehlerDifferential.D ℂ B z)=1)
    (hp : ν (probe J b) = (ν (t z))^(ramification N b:ℤ)) :
    ν (SelectedLocalDVRCanonical318.coefficient frame J) =
      (ν (t z))^(differentialOrder N b) := by
  cases b with
  | zero =>
    have h := SelectedLocalDVRCanonical318.finite_order frame z hz dz J 0 3 (by decide) hp
    simpa only [differentialOrder, show ((3:ℕ):ℤ)-1=2 by decide] using h
  | elliptic =>
    have h := SelectedLocalDVRCanonical318.finite_order frame z hz dz J 1728 2 (by decide) hp
    simpa only [differentialOrder, show ((2:ℕ):ℤ)-1=1 by decide] using h
  | cusp g =>
    let w := ramification N (.cusp g)
    have hw : 0 < w := ramification_positive N hN (.cusp g)
    change ν (J⁻¹) = (ν (t z))^(w:ℤ) at hp
    have hJ : ν J = (ν (t z))^(-(w:ℤ)) := by
      calc
        _ = (ν (J⁻¹))⁻¹ := by rw [Valuation.map_inv ν,inv_inv]
        _ = _ := by rw [hp,zpow_neg]
    exact SelectedLocalDVRCanonical318.cusp_order frame z hz dz J w hw hJ
  | ordinary a =>
    have h := SelectedLocalDVRCanonical318.finite_order frame z hz dz J a 1 (by decide) hp
    simpa only [differentialOrder, show ((1:ℕ):ℤ)-1=0 by decide] using h

/-- Apply the genuine local-analytic/algebraic order comparison to
the order actually derived from the chart, not to an assumed source
ramification row. The comparison is of the one literal probe above. -/
theorem chart_differential (N : ℕ) [NeZero N] (hN : 4 < N) (b : Branch)
    (J : K) (z : B) (hz : Irreducible z)
    (frame : KaehlerDifferential ℂ B ≃ₗ[B] B) (dz : frame (KaehlerDifferential.D ℂ B z)=1)
    (S F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (simple : analyticOrderAt F 0 = 1)
    (chart : S =ᶠ[𝓝 0] (F ∘ fun x : ℂ => x^(ramification N b)))
    (compare : ∀ n : ℕ, analyticOrderAt S 0 = n →
      ν (probe J b) = (ν (t z))^(n:ℤ)) :
    ν (SelectedLocalDVRCanonical318.coefficient frame J) =
      (ν (t z))^(differentialOrder N b) := by
  have ht : analyticOrderAt S 0 = (ramification N b:ℕ) := by
    cases b with
    | cusp g =>
      exact SelectedGammaOneCuspGerm318.actual_inverse_j_order N hN g S F hF simple chart
    | zero =>
      exact (analyticOrderAt_congr chart).trans
        (SelectedGammaOneCuspGerm318.width_order 3 (by decide) F hF simple)
    | elliptic =>
      exact (analyticOrderAt_congr chart).trans
        (SelectedGammaOneCuspGerm318.width_order 2 (by decide) F hF simple)
    | ordinary a =>
      exact (analyticOrderAt_congr chart).trans
        (SelectedGammaOneCuspGerm318.width_order 1 (by decide) F hF simple)
  exact local_differential N hN b J z hz frame dz (compare _ ht)

end Local

section AllPoints
variable {P K : Type*} [Field K] [Algebra ℂ K]
variable (B : P → Type*) [∀ p, CommRing (B p)] [∀ p, IsDomain (B p)]
    [∀ p, IsDiscreteValuationRing (B p)] [∀ p, Algebra ℂ (B p)] [∀ p, Algebra (B p) K]
    [∀ p, IsScalarTower ℂ (B p) K] [∀ p, IsFractionRing (B p) K]

/-- The actual all-geometric-points statement. The inputs are one
global field/function, its true local stalks/normalized frames, and the
genuine charts plus analytic/algebraic comparison. The integer supplied
by the divisor has its actual valuation characterization. -/
theorem all_coefficients (N : ℕ) [NeZero N] (hN : 4 < N) (J : K)
    (b : P → Branch) (z : (p : P) → B p) (hz : ∀ p, Irreducible (z p))
    (frame : (p : P) → KaehlerDifferential ℂ (B p) ≃ₗ[B p] B p)
    (dz : ∀ p, frame p (KaehlerDifferential.D ℂ (B p) (z p))=1)
    (S F : P → ℂ → ℂ) (hF : ∀ p, AnalyticAt ℂ (F p) 0)
    (simple : ∀ p, analyticOrderAt (F p) 0 = 1)
    (chart : ∀ p, S p =ᶠ[𝓝 0] (F p ∘ fun x : ℂ => x^(ramification N (b p))))
    (compare : ∀ (p : P) (n : ℕ), analyticOrderAt (S p) 0 = n →
      ValuationRing.valuation (B p) K (probe J (b p)) =
        (ValuationRing.valuation (B p) K (algebraMap (B p) K (z p)))^(n:ℤ))
    (ord : P → ℤ)
    (divisor : ∀ p,
      ValuationRing.valuation (B p) K (SelectedLocalDVRCanonical318.coefficient (frame p) J) =
        (ValuationRing.valuation (B p) K (algebraMap (B p) K (z p)))^(ord p)) :
    ∀ p, ord p = differentialOrder N (b p) := by
  intro p
  apply exponent_injective (K:=K) (z p) (hz p)
  exact (divisor p).symm.trans
    (chart_differential N hN (b p) J (z p) (hz p) (frame p) (dz p)
      (S p) (F p) (hF p) (simple p) (chart p) (compare p))

end AllPoints
end SelectedTrueBranchDivisor318

#print axioms SelectedTrueBranchDivisor318.exponent_injective
#print axioms SelectedTrueBranchDivisor318.local_differential
#print axioms SelectedTrueBranchDivisor318.all_coefficients
