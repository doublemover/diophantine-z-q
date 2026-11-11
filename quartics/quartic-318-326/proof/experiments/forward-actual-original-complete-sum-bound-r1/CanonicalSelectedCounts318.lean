module
public import CanonicalCurveTrace318
public import ActualCMOrientation318
public section
noncomputable section
namespace CanonicalSelectedCounts318
open FiniteCurveCharacterCount318 SelectedReductionOrder318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
set_option maxHeartbeats 1000000

/-- The remaining CM statement concerns ONLY y²=x³−x over the original
prime field. In particular it has no chosen p-adic root or orientation input. -/
@[expose] def CanonicalCM (p : ℕ) [Fact p.Prime] (a : ℤ) : Prop :=
  (traceSum (1:ZMod p))^2=4*a^2

variable (p : ℕ) [Fact p.Prime]

theorem actual_count (rho : ℚ_[p]) (hr : rho^2=2)
    (a b : ℤ) (hray : GaussianRayQuadratic318.Ray p a b)
    (ha7 : a%7=1) (hb7 : b%7=3) (hcm : CanonicalCM p a) :
    pointCount p rho hr=GaussianNeighborNorms318.minus a b ∨
    pointCount p rho hr=GaussianNeighborNorms318.plus a b := by
  have hseven := GaussianSevenCharacter318.actual_seven_character p a b hray ha7 hb7
  have h7 : (7:ZMod p)≠0 := by
    intro he
    rw [he,map_zero] at hseven
    norm_num at hseven
  have hr' := residueRoot_square p rho hr
  have hprod : (3-residueRoot p rho hr)*(3+residueRoot p rho hr)=(7:ZMod p) := by
    linear_combination -hr'
  have hc : 3-residueRoot p rho hr≠0 := by
    intro he
    rw [he,zero_mul] at hprod
    exact h7 hprod.symm
  have hmod := GaussianRayQuadratic318.prime_mod p a b hray
  have hF : ringChar (ZMod p)≠2 := by rw [ringChar_zmod_n]; omega
  have hn : (Fintype.card (ZMod p):ℤ)=a^2+b^2 := by simpa only [ZMod.card] using hray.1
  simpa only [count,Curve,pointCount] using
    CanonicalCurveTrace318.count_neighbors hF (3-residueRoot p rho hr) hc a b hn hcm

variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hp : Values C u w)

@[expose] def AllCanonicalCM (a : Fin 3 × Fin 5 → ℤ) : Prop :=
  ∀ i : Fin 3 × Fin 5,
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
    CanonicalCM p (a i)

/-- All fifteen one-count requirements are constructed on the literal
original curves, simultaneously for EVERY choice of the initial roots. -/
theorem oneCount (r : Roots C u w hp) (a b : Fin 3 × Fin 5 → ℤ)
    (hray : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (ha7 : ∀ i, a i%7=1) (hb7 : ∀ i, b i%7=3)
    (hcm : AllCanonicalCM C u w hp a) : ActualCMOrientation318.OneCount C u w hp r a b := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
  exact actual_count p (r i).val (r i).property (a i) (b i) (hray i) (ha7 i) (hb7 i) (hcm i)

end CanonicalSelectedCounts318
