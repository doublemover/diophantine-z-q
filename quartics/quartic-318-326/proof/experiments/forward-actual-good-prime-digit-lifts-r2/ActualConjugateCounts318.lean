module
public import GaussianSevenCharacter318
public section
noncomputable section
namespace ActualConjugateCounts318
open SelectedReductionOrder318 ActualSelectedOrderModuli318 ConcretePadic318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma residueRoot_negative (rho : ℚ_[p]) (hr : rho^2=2) :
    residueRoot p (-rho) (negative_root p rho hr)= -residueRoot p rho hr := by
  let r : ℤ_[p] := ⟨rho,ActualSplitOrbitEntry318.root_integral p rho hr⟩
  have he : (⟨-rho,ActualSplitOrbitEntry318.root_integral p (-rho)
      (negative_root p rho hr)⟩:ℤ_[p])= -r := by apply Subtype.ext; rfl
  change PadicInt.toZMod (⟨-rho,ActualSplitOrbitEntry318.root_integral p (-rho)
    (negative_root p rho hr)⟩:ℤ_[p])= -PadicInt.toZMod r
  rw [he,map_neg]

/-- Both literal original finite counts, including infinity, are counted
by the coordinate-fiber formula and the actual opposite twist. -/
theorem count_sum (rho : ℚ_[p]) (hr : rho^2=2) (hp2 : p≠2)
    (hseven : quadraticChar (ZMod p) (7:ZMod p)= -1) :
    pointCount p rho hr+pointCount p (-rho) (negative_root p rho hr)=2*(p+1) := by
  have hh := FiniteQuadraticTwistCount318.conjugate_counts
    (by simpa only [ringChar_zmod_n] using hp2 : ringChar (ZMod p)≠2)
    (residueRoot p rho hr) (residueRoot_square p rho hr) hseven
  simpa only [pointCount,residueRoot_negative,sub_neg_eq_add,ZMod.card,
    FiniteCurveCharacterCount318.count,FiniteCurveCharacterCount318.Curve] using hh

/-- This is the actual opposite-trace part of the historical CM argument.
No Frobenius integer or Gaussian norm count is supplied as a premise. -/
theorem count_sum_from_ray (rho : ℚ_[p]) (hr : rho^2=2)
    (a b : ℤ) (hray : GaussianRayQuadratic318.Ray p a b)
    (ha7 : a%7=1) (hb7 : b%7=3) :
    pointCount p rho hr+pointCount p (-rho) (negative_root p rho hr)=2*(p+1) := by
  have hm := GaussianRayQuadratic318.prime_mod p a b hray
  exact count_sum p rho hr (by omega) (GaussianSevenCharacter318.actual_seven_character p a b hray ha7 hb7)

open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318

theorem all_counts_sum {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ)
    (hp : Values C u w) (r : Roots C u w hp) (a b : Fin 3 × Fin 5 → ℤ)
    (hray : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (ha7 : ∀ i, a i%7=1) (hb7 : ∀ i, b i%7=3) :
    ∀ i : Fin 3 × Fin 5, counts C u w hp r false i+counts C u w hp r true i=
      GaussianNeighborNorms318.minus (a i) (b i)+GaussianNeighborNorms318.plus (a i) (b i) := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
  have hsum := count_sum_from_ray p (r i).val (r i).property (a i) (b i) (hray i) (ha7 i) (hb7 i)
  have hnorm : GaussianNeighborNorms318.minus (a i) (b i)+GaussianNeighborNorms318.plus (a i) (b i)=2*(p+1) := by
    have he := GaussianNeighborNorms318.neighbor_errors p (a i) (b i) (hray i).1
    omega
  exact hsum.trans hnorm.symm

end ActualConjugateCounts318
