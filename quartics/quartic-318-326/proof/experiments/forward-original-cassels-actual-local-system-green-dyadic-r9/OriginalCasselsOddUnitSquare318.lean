module
public import ActualTwoDescentHenselSquare318
public import ActualTwoDescentLocalValuationTools318
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public section

noncomputable section

namespace OriginalCasselsOddUnitSquare318

open ActualTwoDescentHenselSquare318 ActualTwoDescentLocalValuationTools318

variable {p : ℕ} [Fact p.Prime]

theorem residue_zero_iff_norm (A : ℤ_[p]) : PadicInt.toZMod A=0 ↔ ‖A‖<1 := by
  rw [←RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton,←PadicInt.norm_lt_one_iff_dvd]

theorem residue_nonzero_iff_unit (A : ℤ_[p]) : PadicInt.toZMod A≠0 ↔ IsUnit A := by
  rw [ne_eq,residue_zero_iff_norm,PadicInt.isUnit_iff]
  exact ⟨fun h => le_antisymm (PadicInt.norm_le_one A) (le_of_not_gt h),
    fun h => by rw [h]; exact lt_irrefl _⟩

theorem actual_odd_unit_normal (x : ℚ_[p]) (hx : x ≠ 0) :
    ∃ U : ℤ_[p], IsUnit U ∧ x=(p:ℚ_[p])^x.valuation*(U:ℚ_[p]) := by
  have hp0 : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpow : (p:ℚ_[p])^x.valuation≠0 := zpow_ne_zero _ hp0
  let z := x/(p:ℚ_[p])^x.valuation
  have hz : z≠0 := div_ne_zero hx hpow
  have hv : z.valuation=0 := by
    dsimp [z]
    rw [actual_valuation_div _ _ hx hpow,Padic.valuation_zpow,Padic.valuation_p,mul_one,sub_self]
  have hn := actual_norm_one_of_valuation_zero z hz hv
  let U : ℤ_[p] := ⟨z,hn.le⟩
  refine ⟨U,PadicInt.isUnit_iff.mpr hn,?_⟩
  change x=(p:ℚ_[p])^x.valuation*(x/(p:ℚ_[p])^x.valuation)
  field_simp [hpow] <;> ring

/-- Equal actual nonzero residues at an odd prime give an actual square
multiplier between the units. Hensel is applied to X²−AB starting at B;
this keeps all coefficients and residues on the same Qp/Zp charts. -/
theorem unit_ratio_square_of_equal_residue (hp2 : p≠2) (A B : ℤ_[p])
    (hB : PadicInt.toZMod B≠0) (hAB : PadicInt.toZMod A=PadicInt.toZMod B) :
    ∃ z : ℚ_[p], z≠0 ∧ (A:ℚ_[p])=(B:ℚ_[p])*z^2 := by
  have hA : PadicInt.toZMod A≠0 := fun h => hB (hAB.symm.trans h)
  have hU : IsUnit B := (residue_nonzero_iff_unit B).mp hB
  have he : ‖B^2-A*B‖<1 := by
    apply (residue_zero_iff_norm _).mp
    rw [map_sub,map_pow,map_mul,hAB,pow_two,sub_self]
  have h2 : ‖(2:ℤ_[p])‖=1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp2)
  have hBn : ‖B‖=1 := by
    simpa only [PadicInt.norm_def] using (PadicInt.isUnit_iff.mp hU)
  obtain ⟨s,hs⟩ := actual_hensel_square (A*B) B (by
    simpa only [norm_mul,h2,hBn,one_mul,one_pow] using he)
  have hB0 : (B:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hU.ne_zero
  have hA0 : (A:ℚ_[p])≠0 :=
    PadicInt.coe_ne_zero.mpr ((residue_nonzero_iff_unit A).mp hA).ne_zero
  have hsq : (s:ℚ_[p])^2=(A:ℚ_[p])*(B:ℚ_[p]) := by
    simpa only [PadicInt.coe_pow,PadicInt.coe_mul] using
      congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hs
  have hs0 : (s:ℚ_[p])≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hsq
    exact (mul_ne_zero hA0 hB0) hsq.symm
  refine ⟨(s:ℚ_[p])/(B:ℚ_[p]),div_ne_zero hs0 hB0,?_⟩
  rw [div_pow,hsq]
  field_simp [hB0] <;> ring

end OriginalCasselsOddUnitSquare318

#print axioms OriginalCasselsOddUnitSquare318.unit_ratio_square_of_equal_residue
