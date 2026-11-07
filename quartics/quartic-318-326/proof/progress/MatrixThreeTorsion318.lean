module
public import MatrixCongruence318
public section
namespace MatrixCongruence318
set_option maxHeartbeats 0
noncomputable section
variable {n:Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℤ

@[expose] def modThree : M→+*Matrix n n (ZMod 3) := (Int.castRingHom (ZMod 3)).mapMatrix

theorem identity_factor (A:M) (hA:modThree A=1) : ∃B:M,A=1+(3:ℤ) • B := by
  have hz:modThree (A-1)=0 := by rw [map_sub,hA,map_one,sub_self]
  have hd:∀i j,(3:ℤ)∣(A-1) i j := by
    intro i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    exact congrArg (fun X:Matrix n n (ZMod 3)=>X i j) hz
  obtain ⟨B,hB⟩:=(exists_smul_iff 3 (A-1)).mpr hd
  refine ⟨B,?_⟩
  rw [←hB]
  abel

/-- The order-prime relation lifts the identity congruence to every power
of three. The exceptional prime3 is handled by its exact cubic expansion. -/
theorem prime_torsion_all_powers (A:M) (q:ℕ) (hq:q.Prime)
    (hA:modThree A=1) (hp:A^q=1) : ∀k:ℕ,∃B:M,A=1+(3:ℤ)^(k+1) • B := by
  intro k
  induction k with
  | zero => simpa using identity_factor A hA
  | succ k ih =>
    obtain ⟨B,hB⟩:=ih
    have hl:∃C:M,B=(3:ℤ) • C := by
      by_cases hq3:q=3
      · subst q
        apply lift_three A B ((3:ℤ)^k) (pow_ne_zero _ (by norm_num)) _ hp
        simpa only [pow_succ,mul_comm (3:ℤ) ((3:ℤ)^k)] using hB
      · apply lift_coprime A B ((3:ℤ)^(k+1)) (pow_ne_zero _ (by norm_num)) _ q _ hB hp
        · exact dvd_pow_self 3 (by omega)
        · intro hdiv
          have hd:3∣q:=Int.natCast_dvd_natCast.mp hdiv
          exact hq3 ((hq.dvd_iff_eq (by decide:3≠1)).mp hd)
    obtain ⟨C,hC⟩:=hl
    refine ⟨C,?_⟩
    rw [hB,hC,smul_smul]
    simp only [pow_succ]

theorem integer_zero_of_all_three_powers (a:ℤ)
    (h:∀k:ℕ,(3:ℤ)^(k+1)∣a) : a=0 := by
  by_contra ha
  let k:=padicValNat 3 a.natAbs
  have hv:=Int.natAbs_dvd_natAbs.mpr (h k)
  have hv':3^(k+1)∣a.natAbs := by simpa only [Int.natAbs_pow,show (3:ℤ).natAbs=3 from rfl] using hv
  have hn:a.natAbs≠0:=Int.natAbs_ne_zero.mpr ha
  have hk: k+1≤padicValNat 3 a.natAbs :=
    (Nat.pow_dvd_iff_le_padicValNat (by decide:3≠1) hn).mp hv'
  omega

/-- A finite-order integral matrix congruent to the identity mod3 cannot
have prime order. This statement needs no invertibility hypothesis. -/
theorem prime_torsion_eq_one (A:M) (q:ℕ) (hq:q.Prime)
    (hA:modThree A=1) (hp:A^q=1) : A=1 := by
  have he:=prime_torsion_all_powers A q hq hA hp
  ext i j
  apply sub_eq_zero.mp
  apply integer_zero_of_all_three_powers
  intro k
  obtain ⟨B,hB⟩:=he k
  have hv:=congrArg (fun X:M=>X i j) hB
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hv
  exact ⟨B i j,by linarith only [hv]⟩

/-- The principal congruence kernel modulo three has no nonidentity
finite-order matrix. The prime-order reduction is internal to the proof. -/
theorem finite_order_eq_one (A:M) (hA:modThree A=1) (hfin:IsOfFinOrder A) : A=1 := by
  by_contra hne
  have ho:orderOf A≠1:=fun h=>hne (orderOf_eq_one_iff.mp h)
  obtain ⟨q,hq,hqd⟩:=Nat.exists_prime_and_dvd ho
  let B:=A^(orderOf A/q)
  have hB:orderOf B=q := orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hqd
  have hmod:modThree B=1 := by dsimp [B]; rw [map_pow,hA,one_pow]
  have hp:B^q=1 := by rw [←hB]; exact pow_orderOf_eq_one B
  have he:=prime_torsion_eq_one B q hq hmod hp
  have hq1:q=1 := by rw [←hB,he,orderOf_one]
  exact hq.ne_one hq1

end
end MatrixCongruence318
#print axioms MatrixCongruence318.finite_order_eq_one
