module
public import ContactHeight318
public section
noncomputable section
namespace CleanSparseHeightCut318
open ContactRadical318 ContactHeight318

def size (u v:ℤ) := max u.natAbs v.natAbs
def S (u v:ℤ) := badProduct*radical u v
def Extreme (u v:ℤ) : Prop := (2:ℕ)^((S u v)^6) < size u v

private theorem support_pos (u v:ℤ) : 0<S u v := by
  unfold S
  exact Nat.mul_pos (by rw [bad_product_exact];decide) (radical_pos u v)
private theorem size_pos {u v:ℤ} (hn:∀j:Fin 5,forms u v j≠0) : 0<size u v := by
  have hv : v≠0 := by simpa [forms] using hn 0
  exact lt_of_lt_of_le (Int.natAbs_pos.mpr hv) (le_max_right _ _)
theorem height_log {u v:ℤ} (hc:IsCoprime u v) : pointHeight u v=Real.log (size u v:ℝ) := by
  rw [primitive_height u v hc]
  simp only [size,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs]

def target (u v:ℤ) : ℝ := 2^68*((210:ℝ)^300)^2*(S u v:ℝ)^((49:ℝ)/8)+128
def OldExtreme : Prop := ∀u v:ℤ, IsCoprime u v → (∀j:Fin 5,forms u v j≠0) →
    Extreme u v → pointHeight u v<target u v
def SharpExtreme : Prop := ∀u v:ℤ, IsCoprime u v → (∀j:Fin 5,forms u v j≠0) →
    Extreme u v → pointHeight u v<27506231*((S u v:ℝ)^2*Real.log (S u v:ℝ))
def IntegerExtreme : Prop := ∀u v:ℤ, IsCoprime u v → (∀j:Fin 5,forms u v j≠0) →
    Extreme u v → size u v < (S u v)^(27506231*(S u v)^2)

/-- Outside the bit-length cut there is no new geometry, CM or transcendental
certificate. The implication is for the clean old target, not the sharp bound. -/
theorem automatic {u v:ℤ} (hc:IsCoprime u v) (hn:∀j:Fin 5,forms u v j≠0)
    (he:¬Extreme u v) : pointHeight u v<target u v := by
  have hs : (1:ℝ)≤S u v := by exact_mod_cast support_pos u v
  have hp : (0:ℝ)<size u v := by exact_mod_cast size_pos hn
  have hle : size u v≤(2:ℕ)^((S u v)^6) := le_of_not_gt he
  have hr : (size u v:ℝ)≤(2:ℝ)^((S u v)^6) := by exact_mod_cast hle
  have hl:=Real.log_le_log hp hr
  rw [Real.log_pow] at hl
  push_cast at hl
  have h1:=mul_le_mul_of_nonneg_left (le_of_lt (by linarith [Real.log_two_lt_d9] : Real.log 2<1))
    (pow_nonneg (Nat.cast_nonneg (S u v):0≤(S u v:ℝ)) 6)
  have hpow : (S u v:ℝ)^6≤(S u v:ℝ)^((49:ℝ)/8) := by
    rw [←Real.rpow_natCast];apply Real.rpow_le_rpow_of_exponent_le hs;norm_num
  have hscale:=mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)≤2^68*((210:ℝ)^300)^2)
    (Real.rpow_nonneg (Nat.cast_nonneg (S u v):0≤(S u v:ℝ)) ((49:ℝ)/8))
  rw [height_log hc];unfold target;linarith

theorem five_iff_old_extreme : FiveContact49Height ↔ OldExtreme := by
  constructor
  · intro H u v hc hn _
    simpa only [target,S,Nat.cast_mul] using H u v hc hn
  · intro H u v hc hn
    by_cases e:Extreme u v
    · simpa only [target,S,Nat.cast_mul] using H u v hc hn e
    · simpa only [target,S,Nat.cast_mul] using automatic hc hn e

theorem literal (H:SharpExtreme) : FiveContact49Height := by
  apply five_iff_old_extreme.mpr
  intro u v hc hn he
  let s:ℝ:=S u v
  have hs : 1≤s := by exact_mod_cast support_pos u v
  have hp : 0<s := lt_of_lt_of_le zero_lt_one hs
  have h:=H u v hc hn he
  change pointHeight u v<27506231*(s^2*Real.log s) at h
  have hl : Real.log s≤s := (Real.log_le_sub_one_of_pos hp).trans (by linarith)
  have h3 : s^2*Real.log s≤s^3 := by
    simpa only [pow_succ] using mul_le_mul_of_nonneg_left hl (sq_nonneg s)
  have hpow : s^3≤s^((49:ℝ)/8) := by
    rw [←Real.rpow_natCast];apply Real.rpow_le_rpow_of_exponent_le hs;norm_num
  have h1:=mul_le_mul_of_nonneg_left (h3.trans hpow) (by norm_num : (0:ℝ)≤27506231)
  have h2:=mul_le_mul_of_nonneg_right (by norm_num : (27506231:ℝ)≤2^68*((210:ℝ)^300)^2)
    (Real.rpow_nonneg hp.le ((49:ℝ)/8))
  change pointHeight u v<2^68*((210:ℝ)^300)^2*s^((49:ℝ)/8)+128
  linarith

/-- On the only remaining pairs, exact integer exponent comparison is
equivalent to the sharp projective-height inequality, including strictness. -/
theorem integer_iff_sharp : IntegerExtreme ↔ SharpExtreme := by
  constructor <;> intro H u v hc hn he
  · have h:=H u v hc hn he
    have hh : (size u v:ℝ)<(S u v:ℝ)^(27506231*(S u v)^2 : ℕ) := by exact_mod_cast h
    have hp : (0:ℝ)<size u v := by exact_mod_cast size_pos hn
    have hl:=Real.log_lt_log hp hh
    rw [Real.log_pow] at hl
    push_cast at hl
    rw [height_log hc];linarith
  · have h:=H u v hc hn he
    have hp : (0:ℝ)<S u v := by exact_mod_cast support_pos u v
    have hlog : Real.log (size u v:ℝ)<Real.log ((S u v:ℝ)^(27506231*(S u v)^2 : ℕ)) := by
      rw [←height_log hc,Real.log_pow];push_cast;linarith
    have hreal : (size u v:ℝ)<(S u v:ℝ)^(27506231*(S u v)^2 : ℕ) :=
      lt_of_not_ge (fun hbad=> (not_lt_of_ge (Real.log_le_log (pow_pos hp _) hbad)) hlog)
    exact_mod_cast hreal

def EmptyTail : Prop := ∀u v:ℤ, IsCoprime u v → (∀j:Fin 5,forms u v j≠0) → ¬Extreme u v

private theorem le_two_pow (n:ℕ) : n≤2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0<(2:ℕ)^n := pow_pos (by decide) n
    omega

theorem integer_ceiling (u v:ℤ) : (S u v)^(27506231*(S u v)^2)≤(2:ℕ)^((S u v)^6) := by
  let s:=S u v
  have hbase : badProduct≤s := by
    change badProduct≤badProduct*radical u v
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left badProduct (show 1≤radical u v from radical_pos u v)
  have hk : 27506231≤s := (show 27506231≤badProduct by rw [bad_product_exact];decide).trans hbase
  have hs : 1≤s := support_pos u v
  have hk3 : 27506231≤s^3 := hk.trans (by
    simpa only [pow_one] using (pow_le_pow_right₀ hs (show 1≤3 by decide)))
  have he : s*(27506231*s^2)≤s^6 := calc
    _ = s^3*27506231 := by ring
    _ ≤ s^3*s^3 := Nat.mul_le_mul_left _ hk3
    _ = s^6 := by ring
  calc
    s^(27506231*s^2) ≤ ((2:ℕ)^s)^(27506231*s^2) :=
      pow_le_pow_left₀ (Nat.zero_le _) (le_two_pow s) _
    _ = (2:ℕ)^(s*(27506231*s^2)) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by decide : 1≤(2:ℕ)) he

/-- No member of this tail could satisfy the sharp upper estimate. Thus the
restricted sharp obligation is precisely nonexistence, not a feasible search
for a flag certifying some actual exception. -/
theorem integer_iff_empty : IntegerExtreme ↔ EmptyTail := by
  constructor
  · intro h u v hc hn e
    have hl : (2:ℕ)^((S u v)^6)<size u v := e
    exact (not_lt_of_ge (integer_ceiling u v)) (hl.trans (h u v hc hn e))
  · intro h u v hc hn e
    exact (h u v hc hn e).elim

theorem literal_of_empty (h:EmptyTail) : FiveContact49Height :=
  five_iff_old_extreme.mpr (by intro u v hc hn e;exact (h u v hc hn e).elim)

theorem literal_integer (H:IntegerExtreme) : FiveContact49Height := literal (integer_iff_sharp.mp H)

end CleanSparseHeightCut318
#print axioms CleanSparseHeightCut318.automatic
#print axioms CleanSparseHeightCut318.five_iff_old_extreme
#print axioms CleanSparseHeightCut318.integer_iff_sharp
#print axioms CleanSparseHeightCut318.integer_iff_empty
#print axioms CleanSparseHeightCut318.literal_of_empty
#print axioms CleanSparseHeightCut318.literal_integer
