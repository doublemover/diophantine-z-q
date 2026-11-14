module
public import Mathlib.Tactic
public section
namespace IntegralBinaryEnergy318
set_option maxHeartbeats 1800000

@[expose] def binaryNorm (a b : ℤ) : ℤ := a^2-a*b-b^2
@[expose] def binaryEnergy (a b : ℤ) : ℤ := 2*a^2-2*a*b+3*b^2
@[expose] def energy (j : Fin 5) (a b c d : ℤ) : ℤ :=
  ![6*binaryEnergy a c+7*binaryEnergy b d,
    2*binaryEnergy a b+21*binaryEnergy c d,
    3*binaryEnergy a b+14*binaryEnergy c d,
    3*binaryEnergy a b+14*binaryEnergy c d,
    2*binaryEnergy a b+21*binaryEnergy c d] j
@[expose] def norm (j : Fin 5) (a b c d : ℤ) : ℤ :=
  ![6*binaryNorm a c-7*binaryNorm b d,
    -2*binaryNorm a b+21*binaryNorm c d,
    3*binaryNorm a b-14*binaryNorm c d,
    -3*binaryNorm a b+14*binaryNorm c d,
    2*binaryNorm a b-21*binaryNorm c d] j
@[expose] def threshold : Fin 5 → ℤ := ![39,109,73,72,96]

/-- Positive-square identity bounds the ENTIRE integer lattice, not a search
window assumed to contain the possible original units. -/
theorem lower (a b : ℤ) : a^2+2*b^2≤binaryEnergy a b := by
  unfold binaryEnergy
  nlinarith [sq_nonneg (a-b)]

private theorem square_interval (x B : ℤ) (hB : 0≤B)
    (h : x^2<(B+1)^2) : -B≤x ∧ x≤B := by
  have hm : -(B+1)<x := by
    by_contra hn
    have hx : B+1≤ -x := by omega
    have hsq := mul_self_le_mul_self (by omega : 0≤B+1) hx
    nlinarith
  have hp : x<B+1 := by
    by_contra hn
    have hx : B+1≤x := by omega
    have hsq := mul_self_le_mul_self (by omega : 0≤B+1) hx
    nlinarith
  omega

/-- Exact finite certificate for reduced form 0; checked by kernel reduction. -/
private theorem box_0 : ∀ (a : Fin 5) (b : Fin 5)
    (c : Fin 3) (d : Fin 3),
    norm 0 ((a.val:ℤ)-2) ((b.val:ℤ)-2) ((c.val:ℤ)-1) ((d.val:ℤ)-1)=1 → 39≤energy 0 ((a.val:ℤ)-2) ((b.val:ℤ)-2) ((c.val:ℤ)-1) ((d.val:ℤ)-1) := by decide

private theorem minimum_0 (a b c d : ℤ)
    (hn : norm 0 a b c d=1) : 39≤energy 0 a b c d := by
  by_contra hh
  have hlt : energy 0 a b c d<39 := by omega
  have hL1 := lower a c
  have hL2 := lower b d
  norm_num [energy] at hlt
  have ha : -(2:ℤ)≤a ∧ a≤2 := by
    apply square_interval a 2 (by norm_num)
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb : -(2:ℤ)≤b ∧ b≤2 := by
    apply square_interval b 2 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc : -(1:ℤ)≤c ∧ c≤1 := by
    apply square_interval c 1 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd : -(1:ℤ)≤d ∧ d≤1 := by
    apply square_interval d 1 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  let af : Fin 5 := ⟨(a+2).toNat,by omega⟩
  have ea : ((af.val:ℤ)-2)=a := by dsimp [af]; omega
  let bf : Fin 5 := ⟨(b+2).toNat,by omega⟩
  have eb : ((bf.val:ℤ)-2)=b := by dsimp [bf]; omega
  let cf : Fin 3 := ⟨(c+1).toNat,by omega⟩
  have ec : ((cf.val:ℤ)-1)=c := by dsimp [cf]; omega
  let df : Fin 3 := ⟨(d+1).toNat,by omega⟩
  have ed : ((df.val:ℤ)-1)=d := by dsimp [df]; omega
  have H := box_0 af bf cf df
  rw [ea,eb,ec,ed] at H
  exact hh (H hn)

/-- Exact finite certificate for reduced form 1; checked by kernel reduction. -/
private theorem box_1 : ∀ (a : Fin 15) (b : Fin 11)
    (c : Fin 5) (d : Fin 3),
    norm 1 ((a.val:ℤ)-7) ((b.val:ℤ)-5) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → 109≤energy 1 ((a.val:ℤ)-7) ((b.val:ℤ)-5) ((c.val:ℤ)-2) ((d.val:ℤ)-1) := by decide

private theorem minimum_1 (a b c d : ℤ)
    (hn : norm 1 a b c d=1) : 109≤energy 1 a b c d := by
  by_contra hh
  have hlt : energy 1 a b c d<109 := by omega
  have hL1 := lower a b
  have hL2 := lower c d
  norm_num [energy] at hlt
  have ha : -(7:ℤ)≤a ∧ a≤7 := by
    apply square_interval a 7 (by norm_num)
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb : -(5:ℤ)≤b ∧ b≤5 := by
    apply square_interval b 5 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc : -(2:ℤ)≤c ∧ c≤2 := by
    apply square_interval c 2 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd : -(1:ℤ)≤d ∧ d≤1 := by
    apply square_interval d 1 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  let af : Fin 15 := ⟨(a+7).toNat,by omega⟩
  have ea : ((af.val:ℤ)-7)=a := by dsimp [af]; omega
  let bf : Fin 11 := ⟨(b+5).toNat,by omega⟩
  have eb : ((bf.val:ℤ)-5)=b := by dsimp [bf]; omega
  let cf : Fin 5 := ⟨(c+2).toNat,by omega⟩
  have ec : ((cf.val:ℤ)-2)=c := by dsimp [cf]; omega
  let df : Fin 3 := ⟨(d+1).toNat,by omega⟩
  have ed : ((df.val:ℤ)-1)=d := by dsimp [df]; omega
  have H := box_1 af bf cf df
  rw [ea,eb,ec,ed] at H
  exact hh (H hn)

/-- Exact finite certificate for reduced form 2; checked by kernel reduction. -/
private theorem box_2 : ∀ (a : Fin 9) (b : Fin 7)
    (c : Fin 5) (d : Fin 3),
    norm 2 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → 73≤energy 2 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1) := by decide

private theorem minimum_2 (a b c d : ℤ)
    (hn : norm 2 a b c d=1) : 73≤energy 2 a b c d := by
  by_contra hh
  have hlt : energy 2 a b c d<73 := by omega
  have hL1 := lower a b
  have hL2 := lower c d
  norm_num [energy] at hlt
  have ha : -(4:ℤ)≤a ∧ a≤4 := by
    apply square_interval a 4 (by norm_num)
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb : -(3:ℤ)≤b ∧ b≤3 := by
    apply square_interval b 3 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc : -(2:ℤ)≤c ∧ c≤2 := by
    apply square_interval c 2 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd : -(1:ℤ)≤d ∧ d≤1 := by
    apply square_interval d 1 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  let af : Fin 9 := ⟨(a+4).toNat,by omega⟩
  have ea : ((af.val:ℤ)-4)=a := by dsimp [af]; omega
  let bf : Fin 7 := ⟨(b+3).toNat,by omega⟩
  have eb : ((bf.val:ℤ)-3)=b := by dsimp [bf]; omega
  let cf : Fin 5 := ⟨(c+2).toNat,by omega⟩
  have ec : ((cf.val:ℤ)-2)=c := by dsimp [cf]; omega
  let df : Fin 3 := ⟨(d+1).toNat,by omega⟩
  have ed : ((df.val:ℤ)-1)=d := by dsimp [df]; omega
  have H := box_2 af bf cf df
  rw [ea,eb,ec,ed] at H
  exact hh (H hn)

/-- Exact finite certificate for reduced form 3; checked by kernel reduction. -/
private theorem box_3 : ∀ (a : Fin 9) (b : Fin 7)
    (c : Fin 5) (d : Fin 3),
    norm 3 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → 72≤energy 3 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1) := by decide

private theorem minimum_3 (a b c d : ℤ)
    (hn : norm 3 a b c d=1) : 72≤energy 3 a b c d := by
  by_contra hh
  have hlt : energy 3 a b c d<72 := by omega
  have hL1 := lower a b
  have hL2 := lower c d
  norm_num [energy] at hlt
  have ha : -(4:ℤ)≤a ∧ a≤4 := by
    apply square_interval a 4 (by norm_num)
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb : -(3:ℤ)≤b ∧ b≤3 := by
    apply square_interval b 3 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc : -(2:ℤ)≤c ∧ c≤2 := by
    apply square_interval c 2 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd : -(1:ℤ)≤d ∧ d≤1 := by
    apply square_interval d 1 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  let af : Fin 9 := ⟨(a+4).toNat,by omega⟩
  have ea : ((af.val:ℤ)-4)=a := by dsimp [af]; omega
  let bf : Fin 7 := ⟨(b+3).toNat,by omega⟩
  have eb : ((bf.val:ℤ)-3)=b := by dsimp [bf]; omega
  let cf : Fin 5 := ⟨(c+2).toNat,by omega⟩
  have ec : ((cf.val:ℤ)-2)=c := by dsimp [cf]; omega
  let df : Fin 3 := ⟨(d+1).toNat,by omega⟩
  have ed : ((df.val:ℤ)-1)=d := by dsimp [df]; omega
  have H := box_3 af bf cf df
  rw [ea,eb,ec,ed] at H
  exact hh (H hn)

/-- Exact finite certificate for reduced form 4; checked by kernel reduction. -/
private theorem box_4 : ∀ (a : Fin 13) (b : Fin 9)
    (c : Fin 5) (d : Fin 3),
    norm 4 ((a.val:ℤ)-6) ((b.val:ℤ)-4) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → 96≤energy 4 ((a.val:ℤ)-6) ((b.val:ℤ)-4) ((c.val:ℤ)-2) ((d.val:ℤ)-1) := by decide

private theorem minimum_4 (a b c d : ℤ)
    (hn : norm 4 a b c d=1) : 96≤energy 4 a b c d := by
  by_contra hh
  have hlt : energy 4 a b c d<96 := by omega
  have hL1 := lower a b
  have hL2 := lower c d
  norm_num [energy] at hlt
  have ha : -(6:ℤ)≤a ∧ a≤6 := by
    apply square_interval a 6 (by norm_num)
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb : -(4:ℤ)≤b ∧ b≤4 := by
    apply square_interval b 4 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc : -(2:ℤ)≤c ∧ c≤2 := by
    apply square_interval c 2 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd : -(1:ℤ)≤d ∧ d≤1 := by
    apply square_interval d 1 (by norm_num)
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  let af : Fin 13 := ⟨(a+6).toNat,by omega⟩
  have ea : ((af.val:ℤ)-6)=a := by dsimp [af]; omega
  let bf : Fin 9 := ⟨(b+4).toNat,by omega⟩
  have eb : ((bf.val:ℤ)-4)=b := by dsimp [bf]; omega
  let cf : Fin 5 := ⟨(c+2).toNat,by omega⟩
  have ec : ((cf.val:ℤ)-2)=c := by dsimp [cf]; omega
  let df : Fin 3 := ⟨(d+1).toNat,by omega⟩
  have ed : ((df.val:ℤ)-1)=d := by dsimp [df]; omega
  have H := box_4 af bf cf df
  rw [ea,eb,ec,ed] at H
  exact hh (H hn)

/-- Every integer solution of the ORIGINAL reduced norm-one equation
satisfies the stated energy lower bound, without a boundedness hypothesis. -/
theorem minimum (j : Fin 5) (a b c d : ℤ) (hn : norm j a b c d=1) :
    threshold j≤energy j a b c d := by
  fin_cases j
  · exact minimum_0 a b c d hn
  · exact minimum_1 a b c d hn
  · exact minimum_2 a b c d hn
  · exact minimum_3 a b c d hn
  · exact minimum_4 a b c d hn
end IntegralBinaryEnergy318
