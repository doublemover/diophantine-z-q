module
public import IntegralBinaryEnergy318
public section
namespace IntegralBinaryEnergyMinimizers318
open IntegralBinaryEnergy318
set_option maxHeartbeats 3000000

/-- ALL reduced norm-one energy minimizers. Repeated entries in the eight-
point cases keep a common finite index; no extra solutions are introduced. -/
@[expose] def minimizer : Fin 5 → Fin 16 → Fin 4 → ℤ := ![![![-1,-1,-1,-1],![-1,0,-1,-1],![-1,0,-1,1],![-1,1,-1,1],![0,-1,-1,-1],![0,-1,1,-1],![0,0,-1,-1],![0,0,-1,1],![0,0,1,-1],![0,0,1,1],![0,1,-1,1],![0,1,1,1],![1,-1,1,-1],![1,0,1,-1],![1,0,1,1],![1,1,1,1]],![![-2,-3,-1,-1],![-2,-3,0,-1],![-2,-3,0,1],![-2,-3,1,1],![-1,-3,-1,-1],![-1,-3,0,-1],![-1,-3,0,1],![-1,-3,1,1],![1,3,-1,-1],![1,3,0,-1],![1,3,0,1],![1,3,1,1],![2,3,-1,-1],![2,3,0,-1],![2,3,0,1],![2,3,1,1]],![![-3,-1,-1,0],![-3,-1,1,0],![-2,1,-1,0],![-2,1,1,0],![2,-1,-1,0],![2,-1,1,0],![3,1,-1,0],![3,1,1,0],![-3,-1,-1,0],![-3,-1,1,0],![-2,1,-1,0],![-2,1,1,0],![2,-1,-1,0],![2,-1,1,0],![3,1,-1,0],![3,1,1,0]],![![-1,-2,-1,-1],![-1,-2,0,-1],![-1,-2,0,1],![-1,-2,1,1],![1,2,-1,-1],![1,2,0,-1],![1,2,0,1],![1,2,1,1],![-1,-2,-1,-1],![-1,-2,0,-1],![-1,-2,0,1],![-1,-2,1,1],![1,2,-1,-1],![1,2,0,-1],![1,2,0,1],![1,2,1,1]],![![-4,-1,-1,0],![-4,-1,1,0],![-3,1,-1,0],![-3,1,1,0],![3,-1,-1,0],![3,-1,1,0],![4,1,-1,0],![4,1,1,0],![-4,-1,-1,0],![-4,-1,1,0],![-3,1,-1,0],![-3,1,1,0],![3,-1,-1,0],![3,-1,1,0],![4,1,-1,0],![4,1,1,0]]]

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

private theorem box_0 : ∀ (a : Fin 5) (b : Fin 5) (c : Fin 3) (d : Fin 3),
    norm 0 ((a.val:ℤ)-2) ((b.val:ℤ)-2) ((c.val:ℤ)-1) ((d.val:ℤ)-1)=1 → energy 0 ((a.val:ℤ)-2) ((b.val:ℤ)-2) ((c.val:ℤ)-1) ((d.val:ℤ)-1)=39 →
    ∃ k : Fin 16, ![((a.val:ℤ)-2),((b.val:ℤ)-2),((c.val:ℤ)-1),((d.val:ℤ)-1)]=minimizer 0 k := by decide

private theorem equality_0 (a b c d : ℤ)
    (hn : norm 0 a b c d=1) (he : energy 0 a b c d=39) :
    ∃ k : Fin 16, ![a,b,c,d]=minimizer 0 k := by
  have hlt : energy 0 a b c d<40 := by omega
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
  exact H hn he

private theorem box_1 : ∀ (a : Fin 15) (b : Fin 11) (c : Fin 5) (d : Fin 3),
    norm 1 ((a.val:ℤ)-7) ((b.val:ℤ)-5) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → energy 1 ((a.val:ℤ)-7) ((b.val:ℤ)-5) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=109 →
    ∃ k : Fin 16, ![((a.val:ℤ)-7),((b.val:ℤ)-5),((c.val:ℤ)-2),((d.val:ℤ)-1)]=minimizer 1 k := by decide

private theorem equality_1 (a b c d : ℤ)
    (hn : norm 1 a b c d=1) (he : energy 1 a b c d=109) :
    ∃ k : Fin 16, ![a,b,c,d]=minimizer 1 k := by
  have hlt : energy 1 a b c d<110 := by omega
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
  exact H hn he

private theorem box_2 : ∀ (a : Fin 9) (b : Fin 7) (c : Fin 5) (d : Fin 3),
    norm 2 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → energy 2 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=73 →
    ∃ k : Fin 16, ![((a.val:ℤ)-4),((b.val:ℤ)-3),((c.val:ℤ)-2),((d.val:ℤ)-1)]=minimizer 2 k := by decide

private theorem equality_2 (a b c d : ℤ)
    (hn : norm 2 a b c d=1) (he : energy 2 a b c d=73) :
    ∃ k : Fin 16, ![a,b,c,d]=minimizer 2 k := by
  have hlt : energy 2 a b c d<74 := by omega
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
  exact H hn he

private theorem box_3 : ∀ (a : Fin 9) (b : Fin 7) (c : Fin 5) (d : Fin 3),
    norm 3 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → energy 3 ((a.val:ℤ)-4) ((b.val:ℤ)-3) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=72 →
    ∃ k : Fin 16, ![((a.val:ℤ)-4),((b.val:ℤ)-3),((c.val:ℤ)-2),((d.val:ℤ)-1)]=minimizer 3 k := by decide

private theorem equality_3 (a b c d : ℤ)
    (hn : norm 3 a b c d=1) (he : energy 3 a b c d=72) :
    ∃ k : Fin 16, ![a,b,c,d]=minimizer 3 k := by
  have hlt : energy 3 a b c d<73 := by omega
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
  exact H hn he

private theorem box_4 : ∀ (a : Fin 13) (b : Fin 9) (c : Fin 5) (d : Fin 3),
    norm 4 ((a.val:ℤ)-6) ((b.val:ℤ)-4) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=1 → energy 4 ((a.val:ℤ)-6) ((b.val:ℤ)-4) ((c.val:ℤ)-2) ((d.val:ℤ)-1)=96 →
    ∃ k : Fin 16, ![((a.val:ℤ)-6),((b.val:ℤ)-4),((c.val:ℤ)-2),((d.val:ℤ)-1)]=minimizer 4 k := by decide

private theorem equality_4 (a b c d : ℤ)
    (hn : norm 4 a b c d=1) (he : energy 4 a b c d=96) :
    ∃ k : Fin 16, ![a,b,c,d]=minimizer 4 k := by
  have hlt : energy 4 a b c d<97 := by omega
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
  exact H hn he

/-- Equality classification over the ENTIRE integer lattice. Bounds are
proved from energy equality before the finite box is used. -/
theorem equality (j : Fin 5) (a b c d : ℤ)
    (hn : norm j a b c d=1) (he : energy j a b c d=threshold j) :
    ∃ k : Fin 16, ![a,b,c,d]=minimizer j k := by
  fin_cases j
  · exact equality_0 a b c d hn he
  · exact equality_1 a b c d hn he
  · exact equality_2 a b c d hn he
  · exact equality_3 a b c d hn he
  · exact equality_4 a b c d hn he
end IntegralBinaryEnergyMinimizers318
