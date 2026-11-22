module
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic
public section
noncomputable section

namespace LinearA4GaussianCounts318
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev Plane (K : Type*) := K × K
@[expose] def norm (v : Plane K) : K := v.1^2+v.2^2
@[expose] def diff (v : Plane K) : K := v.1^2-v.2^2
abbrev Fibre {X Y : Type*} (f : X → Y) (r : Y) := {z : X // f z=r}
abbrev χ (K : Type*) [Field K] [Fintype K] [DecidableEq K] : ℤ := quadraticChar K (-1)
abbrev size (K : Type*) [Fintype K] : ℤ := Fintype.card K
@[expose] def fibreSize {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (r : Y) : ℤ :=
  Fintype.card (Fibre f r)

/-- Cardinality by the first free coordinate, with no duplicate fibre
witnesses. Use integer counts so the quadratic-character signs stay literal. -/
theorem count_by_first {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → Prop) [Fintype {z : X × Y // P z.1 z.2}]
    [∀ x, Fintype {y : Y // P x y}] :
    (Fintype.card {z : X × Y // P z.1 z.2}:ℤ) =
      ∑ x : X, (Fintype.card {y : Y // P x y}:ℤ) := by
  let e : {z : X × Y // P z.1 z.2} ≃ (Σ x : X, {y : Y // P x y}) :=
    ⟨fun z => ⟨z.val.1, ⟨z.val.2,z.property⟩⟩,
      fun z => ⟨(z.1,z.2.val),z.2.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e,Fintype.card_sigma,Nat.cast_sum]

theorem sum_split_zero (f : K → ℤ) (c : ℤ) (h : ∀ x, x≠0 → f x=c) :
    ∑ x : K, f x = f 0+(size K-1)*c := by
  classical
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ (0:K))]
  congr 1
  calc
    _ = ∑ x ∈ (Finset.univ : Finset K).erase 0, c :=
      Finset.sum_congr rfl (fun x hx => h x (Finset.mem_erase.mp hx).1)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ (0:K)),
        Finset.card_univ,Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card K),Nat.cast_one]

theorem char_root_count (hp : ringChar K ≠ 2) (r : K) :
    (Fintype.card {a : K // a^2=r}:ℤ) = quadraticChar K r+1 := by
  have e : ({x : K | x^2=r} : Set K).toFinset =
      Finset.univ.filter (fun x : K => x^2=r) := by
    ext x
    simp
  rw [Fintype.card_subtype]
  simpa only [e] using quadraticChar_card_sqrts hp r

theorem mul_count (r : K) :
    fibreSize (fun z : Plane K => z.1*z.2) r =
      (if r=0 then 2*size K-1 else size K-1) := by
  unfold fibreSize
  rw [count_by_first (fun x y : K => x*y=r)]
  have nz (x : K) (hx : x≠0) : (Fintype.card {y : K // x*y=r}:ℤ)=1 := by
    let e : {y : K // x*y=r} ≃ {y : K // y=r/x} :=
      ⟨fun z => ⟨z.val,(eq_div_iff hx).2 (by simpa only [mul_comm z.val x] using z.property)⟩,
        fun z => ⟨z.val,by rw [mul_comm]; exact (eq_div_iff hx).1 z.property⟩,
        fun _ => rfl,fun _ => rfl⟩
    rw [Fintype.card_congr e,Fintype.card_subtype_eq]
    norm_num
  rw [sum_split_zero _ 1 nz]
  split_ifs with hr
  · subst r
    simp [zero_mul]
    ring
  · let empty : IsEmpty {y : K // (0:K)*y=r} :=
      ⟨fun y => hr (((zero_mul y.val).symm.trans y.property).symm)⟩
    have hz : Fintype.card {y : K // (0:K)*y=r} = 0 :=
      Fintype.card_eq_zero_iff.mpr empty
    simp only [hz,Nat.cast_zero,zero_add,mul_one]

/-- Squaring difference, not a heuristic character sum: the two coordinates
are obtained from the invertible linear map (x,y)↦(x+y,x−y). -/
def diffEquiv (h2 : (2:K) ≠ 0) (r : K) :
    Fibre diff r ≃ Fibre (fun z : Plane K => z.1*z.2) r where
  toFun z := ⟨(z.val.1+z.val.2,z.val.1-z.val.2),by
    change (z.val.1+z.val.2)*(z.val.1-z.val.2)=r
    have hz : z.val.1^2-z.val.2^2=r := z.property
    exact (by ring : (z.val.1+z.val.2)*(z.val.1-z.val.2)=z.val.1^2-z.val.2^2).trans hz⟩
  invFun z := ⟨((z.val.1+z.val.2)/2,(z.val.1-z.val.2)/2),by
    change ((z.val.1+z.val.2)/2)^2-((z.val.1-z.val.2)/2)^2=r
    calc
      _ = z.val.1*z.val.2 := by
        field_simp [h2]
        ring
      _ = r := z.property⟩
  left_inv z := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> field_simp [h2] <;> ring
  right_inv z := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> field_simp [h2] <;> ring

theorem diff_count (h2 : (2:K) ≠ 0) (r : K) :
    fibreSize diff r = if r=0 then 2*size K-1 else size K-1 := by
  rw [fibreSize, Fintype.card_congr (diffEquiv h2 r)]
  exact mul_count r

theorem sum_char_diff (hp : ringChar K ≠ 2) (h2 : (2:K) ≠ 0) (r : K) :
    (∑ x : K, quadraticChar K (x^2+r)) = if r=0 then size K-1 else -1 := by
  have count : fibreSize diff r = size K + ∑ x : K, quadraticChar K (x^2+r) := by
    let e : Fibre diff r ≃ {z : K × K // z.2^2=z.1^2+r} :=
      ⟨fun z => ⟨z.val.swap,by
          have h := z.property
          change z.val.1^2-z.val.2^2=r at h
          change z.val.1^2=z.val.2^2+r
          linear_combination h⟩,
        fun z => ⟨z.val.swap,by
          have h := z.property
          change z.val.2^2-z.val.1^2=r
          linear_combination h⟩,
        fun _ => rfl,fun _ => rfl⟩
    rw [fibreSize,Fintype.card_congr e,count_by_first (fun x y : K => y^2=x^2+r)]
    simp only [char_root_count hp,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    ring
  rw [diff_count h2] at count
  split_ifs at count ⊢ <;> linarith

/-- Both exact fibres, including the exceptional zero fibre. The nonzero
formula holds for every r, not only for a chosen or square r. -/
theorem norm_count (hp : ringChar K ≠ 2) (h2 : (2:K) ≠ 0) (r : K) :
    fibreSize norm r = if r=0 then size K+(size K-1)*χ K else size K-χ K := by
  have e : Fibre norm r ≃ {z : K × K // z.2^2=r-z.1^2} :=
    ⟨fun z => ⟨z.val.swap,by
        have h := z.property
        change z.val.1^2+z.val.2^2=r at h
        change z.val.1^2=r-z.val.2^2
        linear_combination h⟩,
      fun z => ⟨z.val.swap,by
        have h := z.property
        change z.val.2^2+z.val.1^2=r
        linear_combination h⟩,
      fun _ => rfl,fun _ => rfl⟩
  rw [fibreSize,Fintype.card_congr e,count_by_first (fun x y : K => y^2=r-x^2)]
  have ch (x : K) : quadraticChar K (r-x^2) = χ K * quadraticChar K (x^2+(-r)) := by
    rw [show r-x^2=(-1)*(x^2+(-r)) by ring,map_mul]
  simp only [char_root_count hp,ch,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,sum_char_diff hp h2]
  by_cases hr : r=0
  · simp only [hr,neg_zero,ite_true]
    ring
  · have hn : -r≠0 := neg_ne_zero.mpr hr
    simp only [hr,hn,ite_false]
    ring

end LinearA4GaussianCounts318
