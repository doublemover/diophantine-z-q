module
public import ActualThreeQMeromorphic318
public section
noncomputable section
open Filter Topology WithTop.LinearOrderedAddCommGroup
namespace ThreeParameterCompositionOrder318
open ThreeCompactParameter318
set_option maxHeartbeats 0

lemma J_comp_order {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    meromorphicOrderAt (fun z => J (f z)) x =
      meromorphicOrderAt (fun z => f z + 27) x +
      3 * meromorphicOrderAt (fun z => f z + 243) x -
      3 * meromorphicOrderAt f x := by
  change meromorphicOrderAt ((f + (fun _ => 27)) * (f + (fun _ => 243))^3 / f^3) x = _
  rw [meromorphicOrderAt_div ((hf.add (MeromorphicAt.const 27 x)).mul
    ((hf.add (MeromorphicAt.const 243 x)).pow 3)) (hf.pow 3),
    meromorphicOrderAt_mul (hf.add (MeromorphicAt.const 27 x))
      ((hf.add (MeromorphicAt.const 243 x)).pow 3),
    meromorphicOrderAt_pow (hf.add (MeromorphicAt.const 243 x)),meromorphicOrderAt_pow hf]
  rfl

lemma J_comp_order_of_neg {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (m : ℤ) (hm : meromorphicOrderAt f x = (m:WithTop ℤ)) (hn : m < 0) :
    meromorphicOrderAt (fun z => J (f z)) x = (m:WithTop ℤ) := by
  have hc (c : ℂ) (hc : c ≠ 0) : meromorphicOrderAt (fun z => f z + c) x = (m:WithTop ℤ) := by
    change meromorphicOrderAt (f + (fun _ => c)) x = _
    rw [meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const c x)]
    · exact hm
    · rw [hm,meromorphicOrderAt_const]
      simpa [hc] using hn
  rw [J_comp_order hf,hc 27 (by norm_num),hc 243 (by norm_num),hm]
  change (m:WithTop ℤ) + ((3:ℤ):WithTop ℤ) * (m:WithTop ℤ) - ((3:ℤ):WithTop ℤ) * (m:WithTop ℤ) = (m:WithTop ℤ)
  rw [←WithTop.coe_mul,←WithTop.coe_add,←WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  ring

lemma J_comp_order_of_pos {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (m : ℤ) (hm : meromorphicOrderAt f x = (m:WithTop ℤ)) (hn : 0 < m) :
    meromorphicOrderAt (fun z => J (f z)) x = (-3*m:ℤ) := by
  have hc (c : ℂ) (hc : c ≠ 0) : meromorphicOrderAt (fun z => f z + c) x = 0 := by
    change meromorphicOrderAt (f + (fun _ => c)) x = _
    rw [meromorphicOrderAt_add_eq_right_of_lt hf]
    · simp [meromorphicOrderAt_const,hc]
    · rw [hm,meromorphicOrderAt_const]
      simpa [hc] using hn
  rw [J_comp_order hf,hc 27 (by norm_num),hc 243 (by norm_num),hm]
  simp only [mul_zero,add_zero,zero_sub]
  change -(((3:ℤ):WithTop ℤ) * (m:WithTop ℤ)) = ((-3*m:ℤ):WithTop ℤ)
  rw [←WithTop.coe_mul,←WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  ring

lemma J_comp_order_nonneg_of_zero {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (hm : meromorphicOrderAt f x = 0) :
    0 ≤ meromorphicOrderAt (fun z => J (f z)) x := by
  have hc (c : ℂ) : 0 ≤ meromorphicOrderAt (fun z => f z + c) x := by
    have h := meromorphicOrderAt_add hf (MeromorphicAt.const c x)
    change min (meromorphicOrderAt f x) (meromorphicOrderAt (fun _ => c) x) ≤
      meromorphicOrderAt (fun z => f z+c) x at h
    by_cases hcz : c=0
    · simp [hm,hcz]
    · simpa [hm,meromorphicOrderAt_const,hcz] using h
  rw [J_comp_order hf,hm,mul_zero,sub_zero]
  apply add_nonneg (hc 27)
  have h := hc 243
  generalize meromorphicOrderAt (fun z => f z + 243) x = a at *
  cases a with
  | top => simp
  | coe a =>
    change ((0:ℤ):WithTop ℤ) ≤ ((3:ℤ):WithTop ℤ) * (a:WithTop ℤ)
    rw [←WithTop.coe_mul,WithTop.coe_le_coe]
    exact mul_nonneg (by norm_num) (by exact_mod_cast h)

end ThreeParameterCompositionOrder318
