module
public import Contact49Growth318
public section
noncomputable section
namespace FiveContactMetricBounds318
set_option maxHeartbeats 0

/-- The six actual differences for the scaled finite contacts0,32,76832,−343. -/
theorem contact_differences :
    (32:ℤ)-0=32 ∧ 76832-0=76832 ∧ 0-(-343)=343 ∧
    76832-32=76800 ∧ 32-(-343)=375 ∧ 76832-(-343)=77175 := by norm_num

theorem difference_factorizations :
    (32:ℕ)=2^5 ∧ 76832=2^5*7^4 ∧ 343=7^3 ∧
    76800=2^10*3*5^2 ∧ 375=3*5^3 ∧ 77175=3^2*5^2*7^3 := by norm_num

/-- Thus J is exactly the lcm, not just a multiple of the determinant support. -/
theorem exact_J :
    Nat.lcm 32 (Nat.lcm 76832 (Nat.lcm 343 (Nat.lcm 76800 (Nat.lcm 375 77175))))=2765952000 := by norm_num

theorem J_factorization : (2765952000:ℕ)=2^10*3^2*5^3*7^4 := by norm_num

theorem metric_constant : (16:ℕ)*(12*76832+9)^3=12540153541944538512 := by norm_num

/-- The arithmetic budget in the original geometric comparison(G). -/
theorem additive_budget_integer :
    (210:ℕ)*2765952000^2*(4*12540153541944538512)*32*16<2^160 := by norm_num

/-- If at most one contact order exceeds delta, the four-contact vertical loss is at most2delta. -/
theorem vertical_budget (a b c d m delta : ℝ)
    (ha : a≤m) (hb : b≤m) (hc : c≤m) (hd : d≤m)
    (he : (b≤delta ∧ c≤delta ∧ d≤delta) ∨
      (a≤delta ∧ c≤delta ∧ d≤delta) ∨
      (a≤delta ∧ b≤delta ∧ d≤delta) ∨
      (a≤delta ∧ b≤delta ∧ c≤delta)) :
    -2*delta≤2*m-(a+b+c+d) := by
  by_cases hm : m≤delta
  · linarith
  · rcases he with h|h|h|h <;> rcases h with ⟨h1,h2,h3⟩ <;> linarith

theorem negative_contact_budget (r : ℝ) (hr : r<0) :
    0≤2*r-4*r ∧ 0≤r+2*r-4*r := by constructor <;> linarith

theorem reciprocal_pair (a b : ℝ) (ha : 0<a) (hb : 0<b) : 2≤a/b+b/a := by
  have h : 0<a*b := mul_pos ha hb
  apply (mul_le_mul_iff_left₀ h).mp
  field_simp
  nlinarith [sq_nonneg (a-b)]

/-- The exact Cauchy lower bound used in the curvature numerator. -/
theorem four_reciprocals (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    16≤(a+b+c+d)*(1/a+1/b+1/c+1/d) := by
  have hab := reciprocal_pair a b ha hb
  have hac := reciprocal_pair a c ha hc
  have had := reciprocal_pair a d ha hd
  have hbc := reciprocal_pair b c hb hc
  have hbd := reciprocal_pair b d hb hd
  have hcd := reciprocal_pair c d hc hd
  have he : (a+b+c+d)*(1/a+1/b+1/c+1/d)=
      4+(a/b+b/a)+(a/c+c/a)+(a/d+d/a)+(b/c+c/b)+(b/d+d/b)+(c/d+d/c) := by
    field_simp; ring
  rw [he]
  linarith

theorem curvature_numerator (a b c d G : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hG : G≤16) :
    1/a+1/b+1/c+1/d≤(1+a+b+c+d)*(1/a+1/b+1/c+1/d)-G := by
  have hh := four_reciprocals a b c d ha hb hc hd
  nlinarith

@[expose] def tripleSum (a b c d : ℝ) := a*b*c+a*b*d+a*c*d+b*c*d

theorem triple_product_lower (a b c : ℝ) (ha : 1/2≤a) (hb : 1/2≤b) (hc : 1/2≤c) :
    (1:ℝ)/8≤a*b*c := by
  calc
    (1:ℝ)/8=(1/2)*(1/2)*(1/2) := by norm_num
    _ ≤ a*b*c := by gcongr

theorem near_triple_bound (a b c d : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (he : (1/2≤b ∧ 1/2≤c ∧ 1/2≤d) ∨
      (1/2≤a ∧ 1/2≤c ∧ 1/2≤d) ∨
      (1/2≤a ∧ 1/2≤b ∧ 1/2≤d) ∨
      (1/2≤a ∧ 1/2≤b ∧ 1/2≤c)) :
    (1:ℝ)/8≤tripleSum a b c d := by
  have habc : 0≤a*b*c := by positivity
  have habd : 0≤a*b*d := by positivity
  have hacd : 0≤a*c*d := by positivity
  have hbcd : 0≤b*c*d := by positivity
  unfold tripleSum
  rcases he with h|h|h|h <;> rcases h with ⟨h1,h2,h3⟩
  · linarith [triple_product_lower b c d h1 h2 h3]
  · linarith [triple_product_lower a c d h1 h2 h3]
  · linarith [triple_product_lower a b d h1 h2 h3]
  · linarith [triple_product_lower a b c h1 h2 h3]

theorem near_curvature_bound (S U : ℝ) (hS : 1/8≤S)
    (hU : 0<U) (hUM : U≤12*76832+9) :
    (12540153541944538512:ℝ)⁻¹≤S/(2*U^3) := by
  have hpow : U^3≤(12*76832+9:ℝ)^3 := pow_le_pow_left₀ hU.le hUM 3
  have hden : 0<2*U^3 := by positivity
  apply (le_div_iff₀ hden).mpr
  norm_num at hpow ⊢
  nlinarith

theorem far_triple_bound (a b c d r : ℝ) (hr : 0≤r)
    (ha : r/2≤a) (hb : r/2≤b) (hc : r/2≤c) (hd : r/2≤d) :
    r^3/2≤tripleSum a b c d := by
  have ha0 : 0≤a := by linarith
  have hb0 : 0≤b := by linarith
  have hc0 : 0≤c := by linarith
  have hd0 : 0≤d := by linarith
  have habc : (r/2)^3≤a*b*c := by calc
    _=(r/2)*(r/2)*(r/2) := by ring
    _≤a*b*c := by gcongr
  have habd : (r/2)^3≤a*b*d := by calc
    _=(r/2)*(r/2)*(r/2) := by ring
    _≤a*b*d := by gcongr
  have hacd : (r/2)^3≤a*c*d := by calc
    _=(r/2)*(r/2)*(r/2) := by ring
    _≤a*c*d := by gcongr
  have hbcd : (r/2)^3≤b*c*d := by calc
    _=(r/2)*(r/2)*(r/2) := by ring
    _≤b*c*d := by gcongr
  unfold tripleSum
  nlinarith

theorem far_curvature_bound (S U r : ℝ) (hr : 0<r) (hS : r^3/2≤S)
    (hU : 0<U) (hUr : U≤7*r) :
    (1372:ℝ)⁻¹≤S/(2*U^3) := by
  have hpow : U^3≤(7*r)^3 := pow_le_pow_left₀ hU.le hUr 3
  apply (le_div_iff₀ (show 0<2*U^3 by positivity)).mpr
  norm_num
  nlinarith


@[expose] def contact (i : Fin 4) : ℂ := ![0,32,76832,-343] i
@[expose] def radius (z : ℂ) (i : Fin 4) : ℝ := dist z (contact i)
@[expose] def U (z : ℂ) : ℝ := 1+∑i : Fin 4,radius z i

theorem contact_norm (i : Fin 4) : ‖contact i‖≤76832 := by
  fin_cases i <;> norm_num [contact]

theorem contact_separation (i j : Fin 4) (h : i≠j) : 1≤dist (contact i) (contact j) := by
  fin_cases i <;> fin_cases j <;> norm_num [contact,dist_eq_norm] at *

/-- Exact actual contact geometry supplies the three large radii. -/
theorem at_most_one_small (z : ℂ) : ∃i : Fin 4, ∀j, j≠i → 1/2≤radius z j := by
  by_cases hall : ∀j : Fin 4,1/2≤radius z j
  · exact ⟨0,fun j _=>hall j⟩
  · push_neg at hall
    obtain ⟨i,hi⟩ := hall
    refine ⟨i,fun j hji=>?_⟩
    have hs := contact_separation i j (Ne.symm hji)
    have ht : dist (contact i) (contact j)≤radius z i+radius z j := by
      simpa only [radius,dist_comm (contact i) z] using dist_triangle (contact i) z (contact j)
    linarith

theorem U_pos (z : ℂ) : 0<U z := by
  unfold U radius
  positivity

theorem near_U (z : ℂ) (hz : ‖z‖≤2*76832+2) : U z≤12*76832+9 := by
  have hr (i : Fin 4) : radius z i≤3*76832+2 := by
    have hh := norm_sub_le z (contact i)
    have hi := contact_norm i
    rw [radius,dist_eq_norm]
    linarith
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hr i)
  norm_num at hh
  unfold U
  linarith

theorem far_radii (z : ℂ) (hz : 2*76832+2<‖z‖) (i : Fin 4) :
    ‖z‖/2≤radius z i ∧ radius z i≤3*‖z‖/2 := by
  have hu := norm_sub_le z (contact i)
  have hl := norm_sub_norm_le z (contact i)
  have hi := contact_norm i
  rw [radius,dist_eq_norm]
  constructor <;> linarith

theorem far_U (z : ℂ) (hz : 2*76832+2<‖z‖) : U z≤7*‖z‖ := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(far_radii z hz i).2)
  norm_num at hh
  unfold U
  linarith


/-- The actual contact distances satisfy the source's uniform curvature quotient bound. -/
theorem global_curvature_ratio_bound (z : ℂ) :
    (12540153541944538512:ℝ)⁻¹≤
      tripleSum (radius z 0) (radius z 1) (radius z 2) (radius z 3)/(2*(U z)^3) := by
  have hr (i : Fin 4) : 0≤radius z i := dist_nonneg
  by_cases hz : ‖z‖≤2*76832+2
  · apply near_curvature_bound _ _ _ (U_pos z) (near_U z hz)
    apply near_triple_bound _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3)
    obtain ⟨i,hi⟩ := at_most_one_small z
    fin_cases i
    · exact Or.inl ⟨hi 1 (by decide),hi 2 (by decide),hi 3 (by decide)⟩
    · exact Or.inr (Or.inl ⟨hi 0 (by decide),hi 2 (by decide),hi 3 (by decide)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hi 0 (by decide),hi 1 (by decide),hi 3 (by decide)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hi 0 (by decide),hi 1 (by decide),hi 2 (by decide)⟩))
  · have hz' : 2*76832+2<‖z‖ := lt_of_not_ge hz
    have hS := far_triple_bound _ _ _ _ ‖z‖ (norm_nonneg z)
      (far_radii z hz' 0).1 (far_radii z hz' 1).1 (far_radii z hz' 2).1 (far_radii z hz' 3).1
    have hh := far_curvature_bound _ _ ‖z‖ (by linarith) hS (U_pos z) (far_U z hz')
    exact (by norm_num : (12540153541944538512:ℝ)⁻¹≤(1372:ℝ)⁻¹).trans hh

end FiveContactMetricBounds318
#print axioms FiveContactMetricBounds318.exact_J
#print axioms FiveContactMetricBounds318.vertical_budget
#print axioms FiveContactMetricBounds318.curvature_numerator
#print axioms FiveContactMetricBounds318.near_curvature_bound
#print axioms FiveContactMetricBounds318.far_curvature_bound

#print axioms FiveContactMetricBounds318.global_curvature_ratio_bound
