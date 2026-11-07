module
public import ContactRadical318
public import DetectorHeightTransfer318
public section
namespace ContactHeight318
open ContactRadical318 NumberField Height
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def pointHeight (u v:ℤ) : ℝ := Height.logHeight (![(u:ℚ),(v:ℚ)] : Fin 2→ℚ)

 theorem primitive_height (u v:ℤ) (hc:IsCoprime u v) :
    pointHeight u v=Real.log (max |(u:ℝ)| |(v:ℝ)|) := by
  have he : gcd u (normalize v)=gcd u v := (normalize_associated v).gcd_eq_right u
  have hg : (Finset.univ:Finset (Fin 2)).gcd ![u,v]=1 := by
    simpa [Finset.univ_fin2,Int.normalize_coe_nat,he,←Int.coe_gcd u v] using
      Int.isCoprime_iff_gcd_eq_one.mp hc
  have hh:=Rat.logHeight_eq_max_abs_of_gcd_eq_one hg
  have hsup : (⨆i:Fin 2,|(![u,v]) i|)=max |u| |v| := by
    apply le_antisymm
    · apply ciSup_le
      intro i
      fin_cases i <;> simp
    · apply max_le
      · exact Finite.le_ciSup_of_le 0 (by simp)
      · exact Finite.le_ciSup_of_le 1 (by simp)
  rw [hsup] at hh
  have hv : (fun i:Fin 2=>(![u,v] i:ℚ))=(![(u:ℚ),(v:ℚ)]) := by ext i; fin_cases i <;> rfl
  simpa only [pointHeight,Function.comp_def,hv,Int.cast_max,Int.cast_abs] using hh

 theorem detector_primitive (t:ℚ) : IsCoprime (2*t.num+t.den) t.num := by
  simpa using (Rat.isCoprime_num_den t).symm

/-- Exact determinant-one contact-map height loss, with the sharp log3 budget. -/
 theorem detector_height_loss (t:ℚ) :
    absLogHeight₁ t≤pointHeight (2*t.num+t.den) t.num+Real.log 3 := by
  let M:ℝ:=max |((2*t.num+(t.den:ℤ)):ℝ)| |(t.num:ℝ)|
  have ha:|(t.num:ℝ)|≤M := le_max_right _ _
  have hu:|((2*t.num+(t.den:ℤ)):ℝ)|≤M := le_max_left _ _
  push_cast at hu
  have hb:(t.den:ℝ)≤3*M := by
    have hh:=abs_sub ((2*t.num+(t.den:ℤ):ℤ):ℝ) (2*(t.num:ℝ))
    have he:((2*t.num+(t.den:ℤ):ℤ):ℝ)-2*(t.num:ℝ)=(t.den:ℝ) := by push_cast; ring
    rw [he,abs_of_nonneg (by positivity),abs_mul,show |(2:ℝ)|=2 by norm_num] at hh
    push_cast at hh
    linarith
  have hab:max |(t.num:ℝ)| (t.den:ℝ)≤3*M := max_le (by linarith [abs_nonneg (t.num:ℝ)]) hb
  have hM:0<M := by
    have hd:0<(t.den:ℝ):=by exact_mod_cast t.den_pos
    linarith
  have hpos:0<max |(t.num:ℝ)| (t.den:ℝ) := lt_of_lt_of_le (by exact_mod_cast t.den_pos) (le_max_right _ _)
  have hh:=Real.log_le_log hpos hab
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hM.ne'] at hh
  rw [DetectorHeightTransfer318.rational_height_eq,Rat.logHeight₁_eq_log_max,primitive_height _ _ (detector_primitive t)]
  simpa only [Nat.cast_max,Nat.cast_natAbs,Int.cast_abs,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,add_comm,M] using hh

/-- The sole geometric interface retained here. This is the actual five-contact
height on primitive rational homogeneous coordinates, with the literal bad-prime
product and finite odd-contact radical. It is not asserted as a theorem. -/
@[expose] def FiveContact49Height : Prop := ∀u v:ℤ, IsCoprime u v →
    (∀j:Fin 5,forms u v j≠0) →
    pointHeight u v<2^68*((210:ℝ)^300)^2*((badProduct:ℝ)*(radical u v:ℝ))^((49:ℝ)/8)+128

 theorem absorbed_contact_height (hFive:FiveContact49Height) (u v:ℤ)
    (hc:IsCoprime u v) (hn:∀j:Fin 5,forms u v j≠0) :
    pointHeight u v<HeightSeparation318.heightConstant*(radical u v:ℝ)^((49:ℝ)/8) := by
  apply HeightSeparation318.height_constant_absorption ((210:ℝ)^300) badProduct (radical u v) _
    (by positivity) HeightSeparation318.conductor_constant_bound.le (by positivity)
    (by exact_mod_cast bad_product_bound.le) (by exact_mod_cast (radical_pos u v))
  exact hFive u v hc hn

 theorem radical_weight_bound (u v N:ℤ) (hN:N≠0) (k:ℕ) (hk:0<k)
    (hdiv:∀p∈contactPrimes u v,(p:ℤ)^k∣N) :
    (radical u v:ℝ)^((49:ℝ)/8)≤|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  have h0:0≤(radical u v:ℝ):=by positivity
  have hh:=Real.rpow_le_rpow (pow_nonneg h0 k) (radical_power_le u v N hN k hdiv)
    (show (0:ℝ)≤49/(8*k) by positivity)
  rw [←Real.rpow_natCast,←Real.rpow_mul h0] at hh
  have he:(k:ℝ)*(49/(8*k))=(49:ℝ)/8 := by
    have hk0:(k:ℝ)≠0:=by exact_mod_cast hk.ne'
    field_simp
  simpa only [he] using hh

 theorem detector_from_prime_divisibility (hFive:FiveContact49Height) (t:ℚ)
    (hn:∀j:Fin 5,forms (2*t.num+t.den) t.num j≠0)
    (N:ℤ) (hN:N≠0) (k:ℕ) (hk:0<k)
    (hdiv:∀p∈detectorPrimes t,(p:ℤ)^k∣N) :
    absLogHeight₁ t≤(HeightSeparation318.heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  have hr:1≤(detectorRadical t:ℝ)^((49:ℝ)/8) := Real.one_le_rpow
    (by exact_mod_cast (radical_pos (2*t.num+t.den) t.num)) (by norm_num)
  have hl:0≤Real.log (3:ℝ):=Real.log_nonneg (by norm_num)
  have hrad:=radical_weight_bound (2*t.num+t.den) t.num N hN k hk hdiv
  have hh:=absorbed_contact_height hFive (2*t.num+t.den) t.num (detector_primitive t) hn
  have hfirst:=detector_height_loss t
  have hfinal:absLogHeight₁ t≤(HeightSeparation318.heightConstant+Real.log 3)*(detectorRadical t:ℝ)^((49:ℝ)/8) := by
    have hlog:=mul_le_mul_of_nonneg_left hr hl
    dsimp only [detectorRadical] at *
    nlinarith
  exact hfinal.trans (mul_le_mul_of_nonneg_left hrad (add_nonneg (le_trans (by norm_num : (0:ℝ)≤1) HeightSeparation318.heightConstant_ge_one) hl))

 theorem detector_one_height (N:ℤ) (hN:N≠0) (k:ℕ) :
    absLogHeight₁ (1:ℚ)≤(HeightSeparation318.heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  rw [DetectorHeightTransfer318.rational_height_eq,Rat.logHeight₁_eq_log_max]
  norm_num
  exact mul_nonneg (add_nonneg (le_trans (by norm_num : (0:ℝ)≤1) HeightSeparation318.heightConstant_ge_one) (Real.log_nonneg (by norm_num))) (Real.rpow_nonneg (abs_nonneg _) _)

end
end ContactHeight318
#print axioms ContactHeight318.detector_height_loss
#print axioms ContactHeight318.detector_from_prime_divisibility
#print axioms ContactHeight318.detector_one_height
