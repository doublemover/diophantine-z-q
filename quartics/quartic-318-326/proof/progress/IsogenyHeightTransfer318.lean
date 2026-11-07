module
public import ActualLogWeight318
public section
noncomputable section
namespace IsogenyHeightTransfer318
set_option maxHeartbeats 0
open ActualLogWeight318

theorem one_le_C : 1 ≤ C := by
  unfold C
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤210)

theorem one_le_C_sq : 1 ≤ C^2 := by nlinarith [one_le_C]

theorem source_exponent_bounds (R : ℝ) (hR : 1≤R) :
    1≤R^((49:ℝ)/8) ∧ R≤R^((49:ℝ)/8) ∧
      R^((97:ℝ)/32)≤R^((49:ℝ)/8) := by
  refine ⟨Real.one_le_rpow hR (by norm_num), ?_,
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num)⟩
  simpa using Real.rpow_le_rpow_of_exponent_le hR (show (1:ℝ)≤49/8 by norm_num)

/-- The actual two-dimensional image height budget; the Rémond/Bost and Jacobian inputs are explicit. -/
theorem image_height (R g hJ hImage : ℝ) (hR : 1≤R)
    (hg : g<2^14*C*R^((97:ℝ)/32))
    (hJb : hJ<2^65*C^2*R^((49:ℝ)/8))
    (hImageb : hImage≤hJ+3*g/2) :
    hImage<2^66*C^2*R^((49:ℝ)/8) := by
  obtain ⟨hr1,hr,he⟩ := source_exponent_bounds R hR
  have hC := one_le_C
  have hC2 : C≤C^2 := by nlinarith
  have hg' : g<2^14*C^2*R^((49:ℝ)/8) := by
    apply hg.trans_le
    have ha := mul_le_mul_of_nonneg_left he (show 0≤(2:ℝ)^14*C by positivity)
    have hb := mul_le_mul_of_nonneg_right hC2 (show 0≤(2:ℝ)^14*R^((49:ℝ)/8) by positivity)
    nlinarith
  have hp : 0<C^2*R^((49:ℝ)/8) := by positivity
  nlinarith

theorem isogeny_max_bound (R degree hImage : ℝ) (hR : 1≤R)
    (hd0 : 0≤degree) (hdegree : degree≤2304*R) (hImageb : hImage≤2^66*C^2*R^((49:ℝ)/8)) :
    max 1 (max (Real.log degree) hImage)≤2^66*C^2*R^((49:ℝ)/8) := by
  obtain ⟨hr1,hr,he⟩ := source_exponent_bounds R hR
  have hc := one_le_C_sq
  have hcr : R^((49:ℝ)/8)≤C^2*R^((49:ℝ)/8) := by
    nlinarith [mul_le_mul_of_nonneg_right hc (by positivity : 0≤R^((49:ℝ)/8))]
  have hlog : Real.log degree≤2304*R := (Real.log_le_self hd0).trans hdegree
  apply max_le
  · nlinarith
  · exact max_le (by nlinarith) hImageb


theorem log_fourteen_lt_three : Real.log (14:ℝ)<3 := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ)<14) (by norm_num : (14:ℝ)<2^4)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

theorem log_field_degree_bound (R degree : ℝ) (hR : 1≤R) (hd0 : 0<degree)
    (hd : degree≤2304*R) : Real.log degree<9+Real.log R := by
  have hr0 : 0<R := by linarith
  have hl := Real.log_le_log hd0 hd
  rw [Real.log_mul (by norm_num : (2304:ℝ)≠0) hr0.ne'] at hl
  have hc := Real.log_lt_log (by norm_num : (0:ℝ)<2304) (by norm_num : (2304:ℝ)<2^12)
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith [Real.log_two_lt_d9]

theorem log_image_cap_bound (R : ℝ) (hR : 1≤R) :
    Real.log (2^66*C^2*R^((49:ℝ)/8))<3700+7*Real.log R := by
  have hr0 : 0<R := by linarith
  have hC := C_pos
  rw [Real.log_mul (mul_ne_zero (by positivity) (pow_ne_zero 2 hC.ne'))
      (Real.rpow_pos_of_pos hr0 _).ne',
    Real.log_mul (by positivity) (pow_ne_zero 2 hC.ne'),
    Real.log_pow,Real.log_pow,Real.log_rpow hr0]
  norm_num only [Nat.cast_ofNat]
  linarith [log_C_lt,Real.log_two_lt_d9,Real.log_nonneg hR]

/-- The exact dimension-two half-log isogeny expression, at the source field-degree bound. -/
theorem half_log_isogeny_bound (R degree hImage : ℝ) (hR : 1≤R)
    (hd0 : 0<degree) (hd : degree≤2304*R)
    (hImageb : hImage≤2^66*C^2*R^((49:ℝ)/8)) :
    8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hImage)))<2^17*R^((49:ℝ)/8) := by
  obtain ⟨hr1,hr,he⟩ := source_exponent_bounds R hR
  have hmax := isogeny_max_bound R degree hImage hR hd0.le hd hImageb
  have hpos : 0<max 1 (max (Real.log degree) hImage) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm := Real.log_le_log hpos hmax
  have hlr : Real.log R≤R^((49:ℝ)/8) := (Real.log_le_self (by linarith)).trans hr
  have hcap := log_image_cap_bound R hR
  have hdeg := log_field_degree_bound R degree hR hd0 hd
  have h14 := log_fourteen_lt_three
  nlinarith

/-- Increasing a Faltings normalization only enlarges the maximum in the primary isogeny theorem. -/
theorem half_log_expression_mono (degree hOriginal hShifted : ℝ)
    (hh : hOriginal≤hShifted) :
    8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hOriginal)))≤
    8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hShifted))) := by
  have hp : 0<max 1 (max (Real.log degree) hOriginal) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm := Real.log_le_log hp (max_le_max (le_refl (1:ℝ)) (max_le_max (le_refl _) hh))
  linarith

/-- The actual isogeny height variation is retained as a premise, not assumed to be zero. -/
theorem surface_height (R degree hImage hSurface : ℝ) (hR : 1≤R)
    (hd0 : 0<degree) (hd : degree≤2304*R)
    (hImageb : hImage<2^66*C^2*R^((49:ℝ)/8))
    (hvariation : hSurface≤hImage+8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hImage)))) :
    hSurface<2^67*C^2*R^((49:ℝ)/8) := by
  have hi := half_log_isogeny_bound R degree hImage hR hd0 hd hImageb.le
  have hc := one_le_C_sq
  have hp : 0≤R^((49:ℝ)/8) := Real.rpow_nonneg (by linarith) _
  have hm := mul_le_mul_of_nonneg_right hc hp
  nlinarith

/-- GR2022 states its bound for the original height; the source may safely insert the larger shifted height. -/
theorem surface_height_from_original (R degree hOriginal hImage hSurface : ℝ)
    (hR : 1≤R) (hd0 : 0<degree) (hd : degree≤2304*R)
    (hImageb : hImage<2^66*C^2*R^((49:ℝ)/8))
    (hNormalization : hOriginal≤hImage)
    (hvariation : hSurface≤hImage+8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hOriginal)))) :
    hSurface<2^67*C^2*R^((49:ℝ)/8) := by
  apply surface_height R degree hImage hSurface hR hd0 hd hImageb
  have hm := half_log_expression_mono degree hOriginal hImage hNormalization
  linarith

/-- The retained geometric height comparison has its true additive constant, with slack to 128. -/
theorem contact_height_from_surface (R hSurface hContact : ℝ)
    (hSurfaceb : hSurface<2^67*C^2*R^((49:ℝ)/8))
    (hGeometric : hContact≤2*hSurface+120) :
    hContact<2^68*C^2*R^((49:ℝ)/8)+128 := by nlinarith

/-- The source CM bound is dominated separately; no modular-Jacobian argument is used. -/
theorem contact_height_CM (R hContact : ℝ) (hR : 1≤R) (hCM : hContact≤854*R) :
    hContact<2^68*C^2*R^((49:ℝ)/8)+128 := by
  obtain ⟨hr1,hr,he⟩ := source_exponent_bounds R hR
  have hc := one_le_C_sq
  have hm := mul_le_mul_of_nonneg_right hc (show 0≤R^((49:ℝ)/8) by positivity)
  nlinarith


/-- Assembly of the real-valued consequences of the named geometric/arithmetic producers. -/
theorem source_nonCM_height (R d N g degree hJ hImage hSurface hContact : ℝ)
    (hR : 1≤R) (hd1 : 1≤d) (hN1 : 1≤N) (hgd : g≤d)
    (hindex : d<2^14*C*R^((97:ℝ)/32)) (hlevel : N≤C*R^2)
    (hJb : hJ≤2^11*d^2*(Real.log (6*d*N))^2)
    (hImageb : hImage≤hJ+3*g/2)
    (hdegree0 : 0<degree) (hdegree : degree≤2304*R)
    (hvariation : hSurface≤hImage+8*(32*Real.log 14+Real.log degree+
      Real.log (max 1 (max (Real.log degree) hImage))))
    (hGeometric : hContact≤2*hSurface+120) :
    hContact<2^68*C^2*R^((49:ℝ)/8)+128 := by
  have hj := actual_jacobian_growth R d N hJ hR hd1 hN1 hindex hlevel hJb
  have hi := image_height R g hJ hImage hR (hgd.trans_lt hindex) hj hImageb
  exact contact_height_from_surface R hSurface hContact
    (surface_height R degree hImage hSurface hR hdegree0 hdegree hi hvariation) hGeometric

/-- The historical fixed constant dominates the adopted 49/8 bound without changing its exponent. -/
theorem inherited_contact_constant (B M hContact : ℝ) (hB : 1≤B) (hM : 1≤M)
    (hh : hContact≤2^68*C^2*(B*M)^((49:ℝ)/8)+128) :
    hContact≤(2^110*C^6*B^19+128)*M^((49:ℝ)/8) := by
  have hB0 : 0≤B := by linarith
  have hM0 : 0≤M := by linarith
  have hm1 := Real.one_le_rpow hM (show (0:ℝ)≤49/8 by norm_num)
  have hb1 := Real.one_le_rpow hB (show (0:ℝ)≤49/8 by norm_num)
  have hbp : B^((49:ℝ)/8)≤B^19 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hB (show (49:ℝ)/8≤(19:ℕ) by norm_num)
  have hcp : C^2≤C^6 := by
    exact pow_le_pow_right₀ one_le_C (by norm_num : 2≤6)
  have hc2 := one_le_C_sq
  have hcb : C^2*B^((49:ℝ)/8)≤C^6*B^19 :=
    mul_le_mul hcp hbp (by positivity) (by positivity)
  have hcb0 : 0≤C^6*B^19 := by positivity
  have hbudget : 2^68*C^2*B^((49:ℝ)/8)≤2^110*C^6*B^19 := by
    have h := mul_le_mul_of_nonneg_left hcb (show (0:ℝ)≤2^68 by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hbudget (show 0≤M^((49:ℝ)/8) by positivity)
  rw [Real.mul_rpow hB0 hM0] at hh
  nlinarith

end IsogenyHeightTransfer318
