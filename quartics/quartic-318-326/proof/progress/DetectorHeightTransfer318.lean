module
public import PrimitiveQuadraticMahler318
public import Mathlib.Analysis.Complex.ExponentialBounds
public section
noncomputable section
namespace DetectorHeightTransfer318
open NumberField Height ConcreteG8Domain Polynomial HeightCoverageFromMahler318
set_option maxHeartbeats 0

/-- This is the actual absolute height, with the rational relative normalization discharged. -/
theorem rational_height_eq (q : ℚ) : absLogHeight₁ q=Height.logHeight₁ q := by
  have h1 : absLogHeight₁ q=Real.log (max q.num.natAbs q.den : ℝ) := by
    simpa using RationalAbsoluteHeight.absLogHeight_ratCast ℚ q
  have h2 : Height.mulHeight₁ q=(max q.num.natAbs q.den : ℝ) := by
    simpa using (RationalAbsoluteHeight.mulHeight_ratCast (K:=ℚ) q)
  rw [h1,Height.logHeight₁_eq_log_mulHeight₁,h2]

theorem rational_square_height (q : ℚ) : absLogHeight₁ (q^2)=2*absLogHeight₁ q := by
  simp only [rational_height_eq,Height.logHeight₁_pow,Nat.cast_ofNat]

theorem rational_height_nonneg (q : ℚ) : 0≤absLogHeight₁ q := by
  rw [rational_height_eq]
  exact Height.zero_le_logHeight₁ q

/-- Nonzero lambda is indispensable; it is supplied by the literal detector branch. -/
theorem detector_scale_bound (lambda s : ℚ) (hl : lambda≠0) (T : ℝ)
    (h0 : absLogHeight₁ lambda≤T) (hs : absLogHeight₁ (s^2*lambda)≤T) :
    absLogHeight₁ s≤T := by
  have he : (s^2*lambda)*lambda⁻¹=s^2 := by field_simp
  have hh := Height.logHeight₁_mul_le (s^2*lambda) lambda⁻¹
  rw [he,Height.logHeight₁_inv,Height.logHeight₁_pow] at hh
  simp only [rational_height_eq] at h0 hs ⊢
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem three_detector_bounds (lambda B n : ℚ) (hl : lambda≠0) (T : ℝ)
    (h0 : absLogHeight₁ lambda≤T) (hB : absLogHeight₁ (B^2*lambda)≤T)
    (hn : absLogHeight₁ (n^2*lambda)≤T) :
    absLogHeight₁ B≤T ∧ absLogHeight₁ n≤T :=
  ⟨detector_scale_bound lambda B hl T h0 hB,detector_scale_bound lambda n hl T h0 hn⟩

/-- Literal numerator/denominator height, not an assumed replacement. -/
@[expose] def rationalSize (q : ℚ) : ℝ := (max q.num.natAbs q.den : ℝ)

theorem rationalSize_pos (q : ℚ) : 0<rationalSize q := by
  unfold rationalSize
  exact_mod_cast (lt_of_lt_of_le q.den_pos (le_max_right q.num.natAbs q.den))

theorem rationalSize_height (q : ℚ) : Real.log (rationalSize q)=absLogHeight₁ q :=
  (RationalAbsoluteHeight.absLogHeight_ratCast ℚ q).symm

theorem numerator_bound (q : ℚ) : |(q.num:ℝ)|≤rationalSize q := by
  have h : (q.num.natAbs:ℝ)≤rationalSize q := by
    unfold rationalSize
    exact_mod_cast le_max_left q.num.natAbs q.den
  simpa using h

theorem denominator_bound (q : ℚ) : (q.den:ℝ)≤rationalSize q := by
  unfold rationalSize
  exact_mod_cast le_max_right q.num.natAbs q.den


/-- Denominator clearing is tied to the literal shifted trace B=u+n. -/
theorem cleared_scale_quadratic (u v B n : ℚ)
    (hB : B=u+n) (hn : n=u^2-2*v^2) :
    ∃ (a : ℕ) (b c : ℤ), 0<a ∧
      (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 ∧
      (a:ℝ)≤4*rationalSize B*rationalSize n ∧
      |(b:ℝ)|≤4*rationalSize B*rationalSize n ∧
      |(c:ℝ)|≤4*rationalSize B*rationalSize n := by
  let a : ℕ := B.den*n.den
  let b : ℤ := -2*B.num*n.den+2*n.num*B.den
  let c : ℤ := n.num*B.den
  have ha : 0<a := Nat.mul_pos B.den_pos n.den_pos
  have hc : (a:ℚ)*n=(c:ℚ) := by
    dsimp [a,c]
    push_cast
    linear_combination (B.den:ℚ)*n.den_mul_eq_num
  have hb : (b:ℚ) = -2*(a:ℚ)*u := by
    dsimp [a,b]
    push_cast
    linear_combination 2*(n.den:ℚ)*B.den_mul_eq_num-
      2*(B.den:ℚ)*n.den_mul_eq_num-2*(B.den:ℚ)*(n.den:ℚ)*hB
  have hroot : (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 := by
    have hc' : (c:ℚ)=(a:ℚ)*(u^2-2*v^2) := by rw [←hc,hn]
    ext <;> norm_num [pair,pow_succ]
    · linear_combination u*hb+hc'
    · linear_combination v*hb
  have hBn := numerator_bound B
  have hBd := denominator_bound B
  have hnn := numerator_bound n
  have hnd := denominator_bound n
  have hBpos := (rationalSize_pos B).le
  have hnpos := (rationalSize_pos n).le
  have hdd : (a:ℝ)≤rationalSize B*rationalSize n := by
    dsimp [a]; push_cast
    exact mul_le_mul hBd hnd (by positivity) hBpos
  have hnd' : |(c:ℝ)|≤rationalSize B*rationalSize n := by
    dsimp [c]; push_cast
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤B.den)]
    exact (mul_le_mul hnn hBd (by positivity) hnpos).trans_eq (mul_comm _ _)
  have hbn' : |(B.num:ℝ)*(n.den:ℝ)|≤rationalSize B*rationalSize n := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤n.den)]
    exact mul_le_mul hBn hnd (by positivity) hBpos
  have hbnd : |(b:ℝ)|≤4*rationalSize B*rationalSize n := by
    dsimp [b]; push_cast
    have hh := abs_add_le (-2*(B.num:ℝ)*(n.den:ℝ)) (2*(n.num:ℝ)*(B.den:ℝ))
    have he1 : |-2*(B.num:ℝ)*(n.den:ℝ)|=2*|(B.num:ℝ)*(n.den:ℝ)| := by
      rw [mul_assoc,abs_mul]; norm_num
    have he2 : |2*(n.num:ℝ)*(B.den:ℝ)|=2*|(c:ℝ)| := by
      dsimp [c]; push_cast; rw [mul_assoc,abs_mul]; norm_num
    rw [he1,he2] at hh
    nlinarith
  refine ⟨a,b,c,ha,hroot,?_,hbnd,?_⟩
  · nlinarith [mul_nonneg hBpos hnpos]
  · nlinarith [mul_nonneg hBpos hnpos]

/-- Gcd division cannot enlarge the literal coefficient budget. -/
theorem primitive_scale_quadratic (u v B n : ℚ)
    (hB : B=u+n) (hn : n=u^2-2*v^2) :
    ∃ (a : ℕ) (b c : ℤ), 1≤a ∧ Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1 ∧
      (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 ∧
      (a:ℝ)≤4*rationalSize B*rationalSize n ∧
      |(b:ℝ)|≤4*rationalSize B*rationalSize n ∧
      |(c:ℝ)|≤4*rationalSize B*rationalSize n := by
  obtain ⟨a,b,c,ha,hr,haM,hbM,hcM⟩ := cleared_scale_quadratic u v B n hB hn
  obtain ⟨A,g,Bc,Cc,hA,hg,hea,heb,hec,hprim⟩ := PrimitiveQuadratic318.primitive_triple a b c ha
  have hg0 : (g:K)≠0 := by exact_mod_cast hg.ne'
  have hr' : (A:K)*(pair u v)^2+(Bc:K)*(pair u v)+(Cc:K)=0 := by
    apply (mul_eq_zero.mp (show (g:K)*((A:K)*(pair u v)^2+(Bc:K)*(pair u v)+(Cc:K))=0 from ?_)).resolve_left hg0
    rw [hea,heb,hec] at hr
    push_cast at hr
    linear_combination hr
  have hgR : (1:ℝ)≤g := by exact_mod_cast hg
  have heaR : (a:ℝ)=(g:ℝ)*(A:ℝ) := by exact_mod_cast hea
  have hebR : |(b:ℝ)|=(g:ℝ)*|(Bc:ℝ)| := by
    rw [heb]; push_cast; rw [abs_mul,abs_of_nonneg (by positivity)]
  have hecR : |(c:ℝ)|=(g:ℝ)*|(Cc:ℝ)| := by
    rw [hec]; push_cast; rw [abs_mul,abs_of_nonneg (by positivity)]
  refine ⟨A,Bc,Cc,hA,hprim,hr',?_,?_,?_⟩
  · nlinarith [show (0:ℝ)≤A by positivity]
  · nlinarith [abs_nonneg (Bc:ℝ)]
  · nlinarith [abs_nonneg (Cc:ℝ)]


/-- The exact source constant follows from Mathlib's Landau inequality. -/
theorem quadratic_mahler_bound (a : ℕ) (b c : ℤ) (ha : 1≤a) (M : ℝ)
    (haM : (a:ℝ)≤M) (hbM : |(b:ℝ)|≤M) (hcM : |(c:ℝ)|≤M) :
    ((quadratic a b c).map (Int.castRingHom ℂ)).mahlerMeasure≤Real.sqrt 3*M := by
  let P := (quadratic a b c).map (Int.castRingHom ℂ)
  have hd : P.natDegree=2 := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact Polynomial.natDegree_quadratic (by exact_mod_cast (by omega : a≠0))
  have hc (j : ℕ) : ‖P.coeff j‖≤M := by
    rcases j with _|j
    · simp only [P,coeff_map,quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
      norm_num
      exact hcM
    rcases j with _|j
    · simp only [P,coeff_map,quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
      norm_num
      exact hbM
    rcases j with _|j
    · simp only [P,coeff_map,quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
      norm_num
      exact haM
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simpa using (abs_nonneg (c:ℝ)).trans hcM
  have hs : P.supNorm≤M := by
    obtain ⟨j,hj⟩ := P.exists_eq_supNorm
    rw [hj]
    exact hc j
  have hm := P.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
  rw [hd] at hm
  norm_num only [Nat.cast_ofNat] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 3))

theorem nonrational_product_height_bound (u v B n : ℚ) (hv : v≠0)
    (hB : B=u+n) (hn : n=u^2-2*v^2) :
    2*absLogHeight₁ (pair u v)≤absLogHeight₁ B+absLogHeight₁ n+Real.log 4+Real.log 3/2 := by
  obtain ⟨a,b,c,ha,hg,hr,haM,hbM,hcM⟩ := primitive_scale_quadratic u v B n hB hn
  have hm := quadratic_mahler_bound a b c ha _ haM hbM hcM
  rw [PrimitiveQuadraticMahler318.primitive_height_identity u v hv a b c ha hg hr] at hm
  have hlog := Real.log_le_log (Real.exp_pos _) hm
  rw [Real.log_exp] at hlog
  have h4 : (4:ℝ)≠0 := by norm_num
  have hBp := (rationalSize_pos B).ne'
  have hnp := (rationalSize_pos n).ne'
  have hs : Real.sqrt (3:ℝ)≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  rw [Real.log_mul hs (mul_ne_zero (mul_ne_zero h4 hBp) hnp),
    Real.log_mul (mul_ne_zero h4 hBp) hnp,Real.log_mul h4 hBp,
    Real.log_sqrt (by norm_num : (0:ℝ)≤3),rationalSize_height,rationalSize_height] at hlog
  linarith

theorem product_height_bound (u v B n : ℚ)
    (hB : B=u+n) (hn : n=u^2-2*v^2) :
    2*absLogHeight₁ (pair u v)≤absLogHeight₁ B+absLogHeight₁ n+Real.log 4+Real.log 3/2 := by
  by_cases hv : v=0
  · subst v
    have hn' : n=u^2 := by simpa using hn
    have hx : absLogHeight₁ (pair u 0)=absLogHeight₁ u := by
      rw [RationalPointBox318.pair_zero_ratCast,RationalAbsoluteHeight.absLogHeight_ratCast]
      exact (rationalSize_height u)
    rw [hx,hn',rational_square_height]
    have := rational_height_nonneg B
    have := Real.log_nonneg (show (1:ℝ)≤4 by norm_num)
    have := Real.log_nonneg (show (1:ℝ)≤3 by norm_num)
    linarith
  · exact nonrational_product_height_bound u v B n hv hB hn

/-- The rational and genuinely quadratic branches are both included. -/
theorem detector_product_height (u v B n lambda : ℚ)
    (hB : B=u+n) (hn : n=u^2-2*v^2) (hl : lambda≠0) (T : ℝ)
    (h0 : absLogHeight₁ lambda≤T) (h1 : absLogHeight₁ (B^2*lambda)≤T)
    (h2 : absLogHeight₁ (n^2*lambda)≤T) :
    2*absLogHeight₁ (pair u v)≤2*T+Real.log 4+Real.log 3/2 := by
  obtain ⟨hB',hn'⟩ := three_detector_bounds lambda B n hl T h0 h1 h2
  have := product_height_bound u v B n hB hn
  linarith

theorem absolute_height_square (x : K) : absLogHeight₁ (x^2)=2*absLogHeight₁ x := by
  let : NumberField K := {}
  simp only [AbsoluteHeightNormalization318.absLogHeight_eq_half_relative]
  rw [Height.mulHeight₁_pow,Real.log_pow]
  norm_num
  ring

theorem squared_product_height (u v B n lambda : ℚ)
    (hB : B=u+n) (hn : n=u^2-2*v^2) (hl : lambda≠0) (T : ℝ)
    (h0 : absLogHeight₁ lambda≤T) (h1 : absLogHeight₁ (B^2*lambda)≤T)
    (h2 : absLogHeight₁ (n^2*lambda)≤T) :
    absLogHeight₁ ((pair u v)^2)≤2*T+Real.log 4+Real.log 3/2 := by
  rw [absolute_height_square]
  exact detector_product_height u v B n lambda hB hn hl T h0 h1 h2


/-- A kernel-checked numerical margin for the source's unchanged constant seven. -/
theorem constant_margin : 2+2*Real.log 3+Real.log 4+Real.log 3/2<7 := by
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [h4]
  linarith [Real.log_two_lt_d9,Real.log_three_lt_d9]

theorem absorb_height_constant (H W : ℝ) (hH : 1≤H) (hW : 1≤W) :
    2*((H+Real.log 3)*W)+Real.log 4+Real.log 3/2<7*H*W := by
  have h3 := Real.log_nonneg (show (1:ℝ)≤3 by norm_num)
  have h4 := Real.log_nonneg (show (1:ℝ)≤4 by norm_num)
  have hw : 0<W := by linarith
  have hh : 0<H := by linarith
  have hc : 0≤Real.log 4+Real.log 3/2 := by linarith
  have hc' : 0≤2*Real.log 3+Real.log 4+Real.log 3/2 := by linarith
  have hl := mul_le_mul_of_nonneg_left hW hc
  have hl' := mul_le_mul_of_nonneg_left hH hc'
  have hm := mul_lt_mul_of_pos_right constant_margin hh
  have hf : 2*H+2*Real.log 3+Real.log 4+Real.log 3/2<7*H := by nlinarith
  have hf' := mul_lt_mul_of_pos_right hf hw
  nlinarith

/-- Source-facing transfer with W=|N|^(19/k), once its elementary W≥1 is supplied. -/
theorem source_squared_product_height (u v B n lambda : ℚ)
    (hB : B=u+n) (hn : n=u^2-2*v^2) (hl : lambda≠0) (H W : ℝ)
    (hH : 1≤H) (hW : 1≤W)
    (h0 : absLogHeight₁ lambda≤(H+Real.log 3)*W)
    (h1 : absLogHeight₁ (B^2*lambda)≤(H+Real.log 3)*W)
    (h2 : absLogHeight₁ (n^2*lambda)≤(H+Real.log 3)*W) :
    absLogHeight₁ ((pair u v)^2)<7*H*W :=
  (squared_product_height u v B n lambda hB hn hl _ h0 h1 h2).trans_lt
    (absorb_height_constant H W hH hW)


/-- Literal quadratic-algebra norm and shifted real coefficient, without a supplied norm identity. -/
theorem actual_norm_detector_height (x : K) (lambda : ℚ) (hl : lambda≠0) (H W : ℝ)
    (hH : 1≤H) (hW : 1≤W)
    (h0 : absLogHeight₁ lambda≤(H+Real.log 3)*W)
    (h1 : absLogHeight₁ ((x.re+x.norm)^2*lambda)≤(H+Real.log 3)*W)
    (h2 : absLogHeight₁ (x.norm^2*lambda)≤(H+Real.log 3)*W) :
    absLogHeight₁ (x^2)<7*H*W := by
  rcases x with ⟨u,v⟩
  apply source_squared_product_height u v (u+(pair u v).norm) (pair u v).norm lambda
    rfl _ hl H W hH hW h0 h1 h2
  simp only [QuadraticAlgebra.norm_def,pair]
  ring

/-- The real radical exponent used by the detector is at least one. -/
theorem radical_weight_ge_one (N : ℤ) (hN : N≠0) (k : ℕ) :
    1≤(|(N:ℝ)|^((19:ℝ)/(k:ℝ))) := by
  apply Real.one_le_rpow
  · exact_mod_cast (show (1:ℤ)≤|N| from Int.one_le_abs hN)
  · positivity

theorem actual_norm_radical_height (x : K) (lambda : ℚ) (hl : lambda≠0)
    (H : ℝ) (hH : 1≤H) (N : ℤ) (hN : N≠0) (k : ℕ)
    (h0 : absLogHeight₁ lambda≤(H+Real.log 3)*|(N:ℝ)|^((19:ℝ)/(k:ℝ)))
    (h1 : absLogHeight₁ ((x.re+x.norm)^2*lambda)≤(H+Real.log 3)*|(N:ℝ)|^((19:ℝ)/(k:ℝ)))
    (h2 : absLogHeight₁ (x.norm^2*lambda)≤(H+Real.log 3)*|(N:ℝ)|^((19:ℝ)/(k:ℝ))) :
    absLogHeight₁ (x^2)<7*H*|(N:ℝ)|^((19:ℝ)/(k:ℝ)) :=
  actual_norm_detector_height x lambda hl H _ hH (radical_weight_ge_one N hN k) h0 h1 h2


/-- The transfer works for any nonnegative contact exponent, not only the historical19. -/
theorem actual_norm_exponent_height (x : K) (lambda : ℚ) (hl : lambda≠0)
    (H : ℝ) (hH : 1≤H) (N : ℤ) (hN : N≠0) (e : ℝ) (he : 0≤e)
    (h0 : absLogHeight₁ lambda≤(H+Real.log 3)*|(N:ℝ)|^e)
    (h1 : absLogHeight₁ ((x.re+x.norm)^2*lambda)≤(H+Real.log 3)*|(N:ℝ)|^e)
    (h2 : absLogHeight₁ (x.norm^2*lambda)≤(H+Real.log 3)*|(N:ℝ)|^e) :
    absLogHeight₁ (x^2)<7*H*|(N:ℝ)|^e := by
  apply actual_norm_detector_height x lambda hl H _ hH _ h0 h1 h2
  exact Real.one_le_rpow (by exact_mod_cast (show (1:ℤ)≤|N| from Int.one_le_abs hN)) he

/-- The adopted49/8 contact exponent, divided by the number of selected primes. -/
theorem actual_norm_49_over_8_height (x : K) (lambda : ℚ) (hl : lambda≠0)
    (H : ℝ) (hH : 1≤H) (N : ℤ) (hN : N≠0) (k : ℕ)
    (h0 : absLogHeight₁ lambda≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h1 : absLogHeight₁ ((x.re+x.norm)^2*lambda)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h2 : absLogHeight₁ (x.norm^2*lambda)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k))) :
    absLogHeight₁ (x^2)<7*H*|(N:ℝ)|^((49:ℝ)/(8*k)) :=
  actual_norm_exponent_height x lambda hl H hH N hN _ (by positivity) h0 h1 h2

end DetectorHeightTransfer318
#print axioms DetectorHeightTransfer318.rational_height_eq
#print axioms DetectorHeightTransfer318.detector_scale_bound
#print axioms DetectorHeightTransfer318.three_detector_bounds

#print axioms DetectorHeightTransfer318.product_height_bound
#print axioms DetectorHeightTransfer318.squared_product_height

#print axioms DetectorHeightTransfer318.constant_margin
#print axioms DetectorHeightTransfer318.source_squared_product_height

#print axioms DetectorHeightTransfer318.actual_norm_detector_height
#print axioms DetectorHeightTransfer318.actual_norm_radical_height

#print axioms DetectorHeightTransfer318.actual_norm_exponent_height
#print axioms DetectorHeightTransfer318.actual_norm_49_over_8_height
