module
public import ContactCoordinates318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace ComplexLegendreCoordinates318
set_option maxHeartbeats 800000
local instance : DecidableEq ℂ := Classical.decEq ℂ

@[expose] def legendreJ (t : ℂ) : ℂ := 256*(1-t+t^2)^3/(t^2*(1-t)^2)
@[expose] def crossRatios (l : ℂ) : Finset ℂ := by
  classical
  exact {l,1-l,1/l,1/(1-l),(l-1)/l,l/(l-1)}

lemma legendreJ_rat (t : ℚ) : legendreJ (t : ℂ) = (ContactCoordinates318.legendreJ t : ℂ) := by
  simp [legendreJ, ContactCoordinates318.legendreJ]

lemma crossRatios_rat (l : ℚ) :
    crossRatios (l : ℂ) = (ContactCoordinates318.crossRatios l).image (fun q : ℚ => (q : ℂ)) := by
  classical
  simp [crossRatios, ContactCoordinates318.crossRatios]

lemma factorization (t l : ℂ) :
    (1-t+t^2)^3*l^2*(1-l)^2-(1-l+l^2)^3*t^2*(1-t)^2 =
      -(t-l)*(t+l-1)*(l*t-1)*((1-l)*t-1)*(l*t-l+1)*((l-1)*t-l) := by ring

/-- The complete geometric j-fiber consists of the six actual cross-ratios.
This is an identity in C, not an inference of rationality from a rational j. -/
theorem equal_legendre_mem (t l : ℂ) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hj : legendreJ t = legendreJ l) :
    t ∈ crossRatios l := by
  classical
  have ht : t^2*(1-t)^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1)))
  have hl : l^2*(1-l)^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hl0) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hl1)))
  have he := (div_eq_div_iff ht hl).mp hj
  have hp : (1-t+t^2)^3*l^2*(1-l)^2-(1-l+l^2)^3*t^2*(1-t)^2 = 0 := by
    have hmul : (256 : ℂ)*((1-t+t^2)^3*l^2*(1-l)^2-
        (1-l+l^2)^3*t^2*(1-t)^2) = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  rw [factorization] at hp
  simp only [mul_eq_zero,neg_eq_zero,sub_eq_zero,or_assoc] at hp
  simp only [crossRatios,Finset.mem_insert,Finset.mem_singleton]
  rcases hp with h|h|h|h|h|h
  · exact Or.inl h
  · right; left; linear_combination h
  · right; right; left
    apply (eq_div_iff hl0).mpr
    linear_combination h
  · right; right; right; left
    apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hl1))).mpr
    linear_combination h
  · right; right; right; right; left
    apply (eq_div_iff hl0).mpr
    linear_combination h
  · right; right; right; right; right
    apply (eq_div_iff (sub_ne_zero.mpr hl1)).mpr
    linear_combination h

/-- A complex parameter with this SPECIFIC rational Legendre invariant has
a rational representative because every member of its full six-point fiber
is rational. No general rational-j-implies-rational-parameter claim is made. -/
theorem rational_parameter (t : ℂ) (l : ℚ) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (hj : legendreJ t = (ContactCoordinates318.legendreJ l : ℂ)) :
    ∃ q : ℚ, t = (q : ℂ) := by
  classical
  have hmem : t ∈ crossRatios (l : ℂ) :=
    equal_legendre_mem t (l : ℂ) ht0 ht1
      (by exact_mod_cast hl0) (by exact_mod_cast hl1) (hj.trans (legendreJ_rat l).symm)
  rw [crossRatios_rat] at hmem
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hmem
  exact ⟨q,hq.symm⟩

/-- The four original published quartic-row invariants force the SAME
normalized complex branch values. Rationality is derived, not supplied. -/
theorem coordinates_of_original_models (l m : ℂ) (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (hm0 : m ≠ 0) (hm1 : m ≠ 1)
    (h30 : legendreJ l = (ContactCoordinates318.quarticJ (-43) (-686) (-2915) (-1372) (-172) : ℂ))
    (h42 : legendreJ m = (ContactCoordinates318.quarticJ (-43) 600 (-986) (-600) (-43) : ℂ))
    (h70 : legendreJ (m/l) = (ContactCoordinates318.quarticJ (-43) 256 (-130) (-768) (-387) : ℂ))
    (h105 : legendreJ ((m-1)/(l-1)) = (ContactCoordinates318.quarticJ (-43) 2 505 12 (-1548) : ℂ)) :
    l = 2401 ∧ m = -343/32 := by
  obtain ⟨e30,e42,_,_⟩ := ContactCoordinates318.original_quartic_invariants
  have hlJ : legendreJ l = (ContactCoordinates318.legendreJ (1/2401) : ℂ) := by rw [h30,e30]
  have hmJ : legendreJ m = (ContactCoordinates318.legendreJ (32/375) : ℂ) := by rw [h42,e42]
  obtain ⟨lq,rfl⟩ := rational_parameter l (1/2401) hl0 hl1 (by norm_num) (by norm_num) hlJ
  obtain ⟨mq,rfl⟩ := rational_parameter m (32/375) hm0 hm1 (by norm_num) (by norm_num) hmJ
  have h30q : ContactCoordinates318.legendreJ lq =
      ContactCoordinates318.quarticJ (-43) (-686) (-2915) (-1372) (-172) := by
    rw [legendreJ_rat] at h30
    exact_mod_cast h30
  have h42q : ContactCoordinates318.legendreJ mq =
      ContactCoordinates318.quarticJ (-43) 600 (-986) (-600) (-43) := by
    rw [legendreJ_rat] at h42
    exact_mod_cast h42
  have h70q : ContactCoordinates318.legendreJ (mq/lq) =
      ContactCoordinates318.quarticJ (-43) 256 (-130) (-768) (-387) := by
    have h := h70
    rw [← Rat.cast_div,legendreJ_rat] at h
    exact_mod_cast h
  have h105q : ContactCoordinates318.legendreJ ((mq-1)/(lq-1)) =
      ContactCoordinates318.quarticJ (-43) 2 505 12 (-1548) := by
    have h := h105
    have hc : ((mq : ℂ)-1)/((lq : ℂ)-1) = (((mq-1)/(lq-1) : ℚ) : ℂ) := by
      simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_one]
    rw [hc,legendreJ_rat] at h
    exact_mod_cast h
  obtain ⟨hl,hm⟩ := ContactCoordinates318.coordinates_of_original_models lq mq
    (by exact_mod_cast hl0) (by exact_mod_cast hl1)
    (by exact_mod_cast hm0) (by exact_mod_cast hm1) h30q h42q h70q h105q
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hm
end ComplexLegendreCoordinates318
