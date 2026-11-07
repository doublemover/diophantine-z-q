module
public import Mathlib.Tactic
public section
noncomputable section
namespace ContactCoordinates318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def legendreJ (t:ℚ):ℚ := 256*(1-t+t^2)^3/(t^2*(1-t)^2)
@[expose] def quarticJ (a b c d e:ℚ):ℚ :=
  let I:=12*a*e-3*b*d+c^2
  let J:=72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3
  6912*I^3/(4*I^3-J^2)
@[expose] def crossRatios (l:ℚ):Finset ℚ :=
  {l,1-l,1/l,1/(1-l),(l-1)/l,l/(l-1)}

theorem legendre_factorization (t l:ℚ) :
    (1-t+t^2)^3*l^2*(1-l)^2-(1-l+l^2)^3*t^2*(1-t)^2 =
      -(t-l)*(t+l-1)*(l*t-1)*((1-l)*t-1)*(l*t-l+1)*((l-1)*t-l) := by ring

/-- Equality of actual Legendre invariants forces precisely the six cross-ratios. -/
theorem equal_legendre_mem (t l:ℚ) (ht0:t≠0) (ht1:t≠1) (hl0:l≠0) (hl1:l≠1)
    (hj:legendreJ t=legendreJ l) : t∈crossRatios l := by
  have ht: t^2*(1-t)^2≠0 := mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1)))
  have hl: l^2*(1-l)^2≠0 := mul_ne_zero (pow_ne_zero 2 hl0) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hl1)))
  have he := (div_eq_div_iff ht hl).mp hj
  have hp: (1-t+t^2)^3*l^2*(1-l)^2-(1-l+l^2)^3*t^2*(1-t)^2=0 := by
    nlinarith only [he]
  rw [legendre_factorization] at hp
  simp only [mul_eq_zero,neg_eq_zero,sub_eq_zero,or_assoc] at hp
  simp only [crossRatios,Finset.mem_insert,Finset.mem_singleton]
  rcases hp with h|h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by linarith))
  · right;right;left
    apply (eq_div_iff hl0).mpr
    nlinarith only [h]
  · right;right;right;left
    apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hl1))).mpr
    nlinarith only [h]
  · right;right;right;right;left
    apply (eq_div_iff hl0).mpr
    nlinarith only [h]
  · right;right;right;right;right
    apply (eq_div_iff (sub_ne_zero.mpr hl1)).mpr
    nlinarith only [h]

theorem original_quartic_invariants :
    quarticJ (-43) (-686) (-2915) (-1372) (-172)=legendreJ (1/2401) ∧
    quarticJ (-43) 600 (-986) (-600) (-43)=legendreJ (32/375) ∧
    quarticJ (-43) 256 (-130) (-768) (-387)=legendreJ (1/225) ∧
    quarticJ (-43) 2 505 12 (-1548)=legendreJ (5/1029) := by
  norm_num [quarticJ,legendreJ]

/-- The actual labeled four-subset invariants determine the unique normalized contact tuple. -/
theorem contact_coordinates_unique (l m:ℚ) (hl:l∈crossRatios (1/2401))
    (hm:m∈crossRatios (32/375))
    (h70:legendreJ (m/l)=legendreJ (1/225))
    (h105:legendreJ ((m-1)/(l-1))=legendreJ (5/1029)) :
    l=2401 ∧ m= -343/32 := by
  norm_num [crossRatios] at hl hm
  rcases hl with hl|hl|hl|hl|hl|hl <;> rcases hm with hm|hm|hm|hm|hm|hm <;>
    simp_all [legendreJ] <;> norm_num at *


@[expose] def quarticDen (a b c d e:ℚ):ℚ :=
  let I:=12*a*e-3*b*d+c^2
  let J:=72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3
  4*I^3-J^2

theorem source_quartics_nondegenerate :
    quarticDen (-43) (-686) (-2915) (-1372) (-172)≠0 ∧
    quarticDen (-43) 600 (-986) (-600) (-43)≠0 ∧
    quarticDen (-43) 256 (-130) (-768) (-387)≠0 ∧
    quarticDen (-43) 2 505 12 (-1548)≠0 := by norm_num [quarticDen]

/-- No six-value candidate premise is supplied: it is derived from the four actual published rows. -/
theorem coordinates_of_original_models (l m:ℚ) (hl0:l≠0) (hl1:l≠1)
    (hm0:m≠0) (hm1:m≠1)
    (h30:legendreJ l=quarticJ (-43) (-686) (-2915) (-1372) (-172))
    (h42:legendreJ m=quarticJ (-43) 600 (-986) (-600) (-43))
    (h70:legendreJ (m/l)=quarticJ (-43) 256 (-130) (-768) (-387))
    (h105:legendreJ ((m-1)/(l-1))=quarticJ (-43) 2 505 12 (-1548)) :
    l=2401 ∧ m= -343/32 := by
  obtain ⟨e30,e42,e70,e105⟩:=original_quartic_invariants
  apply contact_coordinates_unique l m
  · exact equal_legendre_mem l (1/2401) hl0 hl1 (by norm_num) (by norm_num) (h30.trans e30)
  · exact equal_legendre_mem m (32/375) hm0 hm1 (by norm_num) (by norm_num) (h42.trans e42)
  · exact h70.trans e70
  · exact h105.trans e105

theorem literal_contacts_match :
    legendreJ 2401=quarticJ (-43) (-686) (-2915) (-1372) (-172) ∧
    legendreJ (-343/32)=quarticJ (-43) 600 (-986) (-600) (-43) ∧
    legendreJ ((-343/32)/2401)=quarticJ (-43) 256 (-130) (-768) (-387) ∧
    legendreJ ((-343/32-1)/(2401-1))=quarticJ (-43) 2 505 12 (-1548) := by
  norm_num [legendreJ,quarticJ]

end ContactCoordinates318
