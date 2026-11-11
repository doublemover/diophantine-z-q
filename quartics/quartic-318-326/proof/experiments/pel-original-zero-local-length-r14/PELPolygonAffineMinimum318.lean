module
public import PELOriginalDirichletPolygon318
public import PELDirichletSidePairingData318
public section
noncomputable section
namespace PELPolygonAffineMinimum318
open PELOriginalDirichletPolygon318 PELDirichletSidePairingData318 PELDirichletOriginalUnits318
set_option maxHeartbeats 1800000

/-- An affine lower bound on the four corners controls the entire closed
trapezoid. Both horizontal sides and endpoints are included. -/
theorem trapezoid (p q c A B m t lo hi : ℝ)
    (hinterval : lo < hi) (hlo : lo ≤ B) (hhi : B ≤ hi)
    (hleft : -(m*B+t) ≤ A) (hright : A ≤ m*B+t)
    (hll : 1 ≤ p*(-(m*lo+t))+q*lo+c)
    (hlr : 1 ≤ p*(m*lo+t)+q*lo+c)
    (hul : 1 ≤ p*(-(m*hi+t))+q*hi+c)
    (hur : 1 ≤ p*(m*hi+t)+q*hi+c) :
    1 ≤ p*A+q*B+c := by
  by_cases hp : 0 ≤ p
  · have hA := mul_nonneg hp (by linarith : 0 ≤ A+(m*B+t))
    have hL := mul_nonneg (by linarith : 0 ≤ hi-B) (sub_nonneg.mpr hll)
    have hU := mul_nonneg (by linarith : 0 ≤ B-lo) (sub_nonneg.mpr hul)
    have hW := mul_nonneg (by linarith : 0 ≤ hi-lo) hA
    nlinarith
  · have hA := mul_nonneg (by linarith : 0 ≤ -p) (by linarith : 0 ≤ m*B+t-A)
    have hL := mul_nonneg (by linarith : 0 ≤ hi-B) (sub_nonneg.mpr hlr)
    have hU := mul_nonneg (by linarith : 0 ≤ B-lo) (sub_nonneg.mpr hur)
    have hW := mul_nonneg (by linarith : 0 ≤ hi-lo) hA
    nlinarith

/-- All 28 original rational vertices suffice for every real point of the
literal finite halfplane polygon. No convex-hull equality is assumed. -/
theorem whole_polygon (p q c A B : ℝ) (hP : inequalities A B)
    (hv : ∀ v : Fin 28, 1 ≤ p*((vertex v).1:ℝ)+q*((vertex v).2:ℝ)+c) :
    1 ≤ p*A+q*B+c := by
  have hlo := hP 7 false true
  have hhi := hP 7 false false
  norm_num [rowFirst,rowSecond,rowConstant,sign] at hlo hhi
  by_cases hb0 : B ≤ (-135/109 : ℝ)
  · have hleft := hP 6 true true
    have hright := hP 6 false true
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 0
    have hlr := hv 1
    have hul := hv 2
    have hur := hv 3
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (165/13) (555/13) (-5/3) (-135/109)
    all_goals norm_num at * <;> linarith
  by_cases hb1 : B ≤ (-75/73 : ℝ)
  · have hleft := hP 5 true true
    have hright := hP 5 false true
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 2
    have hlr := hv 3
    have hul := hv 4
    have hur := hv 5
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (17/2) (75/2) (-135/109) (-75/73)
    all_goals norm_num at * <;> linarith
  by_cases hb2 : B ≤ (-35/36 : ℝ)
  · have hleft := hP 4 true true
    have hright := hP 4 false true
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 4
    have hlr := hv 5
    have hul := hv 6
    have hur := hv 7
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (210/29) (1050/29) (-75/73) (-35/36)
    all_goals norm_num at * <;> linarith
  by_cases hb3 : B ≤ (-35/48 : ℝ)
  · have hleft := hP 3 true true
    have hright := hP 3 false true
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 6
    have hlr := hv 7
    have hul := hv 8
    have hur := hv 9
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (6) (35) (-35/36) (-35/48)
    all_goals norm_num at * <;> linarith
  by_cases hb4 : B ≤ (-75/109 : ℝ)
  · have hleft := hP 2 true true
    have hright := hP 2 false true
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 8
    have hlr := hv 9
    have hul := hv 10
    have hur := hv 11
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (210/43) (1470/43) (-35/48) (-75/109)
    all_goals norm_num at * <;> linarith
  by_cases hb5 : B ≤ (-5/39 : ℝ)
  · have hleft := hP 1 true true
    have hright := hP 1 false true
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 10
    have hlr := hv 11
    have hul := hv 12
    have hur := hv 13
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (45/17) (555/17) (-75/109) (-5/39)
    all_goals norm_num at * <;> linarith
  by_cases hb6 : B ≤ (5/39 : ℝ)
  · have hleft := hP 0 true false
    have hright := hP 0 false false
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 12
    have hlr := hv 13
    have hul := hv 14
    have hur := hv 15
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (0) (420/13) (-5/39) (5/39)
    all_goals norm_num at * <;> linarith
  by_cases hb7 : B ≤ (75/109 : ℝ)
  · have hleft := hP 1 true false
    have hright := hP 1 false false
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 14
    have hlr := hv 15
    have hul := hv 16
    have hur := hv 17
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (-45/17) (555/17) (5/39) (75/109)
    all_goals norm_num at * <;> linarith
  by_cases hb8 : B ≤ (35/48 : ℝ)
  · have hleft := hP 2 true false
    have hright := hP 2 false false
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 16
    have hlr := hv 17
    have hul := hv 18
    have hur := hv 19
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (-210/43) (1470/43) (75/109) (35/48)
    all_goals norm_num at * <;> linarith
  by_cases hb9 : B ≤ (35/36 : ℝ)
  · have hleft := hP 3 true false
    have hright := hP 3 false false
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 18
    have hlr := hv 19
    have hul := hv 20
    have hur := hv 21
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (-6) (35) (35/48) (35/36)
    all_goals norm_num at * <;> linarith
  by_cases hb10 : B ≤ (75/73 : ℝ)
  · have hleft := hP 4 true false
    have hright := hP 4 false false
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 20
    have hlr := hv 21
    have hul := hv 22
    have hur := hv 23
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (-210/29) (1050/29) (35/36) (75/73)
    all_goals norm_num at * <;> linarith
  by_cases hb11 : B ≤ (135/109 : ℝ)
  · have hleft := hP 5 true false
    have hright := hP 5 false false
    norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
    have hll := hv 22
    have hlr := hv 23
    have hul := hv 24
    have hur := hv 25
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid p q c A B (-17/2) (75/2) (75/73) (135/109)
    all_goals norm_num at * <;> linarith
  have hleft := hP 6 true false
  have hright := hP 6 false false
  norm_num [rowFirst,rowSecond,rowConstant,sign] at hleft hright
  have hll := hv 24
  have hlr := hv 25
  have hul := hv 26
  have hur := hv 27
  norm_num [vertex] at hll hlr hul hur
  apply trapezoid p q c A B (-165/13) (555/13) (135/109) (5/3)
  all_goals norm_num at * <;> linarith
end PELPolygonAffineMinimum318
