module
public import PELNormalizerOctagonVertices318
public section
namespace PELNormalizerOctagonAffine318
open PELNormalizerOctagonVertices318
set_option maxHeartbeats 2000000
@[expose] def inequalities (A B : ℝ) : Prop :=
  -1≤B ∧ B≤1 ∧ -30≤A ∧ A≤30 ∧
    -35≤A+7*B ∧ A+7*B≤35 ∧ -35≤A-7*B ∧ A-7*B≤35
@[expose] def octagon : Set (ℝ × ℝ) := {P | inequalities P.1 P.2}

/-- General affine bound on a whole closed trapezoid, with all endpoints. -/
theorem trapezoid (L p q c A B m t lo hi : ℝ)
    (hinterval : lo<hi) (hlo : lo≤B) (hhi : B≤hi)
    (hleft : -(m*B+t)≤A) (hright : A≤m*B+t)
    (hll : L≤p*(-(m*lo+t))+q*lo+c)
    (hlr : L≤p*(m*lo+t)+q*lo+c)
    (hul : L≤p*(-(m*hi+t))+q*hi+c)
    (hur : L≤p*(m*hi+t)+q*hi+c) : L≤p*A+q*B+c := by
  by_cases hp : 0≤p
  · have hA := mul_nonneg hp (by linarith : 0≤A+(m*B+t))
    have hL := mul_nonneg (by linarith : 0≤hi-B) (sub_nonneg.mpr hll)
    have hU := mul_nonneg (by linarith : 0≤B-lo) (sub_nonneg.mpr hul)
    have hW := mul_nonneg (by linarith : 0≤hi-lo) hA
    nlinarith
  · have hA := mul_nonneg (by linarith : 0≤-p) (by linarith : 0≤m*B+t-A)
    have hL := mul_nonneg (by linarith : 0≤hi-B) (sub_nonneg.mpr hlr)
    have hU := mul_nonneg (by linarith : 0≤B-lo) (sub_nonneg.mpr hur)
    have hW := mul_nonneg (by linarith : 0≤hi-lo) hA
    nlinarith

/-- All eight vertices control the full real octagon, without assuming a
convex-hull presentation or restricting the point coordinates to rationals. -/
theorem whole_octagon (L p q c A B : ℝ) (hP : inequalities A B)
    (hv : ∀ v : Fin 8,L≤p*((vertex v).1:ℝ)+q*((vertex v).2:ℝ)+c) :
    L≤p*A+q*B+c := by
  obtain ⟨hb0,hb1,ha0,ha1,hs0,hs1,ht0,ht1⟩ := hP
  by_cases hb : B≤(-5/7:ℝ)
  · have hll := hv 4
    have hlr := hv 5
    have hul := hv 3
    have hur := hv 6
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid L p q c A B 7 35 (-1) (-5/7)
    all_goals norm_num at * <;> linarith
  by_cases hc : B≤(5/7:ℝ)
  · have hll := hv 3
    have hlr := hv 6
    have hul := hv 2
    have hur := hv 7
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid L p q c A B 0 30 (-5/7) (5/7)
    all_goals norm_num at * <;> linarith
  · have hll := hv 2
    have hlr := hv 7
    have hul := hv 1
    have hur := hv 0
    norm_num [vertex] at hll hlr hul hur
    apply trapezoid L p q c A B (-7) 35 (5/7) 1
    all_goals norm_num at * <;> linarith
end PELNormalizerOctagonAffine318
