module
public import FirstFieldClasses318
public section
namespace GlobalFirstDescent318
open ConcreteG8Domain LocalGenerator318 GlobalNormCoset318
open WeierstrassCurve.Affine FirstPrimeParity318 FirstFieldClasses318
set_option maxHeartbeats 0

/-- The exact eight-squareclass first-descent bound, now derived from the
actual curve, Euclidean factorization and the four actual unit classes. -/
theorem first_descent_classes : FirstDescentClasses := by
  intro x y h hx
  have he:y^2=x^3-D*x := by
    have hh:=h.1
    rw [equation_iff] at hh
    simpa [E,sub_eq_add_neg] using hh
  rcases even_adjustment x y hx he with hall|hall
  · obtain ⟨r,hr,h0|h1|h2|h3⟩:=field_four_classes x hx hall
    · exact ⟨0,r,hr,by simpa [classRepresentative] using h0⟩
    · exact ⟨1,r,hr,by simpa [classRepresentative] using h1⟩
    · exact ⟨2,r,hr,by simpa [classRepresentative] using h2⟩
    · refine ⟨3,r,hr,?_⟩
      have hh:-(pair 1 1)=pair (-1) (-1) := by ext <;> rfl
      simpa [classRepresentative,hh] using h3
  · have hd:3-i≠(0:K) := (DeltaPrime318.place.ne_top_iff).mp (by rw [DeltaPrime318.value_delta]; simp)
    have hdx:x/(3-i)≠0:=div_ne_zero hx hd
    have hdrep:3-i=pair 3 (-1) := by ext <;> norm_num [i,pair,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    have hnrep:-(3-i)=pair (-3) 1 := by rw [hdrep]; ext <;> rfl
    have hprod:(3-i)*pair 1 1=pair 1 2 := by rw [hdrep,pair_product]; norm_num
    have hnprod: -((3-i)*pair 1 1)=pair (-1) (-2) := by rw [hprod]; ext <;> rfl
    obtain ⟨r,hr,h0|h1|h2|h3⟩:=field_four_classes (x/(3-i)) hdx hall
    · refine ⟨4,r,hr,?_⟩
      have hh: x=(3-i)*r^2 := by have hh:=(div_eq_iff hd).mp h0; linear_combination hh
      simpa [classRepresentative,hdrep] using hh
    · refine ⟨5,r,hr,?_⟩
      have hh: x=(-(3-i))*r^2 := by have hh:=(div_eq_iff hd).mp h1; linear_combination hh
      simpa [classRepresentative,hnrep] using hh
    · refine ⟨6,r,hr,?_⟩
      have hh:x=((3-i)*pair 1 1)*r^2 := by have hh:=(div_eq_iff hd).mp h2; linear_combination hh
      simpa [classRepresentative,hprod] using hh
    · refine ⟨7,r,hr,?_⟩
      have hh:x=(-((3-i)*pair 1 1))*r^2 := by have hh:=(div_eq_iff hd).mp h3; linear_combination hh
      simpa [classRepresentative,hnprod] using hh

end GlobalFirstDescent318
#print axioms GlobalFirstDescent318.first_descent_classes
