module
public import ContactProjectivePointPresentation318
public section
noncomputable section
namespace ContactProjectivePointRecovery318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  (x : ContactProjectiveParameterPoint318.Point c n S)
/-- The actual universal-family extraction followed by original global
classification is the identity on ALL parameter scheme points. -/
lemma recover : ContactProjectiveGlobalClassifyingMap318.point c n S
    (ContactProjectivePointFamily318.into c n S x) (ContactProjectivePointPresentation318.data c n S x)=x := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext (AffineCoefficientCover318.cover ℚ S
    (ContactProjectivePointCover318.coefficients c n S x)) _ _
  intro i
  exact (ContactProjectiveGlobalClassifyingMap318.local_classify c n S
    (ContactProjectivePointFamily318.into c n S x) (ContactProjectivePointPresentation318.data c n S x) i).trans
      (ContactProjectivePointPresentation318.local_point c n S x i)
/-- Any independent presentation of the same actual point fiber also
recovers the original point, with no chart or cover compatibility input. -/
lemma recover_any (D : ContactProjectiveLocalPresentation318.Data c n S
    (ContactProjectivePointFamily318.into c n S x)) :
    ContactProjectiveGlobalClassifyingMap318.point c n S (ContactProjectivePointFamily318.into c n S x) D=x :=
  (ContactProjectivePresentationIndependence318.independent c n S _ D
    (ContactProjectivePointPresentation318.data c n S x)).trans (recover c n S x)
end ContactProjectivePointRecovery318
