module
public import ContactFixedDegreePresentation318
public section
noncomputable section
namespace ContactFixedDegreeGlobalClassifier318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveDegreeData318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedDegree S c n)
/-- Every original effective finite-flat Cartier divisor of degree n
has an ACTUAL GLOBAL classifying point of the glued original-source
quotient parameter scheme. Full moduli recovery is a separate theorem. -/
@[expose] def point : ContactProjectiveParameterPoint318.Point c n S :=
  ContactProjectiveGlobalClassifyingMap318.point c n S
    (ContactProjectiveQuotientGluing318.into S c D.val.datum)
    (ContactFixedDegreePresentation318.data S c n D)
@[reassoc] lemma local_classify (a : (ContactFixedDegreeLocalClassifier318.cover S c n D).I₀) :
    Spec.map (CommRingCat.ofHom
      (ContactBoundedAvoidanceAffineCover318.coefficient S c n
        (ContactFixedDegreeLocalClassifier318.bounded S c n D) a).toRingHom) ≫ (point S c n D).val=
      (ContactProjectiveParameterPoint318.ofIdeal c n
        (ContactBoundedAvoidanceAffineCover318.ring S c n
          (ContactFixedDegreeLocalClassifier318.bounded S c n D) a)
        (ContactFixedDegreeLocalIdeal318.chart S c n D a) (ContactFixedDegreeLocalIdeal318.ideal S c n D a)).val :=
  ContactProjectiveGlobalClassifyingMap318.local_classify c n S
    (ContactProjectiveQuotientGluing318.into S c D.val.datum)
    (ContactFixedDegreePresentation318.data S c n D) a
end ContactFixedDegreeGlobalClassifier318
