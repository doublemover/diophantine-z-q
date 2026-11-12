module
public import ContactProjectiveGlobalNaturality318
public import ContactFixedDegreeGlobalClassifier318
public section
noncomputable section
namespace ContactFixedDegreeClassifierCoherence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveDegreeData318
variable (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedDegree S c n)
local notation "q" => ContactProjectiveQuotientGluing318.into S c D.val.datum
/-- The actual fixed-degree classifier is independent of the chosen
original closed model, using an isomorphism over the SAME original curve. -/
lemma iso_invariant (E : FixedDegree S c n)
    (e : ContactProjectiveQuotientGluing318.family S c D.val.datum ≅
      ContactProjectiveQuotientGluing318.family S c E.val.datum)
    (he : e.hom ≫ ContactProjectiveQuotientGluing318.into S c E.val.datum=q) :
    ContactFixedDegreeGlobalClassifier318.point S c n D=
      ContactFixedDegreeGlobalClassifier318.point S c n E :=
  ContactProjectivePresentationIso318.invariant c n S q
    (ContactProjectiveQuotientGluing318.into S c E.val.datum) e he
    (ContactFixedDegreePresentation318.data S c n D)
    (ContactFixedDegreePresentation318.data S c n E)
/-- Every ACTUAL Cartesian coefficient change of original fixed-degree
Cartier families induces the corresponding pullback of global points.
No agreement of avoidance covers or chosen local frames is assumed. -/
lemma natural (φ : S →ₐ[ℚ] T) (E : FixedDegree T c n)
    (h : ContactProjectiveQuotientGluing318.family T c E.val.datum ⟶
      ContactProjectiveQuotientGluing318.family S c D.val.datum)
    (H : IsPullback h (ContactProjectiveQuotientGluing318.into T c E.val.datum) q
      (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
        (ContactIntrinsicDifferentials318.structureMap c))) :
    ContactFixedDegreeGlobalClassifier318.point T c n E=
      ContactProjectiveParameterPoint318.map c n S T φ
        (ContactFixedDegreeGlobalClassifier318.point S c n D) :=
  ContactProjectiveGlobalNaturality318.natural c n S T φ q
    (ContactProjectiveQuotientGluing318.into T c E.val.datum) h H
    (ContactFixedDegreePresentation318.data S c n D)
    (ContactFixedDegreePresentation318.data T c n E)
end ContactFixedDegreeClassifierCoherence318
