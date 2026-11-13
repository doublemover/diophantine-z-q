module
public import ContactBoundedCartierKernel318
public section
noncomputable section
namespace ContactBoundedCartierAbel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
@[expose] def divisorLine (D : ContactBoundedCartierEquiv318.Data c N b) : Line (pullback p b) :=
  FramedLineInverse318.inverse (ContactBoundedCartierKernel318.inputLine c N b D)
@[expose] def fiberDivisorLine (f : ContactBoundedCartierEquiv318.Point c N b) : Line (pullback p b) :=
  FramedLineInverse318.inverse (ActualCartierIdealLine318.line
    (ContactBoundedPointFamily318.into c N b f.val) f.property)
/-- The actual original O(D) gives an Abel transformation on ALL scheme
tests into the EXISTING relative fppf line-class sheaf. -/
@[expose] def transformation (D : ContactBoundedCartierEquiv318.Data c N b) : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation p b (divisorLine c N b D)
@[expose] def fiberTransformation (f : ContactBoundedCartierEquiv318.Point c N b) : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation p b (fiberDivisorLine c N b f)
/-- Bounded classification and the original Abel construction commute
as actual transformations on all scheme tests, not only on points. -/
lemma classification (D : ContactBoundedCartierEquiv318.Data c N b) :
    transformation c N b D=fiberTransformation c N b (ContactBoundedCartierEquiv318.equivalence c N b D) :=
  OriginalLineAbelTransformation318.class_congr p b _ _ (ContactBoundedCartierKernel318.divisor_class c N b D)
lemma charts_independent (D : ContactBoundedSchemeHilbertData318.Data c N b)
    (h h' : OriginalRegularClosedCharts318.Property D.ideal.subschemeι) :
    transformation c N b ⟨D,h⟩=transformation c N b ⟨D,h'⟩ := by
  apply OriginalLineAbelTransformation318.class_congr
  change classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line D.ideal.subschemeι h))=
    classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line D.ideal.subschemeι h'))
  rw [LineSheafClassGroup318.classOf_inverse,LineSheafClassGroup318.classOf_inverse]
  exact congrArg (fun x => x⁻¹) (CartierIdealClass318.chart_independent D.ideal.subschemeι h h')
end ContactBoundedCartierAbel318
