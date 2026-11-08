module
public import ChartPointEvaluation318
public import SchemeAffineTestExt318
public section
noncomputable section
namespace ChartSchemeCompatibility318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318 CompletedAdditionCharts318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
/-- The coefficient-algebra structure is induced by the actual common map to
the original base, so every affine Scheme test object is covered. -/
theorem affine_agreement {S:Type u} [CommRing S]
    (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j k l:Fin 2)
    (x:Spec (CommRingCat.of S) ⟶ pullback (chartStructure A B i) (chartStructure A B j))
    (y:Spec (CommRingCat.of S) ⟶ pullback (chartStructure A B k) (chartStructure A B l))
    (h1:x ≫ pullback.fst _ _ ≫ intoCurve A B i=y ≫ pullback.fst _ _ ≫ intoCurve A B k)
    (h2:x ≫ pullback.snd _ _ ≫ intoCurve A B j=y ≫ pullback.snd _ _ ≫ intoCurve A B l) :
    x ≫ chartAddition A B hD i j=y ≫ chartAddition A B hD k l := by
  obtain ⟨b,hb⟩:=Spec.map_surjective (x ≫ pullback.fst _ _ ≫ chartStructure A B i)
  letI : Algebra R S:=b.hom.toAlgebra
  have hx1:x ≫ pullback.fst _ _ ≫ chartStructure A B i=Spec.algebraMap R S := hb.symm
  have hx2:x ≫ pullback.snd _ _ ≫ chartStructure A B j=Spec.algebraMap R S := by
    rw [←pullback.condition]
    exact hx1
  have hy1:y ≫ pullback.fst _ _ ≫ chartStructure A B k=Spec.algebraMap R S := by
    have hh:=congrArg (fun f=>f ≫ WeierstrassGluing318.structureMap A B) h1
    simp only [Category.assoc,intoCurve_over_base] at hh
    exact hh.symm.trans hx1
  have hy2:y ≫ pullback.snd _ _ ≫ chartStructure A B l=Spec.algebraMap R S := by
    rw [←pullback.condition]
    exact hy1
  exact ChartPointEvaluation318.agreement_over_algebra A B hD i j k l x y hx1 hx2 hy1 hy2 h1 h2

/-- Actual chart additions agree on every Scheme test object, with no affine,
reducedness, or field-valued-point restriction. -/
theorem scheme_agreement {X:Scheme.{u}}
    (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j k l:Fin 2)
    (x:X ⟶ pullback (chartStructure A B i) (chartStructure A B j))
    (y:X ⟶ pullback (chartStructure A B k) (chartStructure A B l))
    (h1:x ≫ pullback.fst _ _ ≫ intoCurve A B i=y ≫ pullback.fst _ _ ≫ intoCurve A B k)
    (h2:x ≫ pullback.snd _ _ ≫ intoCurve A B j=y ≫ pullback.snd _ _ ≫ intoCurve A B l) :
    x ≫ chartAddition A B hD i j=y ≫ chartAddition A B hD k l := by
  apply SchemeAffineTestExt318.hom_ext
  intro S t
  rw [←Category.assoc,←Category.assoc]
  apply affine_agreement
  · simpa only [Category.assoc] using congrArg (fun f=>t ≫ f) h1
  · simpa only [Category.assoc] using congrArg (fun f=>t ≫ f) h2
end ChartSchemeCompatibility318
