module
public import OriginalCartesianChartCoefficients318
public import OriginalOpenChartGeneric318
public import OriginalNormalSectionClosure318
public import OriginalNormalClosureChartAction318
public import OriginalCurveGeometricStabilizers318
public section
noncomputable section
namespace OriginalCartesianNormalChart318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "R" => Polynomial ℚ
local notation "B" => ProjectiveJLine318.scheme ℚ
variable {Y : Scheme} [IsIntegral Y] [IsIntegral B]
  (p : Y ⟶ B) [IsDominant p] [IsIntegralHom p]
  {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (f : R →+* A)
  (H : IsPullback (Spec.map (CommRingCat.ofHom f)) j (JLineAtlas318.chart ℚ 1) p)

/-- Named original actions, not registrations with hidden morphism inputs. -/
@[expose, instance_reducible] def quotientAlgebra : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
@[expose, instance_reducible] def chartAlgebra : Algebra A Y.functionField :=
  ActualOpenFractionField318.sourceAlgebra j
@[expose, instance_reducible] def coefficientAlgebra : Algebra R A := f.toAlgebra

variable [hfinite : letI := quotientAlgebra p; FiniteDimensional (RatFunc ℚ) Y.functionField]
  [hgalois : letI := quotientAlgebra p; IsGalois (RatFunc ℚ) Y.functionField]

/-- Original full Cartesian affine ring, embedded through its actual generic
stalk, identified with the exact integral closure. -/
@[expose] def sections :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    letI := coefficientAlgebra f
    A ≃ₐ[R] Order Y.functionField := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  letI := chartAlgebra j
  letI := coefficientAlgebra f
  letI : IsScalarTower R A Y.functionField :=
    OriginalCartesianChartCoefficients318.coefficient_tower p j f H
  letI : Algebra.IsIntegral R A :=
    OriginalCartesianChartCoefficients318.coefficient_integral p j f H
  letI : IsFractionRing A Y.functionField := ActualOpenFractionField318.fractionRing j
  exact OriginalNormalSectionClosure318.equivalence R A Y.functionField

@[expose] def specIso :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    Spec (CommRingCat.of (Order Y.functionField)) ≅ Spec (CommRingCat.of A) := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  exact Scheme.Spec.mapIso (sections p j f H).toRingEquiv.toCommRingCatIso.op

@[expose] def chart :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    Spec (CommRingCat.of (Order Y.functionField)) ⟶ Y := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  exact (specIso p j f H).hom ≫ j

instance chart_openImmersion :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    IsOpenImmersion (chart p j f H) := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  unfold chart
  infer_instance

@[reassoc] theorem fraction_chart :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    OriginalNormalClosureChartAction318.fraction Y.functionField ≫ chart p j f H =
      OriginalGenericStalkNaturality318.generic Y := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  letI := chartAlgebra j
  letI := coefficientAlgebra f
  letI : IsScalarTower R A Y.functionField :=
    OriginalCartesianChartCoefficients318.coefficient_tower p j f H
  letI : Algebra.IsIntegral R A :=
    OriginalCartesianChartCoefficients318.coefficient_integral p j f H
  letI : IsFractionRing A Y.functionField := ActualOpenFractionField318.fractionRing j
  have he : OriginalNormalClosureChartAction318.fraction Y.functionField ≫
      (specIso p j f H).hom = Spec.map (CommRingCat.ofHom (algebraMap A Y.functionField)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap (Order Y.functionField) Y.functionField)) ≫
      Spec.map (CommRingCat.ofHom (sections p j f H).toRingHom) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact OriginalNormalSectionClosure318.equivalence_embedding R A Y.functionField
  unfold chart
  rw [← Category.assoc, he, OriginalOpenChartGeneric318.generic_square]

@[reassoc] theorem chart_base :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    chart p j f H ≫ p = OriginalNormalClosureChartAction318.chartBase Y.functionField := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  letI := coefficientAlgebra f
  unfold chart
  rw [Category.assoc, ← H.w, ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (sections p j f H).toRingHom) ≫
    Spec.map (CommRingCat.ofHom f)) ≫ _ = _
  rw [← Spec.map_comp]
  unfold OriginalNormalClosureChartAction318.chartBase
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (sections p j f H).commutes

/-- Every original normal-closure geometric point is evaluated in the SAME
old affine chart, by its literal coordinate ring map. -/
lemma point_chart :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    ∀ (z : Order Y.functionField →+* ℂ),
    OriginalCurveGeometricStabilizers318.point (chart p j f H) z =
      Spec.map (CommRingCat.ofHom (z.comp (sections p j f H).toRingHom)) ≫ j := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  intro z
  change Spec.map (CommRingCat.ofHom z) ≫ ((specIso p j f H).hom ≫ j) = _
  rw [← Category.assoc]
  change (Spec.map (CommRingCat.ofHom z) ≫
    Spec.map (CommRingCat.ofHom (sections p j f H).toRingHom)) ≫ j = _
  rw [← Spec.map_comp]
  all_goals rfl

lemma point_coefficient :
    letI := quotientAlgebra p
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
    letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
    ∀ (z : Order Y.functionField →+* ℂ) (q : R),
    (z.comp (sections p j f H).toRingHom) (f q) =
      z (algebraMap R (Order Y.functionField) q) := by
  letI := quotientAlgebra p
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField := hfinite
  letI : IsGalois (RatFunc ℚ) Y.functionField := hgalois
  letI := coefficientAlgebra f
  intro z q
  exact congrArg z ((sections p j f H).commutes q)
end OriginalCartesianNormalChart318
