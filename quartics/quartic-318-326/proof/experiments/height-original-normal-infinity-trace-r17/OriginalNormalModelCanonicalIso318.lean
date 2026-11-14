module
public import NormalModelComparisonOfFactor318
public import OriginalNormalizationConductorNonzero318
public section
noncomputable section
namespace OriginalNormalModelCanonicalIso318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open IntegralDistinctContactOpen318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "B" => SourceOpenRing c t w D
local notation "N" => arithmeticDenominator R D.coefficients
local instance sourceDomain : IsDomain B :=
  open_domain R a D.coefficients (K c t) (IsFractionRing.injective R (K c t))
    (contacts_injective c t w) (coefficients_ne_zero c t w D)
local instance : Module.Finite (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).1
local instance : Algebra.Etale (Base R a D.coefficients) B :=
  (finite_free_etale R a D.coefficients).2.2
local instance : IsIntegral M.scheme := M.integral
local instance : IsOpenImmersion M.source := M.source_open
local instance : IsDominant M.source := M.source_dense
local instance : IsFinite M.projection := M.finite_projection

lemma source_factor : IntegralTwoChartNormalization318.coverMap R a N B=
    M.source ≫ M.projection :=
  (IntegralTwoChartNormalization318.finite_factor R a N B).trans M.source_projection.symm

/-- Every original proper-normal realization is the SAME canonical
normalization, by its given dense source, finite projection and normal
stalks. Neither regularity nor a normal affine cover is assumed. -/
@[expose] def iso : IntegralTwoChartNormalization318.model R a N B ≅ M.scheme :=
  NormalModelComparisonOfFactor318.iso
    (IntegralTwoChartNormalization318.coverMap R a N B) M.source M.projection
    (source_factor c t w D M) M.normal_stalk

@[reassoc] theorem source : IntegralTwoChartNormalization318.sourceOpen R a N B ≫
    (iso c t w D M).hom=M.source :=
  NormalModelComparisonOfFactor318.source _ _ _ _ _

@[reassoc] theorem base : (iso c t w D M).hom ≫ M.projection=
    IntegralTwoChartNormalization318.modelMap R a N B :=
  NormalModelComparisonOfFactor318.base _ _ _ _ _

/-- The generic point retained here is the literal original fieldPoint,
including its signed root values, not a point picked through birationality. -/
@[reassoc] theorem point :
    Spec.map (CommRingCat.ofHom M.fieldPoint) ≫
      IntegralTwoChartNormalization318.sourceOpen R a N B ≫ (iso c t w D M).hom=
    Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ M.source := by
  rw [source]

/-- Transport the already constructed center, without selecting a new
valuation-ring point or applying a new existence choice. -/
@[expose] def center : Spec (CommRingCat.of R) ⟶
    IntegralTwoChartNormalization318.model R a N B := M.center ≫ (iso c t w D M).inv

@[reassoc] theorem center_original : center c t w D M ≫ (iso c t w D M).hom=M.center := by
  simp only [center,Category.assoc,Iso.inv_hom_id,Category.comp_id]

theorem center_generic :
    Spec.map (CommRingCat.ofHom (algebraMap R (K c t))) ≫ center c t w D M=
    Spec.map (CommRingCat.ofHom M.fieldPoint) ≫
      IntegralTwoChartNormalization318.sourceOpen R a N B := by
  apply (cancel_mono (iso c t w D M).hom).mp
  rw [Category.assoc,center_original,Category.assoc,source]
  exact M.center_generic

theorem center_base : center c t w D M ≫
    IntegralTwoChartNormalization318.modelMap R a N B ≫
      ProjectiveJLine318.structureMap R=𝟙 _ := by
  calc
    _ = (center c t w D M ≫ (iso c t w D M).hom) ≫ M.projection ≫
        ProjectiveJLine318.structureMap R := by rw [Category.assoc,base_assoc]
    _ = 𝟙 _ := by rw [center_original]; exact M.center_base
end OriginalNormalModelCanonicalIso318
