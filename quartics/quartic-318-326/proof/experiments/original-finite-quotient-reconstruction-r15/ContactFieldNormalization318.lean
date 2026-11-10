module
public import AffineFractionGeneric318
public import NormalizationBirationalComparison318
public import ContactGlobalNormal318
public import SourceOpenFractionField318
public section
noncomputable section
namespace ContactFieldNormalization318
open Polynomial AlgebraicGeometry CategoryTheory ContactKummerOrder318
-- The SAME Spec carrier must remain visible to categorical composition.
attribute [local reducible] ContactKummerCover318.cover
variable (c : Fin 4 → ℚˣ)
abbrev Field := SourceFractionField318.L c
local instance actualField : _root_.Field (Field c) :=
  (KummerTensorField318.source_raw_field c).toField
local instance sourceDomain : IsDomain (OpenOrder c) := ContactKummerOpenDomain318.open_domain c
local instance originalAlgebra : Algebra (OpenOrder c) (Field c) :=
  (SourceOpenFractionField318.openEmbedding c).toAlgebra
local instance originalFraction : IsFractionRing (OpenOrder c) (Field c) :=
  SourceOpenFractionField318.open_fractionField c
local instance modelIntegral : IsIntegral (ContactProjectiveModel318.model c) :=
  ContactProjectiveModel318.model_integral c
local instance modelNoetherian : AlgebraicGeometry.IsNoetherian (ContactProjectiveModel318.model c) :=
  ContactGlobalNormal318.noetherian_model c
local instance openImmersion : IsOpenImmersion (ContactProjectiveModel318.sourceOpen c) :=
  ContactProjectiveModel318.sourceOpen_open c
local instance openDominant : IsDominant (ContactProjectiveModel318.sourceOpen c) :=
  ContactProjectiveModel318.sourceOpen_dense c
local instance structureIntegral : IsIntegralHom (ContactProjectiveModel318.modelMap c) :=
  ContactProjectiveModel318.modelMap_integral c

/-- The original generic source of the actual Contact model, through its
specified full open-order fraction-field embedding. -/
@[expose] def genericSource : Spec (CommRingCat.of (Field c)) ⟶ ContactProjectiveModel318.model c :=
  AffineFractionGeneric318.map (OpenOrder c) (Field c) ≫ ContactProjectiveModel318.sourceOpen c

instance generic_dominant : IsDominant (genericSource c) := by
  letI : IsDominant (AffineFractionGeneric318.map (OpenOrder c) (Field c)) :=
    AffineFractionGeneric318.dominant (OpenOrder c) (Field c)
  change IsDominant (AffineFractionGeneric318.map (OpenOrder c) (Field c) ≫
    ContactProjectiveModel318.sourceOpen c)
  infer_instance
instance generic_quasiCompact : QuasiCompact (genericSource c) := by
  unfold genericSource AffineFractionGeneric318.map
  infer_instance
instance generic_quasiSeparated : QuasiSeparated (genericSource c) := by
  unfold genericSource AffineFractionGeneric318.map
  infer_instance

/-- The actual generic-stalk pullback, not an unconnected abstract field map. -/
theorem generic_isIso : IsIso (DominantFunctionField318.map (genericSource c)) := by
  letI := AffineFractionGeneric318.generic_isIso (OpenOrder c) (Field c)
  change IsIso (DominantFunctionField318.map
    (AffineFractionGeneric318.map (OpenOrder c) (Field c) ≫ ContactProjectiveModel318.sourceOpen c))
  rw [DominantFunctionField318.map_comp, DominantFunctionField318.map_open]
  infer_instance
local instance genericIso : IsIso (DominantFunctionField318.map (genericSource c)) := generic_isIso c

@[expose] def genericBase : Spec (CommRingCat.of (Field c)) ⟶ ProjectiveJLine318.scheme ℚ :=
  genericSource c ≫ ContactProjectiveModel318.modelMap c
instance genericBase_quasiCompact : QuasiCompact (genericBase c) := by
  unfold genericBase
  infer_instance
instance genericBase_quasiSeparated : QuasiSeparated (genericBase c) := by
  unfold genericBase
  infer_instance

/-- The exact base coordinate is the original t in the original Kummer field. -/
theorem genericBase_polynomial : genericBase c =
    Spec.map (CommRingCat.ofHom
      ((algebraMap (RatFunc ℚ) (Field c)).comp (algebraMap ℚ[X] (RatFunc ℚ)))) ≫
        JLineAtlas318.chart ℚ 1 := by
  dsimp only [genericBase, genericSource]
  rw [Category.assoc, ContactProjectiveModel318.factorization,
    ContactGlobalProper318.finite_factor, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact SourceOpenFractionField318.openEmbedding_on_polynomial c a

/-- The actual Contact normalization is the SAME normalization of its
specified whole function field over the original projective t-line. -/
@[expose] def iso : (genericBase c).normalization ≅ ContactProjectiveModel318.model c :=
  NormalizationBirationalComparison318.iso (genericSource c) (ContactProjectiveModel318.modelMap c)
    (ContactGlobalNormal318.sourceCover c) (ContactGlobalNormal318.sourceCover_covers c)
    (fun i => (ContactGlobalNormal318.chart_properties c i).2.1)

@[reassoc] theorem iso_source : (genericBase c).toNormalization ≫ (iso c).hom = genericSource c :=
  NormalizationBirationalComparison318.iso_source ..

@[reassoc] theorem iso_base : (iso c).hom ≫ ContactProjectiveModel318.modelMap c =
    (genericBase c).fromNormalization :=
  NormalizationBirationalComparison318.comparison_base ..
end ContactFieldNormalization318
