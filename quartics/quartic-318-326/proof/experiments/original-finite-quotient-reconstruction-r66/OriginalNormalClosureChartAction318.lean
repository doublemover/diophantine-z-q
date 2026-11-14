module
public import OriginalGenericStalkNaturality318
public import NormalClosureGeometricPoints318
public section
noncomputable section
namespace OriginalNormalClosureChartAction318
open AlgebraicGeometry CategoryTheory Polynomial
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (L : Type) [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- The literal fraction map of the original integral closure. -/
@[expose] def fraction : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (Order L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Order L) L))

instance fraction_dominant : IsDominant (fraction L) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap (Order L) L))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (Order L) L)]
  exact bot_le

instance fraction_schematic : IsSchemeTheoreticallyDominant (fraction L) :=
  IsSchemeTheoreticallyDominant.of_isDominant (fraction L)

/-- The entire old normal-closure chart maps to the original t-chart. -/
@[expose] def chartBase : Spec (CommRingCat.of (Order L)) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (Order L))) ≫ JLineAtlas318.chart ℚ 1

@[reassoc] lemma fraction_base : fraction L ≫ chartBase L =
    ReconstructedFieldNormalization318.base L := by
  unfold fraction chartBase ReconstructedFieldNormalization318.base
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2

@[reassoc] lemma fraction_action (σ : OriginalNormalClosureGalois318.Group L) :
    fraction L ≫ schemeMap L σ =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ fraction L := by
  unfold fraction schemeMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (affineAction_generic L σ a).symm

@[reassoc] lemma action_base (σ : OriginalNormalClosureGalois318.Group L) : schemeMap L σ ≫ chartBase L = chartBase L := by
  unfold schemeMap chartBase
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (galRestrict ℚ[X] (RatFunc ℚ) L (Order L) σ).commutes a

variable {L} {Y : Scheme}
  (j : Spec (CommRingCat.of (Order L)) ⟶ Y)
  (g : Spec (CommRingCat.of L) ⟶ Y)
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsSeparated p]
  (hj : fraction L ≫ j = g) (hp : j ≫ p = chartBase L)

include hj hp in
/-- Actual whole-chart equivariance follows from the SAME fraction map,
original generic square and actual chart/base square. It is not supplied as
an additional compatibility premise to the branch reconstruction. -/
theorem chart_action (σ : OriginalNormalClosureGalois318.Group L) (a : Y ⟶ Y) (ha : a ≫ p = p)
    (hg : g ≫ a = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ g) :
    schemeMap L σ ≫ j = j ≫ a := by
  apply SchematicEqualityExtension318.ext p ?_ (fraction L) ?_
  · simp only [Category.assoc, hp, ha, action_base]
  · calc
      fraction L ≫ (schemeMap L σ ≫ j) =
          Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ g := by
            rw [← Category.assoc, fraction_action, Category.assoc, hj]
      _ = g ≫ a := hg.symm
      _ = fraction L ≫ (j ≫ a) := by rw [← Category.assoc, hj]

include hj hp in
lemma generic_base : g ≫ p = ReconstructedFieldNormalization318.base L := by
  rw [← hj, Category.assoc, hp, fraction_base]
end OriginalNormalClosureChartAction318
