module
public import VaryingWordDeterminantOpen318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace VaryingWordChartScheme318
open AlgebraicGeometry CategoryTheory VaryingCommutingMatrixRing318
open VaryingWordDeterminantOpen318
universe u
variable (R σ ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι]

abbrev parameter : Scheme := Spec (CommRingCat.of (algebra R σ ι))
abbrev chart (w : ι → List σ) : Scheme := Spec (CommRingCat.of (ring R σ ι w))
@[expose] def into (w : ι → List σ) : chart R σ ι w ⟶ parameter R σ ι :=
  Spec.map (CommRingCat.ofHom (algebraMap (algebra R σ ι) (ring R σ ι w)))

/-- The word-determinant charts are genuine principal open subschemes of
the SAME represented commuting matrix/vector parameter. -/
instance into_open (w : ι → List σ) : IsOpenImmersion (into R σ ι w) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (delta R σ ι w)

@[expose] def projection : parameter R σ ι ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (algebra R σ ι)))
@[expose] def chartProjection (w : ι → List σ) : chart R σ ι w ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ring R σ ι w)))

@[reassoc] lemma over_base (w : ι → List σ) :
    into R σ ι w ≫ projection R σ ι=chartProjection R σ ι w := by
  rw [into,projection,chartProjection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R (algebra R σ ι) (ring R σ ι w)).symm
end VaryingWordChartScheme318
