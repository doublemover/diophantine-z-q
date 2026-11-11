module
public import ProjectiveParameterPrincipalNormalization318
public import ProjectiveParameterSliceNonzero318
public section
noncomputable section
namespace ProjectiveParameterPrincipalCover318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
abbrev locus : (Spec (CommRingCat.of A)).Opens := ProjectiveParameterNonzeroOpen318.locus R P
abbrev chart (i : Fin F.size) : Scheme := Spec (CommRingCat.of (H i))
@[expose] def affineInto (i : Fin F.size) : chart R P i ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (H i)))
instance affineInto_open (i : Fin F.size) : IsOpenImmersion (affineInto R P i) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway
lemma range_basic (i : Fin F.size) : Set.range (affineInto R P i)=PrimeSpectrum.basicOpen (x i) :=
  PrimeSpectrum.localization_away_comap_range (H i) (x i)
lemma range_locus (i : Fin F.size) : Set.range (affineInto R P i)⊆(locus R P : Set _) := by
  rw [range_basic]
  intro p hp
  change p ∈ ⋃ j : Fin F.size,(PrimeSpectrum.basicOpen (x j):Set (PrimeSpectrum A))
  exact Set.mem_iUnion.mpr ⟨i,hp⟩
@[expose] def into (i : Fin F.size) : chart R P i ⟶ (locus R P).toScheme :=
  IsOpenImmersion.lift (locus R P).ι (affineInto R P i) (by
    rw [Scheme.Opens.range_ι]
    exact range_locus R P i)
@[reassoc] lemma into_affine (i : Fin F.size) : into R P i ≫ (locus R P).ι=affineInto R P i :=
  IsOpenImmersion.lift_fac _ _ _
instance into_open (i : Fin F.size) : IsOpenImmersion (into R P i) := by
  haveI : IsOpenImmersion (into R P i ≫ (locus R P).ι) := by rw [into_affine];infer_instance
  exact IsOpenImmersion.of_comp (into R P i) (locus R P).ι

/-- A full ACTUAL affine localization cover of the ORIGINAL nonzero
parameter open, not a replacement scheme or an assumed cover. -/
@[expose] def cover : (locus R P).toScheme.OpenCover where
  I₀ := Fin F.size
  X := chart R P
  f := into R P
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro y
    have hy := y.property
    change y.val ∈ ⋃ i : Fin F.size,(PrimeSpectrum.basicOpen (x i):Set (PrimeSpectrum A)) at hy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
    rw [← range_basic R P i] at hi
    obtain ⟨z,hz⟩ := hi
    refine ⟨i,z,?_⟩
    apply (locus R P).ι.isOpenEmbedding.injective
    change (into R P i ≫ (locus R P).ι) z=y.val
    rw [into_affine]
    exact hz
end ProjectiveParameterPrincipalCover318
