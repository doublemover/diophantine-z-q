module
public import PELOriginalCharacterActualOverlap318
public import FourRootProjectiveChartPullbacks318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace PELOriginalCharacterRefinedCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalCommonContactBase318 PELOriginalCharacterInfinityMaps318
open PELOriginalCharacterActualOverlap318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def infinityChart (i:Fin 4):Spec (CommRingCat.of (N i))⟶
    FourRootGluedScheme318.scheme branches:=
  FourRootCharacterInfinityOpen318.inclusion branches (indices i)≫
    FourRootGluedScheme318.infinityChart branches
instance infinityChart_open (i:Fin 4):IsOpenImmersion (infinityChart i):=by
  unfold infinityChart
  infer_instance
@[expose] def intoInfinity (i:Fin 4):Spec (CommRingCat.of (O i))⟶Spec (CommRingCat.of (N i)):=
  Spec.map (CommRingCat.ofHom (fromNeighborhood i).toRingHom)
instance intoInfinity_open (i:Fin 4):IsOpenImmersion (intoInfinity i):=
  IsOpenImmersion.of_isLocalization (FourRootCharacterInfinityOpen318.u branches (indices i))
@[expose] def intoFinite (i:Fin 4):Spec (CommRingCat.of (O i))⟶
    FourRootGluedScheme318.finiteScheme branches:=
  Spec.map (CommRingCat.ofHom (fromFinite i).toRingHom)

lemma source_square (i:Fin 4):
    Spec.map (CommRingCat.ofHom (sourceOverlap i).toRingHom)≫
      FourRootGluedScheme318.intoInfinity branches=
    intoInfinity i≫FourRootCharacterInfinityOpen318.inclusion branches (indices i):=by
  unfold FourRootGluedScheme318.intoInfinity intoInfinity FourRootCharacterInfinityOpen318.inclusion
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact source_on_ring i

lemma chart_square (i:Fin 4):intoFinite i≫FourRootGluedScheme318.finiteChart branches=
    intoInfinity i≫infinityChart i:=by
  have hf:intoFinite i=Spec.map (CommRingCat.ofHom (sourceOverlap i).toRingHom)≫
      FourRootGluedScheme318.intoFinite branches:=by
    rw [FourRootGluedScheme318.intoFinite_eq,←Spec.map_comp]
    rfl
  rw [hf,Category.assoc,FourRootGluedScheme318.chart_overlap,←Category.assoc,
    source_square,Category.assoc]
  rfl

/-- The exact intersection of the refined infinity chart with the old
finite chart is the second principal localization. This is an equality
on all prime spectra, not only on complex closed points. -/
lemma refined_preimage (i:Fin 4):infinityChart i ⁻¹ᵁ
    (FourRootGluedScheme318.finiteChart branches).opensRange=(intoInfinity i).opensRange:=by
  rw [infinityChart,Scheme.Hom.comp_preimage,
    FourRootProjectiveChartPullbacks318.infinity_preimage_finite,
    FourRootProjectiveChartPullbacks318.intoInfinity_range]
  unfold FourRootCharacterInfinityOpen318.inclusion
  rw [SpecMap_preimage_basicOpen]
  apply TopologicalSpace.Opens.ext
  exact (PrimeSpectrum.localization_away_comap_range _ _).symm

/-- Actual categorical pullback, including residue fields and local
rings. The API square orientation is the reverse of chart_square. -/
theorem actual_pullback (i:Fin 4):IsPullback (intoFinite i) (intoInfinity i)
    (FourRootGluedScheme318.finiteChart branches) (infinityChart i):=
  IsOpenImmersion.isPullback _ _ _ _ (chart_square i).symm (refined_preimage i)

/-- Every original point is retained. Away from u=0 it is already in the
finite chart; above u=0 all three character ratios are units. -/
theorem covers (i:Fin 4) (p:FourRootGluedScheme318.scheme branches):
    (∃q,FourRootGluedScheme318.finiteChart branches q=p) ∨ (∃q,infinityChart i q=p):=by
  rcases FourRootGluedScheme318.charts_cover branches p with h|⟨q,rfl⟩
  · exact Or.inl h
  · by_cases hu:FourRootInfinityCoordinateRing318.coordinate branches none∈q.asIdeal
    · right
      have hq:q∈(FourRootCharacterInfinityOpen318.inclusion branches (indices i)).opensRange:=by
        change q∈Set.range (PrimeSpectrum.comap (algebraMap I (N i)))
        rw [PrimeSpectrum.localization_away_comap_range]
        exact FourRootCharacterInfinityOpen318.denominator_not_mem branches (indices i) q hu
      obtain ⟨r,hr⟩:=hq
      refine ⟨r,?_⟩
      change FourRootGluedScheme318.infinityChart branches
        (FourRootCharacterInfinityOpen318.inclusion branches (indices i) r)=_
      rw [hr]
    · left
      have hq:q∈(FourRootGluedScheme318.intoInfinity branches).opensRange:=by
        rw [FourRootProjectiveChartPullbacks318.intoInfinity_range]
        exact hu
      obtain ⟨r,hr⟩:=hq
      refine ⟨FourRootGluedScheme318.intoFinite branches r,?_⟩
      change (FourRootGluedScheme318.intoFinite branches≫FourRootGluedScheme318.finiteChart branches) r=_
      rw [FourRootGluedScheme318.chart_overlap]
      change FourRootGluedScheme318.infinityChart branches
        (FourRootGluedScheme318.intoInfinity branches r)=_
      rw [hr]

@[expose] def chart (i:Fin 4):Bool→Scheme
  | false=>FourRootGluedScheme318.finiteScheme branches
  | true=>Spec (CommRingCat.of (N i))
@[expose] def embedding (i:Fin 4):(b:Bool)→chart i b⟶FourRootGluedScheme318.scheme branches
  | false=>FourRootGluedScheme318.finiteChart branches
  | true=>infinityChart i
instance embedding_open (i:Fin 4) (b:Bool):IsOpenImmersion (embedding i b):=by
  cases b <;> dsimp [embedding] <;> infer_instance
@[expose] def cover (i:Fin 4):(FourRootGluedScheme318.scheme branches).OpenCover where
  I₀:=Bool
  X:=chart i
  f:=embedding i
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro p
    rcases covers i p with ⟨q,hq⟩|⟨q,hq⟩
    · exact ⟨false,q,hq⟩
    · exact ⟨true,q,hq⟩
end PELOriginalCharacterRefinedCover318
