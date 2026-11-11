module
public import FourRootIntrinsicCanonicalFrames318
public import FourRootActualFrameDenominatorCover318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section
namespace FourRootWholeCanonicalCover318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
lemma finite_lift(p:finiteScheme b):∃i,∃q,finiteEmbedding b i q=finiteChart b p:=by
  obtain ⟨i,hi⟩:=FourRootActualFrameDenominatorCover318.finite_cover b hb p
  have hm:p∈Set.range (PrimeSpectrum.comap
      (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i))):=by
    rw [PrimeSpectrum.localization_away_comap_range (FiniteRing b i)
      (FourRootActualFiniteBranchChart318.denominator b i)]
    exact hi
  obtain ⟨q,hq⟩:=hm
  exact ⟨i,q,congrArg (finiteChart b) hq⟩
/-- Whole-Scheme five-chart cover, including nonclosed points and all
infinity components. The source is the unchanged actual glued Scheme. -/
theorem frames_cover(x:scheme b):
    (∃i,∃q,finiteEmbedding b i q=x) ∨ (∃q,infinityEmbedding b hb q=x):=by
  rcases charts_cover b x with ⟨p,rfl⟩|⟨p,rfl⟩
  · exact Or.inl (finite_lift b hb p)
  · rcases FourRootActualFrameDenominatorCover318.infinity_cover b hb p with hu|hd
    · have hm:p∈Set.range (PrimeSpectrum.comap
        (algebraMap (FourRootInfinityCoordinateRing318.Ring b)
          (FourRootCoordinateOverlap318.InfinityOverlap b))):=by
        rw [PrimeSpectrum.localization_away_comap_range
          (FourRootCoordinateOverlap318.InfinityOverlap b)
          (FourRootInfinityCoordinateRing318.coordinate b none)]
        exact hu
      obtain ⟨q,hq⟩:=hm
      obtain ⟨i,r,hr⟩:=finite_lift b hb (intoFinite b q)
      refine Or.inl ⟨i,r,hr.trans ?_⟩
      change (intoFinite b≫finiteChart b) q=infinityChart b p
      rw [chart_overlap]
      exact congrArg (infinityChart b) hq
    · have hm:p∈Set.range (PrimeSpectrum.comap
        (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))):=by
        rw [PrimeSpectrum.localization_away_comap_range (InfinityRing b hb)
          (FourRootActualInfinityKaehler318.denominator b hb)]
        exact hd
      obtain ⟨q,hq⟩:=hm
      exact Or.inr ⟨q,congrArg (infinityChart b) hq⟩
@[expose] def chart:Option (Fin 4)→Scheme
  | none=>Spec (CommRingCat.of (InfinityRing b hb))
  | some i=>Spec (CommRingCat.of (FiniteRing b i))
@[expose] def embedding:(i:Option (Fin 4))→chart b hb i⟶scheme b
  | none=>infinityEmbedding b hb
  | some i=>finiteEmbedding b i
instance embedding_open(i:Option (Fin 4)):IsOpenImmersion (embedding b hb i):=by
  cases i
  · exact infinityEmbedding_open b hb
  · exact finiteEmbedding_open b _
@[expose] def cover:(scheme b).OpenCover where
  I₀:=Option (Fin 4)
  X:=chart b hb
  f:=embedding b hb
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro x
    rcases frames_cover b hb x with ⟨i,q,hq⟩|⟨q,hq⟩
    · exact ⟨some i,q,hq⟩
    · exact ⟨none,q,hq⟩
/-- Actual rank-one local freeness of the whole intrinsic differential
sheaf, through a produced genuine Scheme open cover and actual O-module
isomorphisms. Not a coefficient record masquerading as a canonical line. -/
@[expose] def localFrame(i:Option (Fin 4)):
    (omega b).restrict (embedding b hb i)≅SheafOfModules.unit (chart b hb i).ringCatSheaf:=by
  cases i with
  | none=>exact (infinityFrame b hb).symm≪≫Scheme.Modules.restrictUnitIso (infinityEmbedding b hb)
  | some i=>exact (finiteFrame b i).symm≪≫Scheme.Modules.restrictUnitIso (finiteEmbedding b i)
end FourRootWholeCanonicalCover318
