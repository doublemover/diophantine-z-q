module
public import IntegralInfinityPrimeFrame318
public import IntegralArithmeticPrimeFrame318
public import IntegralGluedModel318
public import Mathlib.RingTheory.KrullDimension.Basic
public section
noncomputable section
namespace IntegralGlobalHeightOne318
open AlgebraicGeometry CategoryTheory Ring
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual stalk map of an open affine chart, followed by the canonical
Spec stalk-localization isomorphism. No arbitrary local-ring identification. -/
@[expose] def chartStalkEquiv (A : Type) [CommRing A] (X : Scheme)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (p : PrimeSpectrum A) :
    X.presheaf.stalk (f p) ≃+* Localization.AtPrime p.asIdeal :=
  (asIso (f.stalkMap p)).commRingCatIsoToRingEquiv.trans
    (Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv

theorem chart_stalk_domain (A : Type) [CommRing A] [IsDomain A] (X : Scheme)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (p : PrimeSpectrum A) :
    IsDomain (X.presheaf.stalk (f p)) :=
  Function.Injective.isDomain (chartStalkEquiv A X f p).toRingHom
    (chartStalkEquiv A X f p).injective

/-- Intrinsic local dimension one is transported to the actual prime height;
height-one coverage is not a new caller choice of a different chart point. -/
theorem chart_height_one (A : Type) [CommRing A] (X : Scheme)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (p : PrimeSpectrum A)
    (hp : ringKrullDim (X.presheaf.stalk (f p))=1) : p.asIdeal.height=1 := by
  have he := (chartStalkEquiv A X f p).ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),hp] at he
  exact_mod_cast he.symm

variable (R : Type) [CommRing R] [IsDomain R] [Algebra R ℚ]
  [IsIntegrallyClosed R] [IsNoetherianRing R] (c : Fin 4 → Rˣ)
abbrev Stalk (x : IntegralGluedModel318.scheme R c) :=
  (IntegralGluedModel318.scheme R c).presheaf.stalk x

/-- Every stalk of the literal original glued model is a domain. Its full
finite/infinity chart cover, including u=0, supplies the corresponding point. -/
theorem stalk_domain (hR : Function.Injective (algebraMap R ℚ))
    (x : IntegralGluedModel318.scheme R c) : IsDomain (Stalk R c x) := by
  rcases IntegralGluedModel318.charts_cover R c x with ⟨p,rfl⟩ | ⟨p,rfl⟩
  · letI := IntegralSourceArithmeticDomain318.source_domain R c hR
    exact chart_stalk_domain (IntegralSourceBranches318.SourceOrder R c)
      (IntegralGluedModel318.scheme R c) (IntegralGluedModel318.finiteChart R c) p
  · letI := IntegralInfinityArithmeticDomain318.order_domain R c hR
    exact chart_stalk_domain (IntegralInfinityChart318.Order R c)
      (IntegralGluedModel318.scheme R c) (IntegralGluedModel318.infinityChart R c) p

/-- ALL intrinsic codimension-one stalks of the original good-base integral
model are DVRs. The complete original finite/infinity cover supplies the prime,
and actual stalk isomorphisms transport its height and local ring. -/
theorem stalk_dvr (hR : Function.Injective (algebraMap R ℚ)) (h2 : IsUnit (2 : R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R))
    (x : IntegralGluedModel318.scheme R c) (hx : ringKrullDim (Stalk R c x)=1) :
    letI := stalk_domain R c hR x
    IsDiscreteValuationRing (Stalk R c x) := by
  letI := stalk_domain R c hR x
  rcases IntegralGluedModel318.charts_cover R c x with ⟨p,rfl⟩ | ⟨p,rfl⟩
  · letI := IntegralSourceArithmeticDomain318.source_domain R c hR
    letI := IntegralArithmeticHeightOne318.localization_domain R c hR p.asIdeal
    have hp := chart_height_one (IntegralSourceBranches318.SourceOrder R c)
      (IntegralGluedModel318.scheme R c) (IntegralGluedModel318.finiteChart R c) p hx
    letI := IntegralArithmeticHeightOne318.localization_dvr R c hR h2 hN p.asIdeal hp
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (chartStalkEquiv (IntegralSourceBranches318.SourceOrder R c)
        (IntegralGluedModel318.scheme R c) (IntegralGluedModel318.finiteChart R c) p).symm
  · letI := IntegralInfinityArithmeticDomain318.order_domain R c hR
    letI := IntegralInfinityHeightOne318.localization_domain R c hR p.asIdeal
    have hp := chart_height_one (IntegralInfinityChart318.Order R c)
      (IntegralGluedModel318.scheme R c) (IntegralGluedModel318.infinityChart R c) p hx
    letI := IntegralInfinityHeightOne318.localization_dvr R c hR h2 p.asIdeal hp
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (chartStalkEquiv (IntegralInfinityChart318.Order R c)
        (IntegralGluedModel318.scheme R c) (IntegralGluedModel318.infinityChart R c) p).symm
end IntegralGlobalHeightOne318
