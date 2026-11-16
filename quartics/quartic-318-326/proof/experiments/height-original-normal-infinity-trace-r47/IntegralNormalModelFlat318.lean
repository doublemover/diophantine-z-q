module
public import IntegralNormalModelCodimensionOne318
public import BivariateIntegral318
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public section
noncomputable section
namespace IntegralNormalModelFlat318
open Polynomial CategoryTheory AlgebraicGeometry Opposite
open IntegralReciprocalBase318 IntegralTwoChartNormalization318
set_option maxHeartbeats 1200000
universe u

/-- The map on the entire affine section ring is the actual map of the
scheme morphism. Dominance over a Dedekind base supplies torsion-freeness. -/
theorem affine_flat {R : Type u} [CommRing R] [IsDedekindDomain R]
    (X : Scheme.{u}) [IsAffine X] [IsDomain Γ(X,⊤)]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsDominant f] : Flat f := by
  let A := Γ(Spec (CommRingCat.of R),⊤)
  let e : A ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  letI : IsDomain A := Function.Injective.isDomain e e.injective
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R e.symm
  letI : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_ringEquiv e
  letI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.symm
  letI : IsDedekindDomain A :=
    { (inferInstance : IsDomain A), (inferInstance : IsNoetherianRing A),
      (inferInstance : Ring.DimensionLEOne A), (inferInstance : IsIntegrallyClosed A) with }
  letI : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  change (f.appTop).hom.Flat
  letI : Algebra A Γ(X,⊤) := (f.appTop).hom.toAlgebra
  exact BivariateIntegral318.flat_of_injective (f.app_injective ⊤)

/-- The affine neighborhoods are chosen from the actual scheme cover,
with a specified point in each; empty-open domain shortcuts are avoided. -/
theorem integral_dominant_flat {R : Type u} [CommRing R] [IsDedekindDomain R]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))
    [IsDominant f] : Flat f := by
  let U : X → X.Opens := fun x => (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU (x : X) : IsAffineOpen (U x) := isAffineOpen_opensRange _
  have hx (x : X) : x ∈ U x := X.affineCover.covers x
  have hcover : (⨆ x, U x) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x,hx x⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top U hcover
  intro x
  letI : Nonempty (U x) := ⟨⟨x,hx x⟩⟩
  letI : IsAffine (U x) := hU x
  letI : IsIntegral (U x) := isIntegral_of_isOpenImmersion (U x).ι
  letI : IsDominant (U x).ι :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (U x).ι (U x).ι.isOpenEmbedding.isOpenMap⟩
  exact affine_flat (U x) ((U x).ι ≫ f)

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R]
  [IsIntegrallyClosed R[X]] (a : Fin 4 → R) (N : R) (B : Type u)
  [CommRing B] [IsDomain B] [Algebra (FiniteBase R a N) B]
  [Module.Finite (FiniteBase R a N) B] [Algebra.Etale (FiniteBase R a N) B]

@[expose] def scalarMap : R →+* B :=
  (algebraMap (FiniteBase R a N) B).comp (algebraMap R (FiniteBase R a N))

theorem scalarMap_injective (hN : N ≠ 0) : Function.Injective (scalarMap R a N B) := by
  have hd := finiteDenominator_ne_zero R a N hN
  letI : IsDomain (FiniteBase R a N) := Localization.Away.isDomain hd
  have hi : Function.Injective (algebraMap R[X] (FiniteBase R a N)) :=
    IsLocalization.injective (M := Submonoid.powers (finiteDenominator R a N)) _
      (by rintro _ ⟨n,rfl⟩; exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd))
  intro x y h
  apply Polynomial.C_injective
  apply hi
  apply FaithfulSMul.algebraMap_injective (FiniteBase R a N) B
  simpa only [IntegralReciprocalBase318.finite_C] using h

theorem source_over_base : sourceOpen R a N B ≫ structureMap R a N B =
    Spec.map (CommRingCat.ofHom (scalarMap R a N B)) := by
  unfold structureMap
  rw [←Category.assoc, factorization, finite_factor, Category.assoc,
    JLineAtlas318.chart_over_base, ←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  change algebraMap (FiniteBase R a N) B
    (algebraMap R[X] (FiniteBase R a N) (C r)) = _
  rw [finite_C]
  rfl

theorem dominant (hN : N ≠ 0) : IsDominant (structureMap R a N B) := by
  have hd : IsDominant (Spec.map (CommRingCat.ofHom (scalarMap R a N B))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (scalarMap R a N B))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (scalarMap_injective R a N B hN)]
    exact bot_le
  letI : IsDominant (sourceOpen R a N B ≫ structureMap R a N B) := by
    rw [source_over_base]
    exact hd
  exact IsDominant.of_comp (f := sourceOpen R a N B) (structureMap R a N B)

theorem flat (hN : N ≠ 0) : Flat (structureMap R a N B) := by
  letI : IsIntegral (model R a N B) := model_integral R a N B
  letI := dominant R a N B hN
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (fun j => (sourceCover R a N B j).1) (sourceCover_covers R a N B)
  intro j
  let U := sourceCover R a N B j
  letI : IsAffine U.1 := U.2
  let e : Γ(U.1,⊤) ≃+* Γ(model R a N B,U) :=
    (Scheme.restrictFunctorΓ.app (op U.1)).commRingCatIsoToRingEquiv
  letI : IsDomain Γ(model R a N B,U) := (chart_properties R a N B hN j).1
  letI : IsDomain Γ(U.1,⊤) := Function.Injective.isDomain e e.injective
  letI : Nonempty U.1 := Nonempty.map U.1.isoSpec.inv inferInstance
  letI : IsDominant U.1.ι :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace U.1.ι U.1.ι.isOpenEmbedding.isOpenMap⟩
  exact affine_flat U.1 (U.1.ι ≫ structureMap R a N B)

/-- All properties concern the SAME structure morphism over the WHOLE
Dedekind coefficient base, not only its punctured generic fiber. -/
theorem proper_flat_surjective (hN : N ≠ 0) :
    IsProper (structureMap R a N B) ∧ Flat (structureMap R a N B) ∧
    Surjective (structureMap R a N B) ∧ LocallyOfFinitePresentation (structureMap R a N B) := by
  letI := proper_model R a N B hN
  letI := dominant R a N B hN
  exact ⟨inferInstance,flat R a N B hN,inferInstance,inferInstance⟩
end IntegralNormalModelFlat318
