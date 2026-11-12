module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Tactic
public section
noncomputable section
namespace AffineIntegralModel318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R Rf B:Type u} [CommRing R] [CommRing Rf] [CommRing B]
  [Algebra R Rf] [Algebra R B] [Algebra Rf B] [IsScalarTower R Rf B]
  (d:R) [IsLocalization.Away d Rf] [Module.Finite Rf B]

abbrev ModelRing := integralClosure R B

include Rf in
/-- Clearing a power of the actual inverted denominator makes every element
of the finite open-cover algebra integral over the original base. -/
theorem integral_multiple (b:B) :
    ∃n:ℕ,IsIntegral R (algebraMap R B d^n*b) := by
  obtain ⟨⟨m,k,hk⟩,hm⟩:=IsIntegral.exists_multiple_integral_of_isLocalization
    (R:=R) (Rₘ:=Rf) (Submonoid.powers d) b (IsIntegral.of_finite Rf b)
  refine ⟨k,?_⟩
  simpa only [←hk,Submonoid.smul_def,Algebra.smul_def,map_pow] using hm

include Rf in
/-- The actual original open algebra is the localization of its integral model,
not merely an abstract algebra having the same generic field. -/
theorem model_localization :
    IsLocalization.Away (algebraMap R (ModelRing (R:=R) (B:=B)) d) B := by
  apply IsLocalization.Away.mk
  · have hu:= (IsLocalization.Away.algebraMap_isUnit (S:=Rf) d).map (algebraMap Rf B)
    simpa only [←IsScalarTower.algebraMap_apply R Rf B,
      ←IsScalarTower.algebraMap_apply R (ModelRing (R:=R) (B:=B)) B] using hu
  · intro b
    obtain ⟨n,hn⟩:=integral_multiple (Rf:=Rf) d b
    refine ⟨n,⟨algebraMap R B d^n*b,hn⟩,?_⟩
    change b*algebraMap R B d^n=algebraMap R B d^n*b
    exact mul_comm _ _
  · intro a b hab
    have he:a=b:=Subtype.ext hab
    exact ⟨0,by rw [he]⟩

abbrev model : Scheme := Spec (CommRingCat.of (ModelRing (R:=R) (B:=B)))
@[expose] def structureMap : model (R:=R) (B:=B) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ModelRing (R:=R) (B:=B))))
@[expose] def openMap : Spec (CommRingCat.of B) ⟶ model (R:=R) (B:=B) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ModelRing (R:=R) (B:=B)) B))

/-- The actual affine model is integral over the original base. Finiteness is
not silently inferred from integrality. -/
theorem structure_integral : IsIntegralHom (structureMap (R:=R) (B:=B)) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  exact algebraMap_isIntegral_iff.mpr inferInstance

include Rf d in
/-- The original cover is an actual open subscheme of the constructed model. -/
theorem open_immersion : IsOpenImmersion (openMap (R:=R) (B:=B)) := by
  let:=model_localization (Rf:=Rf) (B:=B) d
  exact IsOpenImmersion.of_isLocalization (algebraMap R (ModelRing (R:=R) (B:=B)) d)

include Rf in
/-- The image is exactly the basic open where the original denominator is a unit. -/
theorem open_range : Set.range (openMap (R:=R) (B:=B))=
    (PrimeSpectrum.basicOpen (algebraMap R (ModelRing (R:=R) (B:=B)) d)).carrier := by
  let:=model_localization (Rf:=Rf) (B:=B) d
  let:=open_immersion (Rf:=Rf) (B:=B) d
  exact PrimeSpectrum.localization_away_comap_range B _

/-- The open model agrees with the actual original base morphism. -/
theorem open_structure : openMap (R:=R) (B:=B) ≫ structureMap =
    Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  unfold openMap structureMap model
  rw [←Spec.map_comp]
  congr 1

@[expose] def modelOpen : (model (R:=R) (B:=B)).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R (ModelRing (R:=R) (B:=B)) d)

include Rf in
/-- Actual scheme isomorphism from the original cover to the denominator-open
part of the integral model. -/
@[expose] def openIso : Spec (CommRingCat.of B) ≅ (modelOpen (B:=B) d).toScheme := by
  let:=open_immersion (Rf:=Rf) (B:=B) d
  exact IsOpenImmersion.isoOfRangeEq (openMap (R:=R) (B:=B)) (modelOpen (B:=B) d).ι
    (by rw [Scheme.Opens.range_ι]; exact open_range (Rf:=Rf) (B:=B) d)

include Rf in
/-- The isomorphism respects the actual embedding into the model. -/
theorem openIso_hom_fac : (openIso (Rf:=Rf) (B:=B) d).hom ≫ (modelOpen (B:=B) d).ι=
    openMap (R:=R) (B:=B) := by
  let:=open_immersion (Rf:=Rf) (B:=B) d
  unfold openIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end AffineIntegralModel318
