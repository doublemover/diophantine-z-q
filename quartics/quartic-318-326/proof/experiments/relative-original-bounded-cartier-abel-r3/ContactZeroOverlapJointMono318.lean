module
public import ContactZeroOverlapOriginal318
public section
noncomputable section
namespace ContactZeroOverlapJointMono318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i j : Fin F.size)
local notation "S" => ContactNormalizedOverlapCoefficients318.ring R c L hz i j
@[expose] def coefficient : R →ₐ[ℚ] S := IsScalarTower.toAlgHom ℚ R S
local notation "f" => coefficient R c L hz i j

/-- The actual universal overlap point is also a literal triple point
with repeated first coordinate and its genuine unit 1. Distinctness is
not required in the gluing diagram. -/
@[expose] def point : ProjectiveParameterSliceTriplePoints318.Point R P S i j i where
  point := ProjectiveParameterSliceLocalization318.point R P i j
  first_eq := ProjectiveParameterSliceLocalization318.first R P i j
  secondUnit := ProjectiveParameterSliceLocalization318.unit R P i j
  second_eq := (ProjectiveParameterSliceLocalization318.unit_val R P i j).symm
  thirdUnit := 1
  third_eq := ProjectiveParameterSliceLocalization318.first R P i j
local notation "a" => point R c L hz i j
local notation "family" => ContactNormalizedTripleFamilies318.family R c L hz S f a
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "proj" => ContactNormalizedZeroTransitions318.projection R c L hz
local notation "chart" => ContactNormalizedOriginalCurve318.chart R c L hz
local notation "orig" => ContactNormalizedFamilyJointMono318.original R c L hz S f a
local notation "base" => ContactNormalizedTripleProjection318.projection R c L hz S f a

lemma parameter : ContactNormalizedPointZeroFamily318.testMap R c L hz S f i a.point a.first_eq=
    ProjectiveParameterSliceSchemes318.inclusion R P i j := by
  rw [ContactNormalizedPointZeroFamily318.testMap,ProjectiveParameterSliceSchemes318.inclusion]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ContactNormalizedPointZeroFamily318.sliceMap_mk R c L hz S f i a.point a.first_eq z
@[expose] def comparison : family ≅ ContactNormalizedZeroTransitions318.overlap R c L hz i j :=
  pullback.congrHom rfl (parameter R c L hz i j)
@[reassoc] lemma comparison_original : (comparison R c L hz i j).hom ≫ inc i j ≫ chart i=orig := by
  rw [comparison,ContactNormalizedZeroTransitions318.inclusion,
    pullback.congrHom_hom,pullback.lift_fst_assoc]
  rfl
@[reassoc] lemma comparison_projection : (comparison R c L hz i j).hom ≫ proj i j=base := by
  rw [comparison,ContactNormalizedZeroTransitions318.projection,
    pullback.congrHom_hom,pullback.lift_snd]
  rfl
@[reassoc] lemma inv_original : (comparison R c L hz i j).inv ≫ orig=inc i j ≫ chart i := by
  rw [← comparison_original R c L hz i j,Iso.inv_hom_id_assoc]
@[reassoc] lemma inv_projection : (comparison R c L hz i j).inv ≫ base=proj i j := by
  rw [← comparison_projection R c L hz i j,Iso.inv_hom_id_assoc]

/-- The actual pairwise overlap is determined by its old contact-curve
map AND its actual coefficient-overlap projection. This provides the
correct geometric uniqueness principle for the remaining triple leg. -/
lemma hom_ext {X : Scheme} (v w : X ⟶ ContactNormalizedZeroTransitions318.overlap R c L hz i j)
    (hc : v ≫ inc i j ≫ chart i=w ≫ inc i j ≫ chart i)
    (hp : v ≫ proj i j=w ≫ proj i j) : v=w := by
  apply (cancel_mono (comparison R c L hz i j).inv).1
  apply ContactNormalizedFamilyJointMono318.hom_ext R c L hz S f a
  · simpa only [Category.assoc,inv_original] using hc
  · simpa only [Category.assoc,inv_projection] using hp

instance inclusion_self (i : Fin F.size) : IsIso (inc i i) := inferInstance

/-- Actual self-overlap transition is the identity on the whole zero
scheme, not just on its base or its geometric points. -/
lemma transition_self (i : Fin F.size) :
    (ContactNormalizedZeroTransitions318.transition R c L hz i i).hom=𝟙 _ := by
  apply hom_ext R c L hz i i
  · simp only [ContactZeroOverlapOriginal318.transition,Category.id_comp]
  · rw [ContactNormalizedZeroTransitions318.transition_projection,
      ProjectiveParameterSliceSelf318.transition_self,Category.comp_id,Category.id_comp]
end ContactZeroOverlapJointMono318
