module
public import ContactNormalizedOverlapCoefficients318
public import TwoRestrictedFamilyPullback318
public section
noncomputable section
namespace ContactNormalizedZeroOverlap318
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
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "m" k => ContactNormalizedChartZeroFamily318.parameterMap R c L hz k
local notation "p" k => ContactNormalizedChartZeroFamily318.projection R c L hz k
local notation "g₁" => ContactNormalizedOverlapCoefficients318.first R c L hz i j
local notation "g₂" => ContactNormalizedOverlapCoefficients318.second R c L hz i j

@[expose] def left : ProjectiveParameterSliceSchemes318.overlap R P i j ⟶
    ProjectiveParameterSliceSchemes318.chart R P i :=
  ProjectiveParameterSliceSchemes318.inclusion R P i j
@[expose] def right : ProjectiveParameterSliceSchemes318.overlap R P i j ⟶
    ProjectiveParameterSliceSchemes318.chart R P j :=
  (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom ≫
    ProjectiveParameterSliceSchemes318.inclusion R P j i

lemma left_parameter : left R c L hz i j ≫ m i ≫ W.ι=
    Spec.map (CommRingCat.ofHom g₁.toRingHom) := by
  rw [ContactNormalizedChartZeroIdentification318.factor]
  rw [left,ProjectiveParameterSliceSchemes318.inclusion,← Spec.map_comp]
  rfl
lemma right_parameter : right R c L hz i j ≫ m j ≫ W.ι=
    Spec.map (CommRingCat.ofHom g₂.toRingHom) := by
  rw [right,Category.assoc,ContactNormalizedChartZeroIdentification318.factor]
  change Spec.map (CommRingCat.ofHom
    (ProjectiveParameterSliceLocalization318.transition R P i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap
        (ProjectiveParameterSliceAlgebra318.algebra R P j)
        (ProjectiveParameterSliceLocalization318.algebra R P j i))) ≫
      Spec.map (CommRingCat.ofHom
        (ContactNormalizedChartZeroIdentification318.coefficient R c L hz j).toRingHom)=_
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact ProjectiveParameterSliceLocalization318.transition_localized R P i j
    (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P j) a)

/-- The actual two normalized chart families agree on the actual
principal overlap. The map is obtained from the SAME universal zero,
its original classified section, and the invertible normalization
coefficient. It preserves the overlap base, not merely geometric fibers. -/
@[expose] def iso : pullback (p j) (right R c L hz i j) ≅
    pullback (p i) (left R c L hz i j) :=
  TwoRestrictedFamilyPullback318.iso π W.ι (m j) (right R c L hz i j)
    (Spec.map (CommRingCat.ofHom g₂.toRingHom)) (right_parameter R c L hz i j) ≪≫
    ContactNormalizedOverlapCoefficients318.zeroIso R c L hz i j ≪≫
    (TwoRestrictedFamilyPullback318.iso π W.ι (m i) (left R c L hz i j)
      (Spec.map (CommRingCat.ofHom g₁.toRingHom)) (left_parameter R c L hz i j)).symm
@[reassoc] lemma iso_projection : (iso R c L hz i j).hom ≫
    pullback.snd (p i) (left R c L hz i j)=pullback.snd (p j) (right R c L hz i j) := by
  rw [iso,Iso.trans_hom,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    Category.assoc,TwoRestrictedFamilyPullback318.inv_projection,
    ContactNormalizedOverlapCoefficients318.zeroIso_projection,
    TwoRestrictedFamilyPullback318.iso_projection]
end ContactNormalizedZeroOverlap318
