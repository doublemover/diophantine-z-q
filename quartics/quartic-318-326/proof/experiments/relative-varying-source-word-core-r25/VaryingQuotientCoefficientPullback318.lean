module
public import VaryingSourceCoefficientPullback318
public section
noncomputable section
namespace VaryingQuotientCoefficientPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingNormalizedWordFrame318 VaryingSourceCoefficientPullback318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (d : VaryingNormalizedWordParameter318.Point R A ι w S)
local notation "F" => framed R A ι w S d
lemma into_projection :
    CyclicQuotientFiniteFlat318.into F.action F.marked ≫ projection R A S=
      CyclicQuotientFiniteFlat318.projection F.action F.marked := by
  rw [CyclicQuotientFiniteFlat318.into,projection,CyclicQuotientFiniteFlat318.projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq S (S ⊗[R] A)
    ((S ⊗[R] A) ⧸ CyclicQuotientEvaluation318.ideal F.action F.marked)).symm

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "dT" => VaryingNormalizedWordNaturality318.mapPoint R A ι w S T f d
local notation "FT" => framed R A ι w T dT
/-- Actual Cartesian base change of the finite-flat quotient projection
under arbitrary coefficient maps, with both original family maps retained. -/
lemma cartesian : IsPullback
    (Spec.map (VaryingNormalizedFamilyBaseChange318.quotientMap R A ι w S T f d))
    (CyclicQuotientFiniteFlat318.projection FT.action FT.marked)
    (CyclicQuotientFiniteFlat318.projection F.action F.marked)
    (coefficientChange R S T f) := by
  have h := (VaryingNormalizedFamilyBaseChange318.cartesian R A ι w S T f d).flip.paste_vert
    (VaryingSourceCoefficientPullback318.cartesian R A S T f)
  simpa only [into_projection] using h
@[expose] def comparison : CyclicQuotientFiniteFlat318.scheme FT.action FT.marked ≅
    pullback (CyclicQuotientFiniteFlat318.projection F.action F.marked)
      (coefficientChange R S T f) := (cartesian R A ι w S d T f).isoPullback
@[reassoc] lemma comparison_projection :
    (comparison R A ι w S d T f).hom ≫ pullback.snd _ _=
      CyclicQuotientFiniteFlat318.projection FT.action FT.marked :=
  (cartesian R A ι w S d T f).isoPullback_hom_snd
end VaryingQuotientCoefficientPullback318
