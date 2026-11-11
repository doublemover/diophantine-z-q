module
public import VaryingNormalizedIdealBaseChange318
public import AffineQuotientPushout318
public section
noncomputable section
namespace VaryingNormalizedFamilyBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingNormalizedIdealBaseChange318 VaryingNormalizedWordFrame318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S T : Type u) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
variable (f : S →ₐ[R] T) (d : VaryingNormalizedWordParameter318.Point R A ι w S)
local notation "dT" => VaryingNormalizedWordNaturality318.mapPoint R A ι w S T f d
local notation "F" => framed R A ι w S d
local notation "FT" => framed R A ι w T dT
local notation "I" => ideal F.action F.marked
local notation "J" => ideal FT.action FT.marked
local notation "q" => CommRingCat.ofHom (sourceMap R A S T f).toRingHom
@[expose] def quotientMap : CommRingCat.of ((S ⊗[R] A) ⧸ I) ⟶
    CommRingCat.of ((T ⊗[R] A) ⧸ J) :=
  AffineQuotientPushout318.arrow q I J (ideal_map R A ι w S T f d)
lemma quotientMap_mk (z : S ⊗[R] A) :
    (quotientMap R A ι w S T f d).hom (Ideal.Quotient.mk I z)=
      Ideal.Quotient.mk J (sourceMap R A S T f z) := rfl

/-- The coefficient-changed normalized quotient is the ACTUAL pullback
of the old closed quotient along the original source coefficient map. -/
lemma cartesian : IsPullback
    (CyclicQuotientFiniteFlat318.into FT.action FT.marked)
    (Spec.map (quotientMap R A ι w S T f d))
    (Spec.map q)
    (CyclicQuotientFiniteFlat318.into F.action F.marked) :=
  AffineQuotientPushout318.pullback q I J (ideal_map R A ι w S T f d)
@[expose] def comparison :
    CyclicQuotientFiniteFlat318.scheme FT.action FT.marked ≅
      pullback (Spec.map q) (CyclicQuotientFiniteFlat318.into F.action F.marked) :=
  (cartesian R A ι w S T f d).isoPullback
@[reassoc] lemma comparison_fst :
    (comparison R A ι w S T f d).hom ≫ pullback.fst _ _=
      CyclicQuotientFiniteFlat318.into FT.action FT.marked :=
  (cartesian R A ι w S T f d).isoPullback_hom_fst
@[reassoc] lemma comparison_snd :
    (comparison R A ι w S T f d).hom ≫ pullback.snd _ _=
      Spec.map (quotientMap R A ι w S T f d) :=
  (cartesian R A ι w S T f d).isoPullback_hom_snd
end VaryingNormalizedFamilyBaseChange318
