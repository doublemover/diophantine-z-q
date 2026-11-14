module
public import VaryingWordFamilyCocycle318
public section
noncomputable section
namespace VaryingWordFamilyTriplePullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingWordTripleFamilyMaps318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "K" => VaryingWordTripleAlgebra318.ring R A ι w v u
local notation "H" x y => VaryingNormalizedWordOverlap318.ring R A ι x y
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
local notation "Q" => VaryingWordTripleFamily318.ring R A ι w v u
local notation "inc" => VaryingWordOverlapFamily318.into R A ι
local notation "p" => VaryingWordOverlapFamily318.projection R A ι
@[expose] def projection : scheme R A ι w v u ⟶ VaryingWordTriplePullback318.scheme R A ι w v u :=
  Spec.map (CommRingCat.ofHom (algebraMap K Q))

lemma first_cartesian : IsPullback (first R A ι w v u) (projection R A ι w v u)
    (p w v) (VaryingWordTriplePullback318.first R A ι w v u) := by
  have h := VaryingQuotientCoefficientPullback318.cartesian R A ι w (H w v)
    (VaryingWordOverlapFamily318.data R A ι w v) K (VaryingWordTripleMaps318.firstMap R A ι w v u)
  simpa only [VaryingWordTripleFamily318.first_data] using h
lemma second_cartesian : IsPullback (second R A ι w v u) (projection R A ι w v u)
    (p w u) (VaryingWordTriplePullback318.second R A ι w v u) := by
  have h := VaryingQuotientCoefficientPullback318.cartesian R A ι w (H w u)
    (VaryingWordOverlapFamily318.data R A ι w u) K (VaryingWordTripleMaps318.secondMap R A ι w v u)
  simpa only [VaryingWordTripleFamily318.second_data] using h

lemma square : first R A ι w v u ≫ inc w v=second R A ι w v u ≫ inc w u := by
  change Spec.map (firstMap R A ι w v u) ≫ Spec.map _=
    Spec.map (secondMap R A ι w v u) ≫ Spec.map _
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
  change (firstMap R A ι w v u).hom (Ideal.Quotient.mk _
    (Algebra.TensorProduct.map (VaryingNormalizedWordOverlap318.inclusion R A ι w v) (AlgHom.id R A) z))=
    (secondMap R A ι w v u).hom (Ideal.Quotient.mk _
      (Algebra.TensorProduct.map (VaryingNormalizedWordOverlap318.inclusion R A ι w u) (AlgHom.id R A) z))
  rw [first_mk,second_mk]
  apply congrArg (Ideal.Quotient.mk (VaryingWordTripleFamily318.ideal R A ι w v u))
  have h := congrArg (fun f : N →ₐ[R] K => Algebra.TensorProduct.map f (AlgHom.id R A))
    (VaryingWordTripleCocycle318.square R A ι w v u).symm
  rw [Algebra.TensorProduct.map_comp_id,Algebra.TensorProduct.map_comp_id] at h
  exact congrArg (fun f : N ⊗[R] A →ₐ[R] K ⊗[R] A => f z) h

/-- The literal triple quotient family is the ACTUAL intersection of its
pairwise open family inclusions, not only a related affine family. -/
lemma cartesian : IsPullback (first R A ι w v u) (second R A ι w v u) (inc w v) (inc w u) := by
  apply IsPullback.of_right (h₁₂ := p w v)
    (h₂₂ := VaryingNormalizedUniversalFamily318.projection R A ι w)
  · have h := (second_cartesian R A ι w v u).flip.paste_horiz
      (VaryingWordTriplePullback318.cartesian R A ι w v u)
    simpa only [(first_cartesian R A ι w v u).w,
      (VaryingWordOverlapFamily318.cartesian R A ι w u).w] using h
  · exact square R A ι w v u
  · exact (VaryingWordOverlapFamily318.cartesian R A ι w v).flip
@[expose] def comparison : scheme R A ι w v u ≅ pullback (inc w v) (inc w u) :=
  (cartesian R A ι w v u).isoPullback
@[reassoc] lemma comparison_fst : (comparison R A ι w v u).hom ≫ pullback.fst _ _=first R A ι w v u :=
  (cartesian R A ι w v u).isoPullback_hom_fst
@[reassoc] lemma comparison_snd : (comparison R A ι w v u).hom ≫ pullback.snd _ _=second R A ι w v u :=
  (cartesian R A ι w v u).isoPullback_hom_snd
end VaryingWordFamilyTriplePullback318
