module
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Algebra.Hom
public section
noncomputable section
namespace AffineSchemeAlgebraMap318
open AlgebraicGeometry CategoryTheory
universe u
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (f : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S))
  (h : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))=
    Spec.map (CommRingCat.ofHom (algebraMap R T)))
@[expose] def hom : S →ₐ[R] T where
  __ := (Spec.preimage f).hom
  commutes' r := by
    have hr : CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage f=
        CommRingCat.ofHom (algebraMap R T) := by
      apply Spec.map_injective
      simpa only [Spec.map_comp,Spec.map_preimage] using h
    exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom r) hr
lemma spec_hom : Spec.map (CommRingCat.ofHom (hom R S T f h).toRingHom)=f :=
  Spec.map_preimage f
end AffineSchemeAlgebraMap318
