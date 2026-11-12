module
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace AffineSpecOriginalRingTransport318
open AlgebraicGeometry CategoryTheory
universe u
variable {A B : CommRingCat.{u}} (e : Spec B ≅ Spec A)

/-- The original scheme isomorphism reflected through the actual Spec
functor; its direction is A to B. -/
@[expose] def hom : A →+* B := (Spec.preimage e.hom).hom

/-- Public carrier equation for the unchanged actual Spec-preimage ring map. -/
lemma hom_eq : hom e = (Spec.preimage e.hom).hom := rfl

lemma surjective : Function.Surjective (hom e) := by
  have h : Spec.preimage e.inv ≫ Spec.preimage e.hom = 𝟙 B := by
    apply Spec.map_injective
    simpa only [Spec.map_comp,Spec.map_preimage,Spec.map_id] using e.hom_inv_id
  have h' := congrArg CommRingCat.Hom.hom h
  intro b
  refine ⟨(Spec.preimage e.inv).hom b,?_⟩
  exact RingHom.congr_fun h' b
end AffineSpecOriginalRingTransport318
