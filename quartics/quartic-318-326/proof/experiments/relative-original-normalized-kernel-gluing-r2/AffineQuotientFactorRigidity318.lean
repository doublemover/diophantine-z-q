module
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace AffineQuotientFactorRigidity318
open AlgebraicGeometry CategoryTheory
universe u
variable (B : Type u) [CommRing B] (I J : Ideal B)
abbrev quotient := Spec (CommRingCat.of (B ⧸ I))
abbrev into : quotient B I ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
/-- A morphism of the ACTUAL affine closed quotients over the same original
source forces reverse inclusion of their whole ideals, not just radicals. -/
lemma ideal_le (f : quotient B I ⟶ quotient B J) (h : f ≫ into B J=into B I) : J ≤ I := by
  have hr : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ Spec.preimage f=
      CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp,Spec.map_preimage] using h
  intro b hb
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have he := congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ I) => k.hom b) hr
  change (Spec.preimage f).hom (Ideal.Quotient.mk J b)=Ideal.Quotient.mk I b at he
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb,map_zero] at he
  exact he.symm
end AffineQuotientFactorRigidity318
