module
public import AffineSchemeAlgebraMap318
public section
noncomputable section
namespace AffineAlgebraSchemeEquiv318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S]
abbrev base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))
abbrev Points := {f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A) //
  f ≫ base R A=base R S}
lemma spec_over (a : A →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ base R A=base R S := by
  rw [base,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => a.commutes r)
/-- Actual affine anti-equivalence, with the original R-structure square. -/
@[expose] def points : (A →ₐ[R] S) ≃ Points R A S where
  toFun a := ⟨Spec.map (CommRingCat.ofHom a.toRingHom),spec_over R A S a⟩
  invFun f := AffineSchemeAlgebraMap318.hom R A S f.val f.property
  left_inv a := by
    apply AlgHom.ext
    have h := AffineSchemeAlgebraMap318.spec_hom R A S
      (Spec.map (CommRingCat.ofHom a.toRingHom)) (spec_over R A S a)
    have he := congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom)
      (Spec.map_injective h)
    exact fun x => DFunLike.congr_fun he x
  right_inv f := Subtype.ext (AffineSchemeAlgebraMap318.spec_hom R A S f.val f.property)
end AffineAlgebraSchemeEquiv318
