module
public import AffineAlgebraSchemeEquiv318
public section
noncomputable section
namespace AffineOpenAlgebraPoints318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] (U : (Spec (CommRingCat.of A)).Opens)
abbrev Points := {f : Spec (CommRingCat.of S) ⟶ U.toScheme //
  f ≫ U.ι ≫ AffineAlgebraSchemeEquiv318.base R A=AffineAlgebraSchemeEquiv318.base R S}
abbrev Factors (a : A →ₐ[R] S) : Prop :=
  ∃ f : Spec (CommRingCat.of S) ⟶ U.toScheme,f ≫ U.ι=Spec.map (CommRingCat.ofHom a.toRingHom)

@[expose] def coordinate (f : Points R A S U) : A →ₐ[R] S :=
  (AffineAlgebraSchemeEquiv318.points R A S).symm ⟨f.val ≫ U.ι,by
    simpa only [Category.assoc] using f.property⟩
lemma coordinate_spec (f : Points R A S U) :
    Spec.map (CommRingCat.ofHom (coordinate R A S U f).toRingHom)=f.val ≫ U.ι :=
  congrArg Subtype.val ((AffineAlgebraSchemeEquiv318.points R A S).apply_symm_apply _)

/-- Honest relative points of an open affine parameter, including the
actual factor morphism, are equivalent to algebra points that factor. -/
@[expose] def points : Points R A S U ≃ {a : A →ₐ[R] S // Factors R A S U a} where
  toFun f := ⟨coordinate R A S U f,⟨f.val,(coordinate_spec R A S U f).symm⟩⟩
  invFun a := ⟨a.property.choose,by
    rw [←Category.assoc,a.property.choose_spec]
    exact AffineAlgebraSchemeEquiv318.spec_over R A S a.val⟩
  left_inv f := by
    apply Subtype.ext
    apply (cancel_mono U.ι).mp
    exact (show Factors R A S U (coordinate R A S U f) from
      ⟨f.val,(coordinate_spec R A S U f).symm⟩).choose_spec.trans
      (coordinate_spec R A S U f)
  right_inv a := by
    apply Subtype.ext
    apply (AffineAlgebraSchemeEquiv318.points R A S).injective
    apply Subtype.ext
    exact (coordinate_spec R A S U _).trans a.property.choose_spec
end AffineOpenAlgebraPoints318
