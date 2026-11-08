module
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace CartesianSectionPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 500000
variable {E E' B B':Scheme} {f:E' ⟶ E} {p':E' ⟶ B'} {p:E ⟶ B} {b:B' ⟶ B}
/-- Sections of an actual cartesian pullback correspond to the actual
points over the specified base map, with both explicit inverse laws. -/
@[expose] def equiv (h:IsPullback f p' p b) :
    {q:B' ⟶ E' //q ≫ p'=𝟙 _} ≃ {q:B' ⟶ E //q ≫ p=b} where
  toFun q:=⟨q.val ≫ f,by rw [Category.assoc,h.w,←Category.assoc,q.property,Category.id_comp]⟩
  invFun q:=⟨h.lift q.val (𝟙 _) (by simpa using q.property),by simp⟩
  left_inv q:=by
    apply Subtype.ext
    apply h.hom_ext
    · simp
    · simpa using q.property.symm
  right_inv q:=by apply Subtype.ext;simp

/-- Actual over-base isomorphisms identify sections by composition, rather
than by arbitrary matching of the underlying sets. -/
@[expose] def isoEquiv {E E' B:Scheme} (e:E ≅ E') (p:E ⟶ B) (p':E' ⟶ B)
    (h:e.hom ≫ p'=p) : {q:B ⟶ E //q ≫ p=𝟙 _} ≃ {q:B ⟶ E' //q ≫ p'=𝟙 _} where
  toFun q:=⟨q.val ≫ e.hom,by rw [Category.assoc,h];exact q.property⟩
  invFun q:=⟨q.val ≫ e.inv,by rw [Category.assoc,←h];simpa using q.property⟩
  left_inv q:=by apply Subtype.ext;simp
  right_inv q:=by apply Subtype.ext;simp
end CartesianSectionPoints318
