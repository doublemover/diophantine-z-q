module
public import ContactOriginalBaseUnitAction318
public section
noncomputable section
namespace ContactOriginalStabilizerUnitPresheaf318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L L
/-- The literal base-units functor, with restriction along the actual
scheme appTop. This is the relative multiplicative-group functor. -/
@[expose] def unitsPresheaf : (Over (Spec R))ᵒᵖ ⥤ Type 1 where
  obj T := Γ(T.unop.left,⊤)ˣ
  map f := Units.map f.unop.left.appTop.hom.toMonoidHom
  map_id T := by
    funext a
    apply Units.ext
    change (𝟙 T.unop.left).appTop a.val=a.val
    simp only [Scheme.Hom.id_appTop,ConcreteCategory.id_apply]
  map_comp f g := by
    funext a
    apply Units.ext
    change (g.unop.left ≫ f.unop.left).appTop a.val=
      g.unop.left.appTop (f.unop.left.appTop a.val)
    exact ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop g.unop.left f.unop.left) a.val
@[expose] def pointEquiv (T : Over (Spec R)) :
    (T ⟶ Over.mk q) ≃ Points R c L L T.hom where
  toFun z := ⟨z.left,z.w⟩
  invFun z := Over.homMk z.val z.property
  left_inv z := by apply Over.OverMorphism.ext; rfl
  right_inv z := by apply Subtype.ext; rfl
/-- The SAME actual automorphism parameter represents base units on
ALL whole coefficient schemes. This removes the earlier base-Gm gap;
it does not manufacture a represented quotient of the Isom parameter. -/
@[expose] def representation : yoneda.obj (Over.mk q) ≅ unitsPresheaf R :=
  NatIso.ofComponents (fun T => Equiv.toIso
    ((pointEquiv R c L T.unop).trans
      (ContactOriginalBaseUnitAutomorphisms318.equivalence R c L T.unop.hom)))
    (by
      intro T U f
      funext z
      exact ContactOriginalBaseUnitNaturality318.natural R c L T.unop.hom U.unop.hom
        f.unop.left f.unop.w (pointEquiv R c L T.unop z))
end ContactOriginalStabilizerUnitPresheaf318
