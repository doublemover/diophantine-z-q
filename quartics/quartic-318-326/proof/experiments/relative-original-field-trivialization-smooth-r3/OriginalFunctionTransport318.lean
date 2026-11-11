module
public import AffineChartPullbackScalars318
public section
noncomputable section
namespace OriginalFunctionTransport318
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}}

/-- The actual regular-function pullback, normalized only by a proved
inverse-image equality of whole opens. -/
@[expose] def pullTo (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ U = V) : Γ(Y,U) →+* Γ(X,V) := (f.appLE U V h.ge).hom

@[expose] def chartScalar {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (h : j ''ᵁ ⊤ = U) : A →+* Γ(X,U) :=
  ((Scheme.ΓSpecIso A).inv ≫ (j.appIso ⊤).inv ≫
    X.presheaf.map (eqToHom h.symm).op).hom

/-- Actual whole-chart functions commute with the original scheme square.
Neither a local frame nor a comparison of abstract function fields is used. -/
lemma chart_square {A B : CommRingCat.{u}} (a : A ⟶ B) (f : X ⟶ Y)
    (j : Spec B ⟶ X) [IsOpenImmersion j] (k : Spec A ⟶ Y) [IsOpenImmersion k]
    (hs : j ≫ f = Spec.map a ≫ k) (U : Y.Opens) (V : X.Opens)
    (hk : k ''ᵁ ⊤ = U) (hj : j ''ᵁ ⊤ = V) (hp : f ⁻¹ᵁ U = V) (s : A) :
    pullTo f U V hp (chartScalar k U hk s) = chartScalar j V hj (a s) := by
  subst U
  subst V
  simpa only [pullTo,chartScalar,eqToHom_refl,op_id,Functor.map_id,
    Category.comp_id,CommRingCat.comp_apply] using
      AffineChartPullbackScalars318.affine_scalar a f j k hs hp.ge s
end OriginalFunctionTransport318
