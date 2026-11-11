module
public import ActualCartierKernelFrames318
public import ModuleBasisKernel318
public section
noncomputable section
namespace ActualCartierKernelFrameNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineQuotientKernelSections318 AffineZeroKernelRestriction318 ActualCartierKernelFrames318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (A : CommRingCat.{u}) (j : Spec A ⟶ X) [IsOpenImmersion j] (c : A)
  (z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p)
  (hc : ∀ a : A,a*c=0 → a=0)
  (V W : X.affineOpens) (hV : V≤chartOpen A j) (hWV : W≤V)

lemma equation_restrict : X.presheaf.map (homOfLE hWV).op (equation A j c V hV)=
    equation A j c W (hWV.trans hV) := by
  have he : restrictedCoefficient A j V hV ≫ X.presheaf.map (homOfLE hWV).op=
      restrictedCoefficient A j W (hWV.trans hV) := by
    rw [restrictedCoefficient,Category.assoc,← Functor.map_comp]
    rfl
  exact congrArg (fun f => f c) he

/-- The ACTUAL kernel-section frames commute with every genuine affine
restriction, retaining the original inclusion. Thus these are compatible
local sheaf data, not unrelated rank-one vector-space identifications. -/
lemma frame_restrict (a : Γ(X,V.1)) :
    (ActualClosedIdealModule318.object p).presheaf.map (homOfLE hWV).op
      (frame p A j c z hs hc V hV a)=
    frame p A j c z hs hc W (hWV.trans hV) (X.presheaf.map (homOfLE hWV).op a) := by
  apply ModuleBasisKernel318.inclusion_injective (ActualClosedIdealModule318.structure p) W.1
  have hn := congrArg (fun k => k (frame p A j c z hs hc V hV a))
    ((ActualClosedIdealModule318.inclusion p).val.naturality (homOfLE hWV).op)
  change (ActualClosedIdealModule318.inclusion p).app W.1
    ((ActualClosedIdealModule318.object p).presheaf.map (homOfLE hWV).op
      (frame p A j c z hs hc V hV a)) =
    (ActualClosedIdealModule318.inclusion p).app W.1
      (frame p A j c z hs hc W (hWV.trans hV) (X.presheaf.map (homOfLE hWV).op a))
  calc
    _ = X.presheaf.map (homOfLE hWV).op
        ((ActualClosedIdealModule318.inclusion p).app V.1 (frame p A j c z hs hc V hV a)) := hn
    _ = X.presheaf.map (homOfLE hWV).op a * equation A j c W (hWV.trans hV) := by
      rw [frame_inclusion,map_mul,equation_restrict A j c V W hV hWV]
    _ = _ := (frame_inclusion p A j c z hs hc W (hWV.trans hV) _).symm
end ActualCartierKernelFrameNaturality318
