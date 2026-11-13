module
public import SchemeMonoPullbackCancellationRebuild318
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace SchemeOpenPullbackPointsRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {W X Y Z : Scheme.{u}} {a : W ⟶ X} {b : W ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z} [IsOpenImmersion g]
/-- Topological point lifting is used ONLY with an actual open immersion.
No pointwise fiber-product claim for arbitrary scheme maps is assumed. -/
lemma pair (H : IsPullback a b f g) (x : X) (y : Y) (h : f x=g y) :
    ∃ w : W,a w=x ∧ b w=y := by
  have hx : x ∈ Set.range (pullback.fst f g) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact ⟨y,h.symm⟩
  obtain ⟨z,hz⟩ := hx
  let w := H.isoPullback.inv z
  have ha : a w=x := by
    calc
      a w=(pullback.fst f g) z :=
        congrArg (fun k => k z) H.isoPullback_inv_fst
      _=x := hz
  have hb : b w=y := by
    apply g.isOpenEmbedding.injective
    calc
      g (b w)=f (a w) := (congrArg (fun k => k w) H.w).symm
      _=g y := by rw [ha,h]
  exact ⟨w,ha,hb⟩
end SchemeOpenPullbackPointsRebuild318
