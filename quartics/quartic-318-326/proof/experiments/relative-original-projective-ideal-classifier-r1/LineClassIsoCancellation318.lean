module
public import LineClassPullbackHom318
public section
noncomputable section
namespace LineClassIsoCancellation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}}

/-- Pullback along an ACTUAL scheme isomorphism is injective on genuine
line-sheaf classes; both inverse identities are the original pullback laws. -/
lemma injective (e : X ≅ Y) : Function.Injective (LineClassPullbackHom318.pullback e.hom) := by
  intro a b h
  have hm := congrArg (LineClassPullbackHom318.pullback e.inv) h
  have hi (c : Class Y) : LineClassPullbackHom318.pullback e.inv
      (LineClassPullbackHom318.pullback e.hom c)=c := by
    rw [← MonoidHom.comp_apply,← LineClassPullbackHom318.composition,
      e.inv_hom_id,LineClassPullbackHom318.identity]
    rfl
  simpa only [hi] using hm
end LineClassIsoCancellation318
