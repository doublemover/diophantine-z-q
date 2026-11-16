module
public import ClutchedModuleFrames318
public section
noncomputable section
namespace OpenClutchedLine318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (U V:X.Opens)
@[expose] def leftInclusion:(U⊓V: X.Opens).toScheme⟶U.toScheme:=X.homOfLE inf_le_left
@[expose] def rightInclusion:(U⊓V: X.Opens).toScheme⟶V.toScheme:=X.homOfLE inf_le_right
instance leftOpen:IsOpenImmersion (leftInclusion U V):=inferInstanceAs (IsOpenImmersion (X.homOfLE inf_le_left))
instance rightOpen:IsOpenImmersion (rightInclusion U V):=inferInstanceAs (IsOpenImmersion (X.homOfLE inf_le_right))
lemma square:rightInclusion U V≫V.ι=leftInclusion U V≫U.ι:=by
  simp only [leftInclusion,rightInclusion,Scheme.homOfLE_ι]
lemma left_range:U.ι⁻¹ᵁV.ι.opensRange=(leftInclusion U V).opensRange:=by
  simp only [leftInclusion,Scheme.opensRange_homOfLE,Scheme.Opens.opensRange_ι,
    Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]
lemma right_range:V.ι⁻¹ᵁU.ι.opensRange=(rightInclusion U V).opensRange:=by
  simp only [rightInclusion,Scheme.opensRange_homOfLE,Scheme.Opens.opensRange_ι,
    Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,inf_top_eq]
@[expose] def transition (a:Γ(X,U⊓V)ˣ):Γ((U⊓V: X.Opens).toScheme,⊤):=
  (U⊓V: X.Opens).topIso.inv a.val
lemma transition_unit (a:Γ(X,U⊓V)ˣ):IsUnit (transition U V a):=
  a.isUnit.map (U⊓V: X.Opens).topIso.inv.hom
/-- Actual O-module sheaf with relation left coefficient = transition times
right coefficient on the literal entire overlap. -/
@[expose] def line (a:Γ(X,U⊓V)ˣ):X.Modules:=
  ClutchedModule318.sheaf U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a)
@[expose] def firstFrame (a:Γ(X,U⊓V)ˣ):
    (line U V a).restrict U.ι≅ClutchedModule318.unit U.toScheme:=
  ClutchedModuleFrames318.firstFrame U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) (transition_unit U V a) (right_range U V)
@[expose] def secondFrame (a:Γ(X,U⊓V)ˣ):
    (line U V a).restrict V.ι≅ClutchedModule318.unit V.toScheme:=
  ClutchedModuleFrames318.secondFrame U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) (left_range U V)
lemma frames_cover (h:U⊔V=⊤) (x:X):
    (∃y,U.ι y=x)∨(∃y,V.ι y=x):=by
  have hx:x∈U⊔V:=by rw [h];trivial
  rcases hx with hx|hx
  · exact Or.inl ⟨⟨x,hx⟩,rfl⟩
  · exact Or.inr ⟨⟨x,hx⟩,rfl⟩
end OpenClutchedLine318
