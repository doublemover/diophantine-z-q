module
public import LocalFrameSectionDetection318
public section
noncomputable section
namespace IntegralLocalFrameDetection318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
/-- A nonempty common open contained in a genuinely trivialized chart detects
restriction to that whole chart on an integral ambient scheme. -/
theorem chart_eq {X Y:Scheme.{u}} [IsIntegral X] (M:X.Modules)
    (j:Y⟶X) [IsOpenImmersion j]
    (e:M.restrict j≅SheafOfModules.unit Y.ringCatSheaf)
    (W:X.Opens) [hW:Nonempty W] (hle:W≤j ''ᵁ ⊤) (s t:Γ(M,⊤))
    (h:M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op s=
      M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op t):
    M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s=
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op t:=by
  let V:=j ⁻¹ᵁ W
  have hn:Nonempty V:=by
    let x:=Classical.choice hW
    obtain ⟨y,_,hy⟩:=hle x.property
    change j y=x.val at hy
    exact ⟨⟨y,by change j y∈W;rw [hy];exact x.property⟩⟩
  letI:Nonempty V:=hn
  letI:Nonempty Y:=hn.map Subtype.val
  letI:IsIntegral Y:=isIntegral_of_isOpenImmersion j
  have he:j ''ᵁ V=W:=by
    rw [show V=j ⁻¹ᵁ W from rfl,Scheme.Hom.image_preimage_eq_opensRange_inf]
    apply inf_eq_right.mpr
    simpa only [Scheme.Hom.image_top_eq_opensRange] using hle
  exact LocalFrameSectionDetection318.chart_eq M j e V W he s t h
end IntegralLocalFrameDetection318
