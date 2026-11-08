module
public import IntegralLocalFrameDetection318
public section
noncomputable section
namespace IntegralChartSectionDetection318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- An actual frame makes whole-chart sections detectable on any nonempty
ambient open inside the chart, without requiring the sections global. -/
theorem restrict_injective {X Y:Scheme.{u}} [IsIntegral X] (M:X.Modules)
    (j:Y⟶X) [IsOpenImmersion j] (e:M.restrict j≅SheafOfModules.unit Y.ringCatSheaf)
    (W:X.Opens) [hW:Nonempty W] (hle:W≤j ''ᵁ ⊤):
    Function.Injective (M.presheaf.map (homOfLE hle).op):=by
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
  have hi:=LocalFrameSectionDetection318.image_injective M j e V
  have aux (W' : X.Opens) (he' : j ''ᵁ V = W') (hle' : W' ≤ j ''ᵁ ⊤) :
      Function.Injective (M.presheaf.map (homOfLE hle').op) := by
    subst W'
    exact hi
  exact aux W he hle
/-- Pure sheaf restriction composition, with the module kept abstract. -/
theorem global_local_eq {X:Scheme.{u}} (M:X.Modules) {U W:X.Opens} (hWU:W≤U)
    (hinj:Function.Injective (M.presheaf.map (homOfLE hWU).op))
    (s:Γ(M,⊤)) (t:Γ(M,U))
    (h:M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op s=
       M.presheaf.map (homOfLE hWU).op t):
    M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op s=t:=by
  apply hinj
  exact (CategoryTheory.Functor.map_comp_apply M.presheaf
    (homOfLE (show U≤⊤ from le_top)).op (homOfLE hWU).op s).symm.trans h
end IntegralChartSectionDetection318
