module
public import IntegralLocalFrameDetection318
public import FifthGlobalDifferential318
public section
noncomputable section
namespace ContactGlobalSectionDetection318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c:Fin 4→ℚˣ)
abbrev M:=ContactIntrinsicDifferentials318.omega c
abbrev common: (ContactGlobalSmooth318.Model c).Opens:=ContactOverlapIntrinsic318.embedding c ''ᵁ ⊤
instance common_nonempty:Nonempty (common c):=by
  letI:=ContactKummerOpenDomain318.open_domain c
  let x:Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)):=Classical.choice inferInstance
  exact ⟨⟨ContactOverlapIntrinsic318.embedding c x,x,trivial,rfl⟩⟩
lemma common_le (i:Option (Fin 4)):common c≤ContactGlobalBicanonical318.opens c i:=by
  cases i
  · exact ContactInfinityTensorRestrictions318.infinityLE c
  · exact ContactFiniteTensorRestrictions318.branchLE c _
/-- Global intrinsic differential sections on the actual source are detected
on its entire nonempty unbranched chart. This uses the five genuine local
frames and ambient integrality, not an assumed global differential frame. -/
theorem restrict_injective:Function.Injective ((M c).presheaf.map
    (homOfLE (show common c≤⊤ from le_top)).op):=by
  letI:IsIntegral (ContactGlobalSmooth318.Model c):=
    (ContactGlobalSmooth318.smooth_proper_integral_model c).2.2
  intro s t h
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨(M c).presheaf,(M c).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat (ContactGlobalSmooth318.Model c))
    (ContactGlobalBicanonical318.opens c) ⊤ (fun _=>homOfLE le_top)
    (ContactGlobalBicanonical318.cover c) s t
  intro i
  exact IntegralLocalFrameDetection318.chart_eq (M c) (ContactIntrinsicFrames318.embedding c i)
    (ContactIntrinsicFrames318.localFrame c i) (common c) (common_le c i) s t h
end ContactGlobalSectionDetection318
