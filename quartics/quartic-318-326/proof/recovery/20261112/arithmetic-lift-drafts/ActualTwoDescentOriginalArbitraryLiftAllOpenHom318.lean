module
public import ActualTwoDescentOriginalArbitraryLiftSectionAction318
public section
noncomputable section
namespace ActualTwoDescentOriginalArbitraryLiftAllOpenHom318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleSheaf318 ActualTwoDescentOriginalDoublePoleRationalEmbedding318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalFourGenericLatticeAction318
open ActualTwoDescentSemilinearLatticeLiftGroup318
variable {K : Type*} [Field K] [CharZero K]
open ActualTwoDescentOriginalArbitraryLiftOpenAction318 ActualTwoDescentOriginalArbitraryLiftSectionAction318
abbrev pushed (n : K) (hn : n≠0) (a : Lift (data n hn)) :=
  (Scheme.Modules.pushforward (translation n hn a).hom).obj (sheaf n)
def map (n : K) (hn : n≠0) (a : Lift (data n hn)) (U : (originalCubicScheme n).Opens)
    (s : Γ(sheaf n,U)) : Γ(pushed n hn a,U) := by
  classical
  exact if h : Nonempty U then by letI := h; exact sectionMap n hn a U s else 0
lemma map_nonempty (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)) :
    map n hn a U s=sectionMap n hn a U s := by
  classical
  simp only [map,dif_pos (inferInstance : Nonempty U)]
lemma map_additive (n : K) (hn : n≠0) (a : Lift (data n hn)) (U : (originalCubicScheme n).Opens)
    (s t : Γ(sheaf n,U)) : map n hn a U (s+t)=map n hn a U s+map n hn a U t := by
  classical
  by_cases h : Nonempty U
  · letI := h
    simp only [map_nonempty,additive]
  · simp only [map,dif_neg h,zero_add]
lemma map_scalar (n : K) (hn : n≠0) (a : Lift (data n hn)) (U : (originalCubicScheme n).Opens)
    (c : Γ(originalCubicScheme n,U)) (s : Γ(sheaf n,U)) :
    map n hn a U (c • s)=c • map n hn a U s := by
  classical
  by_cases h : Nonempty U
  · letI := h
    rw [map_nonempty,map_nonempty]
    exact scalar_action n hn a U c s
  · simp only [map,dif_neg h,smul_zero]
def linear (n : K) (hn : n≠0) (a : Lift (data n hn)) (U : (originalCubicScheme n).Opens) :
    Γ(sheaf n,U) →ₗ[Γ(originalCubicScheme n,U)] Γ(pushed n hn a,U) where
  toFun := map n hn a U
  map_add' := map_additive n hn a U
  map_smul' := map_scalar n hn a U
lemma naturality (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U V : (originalCubicScheme n).Opens) (h : V≤U) (s : Γ(sheaf n,U)) :
    map n hn a V ((sheaf n).presheaf.map (homOfLE h).op s)=
      (pushed n hn a).presheaf.map (homOfLE h).op (map n hn a U s) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    haveI : Nonempty U := by obtain ⟨x⟩ := hV; exact ⟨⟨x.val,h x.property⟩⟩
    rw [map_nonempty,map_nonempty]
    exact ActualTwoDescentOriginalArbitraryLiftSectionAction318.naturality n hn a U V h s
  · haveI := ActualTwoDescentEmptyModuleSections318.empty_sections_subsingleton (pushed n hn a) V hV
    exact Subsingleton.elim _ _
def hom (n : K) (hn : n≠0) (a : Lift (data n hn)) : sheaf n ⟶ pushed n hn a where
  val.app U := ModuleCat.ofHom (linear n hn a U.unop)
  val.naturality f := by
    ext s
    exact naturality n hn a _ _ (leOfHom f.unop) s
lemma coefficient (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] (s : Γ(sheaf n,U)) :
    value n (inverseOpen n hn a U) ((hom n hn a).app U s)=operator (data n hn) a (value n U s) := by
  change value n (inverseOpen n hn a U) (map n hn a U s)=_
  rw [map_nonempty,value_formula]

end ActualTwoDescentOriginalArbitraryLiftAllOpenHom318
