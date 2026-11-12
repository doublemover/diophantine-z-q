module
public import ActualTwoDescentOriginalArbitraryLiftAllOpenHom318
public section
noncomputable section
namespace ActualTwoDescentOriginalArbitraryLiftSectionBijection318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleSheaf318 ActualTwoDescentOriginalDoublePoleRationalEmbedding318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318 ActualTwoDescentOriginalFourGenericLatticeAction318
open ActualTwoDescentSemilinearLatticeLiftGroup318
variable {K : Type*} [Field K] [CharZero K]
open ActualTwoDescentOriginalArbitraryLiftOpenAction318 ActualTwoDescentOriginalArbitraryLiftSectionAction318
open ActualTwoDescentOriginalArbitraryLiftAllOpenHom318
lemma nonempty_bijective (n : K) (hn : n≠0) (a : Lift (data n hn))
    (U : (originalCubicScheme n).Opens) [Nonempty U] :
    Function.Bijective (sectionMap n hn a U) := by
  constructor
  · intro s t hst
    apply value_injective n U
    apply (operator (data n hn) a).injective
    have h := congrArg (value n (inverseOpen n hn a U)) hst
    simpa only [value_formula] using h
  · intro t
    obtain ⟨f,hf⟩ := (operator (data n hn) a).surjective (value n (inverseOpen n hn a U) t)
    have hall : ∀ y : U,f∈pointImage n y.val := by
      intro y
      let x := (translation n hn a).inv y.val
      have hx : (translation n hn a).hom x=y.val := by
        have hh := congrArg (fun g : originalCubicScheme n ⟶ originalCubicScheme n => g y.val)
          (translation n hn a).inv_hom_id
        exact hh
      have hxU : x∈inverseOpen n hn a U := by change (translation n hn a).hom x∈U; rw [hx]; exact y.property
      have ht := (section_iff n (inverseOpen n hn a U) _).mp
        (show ∃ s : Γ(sheaf n,inverseOpen n hn a U),
          value n (inverseOpen n hn a U) s=value n (inverseOpen n hn a U) t from ⟨t,rfl⟩) ⟨x,hxU⟩
      have hh := (preserves (data n hn) a x f).mpr (hf.symm ▸ ht)
      change f∈pointImage n ((translation n hn a).hom x) at hh
      simpa only [hx] using hh
    obtain ⟨s,hs,_⟩ := unique_section n U f hall
    refine ⟨s,?_⟩
    apply value_injective n (inverseOpen n hn a U)
    rw [value_formula,hs,hf]
lemma all_bijective (n : K) (hn : n≠0) (a : Lift (data n hn)) (U : (originalCubicScheme n).Opens) :
    Function.Bijective (map n hn a U) := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    have he : map n hn a U=sectionMap n hn a U := funext (map_nonempty n hn a U)
    rw [he]
    exact nonempty_bijective n hn a U
  · haveI := ActualTwoDescentEmptyModuleSections318.empty_sections_subsingleton (sheaf n) U hU
    haveI := ActualTwoDescentEmptyModuleSections318.empty_sections_subsingleton (pushed n hn a) U hU
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun t => ⟨0,Subsingleton.elim _ _⟩⟩
instance hom_isIso (n : K) (hn : n≠0) (a : Lift (data n hn)) : IsIso (hom n hn a) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact all_bijective n hn a U

end ActualTwoDescentOriginalArbitraryLiftSectionBijection318
