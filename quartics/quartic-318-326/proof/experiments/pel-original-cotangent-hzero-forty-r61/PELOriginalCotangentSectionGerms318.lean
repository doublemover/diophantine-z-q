module
public import PELOriginalGlobalCotangentLength318
public section
noncomputable section
namespace PELOriginalCotangentSectionGerms318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 FourRootGluedDerivativeIdeal318
abbrev X := FourRootGluedScheme318.scheme branches
abbrev omega := FourRootGlobalRelativeCotangent318.omega branches
/-- Genuine global sections of the SAME intrinsic relative cotangent sheaf. -/
abbrev H0 := Γ(omega, ⊤)
abbrev Stalk (z : zeroScheme branches) := CanonicalStalkModule318.stalk omega (into branches z)
/-- Actual global germs at every original zero-scheme point. No local
frame or arbitrary section basis enters this definition. -/
@[expose] def germs : H0 →+ ∀ z : zeroScheme branches, Stalk z where
  toFun s z := omega.presheaf.germ ⊤ (into branches z) trivial s
  map_zero' := by funext z; exact map_zero _
  map_add' s t := by funext z; exact map_add _ s t
/-- Vanishing of the actual stalk at EVERY point off the closed zero
scheme, including all nonclosed and generic points. -/
lemma outside_subsingleton (x : X) (hx : x ∉ Set.range (into branches)) :
    Subsingleton (CanonicalStalkModule318.stalk omega x) :=
  Module.length_eq_zero_iff.mp
    (FourRootCotangentWholeSupport318.outside_length_zero branches branches_injective x hx)
/-- Global sections are determined by their actual germs on the finite
zero scheme. This is only injectivity; no invalid claim that stalkwise
surjectivity implies sectionwise surjectivity is used. -/
theorem germs_injective : Function.Injective germs := by
  intro s t h
  apply TopCat.Presheaf.section_ext (⟨omega.presheaf,omega.isSheaf⟩ : TopCat.Sheaf Ab X) ⊤ s t
  intro x hx
  by_cases hi : x ∈ Set.range (into branches)
  · obtain ⟨z,rfl⟩ := hi
    exact congrFun h z
  · letI := outside_subsingleton x hi
    exact Subsingleton.elim _ _
end PELOriginalCotangentSectionGerms318
