module
public import OriginalTwoLevelHodgeLattice318
public import Mathlib.NumberTheory.NumberField.Basic
public section
noncomputable section

namespace OriginalHodgeIdealFromFull33_318
open OriginalTwoLevelHodgeLattice318 NumberField
open scoped nonZeroDivisors
variable {E : Type*} [Field E] [NumberField E]

/-- From true generators of the two original level Hodge modules, expressed
in the SAME generic wedge, and their equality only on the level-33
overlap. Produces the nonzero global ideal and its genuine 3,11 opens. -/
theorem build (S3 S11 S33 : Type*) [CommRing S3] [CommRing S11] [CommRing S33]
    [Algebra (𝓞 E) S3] [Algebra (𝓞 E) S11] [Algebra (𝓞 E) S33]
    [Algebra S3 E] [Algebra S11 E] [Algebra S33 E]
    [IsScalarTower (𝓞 E) S3 E] [IsScalarTower (𝓞 E) S11 E] [IsScalarTower (𝓞 E) S33 E]
    [IsLocalization.Away (3:𝓞 E) S3] [IsLocalization.Away (11:𝓞 E) S11]
    [IsLocalization.Away (33:𝓞 E) S33]
    (G J : Finset E) (nonzero : ∃ g∈G,g≠0)
    (same : Submodule.span S33 (G:Set E)=Submodule.span S33 (J:Set E)) :
    ∃ I : FractionalIdeal (𝓞 E)⁰ E,I≠0 ∧
      (I:Submodule (𝓞 E) E)=(Submodule.span S3 (G:Set E)).restrictScalars (𝓞 E) ⊓
        (Submodule.span S11 (J:Set E)).restrictScalars (𝓞 E) ∧
      Submodule.span S3 (I:Set E)=Submodule.span S3 (G:Set E) ∧
      Submodule.span S11 (I:Set E)=Submodule.span S11 (J:Set E) := by
  have hc : IsCoprime (3:𝓞 E) 11 := ⟨4,-1,by ring⟩
  have overlap : sat ((3:𝓞 E)*11) (Submodule.span (𝓞 E) (G:Set E))=
      sat ((3:𝓞 E)*11) (Submodule.span (𝓞 E) (J:Set E)) := by
    rw [show (3:𝓞 E)*11=33 by norm_num,on_open S33,on_open S33,same]
  obtain ⟨I,cut,three,eleven⟩ := glue (3:𝓞 E) 11 hc G J overlap
  have nz : I≠0 := by
    intro h
    have iz : (I:Submodule (𝓞 E) E)=⊥ := FractionalIdeal.coeToSubmodule_eq_bot.mpr h
    have r3 : algebraMap (𝓞 E) E 3≠0 := by norm_num
    rw [iz,sat_bot _ r3] at three
    obtain ⟨g,hg,gn⟩ := nonzero
    have hmem : g∈sat (3:𝓞 E) (Submodule.span (𝓞 E) (G:Set E)) :=
      le_sat _ _ (Submodule.subset_span hg)
    rw [←three] at hmem
    exact gn hmem
  rw [on_open S3,on_open S11] at cut
  have spanI : Submodule.span (𝓞 E) (I:Set E)=(I:Submodule (𝓞 E) E) :=
    (I:Submodule (𝓞 E) E).span_eq
  refine ⟨I,nz,cut,?_,?_⟩
  · have h := on_open S3 (3:𝓞 E) (I:Set E)
    rw [spanI] at h
    rw [h,on_open S3] at three
    ext x
    exact SetLike.ext_iff.mp three x
  · have h := on_open S11 (11:𝓞 E) (I:Set E)
    rw [spanI] at h
    rw [h,on_open S11] at eleven
    ext x
    exact SetLike.ext_iff.mp eleven x

end OriginalHodgeIdealFromFull33_318
