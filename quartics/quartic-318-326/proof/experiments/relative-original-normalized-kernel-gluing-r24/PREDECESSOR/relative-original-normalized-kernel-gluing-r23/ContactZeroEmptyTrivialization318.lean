module
public import AffineCoverSectionIso318
public import ContactOriginalZeroKernelIso318
public import ContactGlobalZeroEmptyIdeals318
public section
noncomputable section
namespace ContactZeroEmptyTrivialization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactOriginalZeroKernelIso318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma isIso_iff_ideals : IsIso (ModuleGlobalSections318.ofTop L.object s) ↔
    finiteIdeal R c L s=⊤ ∧ infinityIdeal R c L s=⊤ := by
  have h := AffineCoverSectionIso318.iff_ideals L s (rings R c) (charts R c) (cover R c)
  apply h.trans
  constructor
  · intro hi
    constructor
    · have h0 := hi 0
      change SectionZeroAffineRefinement318.sectionIdeal _ (finiteInto R c) L s=⊤ at h0
      rw [←ContactZeroAffineRefinement318.finite_ideal] at h0
      exact h0
    · have h1 := hi 1
      change SectionZeroAffineRefinement318.sectionIdeal _ (infinityInto R c) L s=⊤ at h1
      rw [←ContactZeroAffineRefinement318.infinity_ideal] at h1
      exact h1
  · rintro ⟨hf,hi⟩ i
    fin_cases i
    · change SectionZeroAffineRefinement318.sectionIdeal _ (finiteInto R c) L s=⊤
      rw [←ContactZeroAffineRefinement318.finite_ideal]
      exact hf
    · change SectionZeroAffineRefinement318.sectionIdeal _ (infinityInto R c) L s=⊤
      rw [←ContactZeroAffineRefinement318.infinity_ideal]
      exact hi

/-- The exact original whole zero family is empty if and only if the
literal O-to-line morphism is an isomorphism, on every coefficient ring. -/
lemma empty_iff_isIso : IsEmpty ↑(ContactGlobalSectionZero318.scheme R c L s) ↔
    IsIso (ModuleGlobalSections318.ofTop L.object s) :=
  (ContactGlobalZeroEmptyIdeals318.iff_top R c L s).trans (isIso_iff_ideals R c L s).symm

/-- The produced trivialization has the SAME section as its literal value
at one. No arbitrary class-level choice of a line isomorphism is substituted. -/
@[expose] def frame (h : IsEmpty ↑(ContactGlobalSectionZero318.scheme R c L s)) :
    SheafOfModules.unit (curve R c).ringCatSheaf ≅ L.object := by
  letI := (empty_iff_isIso R c L s).mp h
  exact asIso (ModuleGlobalSections318.ofTop L.object s)

lemma frame_value (h : IsEmpty ↑(ContactGlobalSectionZero318.scheme R c L s)) :
    (frame R c L s h).hom.app ⊤ 1=s := ModuleTopMorphisms318.ofTop_top_one _

/-- Full two-sided equivalence between actual nowhere-zero sections and
actual line trivializations, retaining entire sheaf maps. -/
@[expose] def equivalence :
    {s : Γ(L.object,⊤) // IsEmpty ↑(ContactGlobalSectionZero318.scheme R c L s)} ≃
      (SheafOfModules.unit (curve R c).ringCatSheaf ≅ L.object) where
  toFun s := frame R c L s.val s.property
  invFun e := ⟨e.hom.app ⊤ 1,by
    apply (empty_iff_isIso R c L _).mpr
    rw [←ModuleTopExt318.eq_ofTop e.hom]
    infer_instance⟩
  left_inv s := Subtype.ext (frame_value R c L s.val s.property)
  right_inv e := by
    apply Iso.ext
    exact (ModuleTopExt318.eq_ofTop e.hom).symm
end ContactZeroEmptyTrivialization318
