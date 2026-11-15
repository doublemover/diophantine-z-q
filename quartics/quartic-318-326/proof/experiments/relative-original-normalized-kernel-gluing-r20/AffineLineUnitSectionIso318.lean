module
public import AffineLineSectionGenerator318
public import AffineQuasicoherentMapIso318
public import ModuleTopExt318
public section
noncomputable section
namespace AffineLineUnitSectionIso318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
universe u
variable (A : CommRingCat.{u}) (L : Line (Spec A))
  (s : OriginalLineAffineModel318.sections A L)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma section_map (a : A) :
    (moduleSpecΓFunctor.map (ModuleGlobalSections318.ofTop L.object s))
      ((Scheme.ΓSpecIso A).inv a)=a • s := by
  rw [ModuleGlobalSections318.ofTop_apply]
  simp only [show (homOfLE (show (⊤:(Spec A).Opens)≤⊤ from le_top)).op=𝟙 _ from rfl,
    Functor.map_id,ConcreteCategory.id_apply]
  rfl

lemma sections_bijective_iff :
    Function.Bijective (moduleSpecΓFunctor.map (ModuleGlobalSections318.ofTop L.object s)) ↔
      Function.Bijective (fun a : A => a • s) := by
  have he : (moduleSpecΓFunctor.map (ModuleGlobalSections318.ofTop L.object s)) ∘
      (Scheme.ΓSpecIso A).inv = (fun a : A => a • s) := funext (section_map A L s)
  rw [←he]
  constructor
  · intro h
    exact h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv)
  · intro h
    have he := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv
    constructor
    · intro x y hxy
      obtain ⟨a,rfl⟩ := he.2 x
      obtain ⟨b,rfl⟩ := he.2 y
      exact congrArg (Scheme.ΓSpecIso A).inv (h.1 hxy)
    · intro y
      obtain ⟨a,ha⟩ := h.2 y
      exact ⟨(Scheme.ΓSpecIso A).inv a,ha⟩

/-- Exact map-level criterion: empty whole evaluation ideal quotient is
not merely nonvanishing; it makes the ORIGINAL O-to-line map invertible. -/
lemma iff_ideal_top : IsIso (ModuleGlobalSections318.ofTop L.object s) ↔
    OriginalAffineSectionZero318.ideal A L s=⊤ := by
  constructor
  · intro h
    letI := h
    exact (AffineLineSectionGenerator318.bijective_iff A L s).mp
      ((sections_bijective_iff A L s).mp (ConcreteCategory.bijective_of_isIso
        (moduleSpecΓFunctor.map (ModuleGlobalSections318.ofTop L.object s))))
  · intro h
    have hb := (sections_bijective_iff A L s).mpr
      ((AffineLineSectionGenerator318.bijective_iff A L s).mpr h)
    letI : IsIso (moduleSpecΓFunctor.map (ModuleGlobalSections318.ofTop L.object s)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hb
    exact AffineQuasicoherentMapIso318.of_sections A _
end AffineLineUnitSectionIso318
