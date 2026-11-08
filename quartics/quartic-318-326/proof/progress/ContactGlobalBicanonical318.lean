module
public import ContactInfinityTensorRestrictions318
public import ContactBicanonicalSheaf318
public section
noncomputable section
namespace ContactGlobalBicanonical318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
abbrev tensor := ContactDirectTensorSections318.tensor c

/-- The direct-coordinate construction uses exactly the genuine intrinsic
bicanonical sheaf from the prior tensor foundation, not another line bundle. -/
theorem tensor_eq : tensor c=ContactBicanonicalSheaf318.bicanonical c := rfl

@[expose] def opens (i : Option (Fin 4)) : (ContactGlobalSmooth318.Model c).Opens :=
  ContactIntrinsicFrames318.embedding c i ''ᵁ ⊤

@[expose] def localQ0 : (i : Option (Fin 4)) → Γ(tensor c,opens c i)
  | some i => ContactDirectTensorSections318.branchQ0 c i
  | none => ContactDirectTensorSections318.infinityQ0 c
@[expose] def localQ1 : (i : Option (Fin 4)) → Γ(tensor c,opens c i)
  | some i => ContactDirectTensorSections318.branchQ1 c i
  | none => ContactDirectTensorSections318.infinityQ1 c

theorem cover : ⊤ ≤ iSup (opens c) := by
  intro x _
  rcases ContactIntrinsicFrames318.frames_cover c x with ⟨i,q,hq⟩|⟨q,hq⟩
  · exact Opens.mem_iSup.mpr ⟨some i,q,trivial,hq⟩
  · exact Opens.mem_iSup.mpr ⟨none,q,trivial,hq⟩

/-- Full-intersection compatibility for the five actual chart sections. -/
theorem q0_compatible : TopCat.Presheaf.IsCompatible (tensor c).presheaf (opens c) (localQ0 c) := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      exact LocalSectionCompatibility318.symm _ _ _ _ _
        (ContactInfinityTensorRestrictions318.q0_branch_infinity c j)
  | some i =>
    cases j with
    | none => exact ContactInfinityTensorRestrictions318.q0_branch_infinity c i
    | some j =>
      by_cases hij : i=j
      · subst j; rfl
      · exact ContactFiniteTensorRestrictions318.q0_finite_pair c i j hij

/-- A genuine global section of Omega tensor Omega on the complete actual
contact normalization, glued from the universal-coordinate expressions. -/
@[expose] def q0 : Γ(tensor c,⊤) :=
  ModuleGlobalSections318.gluedTop (tensor c) (opens c) (cover c) (localQ0 c) (q0_compatible c)

theorem q0_restrict (i : Option (Fin 4)) :
    (tensor c).presheaf.map (homOfLE (show opens c i ≤ ⊤ from le_top)).op (q0 c)=localQ0 c i :=
  ModuleGlobalSections318.gluedTop_restrict (tensor c) (opens c) (cover c) (localQ0 c) (q0_compatible c) i
/-- Full-intersection compatibility for the five actual chart sections. -/
theorem q1_compatible : TopCat.Presheaf.IsCompatible (tensor c).presheaf (opens c) (localQ1 c) := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      exact LocalSectionCompatibility318.symm _ _ _ _ _
        (ContactInfinityTensorRestrictions318.q1_branch_infinity c j)
  | some i =>
    cases j with
    | none => exact ContactInfinityTensorRestrictions318.q1_branch_infinity c i
    | some j =>
      by_cases hij : i=j
      · subst j; rfl
      · exact ContactFiniteTensorRestrictions318.q1_finite_pair c i j hij

/-- A genuine global section of Omega tensor Omega on the complete actual
contact normalization, glued from the universal-coordinate expressions. -/
@[expose] def q1 : Γ(tensor c,⊤) :=
  ModuleGlobalSections318.gluedTop (tensor c) (opens c) (cover c) (localQ1 c) (q1_compatible c)

theorem q1_restrict (i : Option (Fin 4)) :
    (tensor c).presheaf.map (homOfLE (show opens c i ≤ ⊤ from le_top)).op (q1 c)=localQ1 c i :=
  ModuleGlobalSections318.gluedTop_restrict (tensor c) (opens c) (cover c) (localQ1 c) (q1_compatible c) i
end ContactGlobalBicanonical318
