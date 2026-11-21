module
public import IntrinsicAffineSectionEquiv318
public import IntrinsicChartNaturality318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite

namespace SelectedIntrinsicGlobalToAffine318

universe u
variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
variable (p : Y ⟶ Spec (CommRingCat.of R))
variable (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))

abbrev sectionArrow : op (⊤ : Y.Opens) ⟶ op (j ''ᵁ ⊤) :=
  (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op

/-- Pull back the original global scalar to the actual affine ring. -/
@[expose] def restrictRegular : Γ(Y,⊤) →+* S :=
  (j.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom).hom

abbrev chartScalar (a : S) : Γ(Y,j ''ᵁ ⊤) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)

theorem restrictRegular_norm (a : Γ(Y,⊤)) :
    Y.presheaf.map (sectionArrow j) a = chartScalar j (restrictRegular j a) := by
  have hh : Y.presheaf.map (sectionArrow j) ≫ (j.appIso ⊤).hom = j.appTop := by
    rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE]
    change j.appTop ≫ (Spec (CommRingCat.of S)).presheaf.map (𝟙 (op ⊤)) = j.appTop
    have hid := (Spec (CommRingCat.of S)).presheaf.map_id
      (op (⊤ : (Spec (CommRingCat.of S)).Opens))
    exact (congrArg (fun k => j.appTop ≫ k) hid).trans (Category.comp_id _)
  apply (ConcreteCategory.bijective_of_isIso ((j.appIso ⊤).hom)).injective
  change (j.appIso ⊤).hom (Y.presheaf.map (sectionArrow j) a) =
    (j.appIso ⊤).hom ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of S)).hom (j.appTop a))))
  rw [Iso.inv_hom_id_apply,Iso.hom_inv_id_apply]
  exact congrArg (fun f => f a) hh

/-- Restrict the actual global intrinsic differential to the actual open
immersion, then identify that restriction with its ordinary Kähler element. -/
@[expose] def restrict :
    Γ(FamilyIntrinsicDifferentials318.omega p,⊤) →+ KaehlerDifferential R S :=
  (IntrinsicAffineSectionEquiv318.equivalence j p h).symm.toAddMonoidHom.comp
    ((FamilyIntrinsicDifferentials318.omega p).presheaf.map (sectionArrow j)).hom

theorem restrict_norm (ω : Γ(FamilyIntrinsicDifferentials318.omega p,⊤)) :
    IntrinsicChartSections318.sectionMap j p h (restrict j p h ω) =
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map (sectionArrow j) ω := by
  rw [← IntrinsicAffineSectionEquiv318.apply_eq]
  exact (IntrinsicAffineSectionEquiv318.equivalence j p h).apply_symm_apply _

/-- Ordinary differentiation on the same affine chart is literally
restriction of the global intrinsic derivation. -/
theorem restrict_D (a : Γ(Y,⊤)) :
    restrict j p h ((FamilyIntrinsicDifferentials318.D p).d a) =
      KaehlerDifferential.D R S (restrictRegular j a) := by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p h).1
  let d : Γ(Y,j ''ᵁ ⊤) →+ Γ(FamilyIntrinsicDifferentials318.omega p,j ''ᵁ ⊤) :=
    (FamilyIntrinsicDifferentials318.D p).d (X := op (j ''ᵁ ⊤))
  have h₀ :
      IntrinsicChartSections318.sectionMap j p h
        (restrict j p h ((FamilyIntrinsicDifferentials318.D p).d a)) =
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map (sectionArrow j)
        ((FamilyIntrinsicDifferentials318.D p).d a) :=
    restrict_norm j p h ((FamilyIntrinsicDifferentials318.D p).d a)
  have h₁ :
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map (sectionArrow j)
        ((FamilyIntrinsicDifferentials318.D p).d a) =
      d (Y.presheaf.map (sectionArrow j) a) :=
    ((FamilyIntrinsicDifferentials318.D p).d_map (sectionArrow j) a).symm
  have h₂ : d (Y.presheaf.map (sectionArrow j) a) = d (chartScalar j (restrictRegular j a)) :=
    congrArg d (restrictRegular_norm j a)
  have h₃ :
      IntrinsicChartSections318.sectionMap j p h
        (KaehlerDifferential.D R S (restrictRegular j a)) =
      d (chartScalar j (restrictRegular j a)) :=
    IntrinsicChartSections318.section_D j p h (restrictRegular j a)
  exact h₀.trans (h₁.trans (h₂.trans h₃.symm))

theorem restrict_smul (a : Γ(Y,⊤)) (ω : Γ(FamilyIntrinsicDifferentials318.omega p,⊤)) :
    restrict j p h (a • ω) = (restrictRegular j a) • restrict j p h ω := by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p h).1
  let Q := FamilyIntrinsicDifferentials318.omega p
  calc
    _ = Q.presheaf.map (sectionArrow j) (a • ω) := restrict_norm j p h (a • ω)
    _ = Y.presheaf.map (sectionArrow j) a • Q.presheaf.map (sectionArrow j) ω :=
      Q.val.map_smul (sectionArrow j) a ω
    _ = chartScalar j (restrictRegular j a) • Q.presheaf.map (sectionArrow j) ω :=
      congrArg (fun x : Γ(Y,j ''ᵁ ⊤) => x • Q.presheaf.map (sectionArrow j) ω)
        (restrictRegular_norm j a)
    _ = chartScalar j (restrictRegular j a) •
        IntrinsicChartSections318.sectionMap j p h (restrict j p h ω) :=
      congrArg (fun x : Γ(Q,j ''ᵁ ⊤) => chartScalar j (restrictRegular j a) • x)
        (restrict_norm j p h ω).symm
    _ = _ := (IntrinsicChartSections318.section_smul j p h (restrictRegular j a)
      (restrict j p h ω)).symm

section Nested
variable {T : Type u} [CommRing T] [Algebra R T]
variable (f : S →ₐ[R] T) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
variable (hT : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) ≫ p =
  Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- The compact section restricted directly to the actual smaller chart
equals the universal differential image of its original chart restriction. -/
theorem restrict_nested (ω : Γ(FamilyIntrinsicDifferentials318.omega p,⊤)) :
    restrict (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) p hT ω =
      AlgHomDifferential318.map f (restrict j p h ω) := by
  let k := Spec.map (CommRingCat.ofHom f.toRingHom)
  let A := (FamilyIntrinsicDifferentials318.omega p).presheaf
  let i := (homOfLE (OpenChartSections318.imageLE k j)).op
  have hi : sectionArrow (k ≫ j) = sectionArrow j ≫ i := Subsingleton.elim _ _
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective (k ≫ j) p hT).1
  calc
    _ = A.map (sectionArrow (k ≫ j)) ω := restrict_norm (k ≫ j) p hT ω
    _ = A.map i (A.map (sectionArrow j) ω) := by
      rw [hi]
      exact CategoryTheory.Functor.map_comp_apply _ _ _ _
    _ = A.map i (IntrinsicChartSections318.sectionMap j p h (restrict j p h ω)) := by
      rw [restrict_norm]
    _ = _ := IntrinsicChartNaturality318.section_restrict f j p h hT (restrict j p h ω)

end Nested
end SelectedIntrinsicGlobalToAffine318

#print axioms SelectedIntrinsicGlobalToAffine318.restrict_D
#print axioms SelectedIntrinsicGlobalToAffine318.restrict_nested
