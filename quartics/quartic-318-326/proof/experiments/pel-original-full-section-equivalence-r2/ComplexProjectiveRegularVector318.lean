module
public import ComplexProjectiveBase318
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public section
noncomputable section
namespace ComplexProjectiveRegularVector318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
variable {ι : Type*} {X : Scheme}
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra
abbrev ComplexPoint := Spec (CommRingCat.of ℂ)

/-- The genuine structural complex scalar map on global sections. -/
@[expose] def scalar (π : X ⟶ ComplexPoint) : ℂ →+* Γ(X,⊤) :=
  π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

@[expose] def evaluation (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤)) :
    MvPolynomial ι ℂ →+* Γ(X,⊤) := MvPolynomial.eval₂Hom (scalar π) u

lemma irrelevant_maps_top (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) :
    (HomogeneousIdeal.irrelevant (grading (ι := ι))).toIdeal.map (evaluation π u)=⊤ := by
  apply top_le_iff.mp
  rw [←hu]
  apply Ideal.span_le.mpr
  rintro a ⟨i,rfl⟩
  have hi : MvPolynomial.X i ∈ (HomogeneousIdeal.irrelevant (grading (ι := ι))).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem grading (by norm_num : 0<(1:ℕ))
      (MvPolynomial.isHomogeneous_X ℂ i)
  simpa only [evaluation,MvPolynomial.eval₂Hom_X'] using
    Ideal.mem_map_of_mem (evaluation π u) hi

/-- A basepoint-free vector of ACTUAL regular sections gives a genuine
scheme morphism to the SAME complex polynomial Proj. The unit-ideal
condition is algebraic on the entire scheme, not only on selected points. -/
@[expose] def morphism (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) : X ⟶ Proj (grading (ι := ι)) :=
  Proj.fromOfGlobalSections grading (evaluation π u) (irrelevant_maps_top π u hu)

lemma homogeneous_preimage (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) (p : MvPolynomial ι ℂ) (n : ℕ)
    (hn : 0<n) (hp : p.IsHomogeneous n) :
    morphism π u hu ⁻¹ᵁ Proj.basicOpen grading p=X.basicOpen (evaluation π u p) :=
  Proj.fromOfGlobalSections_preimage_basicOpen grading (evaluation π u)
    (irrelevant_maps_top π u hu) hn hp

/-- Exact original complex-base square for the actual Proj morphism. -/
@[reassoc] theorem over_complex (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (hu : Ideal.span (Set.range u)=⊤) :
    morphism π u hu ≫ ComplexProjectiveBase318.structureMap=π := by
  rw [ComplexProjectiveBase318.structureMap,←Category.assoc,morphism,
    Proj.fromOfGlobalSections_toSpecZero]
  have hc : ((evaluation π u).comp (algebraMap
      (ComplexProjectiveBase318.DegreeZero (ι := ι)) (MvPolynomial ι ℂ))).comp
      ComplexProjectiveBase318.constants.toRingHom=scalar π := by
    ext c
    change evaluation π u (MvPolynomial.C c)=scalar π c
    exact MvPolynomial.eval₂Hom_C _ _ _
  change (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ((evaluation π u).comp _))) ≫
    Spec.map (CommRingCat.ofHom ComplexProjectiveBase318.constants.toRingHom)=π
  rw [Category.assoc,←Spec.map_comp,←CommRingCat.ofHom_comp,hc]
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ π.appTop)=π
  rw [Spec.map_comp,←Category.assoc,←Scheme.toSpecΓ_naturality,Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv,Category.comp_id]

/-- The actual complex coordinate vector obtained by evaluating global
sections at a specified C-valued scheme point. -/
@[expose] def pointVector (u : ι → Γ(X,⊤)) (p : ComplexPoint ⟶ X) : ι → ℂ :=
  fun i => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (u i))

lemma point_scalar (π : X ⟶ ComplexPoint) (p : ComplexPoint ⟶ X)
    (hp : p ≫ π=𝟙 _) (c : ℂ) :
    p.appTop (scalar π c)=ComplexProjectiveSchemePoint318.scalar c := by
  have h : π.appTop ≫ p.appTop=𝟙 _ := by rw [←Scheme.Hom.comp_appTop,hp]; rfl
  exact congrArg (fun f : Γ(ComplexPoint,⊤) ⟶ Γ(ComplexPoint,⊤) =>
    f ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) h

lemma point_evaluation (π : X ⟶ ComplexPoint) (u : ι → Γ(X,⊤))
    (p : ComplexPoint ⟶ X) (hp : p ≫ π=𝟙 _) :
    p.appTop.hom.comp (evaluation π u)=
      ComplexProjectiveSchemePoint318.evaluation (pointVector u p) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    exact point_scalar π p hp c
  · intro i
    change p.appTop (u i)=(Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (u i)))
    exact (ConcreteCategory.congr_hom
      (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of ℂ))) _).symm
end ComplexProjectiveRegularVector318
