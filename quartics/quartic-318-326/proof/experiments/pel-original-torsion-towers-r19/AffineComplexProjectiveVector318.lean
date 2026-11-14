module
public import ComplexProjectiveRegularVectorPoints318
public section
noncomputable section
namespace AffineComplexProjectiveVector318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
variable {ι A : Type*} [CommRing A] [Algebra ℂ A]
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra

@[expose] def structureMap : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
@[expose] def sections (u : ι → A) : ι → Γ(Spec (CommRingCat.of A),⊤) :=
  fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (u i)
lemma sections_span (u : ι → A) (hu : Ideal.span (Set.range u)=⊤) :
    Ideal.span (Set.range (sections u))=⊤ := by
  have he : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (Ideal.span (Set.range u))=Ideal.span (Set.range (sections u)) := by
    rw [Ideal.map_span,Set.image_range]
    rfl
  rw [←he,hu,Ideal.map_top]

/-- A literal unit-ideal vector in the ORIGINAL affine coordinate ring
produces an actual complex projective scheme morphism. -/
@[expose] def morphism (u : ι → A) (hu : Ideal.span (Set.range u)=⊤) :
    Spec (CommRingCat.of A) ⟶ Proj (grading (ι := ι)) :=
  ComplexProjectiveRegularVector318.morphism structureMap (sections u) (sections_span u hu)
@[reassoc] theorem over_complex (u : ι → A) (hu : Ideal.span (Set.range u)=⊤) :
    morphism u hu≫ComplexProjectiveBase318.structureMap=structureMap :=
  ComplexProjectiveRegularVector318.over_complex _ _ _

lemma point_vector (u : ι → A) (f : A →ₐ[ℂ] ℂ) :
    ComplexProjectiveRegularVector318.pointVector (sections u)
      (Spec.map (CommRingCat.ofHom f.toRingHom))=fun i => f (u i) := by
  funext i
  have he := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.toRingHom)) (u i)
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (u i)))=f (u i)
  rw [←he]
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of ℂ))) _

lemma point_over (f : A →ₐ[ℂ] ℂ) :
    Spec.map (CommRingCat.ofHom f.toRingHom)≫structureMap=𝟙 _ := by
  rw [structureMap,←Spec.map_comp]
  have hc : CommRingCat.ofHom (algebraMap ℂ A)≫CommRingCat.ofHom f.toRingHom=𝟙 _ := by
    ext c
    exact f.commutes c
  rw [hc,Spec.map_id]

lemma evaluation_nonzero (u : ι → A) (hu : Ideal.span (Set.range u)=⊤)
    (f : A →ₐ[ℂ] ℂ) : ∃ i, f (u i)≠0 := by
  have h := ComplexProjectiveRegularVectorPoints318.pointVector_nonzero
    (sections u) (sections_span u hu) (Spec.map (CommRingCat.ofHom f.toRingHom))
  rwa [point_vector] at h

/-- Exact point action at EVERY coefficient-preserving algebra point. -/
theorem point_action [Finite ι] (u : ι → A) (hu : Ideal.span (Set.range u)=⊤)
    (f : A →ₐ[ℂ] ℂ) :
    Spec.map (CommRingCat.ofHom f.toRingHom)≫morphism u hu=
      ComplexProjectiveSchemePoint318.point (fun i => f (u i)) (evaluation_nonzero u hu f) := by
  have h := ComplexProjectiveRegularVectorPoints318.point_action structureMap
    (sections u) (sections_span u hu) (Spec.map (CommRingCat.ofHom f.toRingHom)) (point_over f)
  simpa only [point_vector] using h

/-- Every actual affine Spec(C)-morphism over the specified algebra
structure is the Spec map of a coefficient-preserving algebra hom. -/
theorem exists_algebraPoint (p : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of A))
    (hp : p≫structureMap=𝟙 _) :
    ∃ f : A →ₐ[ℂ] ℂ, p=Spec.map (CommRingCat.ofHom f.toRingHom) := by
  obtain ⟨φ,rfl⟩ := Spec.map_surjective p
  have hc : CommRingCat.ofHom (algebraMap ℂ A)≫φ=𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_id]
    exact hp
  let f : A →ₐ[ℂ] ℂ := { φ.hom with
    commutes' := fun c => congrArg (fun h => h.hom c) hc }
  exact ⟨f,rfl⟩
end AffineComplexProjectiveVector318
