module
public import CommonOpenFunctionField318
public import NormalAffineOpen318
public import ProjectiveJLine318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace SelectedGenericCompactNormalization318
universe u
variable {U V B C : Scheme.{u}} (q : U ⟶ V) (v : V ⟶ B)
  [IsFinite q] [IsOpenImmersion v] [QuasiCompact v]
variable (i : U ⟶ C) [IsOpenImmersion i] (j : C ⟶ B) [IsFinite j]
variable [IsIntegral U] [IsIntegral C]

variable (h : i ≫ j = q ≫ v)

/-- For the full finite ordinary chart and the given compact j-map, the
canonical compact comparison comes from relative normalization's universal
property, not a prior birational equivalence with a chosen component. -/
@[expose] def compare : (q ≫ v).normalization ⟶ C :=
  (q ≫ v).normalizationDesc i j h.symm

@[reassoc] theorem compare_open : (q ≫ v).toNormalization ≫ compare q v i j h = i :=
  (q ≫ v).toNormalization_normalizationDesc i j h.symm

@[reassoc] theorem compare_base : compare q v i j h ≫ j = (q ≫ v).fromNormalization :=
  (q ≫ v).normalizationDesc_comp i j h.symm

theorem compare_integral : IsIntegralHom (compare q v i j h) := by
  unfold compare
  infer_instance

theorem compare_dominant : IsDominant (compare q v i j h) := by
  have hi : IsDominant i :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace i i.isOpenEmbedding.isOpenMap⟩
  letI : IsDominant ((q ≫ v).toNormalization ≫ compare q v i j h) := by
    rw [compare_open]
    exact hi
  exact IsDominant.of_comp ((q ≫ v).toNormalization) (compare q v i j h)

/-- Only entire nonempty affine rings on the actual compact target are
used for normality, not normality of the selected ordinary open alone. -/
theorem compare_isIso (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W →
    IsIntegrallyClosed Γ(C,W)) : IsIso (compare q v i j h) := by
  letI : IsIntegralHom (compare q v i j h) := compare_integral q v i j h
  letI : IsDominant (compare q v i j h) := compare_dominant q v i j h
  letI : IsOpenImmersion ((q ≫ v).toNormalization) := by infer_instance
  letI : IsIso (DominantFunctionField318.map (compare q v i j h)) :=
    CommonOpenFunctionField318.actual_generic_iso ((q ≫ v).toNormalization) i
      (compare q v i j h) (compare_open q v i j h)
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  let W := (C.affineCover.f (C.affineCover.idx x)).opensRange
  have hx : x ∈ W := C.affineCover.covers x
  have hW : IsAffineOpen W := isAffineOpen_opensRange _
  letI : Nonempty W := ⟨⟨x,hx⟩⟩
  letI : IsIntegrallyClosed Γ(C,W) := normal W hW inferInstance
  exact ⟨W,hx,IntegralGenericIso318.restrict_isIso (compare q v i j h) W hW⟩

include i j h in
/-- The unique actual normalization conclusion over the original
projective j-line, agreeing with the originally given ordinary immersion. -/
@[expose] def compactIso (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W →
    IsIntegrallyClosed Γ(C,W)) : (q ≫ v).normalization ≅ C := by
  letI : IsIso (compare q v i j h) := compare_isIso q v i j h normal
  exact asIso (compare q v i j h)

theorem compactIso_open (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W →
    IsIntegrallyClosed Γ(C,W)) :
    (q ≫ v).toNormalization ≫ (compactIso q v i j h normal).hom = i :=
  compare_open q v i j h

theorem compactIso_base (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W →
    IsIntegrallyClosed Γ(C,W)) :
    (compactIso q v i j h normal).hom ≫ j = (q ≫ v).fromNormalization :=
  compare_base q v i j h

section RationalJ
variable {U₀ V₀ Y₀ C₀ : Scheme}
  (q₀ : U₀ ⟶ V₀) (v₀ : V₀ ⟶ ProjectiveJLine318.scheme ℚ)
  [IsFinite q₀] [IsOpenImmersion v₀] [QuasiCompact v₀]
  (b₀ : Y₀ ⟶ V₀) (i₀ : Y₀ ⟶ C₀) [IsOpenImmersion i₀]
  (j₀ : C₀ ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite j₀]
  [IsIntegral U₀] [IsIntegral C₀]
  (e₀ : U₀ ≅ Y₀) (he₀ : e₀.hom ≫ b₀ = q₀) (hi₀ : i₀ ≫ j₀ = b₀ ≫ v₀)

include he₀ hi₀ in
/-- Specialization to the actual rational projective j-line. The input
e₀ is the ordinary comparison, not an isomorphism of compact models. -/
@[expose] def rationalJ
    (normal : ∀ W : C₀.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C₀,W)) :
    (q₀ ≫ v₀).normalization ≅ C₀ :=
  compactIso q₀ v₀ (e₀.hom ≫ i₀) j₀
    (by rw [Category.assoc,hi₀,←Category.assoc,he₀]) normal

@[reassoc] theorem rationalJ_over
    (normal : ∀ W : C₀.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C₀,W)) :
    (rationalJ q₀ v₀ b₀ i₀ j₀ e₀ he₀ hi₀ normal).hom ≫ j₀ = (q₀ ≫ v₀).fromNormalization :=
  compactIso_base _ _ _ _ _ _

@[reassoc] theorem rationalJ_open
    (normal : ∀ W : C₀.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C₀,W)) :
    (q₀ ≫ v₀).toNormalization ≫ (rationalJ q₀ v₀ b₀ i₀ j₀ e₀ he₀ hi₀ normal).hom =
      e₀.hom ≫ i₀ :=
  compactIso_open _ _ _ _ _ _

end RationalJ
end SelectedGenericCompactNormalization318

#print axioms SelectedGenericCompactNormalization318.compare_isIso
#print axioms SelectedGenericCompactNormalization318.rationalJ_over
#print axioms SelectedGenericCompactNormalization318.rationalJ_open
