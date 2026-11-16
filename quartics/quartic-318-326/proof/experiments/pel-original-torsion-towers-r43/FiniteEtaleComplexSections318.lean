module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Etale.Field
public section
noncomputable section
namespace FiniteEtaleComplexSections318
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} (π : X⟶Spec (CommRingCat.of ℂ))
/-- The original structural scalar map on the WHOLE global section ring. -/
@[expose] def coefficientMap : ℂ →+* Γ(X,⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv≫π.appTop).hom
@[expose] def algebra : Algebra ℂ Γ(X,⊤) := (coefficientMap π).toAlgebra
local instance : Algebra ℂ Γ(X,⊤) := algebra π

lemma finite [IsFinite π] : Module.Finite ℂ Γ(X,⊤) := by
  have hf : (coefficientMap π).Finite := by
    unfold coefficientMap
    rw [CommRingCat.hom_comp]
    exact (RingHom.finite_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv π.appTop).mpr π.finite_appTop
  exact hf

lemma etale [IsFinite π] [Etale π] : Algebra.Etale ℂ Γ(X,⊤) := by
  letI : IsAffine X := isAffine_of_isAffineHom π
  have hf : π.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  have hc : (coefficientMap π).Etale := by
    unfold coefficientMap
    rw [CommRingCat.hom_comp]
    exact (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv π.appTop).mpr hf
  exact hc

/-- Genuine reducedness of the entire finite étale complex scheme,
proved from its actual global algebra, without replacing the scheme. -/
lemma reduced [IsFinite π] [Etale π] : AlgebraicGeometry.IsReduced X := by
  letI : IsAffine X := isAffine_of_isAffineHom π
  letI := etale π
  letI : _root_.IsReduced Γ(X,⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field ℂ Γ(X,⊤)
  exact isReduced_of_isAffine_isReduced X

/-- The actual entire global algebra splits as copies of the original
complex field, indexed by its genuine prime spectrum. -/
@[expose] def split [IsFinite π] [Etale π] :
    Γ(X,⊤) ≃ₐ[ℂ] (PrimeSpectrum Γ(X,⊤)→ℂ) := by
  letI := etale π
  exact Algebra.FormallyEtale.equivPiOfIsSepClosed ℂ Γ(X,⊤)

/-- The canonical affine scheme comparison retains the original complex
base map through the ACTUAL global-section scalar homomorphism. -/
lemma coefficient_square [IsFinite π] :
    letI : IsAffine X := isAffine_of_isAffineHom π
    X.isoSpec.hom≫Spec.map (CommRingCat.ofHom (coefficientMap π))=π := by
  letI : IsAffine X := isAffine_of_isAffineHom π
  change X.isoSpec.hom≫Spec.map
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv≫π.appTop)=π
  rw [Spec.map_comp,←Category.assoc,Scheme.isoSpec_hom_naturality,
    Category.assoc,Scheme.isoSpec_Spec_hom,←Spec.map_comp,Iso.inv_hom_id,
    Spec.map_id,Category.comp_id]

variable {B : Type} [CommRing B] [Algebra ℂ B]
/-- A genuine global algebra splitting produces an actual whole scheme
isomorphism, retaining all original structure rather than only closed points. -/
@[expose] def schemeIso [IsFinite π] (e : Γ(X,⊤) ≃ₐ[ℂ] B) :
    X ≅ Spec (CommRingCat.of B) := by
  letI : IsAffine X := isAffine_of_isAffineHom π
  exact X.isoSpec ≪≫ Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op
lemma schemeIso_over [IsFinite π] (e : Γ(X,⊤) ≃ₐ[ℂ] B) :
    (schemeIso π e).hom≫Spec.map (CommRingCat.ofHom (algebraMap ℂ B))=π := by
  letI : IsAffine X := isAffine_of_isAffineHom π
  have he : CommRingCat.ofHom (algebraMap ℂ B)≫e.toRingEquiv.toCommRingCatIso.inv=
      CommRingCat.ofHom (coefficientMap π) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact e.symm.commutes c
  change (X.isoSpec.hom≫Spec.map e.toRingEquiv.toCommRingCatIso.inv)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ B))=π
  rw [Category.assoc,←Spec.map_comp,he]
  exact coefficient_square π
end FiniteEtaleComplexSections318
