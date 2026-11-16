module
public import ContactNormalizedTripleFamilies318
public section
noncomputable section
namespace ContactNormalizedTripleProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ProjectiveParameterSliceTriplePoints318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
variable {i j k : Fin F.size}

local notation "family" => ContactNormalizedTripleFamilies318.family R c L hz S f
local notation "comparison" => ContactNormalizedTripleFamilies318.comparison R c L hz S f
local notation "rotation" => ContactNormalizedTripleFamilies318.rotation R c L hz S f
local notation "N" => ContactCoefficientNativeSections318.L' R S f c L

@[expose] def projection (a : Point R P S i j k) : family a ⟶ Spec S := pullback.snd _ _
@[reassoc] lemma comparison_projection (a : Point R P S i j k) :
    (comparison a).hom ≫ projection R c L hz S f a=
    ContactGlobalResidueFlat318.projection S c N
      (ContactOriginalSectionParameter318.points R c L hz S f a.point) :=
  ContactNormalizedPointZeroFamily318.iso_projection R c L hz S f i a.point a.first_eq
@[reassoc] lemma comparison_inv_projection (a : Point R P S i j k) :
    (comparison a).inv ≫ ContactGlobalResidueFlat318.projection S c N
      (ContactOriginalSectionParameter318.points R c L hz S f a.point)=
    projection R c L hz S f a := by
  rw [← comparison_projection R c L hz S f a,Iso.inv_hom_id_assoc]

/-- The actual normalized family rotation is over the SAME coefficient
scheme, not just an isomorphism of its total spaces. -/
@[reassoc] lemma rotation_projection (a : Point R P S i j k) :
    (rotation a).hom ≫ projection R c L hz S f a=
      projection R c L hz S f (rotate R P S i j k a) := by
  rw [ContactNormalizedTripleFamilies318.rotation,Iso.trans_hom,Iso.trans_hom,
    Iso.symm_hom,Category.assoc,Category.assoc,comparison_projection]
  change (comparison (rotate R P S i j k a)).inv ≫
    ((ContactParameterUnitZeros318.zeroIso R c L hz S f a.secondUnit⁻¹ a.point).hom ≫
      ContactGlobalResidueFlat318.projection S c N
        (ContactOriginalSectionParameter318.points R c L hz S f a.point))=_
  rw [ContactParameterUnitZeros318.zeroIso_projection,comparison_inv_projection]
@[reassoc] lemma rotation_inv_projection (a : Point R P S i j k) :
    (rotation a).inv ≫ projection R c L hz S f (rotate R P S i j k a)=
      projection R c L hz S f a := by
  rw [← rotation_projection R c L hz S f a,Iso.inv_hom_id_assoc]
end ContactNormalizedTripleProjection318
