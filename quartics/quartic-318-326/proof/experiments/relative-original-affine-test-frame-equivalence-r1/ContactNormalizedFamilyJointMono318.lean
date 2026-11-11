module
public import ContactNormalizedOriginalCurve318
public section
noncomputable section
namespace ContactNormalizedFamilyJointMono318
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
local notation "embedding" => ContactNormalizedTripleFamilies318.embedding R c L hz S f
local notation "rotation" => ContactNormalizedTripleFamilies318.rotation R c L hz S f
local notation "projection" => ContactNormalizedTripleProjection318.projection R c L hz S f

@[expose] def original (a : Point R P S i j k) : family a ⟶ curve R c :=
  pullback.fst _ _ ≫ ContactNormalizedOriginalCurve318.chart R c L hz i
@[reassoc] lemma embedding_original (a : Point R P S i j k) :
    embedding a ≫ ContactRelativeCoefficientChange318.curveMap R S f c=original R c L hz S f a := by
  rw [ContactNormalizedTripleFamilies318.embedding,Category.assoc,
    ← ContactNormalizedOriginalCurve318.comparison R c L hz S f i a.point a.first_eq,
    Iso.inv_hom_id_assoc]
@[reassoc] lemma embedding_projection (a : Point R P S i j k) :
    embedding a ≫ ContactRelativeStructuralHOne318.projection S c=projection a := by
  rw [ContactNormalizedTripleFamilies318.embedding,Category.assoc]
  change (ContactNormalizedTripleFamilies318.comparison R c L hz S f a).inv ≫
    ContactGlobalResidueFlat318.projection S c _ _=_
  exact ContactNormalizedTripleProjection318.comparison_inv_projection R c L hz S f a

/-- The ORIGINAL curve map and coefficient projection are jointly
monic on the actual normalized zero family. The proof uses the genuine
ambient coefficient Cartesian square and the actual closed immersion,
not an assertion that the map to the old curve alone is injective. -/
lemma hom_ext (a : Point R P S i j k) {X : Scheme} (v w : X ⟶ family a)
    (hc : v ≫ original R c L hz S f a=w ≫ original R c L hz S f a)
    (hp : v ≫ projection a=w ≫ projection a) : v=w := by
  apply (cancel_mono (embedding a)).1
  apply (ContactZeroParameterBaseChange318.ambient_square R S f c).hom_ext
  · simpa only [Category.assoc,embedding_original] using hc
  · simpa only [Category.assoc,embedding_projection] using hp

@[reassoc] lemma rotation_original (a : Point R P S i j k) :
    (rotation a).hom ≫ original R c L hz S f a=
      original R c L hz S f (rotate R P S i j k a) := by
  rw [← embedding_original,← Category.assoc,
    ContactNormalizedTripleFamilies318.rotation_embedding,embedding_original]
@[reassoc] lemma rotation_inv_original (a : Point R P S i j k) :
    (rotation a).inv ≫ original R c L hz S f (rotate R P S i j k a)=
      original R c L hz S f a := by
  rw [← rotation_original R c L hz S f a,Iso.inv_hom_id_assoc]
end ContactNormalizedFamilyJointMono318
