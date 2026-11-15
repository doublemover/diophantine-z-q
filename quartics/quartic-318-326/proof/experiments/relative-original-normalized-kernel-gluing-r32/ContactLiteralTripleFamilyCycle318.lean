module
public import ContactNormalizedFamilyJointMono318
public section
noncomputable section
namespace ContactLiteralTripleFamilyCycle318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
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
local notation "S" i j k => ContactLiteralTripleZeroFamily318.ring R c L hz i j k
local notation "f" i j k => ContactLiteralTripleZeroFamily318.coefficient R c L hz i j k
local notation "a" i j k => ProjectiveParameterSliceTripleAlgebra318.universal R P i j k
local notation "rot" => ContactLiteralTripleFamilyRotation318.rotation R c L hz
local notation "proj" => ContactLiteralTripleFamilyRotation318.projection R c L hz
local notation "orig" i j k => ContactNormalizedFamilyJointMono318.original R c L hz
  (S i j k) (f i j k) (a i j k)
variable (i j k : Fin F.size)

/-- The across-ring family rotation retains its map to the SAME original
contact curve over R, as well as its separately proved base projection. -/
@[reassoc] lemma rotation_original : rot i j k ≫ orig j k i=orig i j k := by
  simp only [ContactLiteralTripleFamilyRotation318.rotation,
    ContactNormalizedFamilyJointMono318.original,Category.assoc]
  rw [ContactLiteralTripleFamilyRotation318.rotatedIso,Iso.symm_hom,
    RestrictedFamilyOriginal.one_inv_assoc]
  exact ContactNormalizedFamilyJointMono318.rotation_inv_original R c L hz
    (S i j k) (f i j k) (a i j k)

/-- Actual cyclic identity across the THREE DIFFERENT literal triple
coefficient rings. The original curve map and the actual base cycle
jointly determine the zero-family arrow through the ambient Cartesian
square and closed immersion. This is not inferred from a base cycle alone. -/
lemma cycle : rot i j k ≫ rot j k i ≫ rot k i j=𝟙 _ := by
  apply ContactNormalizedFamilyJointMono318.hom_ext R c L hz (S i j k) (f i j k)
    (a i j k)
  · simp only [Category.assoc,rotation_original,Category.id_comp]
  · change (rot i j k ≫ rot j k i ≫ rot k i j) ≫ proj i j k=𝟙 _ ≫ proj i j k
    simp only [Category.assoc,ContactLiteralTripleFamilyRotation318.rotation_projection,
      Category.id_comp]
    rw [ProjectiveParameterSliceTripleSchemes318.cycle,Category.comp_id]
end ContactLiteralTripleFamilyCycle318
