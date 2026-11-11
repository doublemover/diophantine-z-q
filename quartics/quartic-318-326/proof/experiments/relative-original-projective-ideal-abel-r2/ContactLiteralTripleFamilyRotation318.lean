module
public import ContactLiteralTripleZeroFamily318
public import ContactNormalizedTripleProjection318
public section
noncomputable section
namespace ContactLiteralTripleFamilyRotation318
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
local notation "pointMap" => ContactNormalizedPointZeroFamily318.testMap R c L hz
local notation "p" i => ContactNormalizedChartZeroFamily318.projection R c L hz i

abbrev family (i j k : Fin F.size) : Scheme :=
  ContactNormalizedTripleFamilies318.family R c L hz (S i j k) (f i j k) (a i j k)
@[expose] def projection (i j k : Fin F.size) : family R c L hz i j k ⟶ Spec (S i j k) :=
  pullback.snd _ _
variable (i j k : Fin F.size)
local notation "rot" => ProjectiveParameterSliceTriplePoints318.rotate R P (S i j k) i j k (a i j k)
local notation "r" => ProjectiveParameterSliceTripleSchemes318.rotation R P i j k

/-- Rotation of the literal triple coefficient algebra induces exactly
the already constructed normalized point. This identifies the actual
chart map across DIFFERENT triple rings, not only within a fixed test. -/
lemma parameter_rotation : r ≫
    pointMap (S j k i) (f j k i) j (a j k i).point (a j k i).first_eq=
    pointMap (S i j k) (f i j k) j rot.point rot.first_eq := by
  rw [ProjectiveParameterSliceTripleSchemes318.rotation,
    ContactNormalizedPointZeroFamily318.testMap,
    ContactNormalizedPointZeroFamily318.testMap,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective b
  change ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k
    (ContactNormalizedPointZeroFamily318.sliceMap R c L hz (S j k i) (f j k i) j
      (a j k i).point (a j k i).first_eq
      (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P j) z))=
    ContactNormalizedPointZeroFamily318.sliceMap R c L hz (S i j k) (f i j k) j
      rot.point rot.first_eq
      (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P j) z)
  rw [ContactNormalizedPointZeroFamily318.sliceMap_mk,
    ContactNormalizedPointZeroFamily318.sliceMap_mk]
  exact DFunLike.congr_fun (congrArg (fun q => q.point)
    (ProjectiveParameterSliceTripleCocycle318.forward_rotate R P i j k)) z

/-- The rotated family over the FIRST literal triple base is the actual
base change of the original family over the NEXT literal triple ring. -/
@[expose] def rotatedIso : ContactNormalizedTripleFamilies318.family R c L hz
    (S i j k) (f i j k) rot ≅ pullback (projection R c L hz j k i) r :=
  (RestrictedFamilyPullback318.iso (p j)
    (pointMap (S j k i) (f j k i) j (a j k i).point (a j k i).first_eq) r
    (pointMap (S i j k) (f i j k) j rot.point rot.first_eq)
    (parameter_rotation R c L hz i j k)).symm

/-- Actual family arrow over the actual cyclic triple-base rotation.
No point-set map is substituted for the geometric base-change arrow. -/
@[expose] def rotation : family R c L hz i j k ⟶ family R c L hz j k i :=
  (ContactNormalizedTripleFamilies318.rotation R c L hz (S i j k) (f i j k) (a i j k)).inv ≫
    (rotatedIso R c L hz i j k).hom ≫ pullback.fst _ _

@[reassoc] lemma rotation_projection : rotation R c L hz i j k ≫
    projection R c L hz j k i=projection R c L hz i j k ≫ r := by
  rw [rotation,Category.assoc,Category.assoc,pullback.condition,
    rotatedIso,Iso.symm_hom,RestrictedFamilyPullback318.inv_projection_assoc]
  change (ContactNormalizedTripleFamilies318.rotation R c L hz (S i j k) (f i j k)
    (a i j k)).inv ≫
      ContactNormalizedTripleProjection318.projection R c L hz (S i j k) (f i j k) rot ≫ r=_
  rw [← Category.assoc,ContactNormalizedTripleProjection318.rotation_inv_projection]
  rfl
end ContactLiteralTripleFamilyRotation318
