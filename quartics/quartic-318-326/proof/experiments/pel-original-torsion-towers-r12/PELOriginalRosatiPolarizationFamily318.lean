module
public import PELOriginalRosatiProductGauge318
public import PELOriginalPolarizationCube318
public section
noncomputable section
namespace PELOriginalRosatiPolarizationFamily318
open AlgebraicGeometry CategoryTheory LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalOrderHermitianAdjoint318
open PELOriginalRosatiProductMaps318 PELOriginalRosatiProductFrames318
open PELOriginalSchemePointGroup318 PELOriginalNormalizedPolarizationFamily318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
@[expose] def threeLine (M : Line (candidate τ hτ)) (side : Bool) : Line (Product τ hτ) :=
  LineSheafTensor318.line
    (LineSheafTensor318.line
      (LineSheafPullback318.line (maps τ hτ a (mainPositions side 0)) M)
      (LineSheafPullback318.line (maps τ hτ a (mainPositions side 1)) M))
    (LineSheafPullback318.line (maps τ hτ a (mainPositions side 2)) M)
@[expose] def sideClass (side : Bool) (c : Class (candidate τ hτ)) : Class (Product τ hτ) :=
  LineClassPullbackGroup318.hom (maps τ hτ a (mainPositions side 0)) c*
    LineClassPullbackGroup318.hom (maps τ hτ a (mainPositions side 1)) c*
    LineClassPullbackGroup318.hom (maps τ hτ a (mainPositions side 2)) c
@[expose] def defect : Class (candidate τ hτ) →* Class (Product τ hτ) where
  toFun c := sideClass τ hτ a true c*(sideClass τ hτ a false c)⁻¹
  map_one' := by simp [sideClass]
  map_mul' c d := by simp only [sideClass,map_mul,mul_inv_rev]; ac_rfl
lemma class_threeLine (M : Line (candidate τ hτ)) (side : Bool) :
    classOf (threeLine τ hτ a M side)=sideClass τ hτ a side (classOf M) := by
  simp only [threeLine,LineSheafClassGroup318.classOf_tensor]
  rfl
lemma defect_one_of_iso (M : Line (candidate τ hτ))
    (e : (threeLine τ hτ a M true).object ≅ (threeLine τ hτ a M false).object) :
    defect τ hτ a (classOf M)=1 := by
  have h := classOf_eq e
  rw [class_threeLine,class_threeLine] at h
  change _*_⁻¹=1
  rw [h,mul_inv_cancel]
lemma cubic_defect : defect τ hτ a (classOf (cubicLine τ hτ))=1 :=
  defect_one_of_iso τ hτ a _
    (PELOriginalRosatiProductGauge318.iso τ hτ a 3 (PELOriginalHyperplaneAllPowerBasis318.cubic τ hτ))
lemma quadratic_defect : defect τ hτ a (classOf (quadraticLine τ hτ))=1 :=
  defect_one_of_iso τ hτ a _
    (PELOriginalRosatiProductGauge318.iso τ hτ a 2 (PELOriginalHyperplaneAllPowerBasis318.quadratic τ hτ))
lemma degree_one_defect : defect τ hτ a (classOf (line τ hτ))=1 := by
  let c := defect τ hτ a (classOf (line τ hτ))
  have h3 : c^3=1 := by
    have h := cubic_defect τ hτ a
    have hc := PELOriginalPolarizationCube318.cube_class τ hτ
    rw [LineSheafTensorPower318.classOf_power] at hc
    rw [←hc,map_pow] at h
    exact h
  have h2 : c^2=1 := by
    have h := quadratic_defect τ hτ a
    have hc := PELOriginalPolarizationCube318.square_class τ hτ
    rw [LineSheafTensorPower318.classOf_power] at hc
    rw [←hc,map_pow] at h
    exact h
  have he : c*c^2=1 := by rw [←pow_succ']; exact h3
  simpa only [h2,mul_one] using he
@[expose] def leftMap : Product τ hτ⟶Product τ hτ :=
  pairMap τ hτ (baseMap τ hτ) (action τ hτ a (firstPoint τ hτ)) (secondPoint τ hτ)
@[expose] def rightMap : Product τ hτ⟶Product τ hτ :=
  pairMap τ hτ (baseMap τ hτ) (firstPoint τ hτ) (action τ hτ (adjoint a) (secondPoint τ hτ))
abbrev leftLine := LineSheafPullback318.line (leftMap τ hτ a) (family τ hτ)
abbrev rightLine := LineSheafPullback318.line (rightMap τ hτ a) (family τ hτ)

/-- Exact comparison of the actual normalized product family with the
six-factor defect. The common zero-line factor cancels algebraically,
not by assuming a rigidification. -/
lemma family_defect : classOf (leftLine τ hτ a)*(classOf (rightLine τ hτ a))⁻¹=
    defect τ hτ a (classOf (line τ hτ)) := by
  rw [leftLine,rightLine,leftMap,rightMap,pair_class,pair_class]
  simp only [PELOriginalPolarizationBicharacter318.pairing]
  let q (i : Fin 9) := LineClassPullbackGroup318.hom (maps τ hτ a i) (classOf (line τ hτ))
  let e := PELOriginalCubeTestClasses318.value τ hτ (baseMap τ hτ)
    (0 : Points τ hτ (Product τ hτ) (baseMap τ hτ))
  change (q 4*(q 2)⁻¹*(q 1)⁻¹*e)*(q 5*(q 0)⁻¹*(q 3)⁻¹*e)⁻¹=
    (q 4*q 0*q 3)*(q 5*q 2*q 1)⁻¹
  group
lemma class_equation : classOf (leftLine τ hτ a)=classOf (rightLine τ hτ a) := by
  have h := degree_one_defect τ hτ a
  rw [←family_defect] at h
  exact mul_inv_eq_one.mp h

/-- Exact whole-product algebraic comparison for the explicit original
Rosati adjoint. Both sides are the SAME normalized polarization family
pulled back along the actual order maps. Ninefold auxiliary theta factors
balance the FULL semicharacter before cancelling, so no torsion
cancellation or represented-dual assertion is used. -/
@[expose] def iso : (leftLine τ hτ a).object ≅ (rightLine τ hτ a).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (class_equation τ hτ a))
lemma hom_inv : (iso τ hτ a).hom≫(iso τ hτ a).inv=𝟙 _ := (iso τ hτ a).hom_inv_id
lemma inv_hom : (iso τ hτ a).inv≫(iso τ hτ a).hom=𝟙 _ := (iso τ hτ a).inv_hom_id
@[expose] def testIso {T : Scheme} (f : T⟶Product τ hτ) :
    (Scheme.Modules.pullback f).obj (leftLine τ hτ a).object ≅
      (Scheme.Modules.pullback f).obj (rightLine τ hτ a).object :=
  (Scheme.Modules.pullback f).mapIso (iso τ hτ a)
end PELOriginalRosatiPolarizationFamily318
