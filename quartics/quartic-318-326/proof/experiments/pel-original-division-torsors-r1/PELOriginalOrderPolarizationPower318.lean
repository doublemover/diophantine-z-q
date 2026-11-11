module
public import PELOriginalOrderHyperplanePowers318
public import PELOriginalPolarizationCube318
public section
noncomputable section
namespace PELOriginalOrderPolarizationPower318
open AlgebraicGeometry CategoryTheory LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalComplementaryOrder318 PELOriginalOrderPolarizationData318
open PELOriginalOrderHyperplanePowers318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Both genuine hyperplane identities control the SAME degree-one
line. Only the square of its defect is killed; no cancellation of
possible two-torsion in the line-class group is used. -/
lemma defect_square (a : order) : (defect τ hτ a (classOf (line τ hτ)))^2=1 := by
  let c := defect τ hτ a (classOf (line τ hτ))
  have h6 : c^6=1 := by
    have h := cubic_defect τ hτ a
    have hc := PELOriginalPolarizationCube318.cube_class τ hτ
    rw [LineSheafTensorPower318.classOf_power] at hc
    rw [←hc,map_pow,←pow_mul] at h
    exact h
  have h4 : c^4=1 := by
    have h := quadratic_defect τ hτ a
    have hc := PELOriginalPolarizationCube318.square_class τ hτ
    rw [LineSheafTensorPower318.classOf_power] at hc
    rw [←hc,map_pow,←pow_mul] at h
    exact h
  have h : c^2*c^4=1 := by rw [←pow_add]; exact h6
  simpa only [h4,mul_one] using h
lemma class_equation (a : order) :
    classOf (source τ hτ a (line τ hτ))=
      classOf (LineSheafTensorPower318.line (line τ hτ) (2*degree a)) := by
  have h := defect_square τ hτ a
  change (_*_*(_^degree a)⁻¹)^2=1 at h
  rw [mul_pow,mul_pow,inv_pow,←pow_mul,Nat.mul_comm (degree a) 2] at h
  have he := mul_inv_eq_one.mp h
  simp only [source,LineSheafClassGroup318.classOf_tensor]
  change LineClassPullbackGroup318.hom (act τ hτ a)
      (classOf (LineSheafTensorPower318.line (line τ hτ) 2))*
    LineClassPullbackGroup318.hom (act τ hτ (complement a))
      (classOf (LineSheafTensorPower318.line (line τ hτ) 2))=_
  simpa only [LineSheafTensorPower318.classOf_power,map_pow] using he

/-- Genuine whole algebraic line isomorphism for each element of the
original half-integral order and its explicit complementary element.
This is a squared polarization norm identity, not a represented-dual
Rosati assertion or an unsquared identity. -/
@[expose] def iso (a : order) :
    (source τ hτ a (line τ hτ)).object ≅
      (LineSheafTensorPower318.line (line τ hτ) (2*degree a)).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (class_equation τ hτ a))
lemma hom_inv (a : order) : (iso τ hτ a).hom≫(iso τ hτ a).inv=𝟙 _ := (iso τ hτ a).hom_inv_id
lemma inv_hom (a : order) : (iso τ hτ a).inv≫(iso τ hτ a).hom=𝟙 _ := (iso τ hτ a).inv_hom_id

/-- Actual pullback of the complete isomorphism, valid for arbitrary
scheme tests, including nonreduced tests. -/
@[expose] def testIso {T : Scheme} (f : T⟶candidate τ hτ) (a : order) :
    (Scheme.Modules.pullback f).obj (source τ hτ a (line τ hτ)).object ≅
      (Scheme.Modules.pullback f).obj (LineSheafTensorPower318.line (line τ hτ) (2*degree a)).object :=
  (Scheme.Modules.pullback f).mapIso (iso τ hτ a)
end PELOriginalOrderPolarizationPower318
