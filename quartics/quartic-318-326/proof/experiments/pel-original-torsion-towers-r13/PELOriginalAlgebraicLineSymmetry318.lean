module
public import PELOriginalNegationLineCocycle318
public import FramedLineUnitGaugeIso318
public import PELOriginalPolarizationCube318
public import LineClassPullbackGroup318
public section
noncomputable section
namespace PELOriginalAlgebraicLineSymmetry318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalNegationLineCover318 PELOriginalNegationLineGauge318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Genuine algebraic symmetry of the SAME original degree-one line:
actual inverse-pullback sheaf is isomorphic to the actual original sheaf.
The regular gauge and whole cocycle equality are produced independently. -/
@[expose] def symmetry : (Scheme.Modules.pullback (negative τ hτ)).obj (sheaf τ hτ) ≅ sheaf τ hτ :=
  FramedLineUnitGaugeIso318.iso (pullback τ hτ) (sheaf τ hτ)
    (chart τ hτ) (targetFrame τ hτ) (sourceFrame τ hτ) (covers τ hτ)
    (gauge τ hτ) (PELOriginalNegationLineCocycle318.gauge_equation τ hτ)
lemma hom_inv : (symmetry τ hτ).hom≫(symmetry τ hτ).inv=𝟙 _ := (symmetry τ hτ).hom_inv_id
lemma inv_hom : (symmetry τ hτ).inv≫(symmetry τ hτ).hom=𝟙 _ := (symmetry τ hτ).inv_hom_id

lemma class_invariant :
    LineClassPullbackGroup318.hom (negative τ hτ) (classOf (line τ hτ))=classOf (line τ hτ) :=
  classOf_eq (symmetry τ hτ)

/-- Every actual tensor power is also algebraically symmetric. The
chosen isomorphism is justified by the quotient relation of genuine
whole-sheaf isomorphisms; no canonical fiber normalization is claimed. -/
@[expose] def powerIso (n : ℕ) :
    (Scheme.Modules.pullback (negative τ hτ)).obj
      (FramedLineTensorPower318.object (sheaf τ hτ) n) ≅
    FramedLineTensorPower318.object (sheaf τ hτ) n := by
  apply Classical.choice
  apply (classOf_eq_iff
    (LineSheafPullback318.line (negative τ hτ) (LineSheafTensorPower318.line (line τ hτ) n))
    (LineSheafTensorPower318.line (line τ hτ) n)).mp
  change LineClassPullbackGroup318.hom (negative τ hτ)
    (classOf (LineSheafTensorPower318.line (line τ hτ) n))=_
  rw [LineSheafTensorPower318.classOf_power,LineSheafTensorPower318.classOf_power,
    map_pow,class_invariant]

/-- The independently constructed cubic hyperplane sheaf has the same
actual inversion symmetry, using the PROVED algebraic cube comparison. -/
@[expose] def cubicIso :
    (Scheme.Modules.pullback (negative τ hτ)).obj (cubicSheaf τ hτ) ≅ cubicSheaf τ hτ :=
  (Scheme.Modules.pullback (negative τ hτ)).mapIso (PELOriginalPolarizationCube318.cubeIso τ hτ).symm ≪≫
    powerIso τ hτ 3 ≪≫ PELOriginalPolarizationCube318.cubeIso τ hτ

@[expose] def quadraticIso :
    (Scheme.Modules.pullback (negative τ hτ)).obj (quadraticSheaf τ hτ) ≅ quadraticSheaf τ hτ :=
  (Scheme.Modules.pullback (negative τ hτ)).mapIso (PELOriginalPolarizationCube318.squareIso τ hτ).symm ≪≫
    powerIso τ hτ 2 ≪≫ PELOriginalPolarizationCube318.squareIso τ hτ
end PELOriginalAlgebraicLineSymmetry318
