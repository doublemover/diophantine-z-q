module
public import PELRealRationalProportionality318
public section
noncomputable section
namespace PELOriginalInertiaOrbitSeparation318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicFixedParameter318
open QuaternionicPositiveDeterminant318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELInertiaArithmeticFixedPoints318
open PELInertiaNormalizerData318 PELInertiaRealFixedPoints318 PELPrincipalThreeStabilizer318
open PELRealRationalProportionality318 PELInertiaRationalConjugacy318
set_option maxHeartbeats 1800000

/-- Equality of original fixed-point orbits forces equality of their
labels. The route passes through full rational conjugation, not their norms
or fixed-point coordinates alone. -/
theorem index_of_upstairs_orbit (g : positiveNormalizer) (i j : Fin 5)
    (h : baseAction g (originalFixedPoint i)=originalFixedPoint j) : i=j := by
  let n : positiveNormalizer := g*inertiaElement i*g⁻¹
  have hfix : baseAction n (originalFixedPoint j)=originalFixedPoint j := by
    rw [←h]
    calc
      baseAction n (baseAction g (originalFixedPoint i))=
        baseAction (n*g) (originalFixedPoint i) := (baseAction_mul n g _).symm
      _ = baseAction g (baseAction (inertiaElement i) (originalFixedPoint i)) := by
        dsimp only [n]
        rw [mul_assoc,inv_mul_cancel,mul_one,baseAction_mul]
      _ = baseAction g (originalFixedPoint i) := by rw [original_fixed]
  have hm : fixesLine (PELPositiveNormalizerMobius318.matrix n) (fixedPoint j) :=
    fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive n)
        (fixedPoint j) (fixedPoint_im_positive j)) (congrArg Subtype.val hfix)
  have hn : fixesLine (PELPositiveNormalizerMobius318.matrix (inertiaElement j)) (fixedPoint j) :=
    fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive (inertiaElement j))
        (fixedPoint j) (fixedPoint_im_positive j)) (fixedPoint_equation j)
  have htrM : PELPositiveNormalizerMobius318.matrix n 0 0+PELPositiveNormalizerMobius318.matrix n 1 1=0 := by
    change representation (n.val:B) 0 0+representation (n.val:B) 1 1=0
    rw [representation_trace]
    change (reducedTrace ((g.val:B)*element i*(↑g.val⁻¹:B)):ℝ)=0
    rw [trace_conjugation,element_trace] <;> norm_num
  have htrN : PELPositiveNormalizerMobius318.matrix (inertiaElement j) 0 0+PELPositiveNormalizerMobius318.matrix (inertiaElement j) 1 1=0 := by
    change representation (element j) 0 0+representation (element j) 1 1=0
    rw [representation_trace,element_trace] <;> norm_num
  have hp := QuaternionicTraceZeroFixedLine318.proportional _ _ (fixedPoint j)
    (fixedPoint_im_positive j) hm hn htrM htrN (lower_left_positive j).ne'
  obtain ⟨q,hq,he⟩ := rational_proportional (n.val:B) (element j)
    (Units.ne_zero n.val) (inertia_coordinate_ne_zero j) _ hp
  exact index_of_element_conjugacy i j g.val q hq he
end PELOriginalInertiaOrbitSeparation318
