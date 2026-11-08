module
public import FinitePairSwap318
public import InfinityAdditionScheme318
public section
noncomputable section
namespace FiniteInfinitySymmetry318
open InfinityAdditionAlgebra318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
lemma mapped_outX (A B:R) (tangent:Bool) (φ:OutputRing A B tangent →ₐ[R] S) :
    φ (outX A B tangent)*φ (pairMap A B tangent (numeratorY A B tangent))=
      φ (pairMap A B tangent (numeratorX A B tangent))*φ (pairMap A B tangent (denominator A B tangent)) := by
  have hi : φ (↑(numeratorYUnit A B tangent)⁻¹)*φ (pairMap A B tangent (numeratorY A B tangent))=1 := by
    simpa only [map_mul,map_one,numeratorYUnit,IsUnit.unit_spec] using
      congrArg φ (Units.inv_mul (numeratorYUnit A B tangent))
  simp only [outX,map_mul]
  rw [mul_assoc,mul_assoc,hi,mul_one]
lemma mapped_outZ (A B:R) (tangent:Bool) (φ:OutputRing A B tangent →ₐ[R] S) :
    φ (outZ A B tangent)*φ (pairMap A B tangent (numeratorY A B tangent))=
      φ (pairMap A B tangent (denominator A B tangent))^3 := by
  have hi : φ (↑(numeratorYUnit A B tangent)⁻¹)*φ (pairMap A B tangent (numeratorY A B tangent))=1 := by
    simpa only [map_mul,map_one,numeratorYUnit,IsUnit.unit_spec] using
      congrArg φ (Units.inv_mul (numeratorYUnit A B tangent))
  simp only [outZ,map_mul,map_pow]
  rw [mul_assoc,hi,mul_one]

/-- Input exchange preserves each actual infinity-output addition chart and its
output, including the tangent and inverse loci over nonreduced base rings. -/
theorem coordinates (A B:R) (tangent:Bool) (φ ψ:OutputRing A B tangent →ₐ[R] S)
    (hp:∀r:RelativeChordAlgebra318.PairRing A B,
      φ (pairMap A B tangent r)=ψ (pairMap A B tangent (FinitePairSwap318.swap A B r))) :
    φ (outX A B tangent)=ψ (outX A B tangent) ∧ φ (outZ A B tangent)=ψ (outZ A B tangent) := by
  have hX:=hp (numeratorX A B tangent)
  rw [FinitePairSwap318.numeratorX_swap] at hX
  have hY:=hp (numeratorY A B tangent)
  have hD:=hp (denominator A B tangent)
  have hunit:=(numeratorY_unit A B tangent).map φ
  have hxφ:=mapped_outX A B tangent φ
  have hzφ:=mapped_outZ A B tangent φ
  have hxψ:=mapped_outX A B tangent ψ
  have hzψ:=mapped_outZ A B tangent ψ
  cases tangent
  · rw [FinitePairSwap318.numeratorY_false,map_neg,map_neg] at hY
    rw [FinitePairSwap318.denominator_false,map_neg,map_neg] at hD
    constructor
    · apply hunit.mul_right_cancel
      rw [hxφ,hX,hD,hY]
      linear_combination hxψ
    · apply hunit.mul_right_cancel
      rw [hzφ,hD,hY]
      linear_combination hzψ
  · rw [FinitePairSwap318.numeratorY_true] at hY
    rw [FinitePairSwap318.denominator_true] at hD
    constructor
    · apply hunit.mul_right_cancel
      rw [hxφ,hX,hD,hY]
      exact hxψ.symm
    · apply hunit.mul_right_cancel
      rw [hzφ,hD,hY]
      exact hzψ.symm

theorem scheme_agreement (A B:R) (tangent:Bool) (φ ψ:OutputRing A B tangent →ₐ[R] S)
    (hp:∀r:RelativeChordAlgebra318.PairRing A B,
      φ (pairMap A B tangent r)=ψ (pairMap A B tangent (FinitePairSwap318.swap A B r))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B tangent=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ InfinityAdditionScheme318.addition A B tangent := by
  have hh:=coordinates A B tangent φ ψ hp
  have he:φ.comp (outputMap A B tangent)=ψ.comp (outputMap A B tangent) := by
    apply InfinityChart318.hom_ext
    · simpa only [AlgHom.comp_apply,outputMap_x] using hh.1
    · simpa only [AlgHom.comp_apply,outputMap_z] using hh.2
  dsimp only [InfinityAdditionScheme318.addition,InfinityAdditionScheme318.chartAddition]
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
end FiniteInfinitySymmetry318
