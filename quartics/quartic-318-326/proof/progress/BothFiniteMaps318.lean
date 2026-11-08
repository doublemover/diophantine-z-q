module
public import BothFiniteTransition318
public import BothInfinitySymmetry318
public import InfinityAdditionScheme318
public section
noncomputable section
namespace BothFiniteMaps318
open BothInfinityAlgebra318 InfinityVietaAlgebra318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Comparison with both actual finite-input homogeneous addition formulas over
any common coefficient algebra, assuming only literal input chart transitions. -/
theorem homogeneous_coordinates (A B:R) (φ : OutputRing A B →ₐ[R] S)
    (ψ : RelativeChordAlgebra318.PairRing A B →ₐ[R] S) (tangent : Bool)
    (hu : φ (u1 A B)*ψ (InfinityAdditionAlgebra318.Y1 A B)=ψ (InfinityAdditionAlgebra318.X1 A B))
    (hv : φ (v1 A B)*ψ (InfinityAdditionAlgebra318.Y1 A B)=1)
    (ht : φ (u2 A B)*ψ (InfinityAdditionAlgebra318.Y2 A B)=ψ (InfinityAdditionAlgebra318.X2 A B))
    (hw : φ (v2 A B)*ψ (InfinityAdditionAlgebra318.Y2 A B)=1) :
    φ (outU A B)*ψ (InfinityAdditionAlgebra318.numeratorY A B tangent)=
      ψ (InfinityAdditionAlgebra318.numeratorX A B tangent)*ψ (InfinityAdditionAlgebra318.denominator A B tangent) ∧
    φ (outV A B)*ψ (InfinityAdditionAlgebra318.numeratorY A B tangent)=
      ψ (InfinityAdditionAlgebra318.denominator A B tangent)^3 := by
  have hm (r : RelativeChordAlgebra318.PairRing A B) (n : ℕ) : ψ (r^n)=(ψ r)^n :=
    ψ.toRingHom.map_pow r n
  have hF := congrArg ψ (InfinityAdditionAlgebra318.first_equation A B)
  have hG := congrArg ψ (InfinityAdditionAlgebra318.second_equation A B)
  simp only [map_sub,map_mul,hm,map_zero,InfinityAdditionAlgebra318.coeffMap,
    Algebra.ofId_apply,AlgHom.commutes] at hF hG
  have hl := congrArg φ (line_first A B)
  have hl' := congrArg φ (line_second A B)
  simp only [map_mul,map_add] at hl hl'
  have hs := congrArg φ (slope_Q A B)
  simp only [map_mul,BothInfinitySymmetry318.map_q,BothInfinitySymmetry318.map_s] at hs
  have hq : IsUnit (q (algebraMap R S A) (algebraMap R S B)
      (φ (u2 A B)) (φ (v1 A B)) (φ (v2 A B))) := by
    rw [←BothInfinitySymmetry318.map_q]
    exact (two_units A B).1.map φ
  have hU := congrArg φ (BothMixedMaps318.outU_relation A B)
  simp only [map_mul,map_sub,BothInfinitySymmetry318.map_c,BothInfinitySymmetry318.map_d] at hU
  have hV : φ (outV A B)=φ (slope A B)*φ (outU A B)-φ (intercept A B) := by
    simp only [outV,map_sub,map_mul]
  have htan := BothFiniteTransition318.tangent_line (algebraMap R S A) (algebraMap R S B)
    (φ (u1 A B)) (φ (v1 A B)) (φ (u2 A B)) (φ (v2 A B))
    (ψ (InfinityAdditionAlgebra318.X1 A B)) (ψ (InfinityAdditionAlgebra318.Y1 A B))
    (ψ (InfinityAdditionAlgebra318.X2 A B)) (ψ (InfinityAdditionAlgebra318.Y2 A B))
    (φ (slope A B)) (φ (intercept A B)) hF hG hu hv ht hw hl hs hq
  have hDL : φ (slope A B)*ψ (InfinityAdditionAlgebra318.denominator A B tangent)+
      φ (intercept A B)*ψ (InfinityAdditionAlgebra318.slopeNumerator A B tangent)=0 := by
    cases tangent
    · simp only [InfinityAdditionAlgebra318.denominator,InfinityAdditionAlgebra318.slopeNumerator,
        Bool.false_eq_true,ite_false,map_sub]
      linear_combination ψ (InfinityAdditionAlgebra318.Y1 A B)*hl-
        ψ (InfinityAdditionAlgebra318.Y2 A B)*hl'+φ (slope A B)*(hu-ht)-hv+hw
    · simpa only [InfinityAdditionAlgebra318.denominator,InfinityAdditionAlgebra318.slopeNumerator,
        ite_true,map_add,map_mul,hm,InfinityAdditionAlgebra318.coeffMap,
        Algebra.ofId_apply,AlgHom.commutes] using htan
  have hh := BothFiniteTransition318.coordinates (algebraMap R S A) (algebraMap R S B)
    (φ (u1 A B)) (φ (v1 A B)) (φ (u2 A B)) (φ (v2 A B))
    (ψ (InfinityAdditionAlgebra318.X1 A B)) (ψ (InfinityAdditionAlgebra318.Y1 A B))
    (ψ (InfinityAdditionAlgebra318.X2 A B)) (ψ (InfinityAdditionAlgebra318.Y2 A B))
    (φ (slope A B)) (φ (intercept A B)) (φ (outU A B)) (φ (outV A B))
    (ψ (InfinityAdditionAlgebra318.denominator A B tangent))
    (ψ (InfinityAdditionAlgebra318.slopeNumerator A B tangent))
    hF hG hu hv ht hw hl hl' hs hq hU hV hDL
  simpa only [InfinityAdditionAlgebra318.numeratorY,InfinityAdditionAlgebra318.numeratorX,
    BothFiniteHomogeneous318.numeratorY,BothFiniteHomogeneous318.numeratorX,
    map_sub,map_add,map_mul,hm] using hh

end BothFiniteMaps318
