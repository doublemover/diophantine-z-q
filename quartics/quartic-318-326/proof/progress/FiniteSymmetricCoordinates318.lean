module
public import FinitePairSwap318
public import TangentOpenScheme318
public section
noncomputable section
namespace FiniteSymmetricCoordinates318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
lemma finite_formula (x y t z m:S) (h:m*(t-x)=z-y) :
    m^2-x-t=m^2-t-x ∧
      m*(x-(m^2-x-t))-y=m*(t-(m^2-t-x))-z := by
  constructor
  · ring
  · linear_combination -h

section Chord
open RelativeChordAlgebra318
theorem chord_coordinates (A B:R) (φ ψ:ChordRing A B →ₐ[R] S)
    (hu:φ (x1 A B)=ψ (x2 A B)) (hv:φ (y1 A B)=ψ (y2 A B))
    (ht:φ (x2 A B)=ψ (x1 A B)) (hw:φ (y2 A B)=ψ (y1 A B)) :
    φ (x3 A B)=ψ (x3 A B) ∧ φ (y3 A B)=ψ (y3 A B) := by
  have h1:=congrArg φ (slope_identity A B)
  have h2:=congrArg ψ (slope_identity A B)
  simp only [map_mul,map_sub,map_add,map_pow,AlgHom.commutes] at h1 h2
  rw [←hu,←ht,←hv,←hw] at h2
  have hunit:=(gap_unit A B).map φ
  simp only [map_sub,map_add] at hunit
  have hs:φ (slope A B)=ψ (slope A B) := by
    apply hunit.mul_right_cancel
    linear_combination h1+h2
  have hg:=congrArg φ (slope_identity A B)
  simp only [map_mul,map_sub] at hg
  simpa only [x3,y3,map_sub,map_mul,map_pow,←hu,←ht,←hv,←hw,←hs] using
    finite_formula (φ (x1 A B)) (φ (y1 A B)) (φ (x2 A B)) (φ (y2 A B)) (φ (slope A B)) hg
end Chord

section Tangent
open TangentOpenAlgebra318
theorem tangent_coordinates (A B:R) (φ ψ:TangentRing A B →ₐ[R] S)
    (hu:φ (x1 A B)=ψ (x2 A B)) (hv:φ (y1 A B)=ψ (y2 A B))
    (ht:φ (x2 A B)=ψ (x1 A B)) (hw:φ (y2 A B)=ψ (y1 A B)) :
    φ (x3 A B)=ψ (x3 A B) ∧ φ (y3 A B)=ψ (y3 A B) := by
  have h1:=congrArg φ (slope_sum A B)
  have h2:=congrArg ψ (slope_sum A B)
  simp only [map_mul,map_sub,map_add,map_pow,AlgHom.commutes] at h1 h2
  rw [←hu,←ht,←hv,←hw] at h2
  have hunit:=(sum_unit A B).map φ
  simp only [map_sub,map_add] at hunit
  have hs:φ (slope A B)=ψ (slope A B) := by
    apply hunit.mul_right_cancel
    linear_combination h1-h2
  have hg:=congrArg φ (slope_gap A B)
  simp only [map_mul,map_sub] at hg
  simpa only [x3,y3,map_sub,map_mul,map_pow,←hu,←ht,←hv,←hw,←hs] using
    finite_formula (φ (x1 A B)) (φ (y1 A B)) (φ (x2 A B)) (φ (y2 A B)) (φ (slope A B)) hg
end Tangent

end FiniteSymmetricCoordinates318
