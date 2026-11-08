module
public import InfinityKernelNeighborhoodPolynomial318
public import BothInfinityAlgebra318
public section
noncomputable section
namespace InfinityKernelNeighborhoodOutput318
open InfinityVietaAlgebra318 BothInfinityAlgebra318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R T:Type*} [CommRing R] [CommRing T]
lemma output_relation (A B:R) :
    c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B)*
      (outU A B-u1 A B-u2 A B)=
    d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) (intercept A B) := by
  have h:=Units.mul_inv (cubicUnit A B)
  have hc:(↑(cubicUnit A B):OutputRing A B)=
    c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) :=
      (cubic_coefficient_unit A B).unit_spec
  rw [hc] at h
  rw [outU]
  linear_combination d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B)
    (slope A B) (intercept A B)*h

/-- The exact regular both-infinity output isolates infinity on the explicit
G,H neighborhood. This retains arbitrary nilpotent coefficient directions. -/
theorem input_zero (A B:R) (φ:OutputRing A B →+* T)
    (hu:φ (u2 A B)=φ (u1 A B)) (hv:φ (v2 A B)=φ (v1 A B))
    (ho:φ (outU A B)=-φ (u1 A B))
    (hg:IsUnit (InfinityKernelNeighborhoodPolynomial318.G
      (φ (algebraMap R (OutputRing A B) B)) (φ (v1 A B))))
    (hh:IsUnit (InfinityKernelNeighborhoodPolynomial318.H
      (φ (algebraMap R (OutputRing A B) A)) (φ (algebraMap R (OutputRing A B) B))
      (φ (u1 A B)) (φ (v1 A B)))) : φ (u1 A B)=0 ∧ φ (v1 A B)=0 := by
  have he:equation (φ (algebraMap R (OutputRing A B) A))
      (φ (algebraMap R (OutputRing A B) B)) (φ (u1 A B)) (φ (v1 A B))=0 := by
    simpa only [equation,map_sub,map_mul,map_pow,map_zero] using congrArg φ (mapped_first A B)
  have ha:φ (slope A B)*InfinityKernelNeighborhoodPolynomial318.Q
      (φ (algebraMap R (OutputRing A B) A)) (φ (algebraMap R (OutputRing A B) B))
      (φ (u1 A B)) (φ (v1 A B))=
    InfinityKernelNeighborhoodPolynomial318.S (φ (algebraMap R (OutputRing A B) A))
      (φ (u1 A B)) (φ (v1 A B)) := by
    simpa only [InfinityKernelNeighborhoodPolynomial318.Q,InfinityKernelNeighborhoodPolynomial318.S,
      q,s,map_sub,map_add,map_mul,map_pow,map_one,hu,hv] using congrArg φ (slope_relation A B)
  have hb:φ (intercept A B)=φ (v1 A B)-φ (slope A B)*φ (u1 A B) := by
    simp only [intercept,map_sub,map_mul]
  have hout:c (φ (algebraMap R (OutputRing A B) A)) (φ (algebraMap R (OutputRing A B) B))
      (φ (slope A B))*(-φ (u1 A B)-φ (u1 A B)-φ (u1 A B))=
    d (φ (algebraMap R (OutputRing A B) A)) (φ (algebraMap R (OutputRing A B) B))
      (φ (slope A B)) (φ (intercept A B)) := by
    simpa only [c,d,map_sub,map_add,map_mul,map_pow,map_one,map_ofNat,ho,hu] using congrArg φ (output_relation A B)
  exact InfinityKernelNeighborhoodPolynomial318.zero_of_equation _ _ _ _ he
    (InfinityKernelNeighborhoodPolynomial318.F_zero_of_output _ _ _ _ _ _ ha hb hout) hg hh
end InfinityKernelNeighborhoodOutput318
