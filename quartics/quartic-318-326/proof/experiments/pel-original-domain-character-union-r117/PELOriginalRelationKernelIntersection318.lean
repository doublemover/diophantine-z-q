module
public import ComplexProjectiveMarkerPoint318
public import PELOriginalHomogeneousRelationVanishing318
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section
namespace PELOriginalRelationKernelIntersection318
open PELOriginalCubicRelationIdeal318 PELOriginalHomogeneousRelationVanishing318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318
attribute [local instance] MvPolynomial.gradedAlgebra
variable (τ:ℂ)(hτ:0<τ.im)
/-- The SAME actual scalar cone-point kernel used for the genuine Proj
point, with no newly selected equations or prime completion. -/
@[expose] def pointKernel(q:Base τ):Ideal Equations:=
  (ComplexProjectiveMarkerPoint318.kernel (baseVector τ hτ 1 q)).toIdeal
lemma coordinate_nonzero(q:Base τ):∃r,baseVector τ hτ 1 q r≠0:=
  PELOriginalFiniteThetaGeneration318.finite_basepoint_free τ hτ 1 q
lemma homogeneous_point_mem(p:Equations)(n:ℕ)(hp:p.IsHomogeneous n)(q:Base τ):
    p∈pointKernel τ hτ q↔MvPolynomial.eval (baseVector τ hτ 1 q) p=0:=
  ComplexProjectiveMarkerPoint318.homogeneous_mem_iff _ (coordinate_nonzero τ hτ q) p n hp
/-- This equivalence holds for ALL polynomials, including mixed-degree
ones: each point kernel retains the formal degree marker. Scalar
pointwise evaluation of a mixed polynomial is not substituted. -/
theorem relation_iff_all_point_kernels(p:Equations):
    p∈relations τ hτ↔∀q:Base τ,p∈pointKernel τ hτ q:=by
  rw [relation_iff_components]
  constructor
  · intro h q
    apply (MvPolynomial.mem_iff_homogeneousComponent_mem
      (ComplexProjectiveMarkerPoint318.kernel (baseVector τ hτ 1 q)).isHomogeneous p).mpr
    intro n
    apply (homogeneous_point_mem τ hτ _ n (MvPolynomial.homogeneousComponent_mem n p) q).mpr
    exact (homogeneous_relation_iff τ hτ _ n (MvPolynomial.homogeneousComponent_mem n p)).mp (h n) q
  · intro h n
    apply (homogeneous_relation_iff τ hτ _ n (MvPolynomial.homogeneousComponent_mem n p)).mpr
    intro q
    apply (homogeneous_point_mem τ hτ _ n (MvPolynomial.homogeneousComponent_mem n p) q).mp
    exact (MvPolynomial.mem_iff_homogeneousComponent_mem
      (ComplexProjectiveMarkerPoint318.kernel (baseVector τ hτ 1 q)).isHomogeneous p).mp (h q) n

/-- The original relation ideal is precisely the intersection of the
actual relevant cone-point primes, not only contained in their radical. -/
theorem actual_kernel_intersection:
    relations τ hτ=⨅q:Base τ,pointKernel τ hτ q:=by
  ext p
  rw [Submodule.mem_iInf]
  exact relation_iff_all_point_kernels τ hτ p
instance pointKernel_prime(q:Base τ):(pointKernel τ hτ q).IsPrime:=
  ComplexProjectiveMarkerPoint318.kernel_isPrime _
theorem relations_radical:(relations τ hτ).IsRadical:=by
  rw [actual_kernel_intersection]
  exact Ideal.isRadical_iInf _ (fun q=>(pointKernel_prime τ hτ q).isRadical)
lemma radical_eq:(relations τ hτ).radical=relations τ hτ:=
  (relations_radical τ hτ).radical
end PELOriginalRelationKernelIntersection318
