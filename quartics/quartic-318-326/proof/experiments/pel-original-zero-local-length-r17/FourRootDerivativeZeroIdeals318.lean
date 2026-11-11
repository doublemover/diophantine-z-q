module
public import FourRootProjectiveDifferentialCharts318
public import FourRootCoordinateOverlap318
public import Mathlib.RingTheory.Ideal.Span
public section
noncomputable section
namespace FourRootDerivativeZeroIdeals318
open FourRootCoordinateOverlap318
open scoped BigOperators
variable (b:Fin 4→ℂ)
/-- Candidate full finite derivative-zero ideal, in the ORIGINAL affine
ring. Its identification with the actual derivative map is supplied by
the genuine local-frame comparison, not by its support alone. -/
@[expose] def finiteGenerator:Affine b:=∏i:Fin 4,FourRootAffineCoordinateRing318.coordinate b (some i)
/-- The entire normalized infinity chart retains all three sign ratios
and u. Including s0=1 makes the overlap computation uniform. -/
@[expose] def infinityGenerator:Infinity b:=
  FourRootInfinityCoordinateRing318.coordinate b none*
    ∏i:Fin 4,FourRootInfinityCoordinateRing318.coordinate b (some i)
@[expose] def finiteIdeal:Ideal (Affine b):=Ideal.span {finiteGenerator b}
@[expose] def infinityIdeal:Ideal (Infinity b):=Ideal.span {infinityGenerator b}
@[expose] def overlapIdeal:Ideal (InfinityOverlap b):=
  (infinityIdeal b).map (algebraMap (Infinity b) (InfinityOverlap b))
lemma finite_generator_overlap:toInfinityBase b (finiteGenerator b)=
    (∏i:Fin 4,s b i)*(ui b)^4:=by
  simp only [finiteGenerator,map_prod,toInfinityBase_z,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
lemma infinity_generator_overlap:
    algebraMap (Infinity b) (InfinityOverlap b) (infinityGenerator b)=
      u b*∏i:Fin 4,s b i:=by
  simp only [infinityGenerator,map_mul,map_prod,u,s]
/-- The two whole affine ideals have the exact genuine unit ratio ui^5
on their actual common chart. Thus the gluing retains scheme-theoretic
multiplicity, not just the same set of branch points. -/
lemma generator_transition:toInfinityBase b (finiteGenerator b)=
    (ui b)^5*algebraMap (Infinity b) (InfinityOverlap b) (infinityGenerator b):=by
  rw [finite_generator_overlap,infinity_generator_overlap]
  calc
    (∏i:Fin 4,s b i)*(ui b)^4=
        (ui b)^4*(∏i:Fin 4,s b i)*(u b*ui b):=by rw [u_ui,mul_one];ring
    _=(ui b)^5*(u b*∏i:Fin 4,s b i):=by ring
lemma inverse_unit:IsUnit (ui b):=
  isUnit_iff_exists_inv.mpr ⟨u b,(mul_comm _ _).trans (u_ui b)⟩
theorem ideal_transition:
    (finiteIdeal b).map (toInfinityBase b).toRingHom=overlapIdeal b:=by
  rw [finiteIdeal,overlapIdeal,infinityIdeal,Ideal.map_span,Ideal.map_span,
    Set.image_singleton,Set.image_singleton,generator_transition,
    Ideal.span_singleton_mul_left_unit ((inverse_unit b).pow 5)]
end FourRootDerivativeZeroIdeals318
