module
public import QuaternionicTraceZeroFixedLine318
public import PELInertiaRationalConjugacy318
public section
noncomputable section
namespace PELRealRationalProportionality318
open QuaternionicRealPeriod318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
set_option maxHeartbeats 1500000

theorem representation_rat_smul (q : ℚ) (x : B) :
    representation (q • x)=(q:ℝ) • representation x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [representation,matrix] <;> push_cast <;> ring

/-- Proportionality in the real splitting is descended to an ACTUAL
rational scalar, using a nonzero original rational quaternion coordinate. -/
theorem rational_proportional (x y : B) (hx : x≠0) (hy : y.imI≠0) (r : ℝ)
    (h : representation x=r • representation y) : ∃ q : ℚ,q≠0 ∧ x=q • y := by
  have h01 := congrArg (fun M : RealMatrices => M 0 1) h
  have h10 := congrArg (fun M : RealMatrices => M 1 0) h
  change -alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ)=
    r*(-alpha*(y.imI:ℝ)+alpha*beta*(y.imK:ℝ)) at h01
  change alpha*(x.imI:ℝ)+alpha*beta*(x.imK:ℝ)=
    r*(alpha*(y.imI:ℝ)+alpha*beta*(y.imK:ℝ)) at h10
  have hh : (2*alpha)*((x.imI:ℝ)-r*(y.imI:ℝ))=0 := by
    linear_combination h10-h01
  have hi : (x.imI:ℝ)=r*(y.imI:ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) alpha_pos.ne'))
  let q : ℚ := x.imI/y.imI
  have hyR : (y.imI:ℝ)≠0 := by exact_mod_cast hy
  have hq : (q:ℝ)=r := by
    change ((x.imI/y.imI:ℚ):ℝ)=r
    push_cast
    exact (div_eq_iff hyR).mpr hi
  have hxy : x=q • y := by
    apply representation_injective
    rw [representation_rat_smul,hq]
    exact h
  refine ⟨q,?_,hxy⟩
  intro hzero
  apply hx
  rw [hxy,hzero,zero_smul]

theorem trace_mul_comm (x y : B) : reducedTrace (x*y)=reducedTrace (y*x) := by
  simp only [reducedTrace]
  change 2*((x*y).re)=2*((y*x).re)
  simp
  <;> ring

theorem trace_conjugation (u : Bˣ) (x : B) :
    reducedTrace ((u:B)*x*(↑u⁻¹:B))=reducedTrace x := by
  rw [trace_mul_comm,←mul_assoc,Units.inv_val,one_mul]

theorem inertia_coordinate_ne_zero (i : Fin 5) :
    (PELInertiaNormalizerData318.element i).imI≠0 := by
  fin_cases i <;> norm_num [PELInertiaNormalizerData318.element,
    PELInertiaNormalizerData318.coefficients,PELPrincipalOrderCoordinates318.embed]
end PELRealRationalProportionality318
