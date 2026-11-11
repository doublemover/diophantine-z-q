module
public import PELOriginalThetaHolomorphy318
public section
noncomputable section
namespace PELOriginalThetaQuasiperiods318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalSiegelMatrix318
open PELOriginalSiegelNormalization318 PELOriginalSymplecticCoordinates318
variable (τ:ℂ)
@[expose] def integerVector (m:Index):ComplexVectors:=![(m.1:ℂ),(m.2:ℂ)]
@[expose] def periodVector (n:Index):ComplexVectors:=fun j=>omega τ j 0*n.1+omega τ j 1*n.2
@[expose] def multiplier (n:Index) (z:ComplexVectors):ℂ:=
  Complex.exp (-(Real.pi:ℂ)*Complex.I*quadratic τ n-2*(Real.pi:ℂ)*Complex.I*linear n z)
lemma term_integer (k m:Index) (z:ComplexVectors):
    term τ k (z+integerVector m)=term τ k z:=by
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨k.1*m.1+k.2*m.2,?_⟩
  simp only [term,linear,integerVector,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring
lemma term_period (k n:Index) (z:ComplexVectors):
    term τ k (z+periodVector τ n)=multiplier τ n z*term τ (k+n) z:=by
  simp only [term,multiplier,←Complex.exp_add]
  congr 1
  simp [quadratic,linear,periodVector,omega]
  push_cast
  ring
lemma theta_integer (m:Index) (z:ComplexVectors):theta τ (z+integerVector m)=theta τ z:=
  tsum_congr (fun k=>term_integer τ k m z)
/-- Exact theta quasi-periodicity under every original b-period, by a
bijection of the full Z² summation lattice, not a finite truncation. -/
lemma theta_period (n:Index) (z:ComplexVectors):
    theta τ (z+periodVector τ n)=multiplier τ n z*theta τ z:=by
  unfold theta
  simp_rw [term_period]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight n).tsum_eq (fun k:Index=>term τ k z)
lemma original_standard_decomposition (p:Pair):
    standardPeriod τ p=integerVector (p.1 0,p.1 1)+periodVector τ (p.2 0,p.2 1):=by
  ext j
  fin_cases j <;> simp [standardPeriod,integerVector,periodVector]
  all_goals ring
/-- Quasi-periodicity on the EXACT original integral-order lattice after
its genuine complex linear normalization. Gauging this classical theta
multiplier to the existing Appell-Humbert factor is a separate step. -/
lemma theta_original_period (p:Pair) (z:ComplexVectors):
    theta τ (z+standardPeriod τ p)=multiplier τ (p.2 0,p.2 1) z*theta τ z:=by
  rw [original_standard_decomposition]
  have he:z+(integerVector (p.1 0,p.1 1)+periodVector τ (p.2 0,p.2 1))=
      (z+periodVector τ (p.2 0,p.2 1))+integerVector (p.1 0,p.1 1):=by abel
  rw [he,theta_integer,theta_period]
end PELOriginalThetaQuasiperiods318
