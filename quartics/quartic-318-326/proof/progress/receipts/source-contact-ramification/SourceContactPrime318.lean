module
public import SourceOrderGaloisAction318
public import Mathlib.RingTheory.Polynomial.Ideal
public section
noncomputable section
namespace SourceContactPrime318
open ContactKummerOrder318 Polynomial
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (i:Fin 4)
/-- The literal finite contact ideal in the original Q[t] base. -/
@[expose] def prime:Ideal R:=Ideal.span {X-C (LinearContactSquareclass318.contacts i)}
theorem maximal:(prime i).IsMaximal:=by
  rw [prime,←Polynomial.ker_evalRingHom]
  apply RingHom.ker_isMaximal_of_surjective
  intro q
  exact ⟨C q,Polynomial.eval_C⟩
local instance contactPrime:(prime i).IsPrime:=(maximal i).isPrime

variable (c:Fin 4→ℚˣ) (Q:Ideal (SourceOrder c)) [Q.IsPrime]
    (hc:algebraMap R (SourceOrder c) (X-C (LinearContactSquareclass318.contacts i))∈Q)
include hc
/-- Every actual source prime containing the contact equation lies over
this exact base ideal, not just an unspecified residue characteristic. -/
theorem liesOver:Q.LiesOver (prime i):=by
  constructor
  apply (maximal i).eq_of_le (Ideal.IsPrime.ne_top (inferInstance:(Q.under R).IsPrime))
  exact Ideal.span_le.mpr (by
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact hc)

omit hc
/-- At the actual rational contact, all residue-field extensions of the
original finite source order are separable. -/
theorem residue_separable (c:Fin 4→ℚˣ) (i:Fin 4):Algebra.HasSeparableResidueFieldsAt R (SourceOrder c) (prime i):=by
  letI:Module.Finite R (SourceOrder c):=(source_finite_free c).1
  letI:Algebra.IsIntegral R (SourceOrder c):=Algebra.IsIntegral.of_finite R (SourceOrder c)
  letI:Algebra ℚ (prime i).ResidueField:=
    ((algebraMap R (prime i).ResidueField).comp (algebraMap ℚ R)).toAlgebra
  letI:CharZero (prime i).ResidueField:=Algebra.charZero_of_charZero ℚ (prime i).ResidueField
  infer_instance
end SourceContactPrime318
