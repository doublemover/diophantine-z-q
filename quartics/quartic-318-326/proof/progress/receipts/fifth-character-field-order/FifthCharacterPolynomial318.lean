module
public import SourceCharacterFields318
public import ContactKummerOrder318
public section
noncomputable section
namespace FifthCharacterPolynomial318
open Polynomial SourceTwistArithmetic318
set_option maxHeartbeats 700000
@[expose] def quartic : ℚ[X] := C (-74088)*X*(X-C 32)*(X-C 76832)*(X+C 343)
@[expose] def reciprocal : ℚ[X] := C (-74088)*(1-C 32*X)*(1-C 76832*X)*(1+C 343*X)
theorem full_product :
    (∏ i:Fin 4, ContactKummerOrder318.coefficient units i)=quartic := by
  apply Polynomial.funext
  intro x
  norm_num [ContactKummerOrder318.coefficient,units,constants,
    LinearContactSquareclass318.contacts,Fin.prod_univ_succ,quartic]
  ring
end FifthCharacterPolynomial318
