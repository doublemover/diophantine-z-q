module
public import ActualQuarticExceptionalNonzero318
public section
noncomputable section
namespace ActualQuarticOffsetPolynomial318
open MvPolynomial TernaryQuadraticLineCover318 OriginalOffsetEliminant318
open OriginalAffineSieveEliminants318 ActualAffineQuarticEliminant318
set_option maxHeartbeats 12000000

@[expose] def R2 (κ : ℤ) (d : Vector ℤ) : MvPolynomial (Fin 2) ℤ := C (r2 κ d)
@[expose] def R1 (κ : ℤ) (u v d : Vector ℤ) : MvPolynomial (Fin 2) ℤ :=
  C (2*κ*d.2.2)*linear u.2.2 v.2.2-C d.2.1*linear u.1 v.1-C d.1*linear u.2.1 v.2.1
@[expose] def R0 (κ t : ℤ) (u v : Vector ℤ) : MvPolynomial (Fin 2) ℤ :=
  C κ*(linear u.2.2 v.2.2)^2-linear u.1 v.1*linear u.2.1 v.2.1+C (t^2+2*t)
@[expose] def S (u v : Vector ℤ) : MvPolynomial (Fin 2) ℤ := linear u.1 v.1+linear u.2.1 v.2.1
@[expose] def E4 (κ : ℤ) (u v d : Vector ℤ) := (R2 κ d)^2
@[expose] def E3 (κ : ℤ) (u v d : Vector ℤ) := C 2*R2 κ d*R1 κ u v d
@[expose] def E2 (κ t : ℤ) (u v d : Vector ℤ) :=
  (R1 κ u v d)^2+C 2*R2 κ d*R0 κ t u v+C (t^2*(d.1+d.2.1)^2)
@[expose] def E1 (κ t : ℤ) (u v d : Vector ℤ) :=
  C 2*R1 κ u v d*R0 κ t u v+C (2*t^2*(d.1+d.2.1))*S u v
@[expose] def E0 (κ t : ℤ) (u v d : Vector ℤ) := (R0 κ t u v)^2+C (t^2)*(S u v)^2

@[expose] def polynomial (κ t : ℤ) (u v d : Vector ℤ) : MvPolynomial (Fin 2) ℤ :=
  ActualQuadraticQuarticEliminant318.eliminant
    (C (fA true κ t d)) (eB true κ t u v d) (eC true κ t u v)
    (E4 κ u v d) (E3 κ u v d) (E2 κ t u v d) (E1 κ t u v d) (E0 κ t u v d)

/-- Exact evaluation on the SAME two remaining basis coefficients. -/
lemma actual_eval (κ t : ℤ) (u v d : Vector ℤ) (i j : ℤ) :
    eval ![i,j] (polynomial κ t u v d)=actualEliminant κ t (offset u v i j) d := by
  simp [polynomial,ActualQuadraticQuarticEliminant318.eliminant,
    ActualQuadraticQuarticEliminant318.linearTerm,ActualQuadraticQuarticEliminant318.constantTerm,
    actualEliminant,R2,R1,R0,S,E4,E3,E2,E1,E0,eB,eC,linear,
    fA,fB,fC,LiteralAdjacentNormSlice318.P',k4,k3,k2,k1,k0,r2,r1,r0,offset,zsmul_eq_mul]
  ring

lemma at_origin (κ t : ℤ) (u v d : Vector ℤ) :
    eval ![0,0] (polynomial κ t u v d)=actualEliminant κ t 0 d := by
  simpa [offset] using actual_eval κ t u v d 0 0
lemma at_first (κ t : ℤ) (u v d : Vector ℤ) :
    eval ![1,0] (polynomial κ t u v d)=actualEliminant κ t u d := by
  simpa [offset] using actual_eval κ t u v d 1 0

end ActualQuarticOffsetPolynomial318
