module
public import OriginalAffinePointTail318
public section
noncomputable section
namespace OriginalOffsetEliminant318
open MvPolynomial TernaryQuadraticLineCover318
open OriginalAffineSieveEliminants318 OriginalQuadraticEliminant318
open OriginalWholeBasisEliminants318 OriginalEliminantLeadingTerm318
set_option maxHeartbeats 7000000

@[expose] def linear (a b : ℤ) : MvPolynomial (Fin 2) ℤ := C a*X 0+C b*X 1
@[expose] def offset (u v : Vector ℤ) (i j : ℤ) : Vector ℤ := i • u+j • v
@[expose] def eB (side : Bool) (κ t : ℤ) (u v d : Vector ℤ) : MvPolynomial (Fin 2) ℤ :=
  if side then C (2*κ*(t+2)*d.2.2)*linear u.2.2 v.2.2-
    C 2*(C d.2.1*linear u.1 v.1+C d.1*linear u.2.1 v.2.1)
  else C (2*κ*d.2.2)*linear u.2.2 v.2.2
@[expose] def eC (side : Bool) (κ t : ℤ) (u v : Vector ℤ) : MvPolynomial (Fin 2) ℤ :=
  if side then C (κ*(t+2))*(linear u.2.2 v.2.2)^2-C 2*linear u.1 v.1*linear u.2.1 v.2.1
  else C κ*(linear u.2.2 v.2.2)^2+C (2*t)
@[expose] def polynomial (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  let dx := normCoordinate coordinate d
  let x := linear (normCoordinate coordinate u) (normCoordinate coordinate v)
  eliminant (C (fA side κ t d)) (eB side κ t u v d) (eC side κ t u v)
    (C (dx^2)) (C (2*dx)*x) (x^2+C (t^2))

/-- This bivariate polynomial evaluates to the literal integer eliminant
on the actual remaining two coefficient coordinates, not an auxiliary form. -/
lemma actual_eval (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) (i j : ℤ) :
    eval ![i,j] (polynomial side coordinate κ t u v d)=
      normEliminant side κ t (offset u v i j) d coordinate := by
  cases side <;> cases coordinate <;>
    simp [polynomial,eB,eC,linear,eliminant,normCoordinate,normEliminant,fA,fB,fC,
      offset,LiteralAdjacentNormSlice318.P,LiteralAdjacentNormSlice318.P',zsmul_eq_mul] <;> ring

lemma linear_degree (a b : ℤ) : (linear a b).totalDegree≤1 := by
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_mul _ _).trans (by simp)) ((totalDegree_mul _ _).trans (by simp)))

lemma eB_degree (side : Bool) (κ t : ℤ) (u v d : Vector ℤ) :
    (eB side κ t u v d).totalDegree≤1 := by
  have hw := linear_degree u.2.2 v.2.2
  have hx := linear_degree u.1 v.1
  have hz := linear_degree u.2.1 v.2.1
  cases side
  · exact (totalDegree_mul _ _).trans (by simpa using hw)
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simpa using hw)
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C,zero_add]
      exact (totalDegree_add _ _).trans (max_le
        ((totalDegree_mul _ _).trans (by simpa using hx))
        ((totalDegree_mul _ _).trans (by simpa using hz)))

lemma eC_degree (side : Bool) (κ t : ℤ) (u v : Vector ℤ) :
    (eC side κ t u v).totalDegree≤2 := by
  have hw := linear_degree u.2.2 v.2.2
  have hx := linear_degree u.1 v.1
  have hz := linear_degree u.2.1 v.2.1
  have hs : ((linear u.2.2 v.2.2)^2).totalDegree≤2 :=
    (totalDegree_pow _ _).trans (by omega)
  cases side
  · exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_mul _ _).trans (by simpa using hs)) (by simp))
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simpa using hs)
    · have h0 := totalDegree_mul (C (2:ℤ)) (linear u.1 v.1)
      have h1 := totalDegree_mul (C (2:ℤ)*linear u.1 v.1) (linear u.2.1 v.2.1)
      simp only [totalDegree_C,zero_add] at h0
      exact h1.trans (by omega)

/-- Exact degree4 budget; bounding each term separately retains the
quadratic/linear/constant coefficient grading of the ACTUAL eliminant. -/
lemma degree (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) :
    (polynomial side coordinate κ t u v d).totalDegree≤4 := by
  let a : MvPolynomial (Fin 2) ℤ := C (fA side κ t d)
  let b := eB side κ t u v d
  let c := eC side κ t u v
  let D : MvPolynomial (Fin 2) ℤ := C ((normCoordinate coordinate d)^2)
  let x := linear (normCoordinate coordinate u) (normCoordinate coordinate v)
  let e := C (2*normCoordinate coordinate d)*x
  let f := x^2+C (t^2)
  have ha : a.totalDegree=0 := totalDegree_C _
  have hb : b.totalDegree≤1 := eB_degree side κ t u v d
  have hc : c.totalDegree≤2 := eC_degree side κ t u v
  have hD : D.totalDegree=0 := totalDegree_C _
  have hx : x.totalDegree≤1 := linear_degree _ _
  have he : e.totalDegree≤1 := (totalDegree_mul _ _).trans (by simpa using hx)
  have hf : f.totalDegree≤2 := (totalDegree_add _ _).trans (max_le
    ((totalDegree_pow _ _).trans (by omega)) (by simp))
  have h1 : (a*f-c*D).totalDegree≤2 := (totalDegree_sub _ _).trans (max_le
    ((totalDegree_mul _ _).trans (by omega)) ((totalDegree_mul _ _).trans (by omega)))
  have h2 : (a*e-b*D).totalDegree≤1 := (totalDegree_sub _ _).trans (max_le
    ((totalDegree_mul _ _).trans (by omega)) ((totalDegree_mul _ _).trans (by omega)))
  have h3 : (b*f-c*e).totalDegree≤3 := (totalDegree_sub _ _).trans (max_le
    ((totalDegree_mul _ _).trans (by omega)) ((totalDegree_mul _ _).trans (by omega)))
  change ((a*f-c*D)^2-(a*e-b*D)*(b*f-c*e)).totalDegree≤4
  exact (totalDegree_sub _ _).trans (max_le
    ((totalDegree_pow _ _).trans (by omega)) ((totalDegree_mul _ _).trans (by omega)))

@[expose] def axis (k : Fin 2) : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] Polynomial ℤ :=
  aeval (fun j => if j=k then Polynomial.X else 0)

lemma first_axis (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) :
    axis 0 (polynomial side coordinate κ t u v d)=lineEliminant side coordinate κ t u d := by
  cases side <;> cases coordinate <;>
    simp [axis,polynomial,eB,eC,linear,eliminant,normCoordinate,lineEliminant,
      scaledEliminant,fA] <;> ring

lemma second_axis (side coordinate : Bool) (κ t : ℤ) (u v d : Vector ℤ) :
    axis 1 (polynomial side coordinate κ t u v d)=lineEliminant side coordinate κ t v d := by
  cases side <;> cases coordinate <;>
    simp [axis,polynomial,eB,eC,linear,eliminant,normCoordinate,lineEliminant,
      scaledEliminant,fA] <;> ring

end OriginalOffsetEliminant318
