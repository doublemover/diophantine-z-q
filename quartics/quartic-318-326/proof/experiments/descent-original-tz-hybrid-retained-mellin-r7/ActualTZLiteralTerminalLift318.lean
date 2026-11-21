module
public import ActualTZJointPolynomialForms318
public import ActualTZDegreeTwoAlgebra318
import all ActualTZJointPolynomialForms318
import all ActualTZTwoBlockCoefficients318
public section
noncomputable section
namespace ActualTZLiteralTerminalLift318
open scoped BigOperators
open ActualTZJointPolynomialForms318 ActualTZTwoBlockCoefficients318
open ActualTZDegreeTwoAlgebra318
open MvPolynomial (C X eval_X eval_C)

variable {m a b j : ℕ}
abbrev Axis (m a j : ℕ) := Fin m ⊕ ((Bool×Fin a) ⊕ Fin j)
abbrev Poly (m a j : ℕ) := MvPolynomial (Axis m a j) ℤ

/-- These are the literal row sites. Filtering marked corners and
inactive linear faces is separate and does not identify sites. -/
inductive Site (a b j : ℕ) where
  | marked (ω : Bits a)
  | linear (c : Fin j) (α : Fin a) (ω : Face a α)
  | nonlinear (c : Fin j) (α : Fin b) (ω : Bits a)

@[expose] def hX (i : Fin m) : Poly m a j := X (.inl i)
@[expose] def kX (t : Bool) (i : Fin a) : Poly m a j := X (.inr (.inl (t,i)))
@[expose] def cX (k : Fin j) : Poly m a j := X (.inr (.inr k))

def slopeP (S : Terminal m a b) (i : Fin a) : Poly m a j :=
  ∑ l : Fin m,C (S.slopeCoeff i l)*hX l

def nonlinearSlopeP (S : Terminal m a b) (i : Fin b) : Poly m a j :=
  C (S.nonlinearSlope0 i)+∑ l : Fin m,C (S.nonlinearSlopeCoeff i l)*hX l

def qP (Q : Quadratic m) : Poly m a j :=
  (C Q.constTerm + (∑ i : Fin m,C (Q.linear i)*hX i))+
    ∑ i : Fin m,∑ q : Fin m,C (qCoeff Q i q)*hX i*hX q

def markedP (S : Terminal m a b) (ω : Bits a) : Poly m a j :=
  -(∑ i : Fin a,slopeP S i*kX (ω i) i)

def coarseP (c : Fin j) (ω : Bits a) : Poly m a j :=
  cX c+∑ i : Fin a,kX (ω i) i

def siteP (S : Terminal m a b) : Site a b j→Poly m a j
  | .marked ω=>markedP S ω
  | .linear c i ω=>
    slopeP S i*cX c+qP (S.constTerm i)+
      ∑ u : {l : Fin a // l≠i},(slopeP S i-slopeP S u.val)*kX (ω u) u.val
  | .nonlinear c i ω=>
    C (S.quadratic i)*(coarseP c ω)^2+
      nonlinearSlopeP S i*coarseP c ω+qP (S.nonlinearConst i)+markedP S ω

def siteB (S : Terminal m a b) : Site a b j→ℕ
  | .marked _=>S.residueMarked
  | .linear _ i _=>S.residueLinear i
  | .nonlinear _ i _=>S.residueNonlinear i

private theorem hDeg (i : Fin m) : (hX (a:=a) (j:=j) i).totalDegree≤1 := varD _
private theorem kDeg (t : Bool) (i : Fin a) : (kX (m:=m) (j:=j) t i).totalDegree≤1 := varD _
private theorem cDeg (i : Fin j) : (cX (m:=m) (a:=a) i).totalDegree≤1 := varD _

private theorem slopeD (S : Terminal m a b) (i : Fin a) :
    (slopeP (j:=j) S i).totalDegree≤1 := by
  unfold slopeP
  exact sumD _ _ 1 (fun _ _=>scaleD _ _ 1 (hDeg _))

private theorem nonlinearSlopeD (S : Terminal m a b) (i : Fin b) :
    (nonlinearSlopeP (j:=j) S i).totalDegree≤1 := by
  unfold nonlinearSlopeP
  exact addD _ _ 1 (constD _ 1) (sumD _ _ 1 (fun _ _=>scaleD _ _ 1 (hDeg _)))

private theorem qD (Q : Quadratic m) : (qP (a:=a) (j:=j) Q).totalDegree≤2 := by
  unfold qP
  apply addD _ _ 2
  · apply addD _ _ 2 (constD _ 2)
    exact sumD _ _ 2 (fun _ _=>(scaleD _ _ 1 (hDeg _)).trans (by decide))
  · exact sumD _ _ 2 (fun _ _=>sumD _ _ 2 (fun _ _=>
      mulD _ _ 1 1 (scaleD _ _ 1 (hDeg _)) (hDeg _)))

private theorem markedD (S : Terminal m a b) (ω : Bits a) :
    (markedP (j:=j) S ω).totalDegree≤2 := by
  unfold markedP
  exact negD _ 2 (sumD _ _ 2 (fun _ _=>mulD _ _ 1 1 (slopeD _ _) (kDeg _ _)))

private theorem coarseD (c : Fin j) (ω : Bits a) : (coarseP (m:=m) c ω).totalDegree≤1 := by
  unfold coarseP
  exact addD _ _ 1 (cDeg _) (sumD _ _ 1 (fun _ _=>kDeg _ _))

theorem siteD (S : Terminal m a b) (u : Site a b j) : (siteP S u).totalDegree≤2 := by
  cases u with
  | marked ω => exact markedD S ω
  | linear c i ω =>
      apply addD _ _ 2 (addD _ _ 2 (mulD _ _ 1 1 (slopeD S i) (cDeg c)) (qD _))
      exact sumD _ _ 2 (fun u _=>mulD _ _ 1 1
        (subD _ _ 1 (slopeD S i) (slopeD S u.val)) (kDeg _ _))
  | nonlinear c i ω =>
      exact addD _ _ 2 (addD _ _ 2
        (addD _ _ 2 (scaleD _ _ 2 (sqD _ (coarseD c ω)))
          (mulD _ _ 1 1 (nonlinearSlopeD S i) (coarseD c ω))) (qD _)) (markedD S ω)

def rawGrid (h : Fin m→ℤ) (k : Bool→Fin a→ℤ) (c : Fin j→ℤ) : Axis m a j→ℤ
  | .inl l=>h l
  | .inr (.inl (t,i))=>k t i
  | .inr (.inr r)=>c r

/-- Evaluation at the same old finite sample: base h begins at 1,
the two independent k digits have signed starts −M, and coarse
copy c begins at 1. No sample or wrap is silently recentered. -/
theorem site_eval {M M₀ : ℕ} (S : Terminal m a b) (u : Site a b j)
    (h : Fin m→Fin M) (k : KPair a M) (c : Fin j→Fin M₀) :
    MvPolynomial.eval (rawGrid (baseDigits h) (kDigit k) (fun r=>(c r).val+1)) (siteP S u)=
      match u with
      | .marked ω=>markedOffset S (baseDigits h) k ω
      | .linear r α ω=>linearOffset S (baseDigits h) ((c r).val+1) k α ω
      | .nonlinear r α ω=>nonlinearOffset S (baseDigits h) ((c r).val+1) k α ω := by
  cases u <;> simp only [siteP,markedP,slopeP,nonlinearSlopeP,qP,coarseP,hX,kX,cX,
    map_sum,map_add,map_sub,map_mul,map_neg,map_pow,eval_C,eval_X,rawGrid,
    markedOffset,linearOffset,nonlinearOffset,slope,nonlinearSlope,
    ActualTZTwoBlockCoefficients318.eval,bilinear]

/-- Physical signed subtraction on one actual wrap with the same x.
The two arbitrary wrap constants are constants of this fixed cell. -/
def physicalP (S : Terminal m a b) (W n : ℕ) (r r' : ℤ)
    (u v : Site a b j) : Poly m a j :=
  C (W:ℤ)*(siteP S u-siteP S v-C ((r-r')*(n:ℤ)))+
    C ((siteB S u:ℤ)-(siteB S v:ℤ))

theorem physicalD (S : Terminal m a b) (W n : ℕ) (r r' : ℤ) (u v : Site a b j) :
    (physicalP S W n r r' u v).totalDegree≤2 := by
  unfold physicalP
  exact addD _ _ 2 (scaleD _ _ 2 (subD _ _ 2 (subD _ _ 2 (siteD S u) (siteD S v)) (constD _ 2)))
    (constD _ 2)

theorem physical_eval (S : Terminal m a b) (W n : ℕ) (x r r' : ℤ) (u v : Site a b j)
    (y : Axis m a j→ℤ) :
    MvPolynomial.eval y (physicalP S W n r r' u v)=
    ((W:ℤ)*(x+MvPolynomial.eval y (siteP S u)-r*(n:ℤ))+(siteB S u:ℤ))-
    ((W:ℤ)*(x+MvPolynomial.eval y (siteP S v)-r'*(n:ℤ))+(siteB S v:ℤ)) := by
  simp only [physicalP,map_add,map_sub,map_mul,eval_C]
  ring

end ActualTZLiteralTerminalLift318
