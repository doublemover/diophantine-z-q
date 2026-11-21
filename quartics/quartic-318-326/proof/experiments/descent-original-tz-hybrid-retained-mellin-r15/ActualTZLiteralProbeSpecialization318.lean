module
public import ActualTZFixedWrapMarkers318
public import ActualTZMomentCoefficientMarkers318
import all ActualTZLiteralTerminalLift318
import all ActualTZJointPolynomialForms318
import all ActualTZTwoBlockCoefficients318
public section
noncomputable section
namespace ActualTZLiteralProbeSpecialization318
open ActualTZLiteralTerminalLift318 ActualTZJointPolynomialForms318 ActualTZTwoBlockCoefficients318
open ActualTZFixedWrapMarkers318 ActualTZMomentCoefficientMarkers318
open scoped BigOperators
open MvPolynomial (eval_C eval_X)

variable {m a b j : ℕ}

def eOffset (S : Terminal m a b) (u : Site a b j)
    (h : Fin m→ℤ) (k : Bool→Fin a→ℤ) (c : Fin j→ℤ) : ℤ :=
  match u with
  | .marked ω=>-(∑ i : Fin a,slope S i h*k (ω i) i)
  | .linear t i ω=>slope S i h*c t+eval (S.constTerm i) h+
    ∑ v : {l : Fin a // l≠i},(slope S i h-slope S v.val h)*k (ω v) v.val
  | .nonlinear t i ω=>
    let v := c t+∑ l : Fin a,k (ω l) l
    S.quadratic i*v^2+nonlinearSlope S i h*v+eval (S.nonlinearConst i) h-
      ∑ l : Fin a,slope S l h*k (ω l) l

theorem eval_raw (S : Terminal m a b) (u : Site a b j)
    (h : Fin m→ℤ) (k : Bool→Fin a→ℤ) (c : Fin j→ℤ) :
    MvPolynomial.eval (rawGrid h k c) (siteP S u)=eOffset S u h k c := by
  cases u <;> simp only [siteP,markedP,slopeP,nonlinearSlopeP,qP,coarseP,hX,kX,cX,
    map_sum,map_add,map_sub,map_mul,map_neg,map_pow,eval_C,eval_X,rawGrid,eOffset,
    slope,nonlinearSlope,ActualTZTwoBlockCoefficients318.eval,bilinear,sub_eq_add_neg]

def basis {T : Type*} [DecidableEq T] (w : T) (v : ℤ) (t : T) : ℤ := if t=w then v else 0

@[simp] theorem basis_self {T : Type*} [DecidableEq T] (w : T) (v : ℤ) : basis w v w=v :=
  if_pos rfl

@[simp] theorem basis_other {T : Type*} [DecidableEq T] {u v : T} (h : u≠v) (x : ℤ) :
    basis v x u=0 := if_neg h

theorem slope_basis (S : Terminal m a b) (i : Fin a) (l : Fin m) (u : ℤ) :
    slope S i (basis l u)=S.slopeCoeff i l*u := by
  unfold slope
  rw [Finset.sum_eq_single l]
  · rw [basis_self]
  · intro t _ ht
    rw [basis_other ht,mul_zero]
  · intro h
    exact (h (Finset.mem_univ l)).elim

@[simp] theorem slope_zero (S : Terminal m a b) (i : Fin a) :
    slope S i (fun _=>0)=0 := by simp [slope]

@[simp] theorem nonlinearSlope_zero (S : Terminal m a b) (i : Fin b) :
    nonlinearSlope S i (fun _=>0)=S.nonlinearSlope0 i := by simp [nonlinearSlope]

theorem nonlinearSlope_basis (S : Terminal m a b) (i : Fin b) (l : Fin m) (u : ℤ) :
    nonlinearSlope S i (basis l u)=S.nonlinearSlope0 i+S.nonlinearSlopeCoeff i l*u := by
  unfold nonlinearSlope
  congr 1
  rw [Finset.sum_eq_single l]
  · rw [basis_self]
  · intro t _ ht
    rw [basis_other ht,mul_zero]
  · intro h
    exact (h (Finset.mem_univ l)).elim

def digitBasis (ε : Bool) (p : Fin a) (x : ℤ) (t : Bool) (i : Fin a) : ℤ :=
  basis (ε,p) x (t,i)

theorem sum_digitBasis (ω : Bits a) (ε : Bool) (p : Fin a) (x : ℤ) (g : Fin a→ℤ) :
    (∑ i : Fin a,g i*digitBasis ε p x (ω i) i)=g p*(if ω p=ε then x else 0) := by
  unfold digitBasis basis
  rw [Finset.sum_eq_single p]
  · simp only [Prod.mk.injEq,and_true]
  · intro i _ hi
    simp only [Prod.mk.injEq,hi,and_false,if_false,mul_zero]
  · intro h
    exact (h (Finset.mem_univ p)).elim

theorem sum_faceBasis (α : Fin a) (ω : Face a α) (ε : Bool)
    (p : {i : Fin a // i≠α}) (x : ℤ) (g : {i : Fin a // i≠α}→ℤ) :
    (∑ i,g i*digitBasis ε p.val x (ω i) i.val)=g p*(if ω p=ε then x else 0) := by
  unfold digitBasis basis
  rw [Finset.sum_eq_single p]
  · simp only [Prod.mk.injEq,and_true]
  · intro i _ hi
    have hne : i.val≠p.val := fun h => hi (Subtype.ext h)
    simp only [Prod.mk.injEq,hne,and_false,if_false,mul_zero]
  · intro h
    exact (h (Finset.mem_univ p)).elim

/-- If a differenced specialisation is nonconstant on any two raw
integer probe values, the literal physical pair consumes the same
marker infrastructure. No modular independence is assumed here. -/
theorem of_pair_values (S : Terminal m a b) (u v : Site a b j)
    (h h' : Fin m→ℤ) (k k' : Bool→Fin a→ℤ) (c c' : Fin j→ℤ)
    (H : eOffset S u h k c-eOffset S v h k c ≠
      eOffset S u h' k' c'-eOffset S v h' k' c') :
    Varies (siteP S u-siteP S v) := by
  exact ⟨rawGrid h k c,rawGrid h' k' c',by simpa only [map_sub,eval_raw] using H⟩

theorem of_coarse_quadratic (S : Terminal m a b) (u v : Site a b j) (c : Fin j) (D : ℤ)
    (hD : D≠0)
    (H : quadraticProbe (fun x=>eOffset S u (fun _=>0) (fun _ _=>0) (basis c x)-
      eOffset S v (fun _=>0) (fun _ _=>0) (basis c x))=2*D) :
    Varies (siteP S u-siteP S v) := by
  by_contra h
  have hh (x : ℤ) : eOffset S u (fun _=>0) (fun _ _=>0) (basis c x)-
      eOffset S v (fun _=>0) (fun _ _=>0) (basis c x)=
      eOffset S u (fun _=>0) (fun _ _=>0) (basis c 0)-
      eOffset S v (fun _=>0) (fun _ _=>0) (basis c 0) := by
    by_contra h'
    exact h (of_pair_values S u v _ _ _ _ _ _ h')
  unfold quadraticProbe at H
  rw [hh 1,hh (-1)] at H
  apply hD
  linarith

theorem of_mixed (S : Terminal m a b) (u v : Site a b j)
    (h : ℤ→ℤ→Fin m→ℤ) (k : ℤ→ℤ→Bool→Fin a→ℤ) (c : ℤ→ℤ→Fin j→ℤ)
    (D : ℤ) (hD : D≠0)
    (H : mixedProbe (fun x y=>eOffset S u (h x y) (k x y) (c x y)-
      eOffset S v (h x y) (k x y) (c x y))=D) :
    Varies (siteP S u-siteP S v) := by
  by_contra Hvar
  have hh (x y : ℤ) : eOffset S u (h x y) (k x y) (c x y)-eOffset S v (h x y) (k x y) (c x y)=
      eOffset S u (h 0 0) (k 0 0) (c 0 0)-eOffset S v (h 0 0) (k 0 0) (c 0 0) := by
    by_contra h'
    exact Hvar (of_pair_values S u v _ _ _ _ _ _ h')
  unfold mixedProbe at H
  rw [hh 1 1,hh 1 0,hh 0 1] at H
  apply hD
  linarith

end ActualTZLiteralProbeSpecialization318
