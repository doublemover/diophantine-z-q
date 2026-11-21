module
public import ActualTZLiteralNonlinearDistinct318
public import ActualTZIntegerGridMarker318
public import ActualTZCanonicalWrapFibres318
import all ActualTZLiteralTerminalLift318
public section
noncomputable section
namespace ActualTZRelabelPhysicalGrid318
open ActualTZLiteralTerminalLift318 ActualTZLiteralNonlinearDistinct318 ActualTZJointPolynomialForms318
open ActualTZSignedGridPushforward318 ActualTZIntegerGridMarker318
open ActualTZCanonicalWrapFibres318
open scoped BigOperators

variable {m a b j : ℕ}

abbrev D (m a j : ℕ) := Fintype.card (Axis m a j)

def finAxis (m a j : ℕ) : Axis m a j≃Fin (D m a j) := Fintype.equivFin _

def axisLength (M M₀ : ℕ) : Axis m a j→ℕ
  | .inl _=>M
  | .inr (.inl _)=>2*M+1
  | .inr (.inr _)=>M₀

def axisStart (M : ℕ) : Axis m a j→ℤ
  | .inl _=>1
  | .inr (.inl _)=>-(M:ℤ)
  | .inr (.inr _)=>1

def len (m a j M M₀ : ℕ) (i : Fin (D m a j)) : ℕ :=
  axisLength M M₀ ((finAxis m a j).symm i)

def start (m a j M : ℕ) (i : Fin (D m a j)) : ℤ :=
  axisStart M ((finAxis m a j).symm i)

theorem len_ge (M M₀ : ℕ) (hM : M≤M₀) : ∀ i,M≤len m a j M M₀ i := by
  intro i
  unfold len
  cases (finAxis m a j).symm i with
  | inl h => exact le_rfl
  | inr r =>
      cases r with
      | inl k => unfold axisLength; omega
      | inr c => exact hM

def py (P : Poly m a j) : MvPolynomial (Fin (D m a j)) ℤ :=
  MvPolynomial.rename (finAxis m a j) P

theorem py_eval (P : Poly m a j) (x : Fin (D m a j)→ℤ) :
    MvPolynomial.eval x (py P)=MvPolynomial.eval (x ∘ finAxis m a j) P :=
  MvPolynomial.eval_rename (finAxis m a j) x P

theorem py_degree (P : Poly m a j) : (py P).totalDegree≤P.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

theorem py_marker (S : Terminal m a b) (W : ℕ) (G : GoodTerminal S W) (hW : 0<W)
    (u v : Site a b j) (h : u≠v) :
    ∃ z : Fin (D m a j)→₀ℕ,∃ κ : ℤ,κ≠0 ∧
      ∀ n (r r' : ℤ),(py (physicalP S W n r r' u v)).coeff z=κ := by
  obtain ⟨z,κ,_,hκ,H⟩ := literal_marker G hW u v h
  refine ⟨z.mapDomain (finAxis m a j),κ,hκ,?_⟩
  intro n r r'
  rw [py,MvPolynomial.coeff_rename_mapDomain _ (finAxis m a j).injective]
  exact H n r r'

theorem physical_wrapped (S : Terminal m a b) (W n : ℕ) (x : ℤ)
    (u v : Site a b j) (z : Fin (D m a j)→ℤ) :
    let U := MvPolynomial.eval (z ∘ finAxis m a j) (siteP S u)
    let V := MvPolynomial.eval (z ∘ finAxis m a j) (siteP S v)
    MvPolynomial.eval z
      (py (physicalP S W n (quotient n (x+U)) (quotient n (x+V)) u v))=
      ((W:ℤ)*residue n (x+U)+(siteB S u:ℤ))-
      ((W:ℤ)*residue n (x+V)+(siteB S v:ℤ)) := by
  intro U V
  rw [py_eval,physical_eval S W n x,residue_split,residue_split] <;> ring

end ActualTZRelabelPhysicalGrid318
