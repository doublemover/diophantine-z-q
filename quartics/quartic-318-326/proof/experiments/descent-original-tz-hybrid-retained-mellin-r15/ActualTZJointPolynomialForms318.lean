module
public import ActualTZTwoBlockCoefficients318
public section
noncomputable section
namespace ActualTZJointPolynomialForms318
open scoped BigOperators
open ActualTZTwoBlockCoefficients318

abbrev Bits (a : ℕ) := Fin a→Bool
abbrev Face (a : ℕ) (α : Fin a) := {i : Fin a // i≠α}→Bool
abbrev KPair (a M : ℕ) := (Bool→Fin a→Fin (2*M+1))
abbrev Sample (n m a M : ℕ) := (Fin m→Fin M) × Fin n × KPair a M
abbrev FineVars (m : ℕ) := Fin m→ℤ

/-- Final actual degree-two, one coarse variable PET system after
anchoring the distinguished node. All residue classes are ordinary.
Any bounded factor replaced by 1 is deleted from the relevant list. -/
structure Terminal (m a b : ℕ) where
  a_pos : 0<a
  slopeCoeff : Fin a→Fin m→ℤ
  constTerm : Fin a→Quadratic m
  quadratic : Fin b→ℤ
  nonlinearSlope0 : Fin b→ℤ
  nonlinearSlopeCoeff : Fin b→Fin m→ℤ
  nonlinearConst : Fin b→Quadratic m
  keepLinear : Fin a→Bool
  residueMarked : ℕ
  residueLinear : Fin a→ℕ
  residueNonlinear : Fin b→ℕ

def slope {m a b : ℕ} (S : Terminal m a b) (i : Fin a) (h : FineVars m) : ℤ :=
  ∑ l : Fin m,S.slopeCoeff i l*h l

def nonlinearSlope {m a b : ℕ} (S : Terminal m a b) (i : Fin b) (h : FineVars m) : ℤ :=
  S.nonlinearSlope0 i+∑ l : Fin m,S.nonlinearSlopeCoeff i l*h l

def FineDiff {m : ℕ} (P Q : Quadratic m) : Prop :=
  (∃ i : Fin m,P.linear i≠Q.linear i) ∨
  ∃ i j : Fin m,qCoeff P i j≠qCoeff Q i j

/-- Exact source conditions before selecting any complex estimate.
The nonlinear constants may differ by a genuine fine polynomial. -/
structure GoodTerminal {m a b : ℕ} (S : Terminal m a b) (W : ℕ) : Prop where
  unitMarked : 1≤S.residueMarked ∧ S.residueMarked≤W ∧ Nat.Coprime S.residueMarked W
  unitLinear : ∀ i,1≤S.residueLinear i ∧ S.residueLinear i≤W ∧ Nat.Coprime (S.residueLinear i) W
  unitNonlinear : ∀ i,1≤S.residueNonlinear i ∧ S.residueNonlinear i≤W ∧ Nat.Coprime (S.residueNonlinear i) W
  slopeNonzero : ∀ i,∃ l,S.slopeCoeff i l≠0
  slopeDistinct : ∀ i j,i≠j→∃ l,S.slopeCoeff i l≠S.slopeCoeff j l
  quadNonzero : ∀ i,S.quadratic i≠0
  nonlinearDistinct : ∀ i j,i≠j→S.quadratic i≠S.quadratic j ∨
    S.nonlinearSlope0 i≠S.nonlinearSlope0 j ∨
    (∃ l,S.nonlinearSlopeCoeff i l≠S.nonlinearSlopeCoeff j l) ∨
    FineDiff (S.nonlinearConst i) (S.nonlinearConst j)

def baseDigits {m M : ℕ} (h : Fin m→Fin M) : FineVars m :=
  fun i => ((h i).val:ℤ)+1

def kDigit {a M : ℕ} (k : KPair a M) (bit : Bool) (i : Fin a) : ℤ :=
  ((k bit i).val:ℤ)-(M:ℤ)

def markedOffset {m a b M : ℕ} (S : Terminal m a b) (h : FineVars m) (k : KPair a M)
    (ω : Bits a) : ℤ :=
  -(∑ i : Fin a,slope S i h*kDigit k (ω i) i)

def linearOffset {m a b M : ℕ} (S : Terminal m a b) (h : FineVars m) (c : ℤ)
    (k : KPair a M) (α : Fin a) (ω : Face a α) : ℤ :=
  slope S α h*c+eval (S.constTerm α) h+
    ∑ i : {i : Fin a // i≠α},(slope S α h-slope S i.val h)*kDigit k (ω i) i.val

def nonlinearOffset {m a b M : ℕ} (S : Terminal m a b) (h : FineVars m) (c : ℤ)
    (k : KPair a M) (α : Fin b) (ω : Bits a) : ℤ :=
  let t := c+∑ i : Fin a,kDigit k (ω i) i
  S.quadratic α*t^2+nonlinearSlope S α h*t+eval (S.nonlinearConst α) h+markedOffset S h k ω

end ActualTZJointPolynomialForms318
