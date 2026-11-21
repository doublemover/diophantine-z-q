module
public import ActualTZLiteralOrdinaryBound318
public import ActualTZOrdinaryCollisionCutoffRate318
public import ActualTZOrdinaryBoundaryDecay318
import all ActualTZSharedXDivisorAverage318
import all ActualTZLiteralOrdinaryCorrection318
public section
noncomputable section
namespace ActualTZLiteralContextBounds318
open scoped BigOperators
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZCanonicalWrapFibres318 ActualTZRelabelPhysicalGrid318
open ActualTZSharedXDivisorAverage318 ActualTZLiteralOrdinaryCorrection318
open ActualTZOrdinaryNumericDensity318 ActualTZPhysicalCorrectionBound318 ActualTZPhysicalEulerSplit318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318
open ActualTZOrdinaryBoundaryScalar318 ActualTZOrdinaryBoundaryDecay318
open ActualTZIntegerGridMarker318

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def keyCount (I : Type*) [Fintype I] (c : ℕ) : ℝ :=
  ((2*c+1)^Fintype.card I:ℕ)

@[expose] def charge (I : Type*) [Fintype I] [DecidableEq I] (m a j : ℕ) : ℝ :=
  (Fintype.card (Context.Pair I):ℝ)*((D m a j:ℝ)*2)

@[expose] def gridConstant (I : Type*) [Fintype I] [DecidableEq I] (m a j c : ℕ) : ℝ :=
  keyCount I c*((2:ℝ)^(D m a j)*charge I m a j)

theorem gridConstant_nonneg (c : ℕ) : 0≤gridConstant I m a j c := by
  unfold gridConstant keyCount charge
  positivity

variable {S : ActualTZJointPolynomialForms318.Terminal m a b}

def scales (X : Context (j:=j) S I) (y N c : ℕ) (d : ℝ) : Prop :=
  X.y=y ∧ X.N=N ∧ X.n=N/primorial y ∧ X.C=c ∧ d*(N:ℝ)^((1:ℝ)/2)≤X.M

def marker (X : Context (j:=j) S I) (A : ℝ) : Prop :=
  ∃ K : ℕ,0<K ∧ Real.log K≤A*(X.y:ℝ) ∧
    ∀ p,¬p∣K→∀ r q,reduced (p:=p) (X.pairPol r q)≠0

theorem keyCount_eq (X : Context (j:=j) S I) :
    (Fintype.card X.Keys:ℝ)=keyCount I X.C := by
  unfold keyCount
  exact_mod_cast card_wrap (I:=I) X.C

theorem lost_le (X : Context (j:=j) S I) (y N c : ℕ) (d : ℝ) (hd : 0<d)
    (h : scales X y N c d) :
    lostBound X≤(keyCount I c*(1+charge I m a j/d))*short (X.n:ℝ) := by
  obtain ⟨hy,hN,hn,hc,hM⟩ := h
  have hn₁ : (1:ℝ)≤X.n := by exact_mod_cast X.npos
  have hNL : X.n≤N := by rw [hn]; exact Nat.div_le_self _ _
  have hPow := Real.rpow_le_rpow (by positivity : 0≤(X.n:ℝ))
    (by exact_mod_cast hNL) (by norm_num : 0≤(1:ℝ)/2)
  have hSize := (mul_le_mul_of_nonneg_left hPow hd.le).trans hM
  have H := lost_scalar (X.n:ℝ) (X.M:ℝ) d (keyCount I c) (charge I m a j)
    hn₁ hd hSize (by unfold keyCount; positivity) (by unfold charge; positivity)
  unfold lostBound
  rw [keyCount_eq X,hc]
  simpa only [charge,short,neg_div,div_eq_mul_inv,one_mul,mul_assoc] using H

theorem three_boundary_terms (X : Context (j:=j) S I) (y N c : ℕ) (d ρ α B : ℝ)
    (hd : 0<d) (h : scales X y N c d) (hR : 1<(X.n:ℝ)^ρ) (hα : 0≤α) (hα' : α≤1) (hB : 0≤B) :
    envelope (Fintype.card I) ((X.n:ℝ)^ρ) B*lostBound X+
      intervalError X α ((X.n:ℝ)^ρ) B+lostBound X≤
      remainder (Fintype.card I) ρ B (keyCount I c*(1+charge I m a j/d)) (X.n:ℝ) := by
  have hn₁ : (1:ℝ)≤X.n := by exact_mod_cast X.npos
  exact total_le _ ρ B _ _ _ _ hn₁ hR (lost_le X y N c d hd h)
    (interval_scalar _ α _ B _ hn₁ hR hα hα' hB)

/-- This is only the equality of the quantitative arguments feeding
the numeric bound: exact old wheel, physical N, fixed wrap count,
and separate Euler P. -/
theorem correction_as (X : Context (j:=j) S I) (y N c P K : ℕ) (d : ℝ) (h : scales X y N c d) :
    correctionBudget X P K=
    let G := goodConst (Fintype.card I)*
        (∑ p∈offWheel (primorial y) P,(1/(p:ℝ))^2)+badConst (Fintype.card I)*extra (primorial y) P K
    (Real.exp G-1)+Real.exp G*(∑ p∈regular y N K,prefixWeight (badConst (Fintype.card I)) p*
      (gridConstant I m a j c*(1/(p:ℝ)+1/(X.M:ℝ)))) := by
  obtain ⟨hy,hN,_,hC,_⟩ := h
  unfold correctionBudget
  rw [hy,hN,keyCount_eq X,hC]
  have hh : keyCount I c*(Fintype.card (Context.Pair I):ℝ)*
      ((2:ℝ)^(D m a j)*(D m a j:ℝ)*(2:ℝ))=gridConstant I m a j c := by
    unfold gridConstant charge
    ring
  rw [hh]

end ActualTZLiteralContextBounds318
