module
public import ActualTZCanonicalCellRange318
public import ActualTZLiteralPhysicalWrapCarrier318
public import ActualTZMultiSieveCell318
import all ActualTZLiteralPhysicalWrapCarrier318
import all ActualTZMultiSieveCell318
import all ActualTZMultiLinearCRT318
import all ActualTZLiteralWrapClipping318
public section
noncomputable section
namespace ActualTZSharedXDivisorCell318
open scoped BigOperators
open ActualTZContiguousFinInterval318 ActualTZCanonicalWrapFibres318
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZLiteralTerminalLift318
open ActualTZOneDivisorExpansion318 ActualTZMultiSieveCell318 ActualTZMultiLinearCRT318
open ActualTZLiteralWrapClipping318

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable {S : ActualTZJointPolynomialForms318.Terminal m a b} (X : Context S I)

def oldSite (z : X.OldGrid) (x : ℤ) (i : I) : ℤ :=
  (primorial X.y:ℤ)*residue X.n (x+X.off z i)+(X.base i:ℤ)

def oldCell (α R : ℝ) (χ : ℝ→ℝ) (z : X.OldGrid) (r : X.Keys) : ℝ :=
  (∑ x∈fibre (X.code z) r,∏ i : I,
     weightedSquare α R χ (oldSite X z ((x.val:ℤ)+1) i).natAbs)/(X.width z r:ℝ)

def mainCell (α R : ℝ) (χ : ℝ→ℝ) (z : X.OldGrid) (r : X.Keys) : ℝ :=
  finiteMain α R χ (primorial X.y) (X.wrapped z r) X.base

theorem oldSite_eq (z : X.OldGrid) (r : X.Keys) (x : Fin X.n)
    (hx : x∈fibre (X.code z) r) (i : I) :
    oldSite X z ((x.val:ℤ)+1) i=
      value (primorial X.y) (X.wrapped z r) X.base ((x.val:ℤ)+1) i := by
  have H := ActualTZCanonicalCellRange318.residue_eq X.npos (X.off z)
    (X.offsetCap z) r x hx i
  unfold oldSite value physicalConst
  rw [H]
  unfold Context.wrapped
  ring

theorem exact_assay (α R : ℝ) (χ : ℝ→ℝ) (z : X.OldGrid) (r : X.Keys)
    (V : Window (fibre (X.code z) r)) :
    oldCell X α R χ z r=assay α R χ (primorial X.y) (X.wrapped z r) X.base
      V.width ((V.start:ℤ)+1) := by
  have hh := V.sum_eq (fun x : ℤ=>∏ i : I,
    weightedSquare α R χ (value (primorial X.y) (X.wrapped z r) X.base x i).natAbs)
  have hw : V.width=X.width z r := V.width_eq
  unfold oldCell assay
  rw [←hw]
  congr 1
  calc
    _ = ∑ x∈fibre (X.code z) r,∏ i : I,
           weightedSquare α R χ
             (value (primorial X.y) (X.wrapped z r) X.base ((x.val:ℤ)+1) i).natAbs := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.prod_congr rfl
      intro i _
      rw [oldSite_eq X z r x hx i]
    _ = _ := hh

theorem width_lower (z : X.OldGrid) (r : X.Keys) (ht : 0<X.theta z r) :
    (X.n:ℝ)^((3:ℝ)/4)≤(X.width z r:ℝ) := by
  by_contra h
  have h' := lt_of_not_ge h
  simp only [Context.theta,kept,if_pos (Or.inl h'),lt_irrefl] at ht

theorem value_pos (z : X.OldGrid) (r : X.Keys) (V : Window (fibre (X.code z) r))
    (t : ℕ) (ht : t<V.width) (i : I) :
    0<value (primorial X.y) (X.wrapped z r) X.base ((V.start:ℤ)+1+(t:ℤ)) i := by
  have hp := ActualTZCanonicalCellRange318.positive_site X.npos (X.off z)
    (X.offsetCap z) r (primorial X.y) (primorial_pos _) X.base
      (fun i=>(X.base_unit i).1) V t ht i
  unfold value physicalConst Context.wrapped
  linarith only [hp]

/-- Former shared-x cyclic average, now exactly one non-wrapping
physical interval, with genuine old (not regulator-truncated) weights. -/
theorem retained_error (α R : ℝ) (χ : ℝ→ℝ) (z : X.OldGrid) (r : X.Keys)
    (ht : 0<X.theta z r) (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (B : ℝ) (hB : ∀ u,|χ u|≤B) :
    |oldCell X α R χ z r-mainCell X α R χ z r|≤
       |(α*Real.log R)^Fintype.card I|*
        ((((⌊R⌋₊+1:ℕ):ℝ))^(2*Fintype.card I)*
          (B^(2*Fintype.card I)/(X.n:ℝ)^((3:ℝ)/4))) := by
  obtain ⟨V⟩ := ActualTZCanonicalCellRange318.window_exists X.npos
    (X.off z) (X.offsetCap z) r
  have hw : V.width=X.width z r := V.width_eq
  have hL := width_lower X z r ht
  have hpow : 0<(X.n:ℝ)^((3:ℝ)/4) :=
    Real.rpow_pos_of_pos (by exact_mod_cast X.npos) _
  have hl' : 0<V.width := by
    have h : (0:ℝ)<V.width := by rw [hw]; exact hpow.trans_le hL
    exact_mod_cast h
  have H := normalized_error α R χ (primorial X.y) (X.wrapped z r) X.base
    V.width ((V.start:ℤ)+1) hR hχ
      (fun t ht i=>(value_pos X z r V t ht i).ne') hl' (fun i=>(X.base_unit i).2.2) B hB
  rw [exact_assay X α R χ z r V,mainCell]
  apply H.trans
  rw [hw]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div_of_nonneg_left (pow_nonneg ((abs_nonneg _).trans (hB 0)) _) hpow hL

end ActualTZSharedXDivisorCell318
