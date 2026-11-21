module
public import ActualTZCanonicalCellRange318
public import ActualTZHybridCanonicalWrap318
public import ActualTZMultiSieveCell318
import all ActualTZHybridCanonicalWrap318
import all ActualTZMultiSieveCell318
import all ActualTZMultiLinearCRT318
import all ActualTZLiteralWrapClipping318
public section
noncomputable section
namespace ActualTZHybridMeanCell318
open scoped BigOperators
open ActualTZContiguousFinInterval318 ActualTZCanonicalWrapFibres318
open ActualTZHybridCanonicalWrap318
open ActualTZOneDivisorExpansion318 ActualTZMultiSieveCell318 ActualTZMultiLinearCRT318
open ActualTZLiteralWrapClipping318

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {a t s : ℕ} (X : Context a t s I)

theorem base_pos (i : I) : 0<X.base i := zero_lt_one.trans_le X.unit.1

theorem base_unit (i : I) : (primorial X.y).Coprime (X.base i) := X.unit.2.2

@[expose] def oldSite (z : X.G) (x : ℤ) (i : I) : ℤ :=
  ((primorial X.y):ℤ)*residue X.n (x+X.offset z i)+(X.base i:ℤ)

@[expose] def oldCell (α R : ℝ) (χ : ℝ→ℝ) (z : X.G) (r : X.Keys) : ℝ :=
  (∑ x∈fibre (X.code z) r,∏ i : I,
     weightedSquare α R χ (oldSite X z ((x.val:ℤ)+1) i).natAbs)/(X.size z r:ℝ)

@[expose] def mainCell (α R : ℝ) (χ : ℝ→ℝ) (z : X.G) (r : X.Keys) : ℝ :=
  finiteMain α R χ ((primorial X.y)) (X.wrapped z r) X.base

theorem oldSite_eq (z : X.G) (r : X.Keys) (x : Fin X.n)
    (hx : x∈fibre (X.code z) r) (i : I) :
    oldSite X z ((x.val:ℤ)+1) i=
      value ((primorial X.y)) (X.wrapped z r) X.base ((x.val:ℤ)+1) i := by
  have H := ActualTZCanonicalCellRange318.residue_eq X.hn (X.offset z)
    (X.offset_cap z) r x hx i
  unfold oldSite value physicalConst
  rw [H]
  unfold Context.wrapped
  ring

theorem exact_assay (α R : ℝ) (χ : ℝ→ℝ) (z : X.G) (r : X.Keys)
    (V : Window (fibre (X.code z) r)) :
    oldCell X α R χ z r=assay α R χ ((primorial X.y)) (X.wrapped z r) X.base
      V.width ((V.start:ℤ)+1) := by
  have hh := V.sum_eq (fun x : ℤ=>∏ i : I,
    weightedSquare α R χ (value ((primorial X.y)) (X.wrapped z r) X.base x i).natAbs)
  have hw : V.width=X.size z r := V.width_eq
  unfold oldCell assay
  rw [←hw]
  congr 1
  calc
    _ = ∑ x∈fibre (X.code z) r,∏ i : I,
           weightedSquare α R χ
             (value ((primorial X.y)) (X.wrapped z r) X.base ((x.val:ℤ)+1) i).natAbs := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.prod_congr rfl
      intro i _
      rw [oldSite_eq X z r x hx i]
    _ = _ := hh

theorem width_lower (z : X.G) (r : X.Keys) (ht : 0<X.θ z r) :
    (X.n:ℝ)^((3:ℝ)/4)≤(X.size z r:ℝ) := by
  exact (X.kept_cells z r ht).1

theorem value_pos (z : X.G) (r : X.Keys) (V : Window (fibre (X.code z) r))
    (t : ℕ) (ht : t<V.width) (i : I) :
    0<value ((primorial X.y)) (X.wrapped z r) X.base ((V.start:ℤ)+1+(t:ℤ)) i := by
  have hp := ActualTZCanonicalCellRange318.positive_site X.hn (X.offset z)
    (X.offset_cap z) r ((primorial X.y)) (primorial_pos _) X.base
      (base_pos X) V t ht i
  unfold value physicalConst Context.wrapped
  linarith only [hp]

/-- Original shared-x cyclic average, now exactly one non-wrapping
physical interval, with genuine old (not regulator-truncated) weights. -/
theorem retained_error (α R : ℝ) (χ : ℝ→ℝ) (z : X.G) (r : X.Keys)
    (ht : 0<X.θ z r) (hR : 1<R) (hχ : ∀ t>1,χ t=0)
    (B : ℝ) (hB : ∀ u,|χ u|≤B) :
    |oldCell X α R χ z r-mainCell X α R χ z r|≤
       |(α*Real.log R)^Fintype.card I| *
        ((((⌊R⌋₊+1:ℕ):ℝ))^(2*Fintype.card I)*
          (B^(2*Fintype.card I)/(X.n:ℝ)^((3:ℝ)/4))) := by
  obtain ⟨V⟩ := ActualTZCanonicalCellRange318.window_exists X.hn
    (X.offset z) (X.offset_cap z) r
  have hw : V.width=X.size z r := V.width_eq
  have hL := width_lower X z r ht
  have hpow : 0<(X.n:ℝ)^((3:ℝ)/4) :=
    Real.rpow_pos_of_pos (by exact_mod_cast X.hn) _
  have hl' : 0<V.width := by
    have h : (0:ℝ)<V.width := by rw [hw]; exact hpow.trans_le hL
    exact_mod_cast h
  have H := normalized_error α R χ ((primorial X.y)) (X.wrapped z r) X.base
    V.width ((V.start:ℤ)+1) hR hχ
      (fun t ht i=>(value_pos X z r V t ht i).ne') hl' (base_unit X) B hB
  rw [exact_assay X α R χ z r V,mainCell]
  apply H.trans
  rw [hw]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div_of_nonneg_left (pow_nonneg ((abs_nonneg _).trans (hB 0)) _) hpow hL

end ActualTZHybridMeanCell318
