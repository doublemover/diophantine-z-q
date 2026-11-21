module
public import ActualTZSharedXDivisorCell318
public import ActualTZNestedWeightedError318
public import ActualTZOrdinaryCutoffEnvelope318
import all ActualTZLiteralPhysicalWrapCarrier318
import all ActualTZCanonicalWrapFibres318
import all ActualTZLiteralWrapClipping318
import all ActualTZSharedXDivisorCell318
public section
noncomputable section
namespace ActualTZSharedXDivisorAverage318
open scoped BigOperators
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZCanonicalWrapFibres318 ActualTZRetainedHorizon318
open ActualTZLiteralWrapClipping318 ActualTZSharedXDivisorCell318 ActualTZOneDivisorExpansion318

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable {S : ActualTZJointPolynomialForms318.Terminal m a b} (X : Context S I)

def mass (_ : X.OldGrid) : ℝ :=
  (ActualTZExactZeroIntegerGrid318.uniform
    (ActualTZRelabelPhysicalGrid318.len m a j X.M X.M₀):ℝ)

def avg (w : X.OldGrid→X.Keys→ℝ) (F : X.OldGrid→X.Keys→ℝ) : ℝ :=
  ∑ z : X.OldGrid,mass X z*(∑ r : X.Keys,w z r*F z r)

def original (α R : ℝ) (χ : ℝ→ℝ) : ℝ :=
  ∑ z : X.OldGrid,mass X z*((∑ x : Fin X.n,∏ i : I,
    weightedSquare α R χ (oldSite X z ((x.val:ℤ)+1) i).natAbs)/(X.n:ℝ))

def clipped (α R : ℝ) (χ : ℝ→ℝ) : ℝ :=
  avg X X.theta (oldCell X α R χ)

def gridMain (α R : ℝ) (χ : ℝ→ℝ) : ℝ :=
  avg X X.theta (mainCell X α R χ)

def retainedMass : ℝ :=
  ∑ z : X.OldGrid,mass X z*(∑ r : X.Keys,X.theta z r)

def lostBound : ℝ :=
  (Fintype.card X.Keys:ℝ)*((X.n:ℝ)^(-(1:ℝ)/4)+
     (Fintype.card (Context.Pair I):ℝ)*((ActualTZRelabelPhysicalGrid318.D m a j:ℝ)*((2:ℝ)/(X.M:ℝ))))

def intervalError (α R B : ℝ) : ℝ :=
  |(α*Real.log R)^Fintype.card I|*
    ((((⌊R⌋₊+1:ℕ):ℝ))^(2*Fintype.card I)*
      (B^(2*Fintype.card I)/(X.n:ℝ)^((3:ℝ)/4)))

theorem original_eq (α R : ℝ) (χ : ℝ→ℝ) :
    original X α R χ=avg X (wrapMass X.n X.width) (oldCell X α R χ) := by
  unfold original avg
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [←ActualTZCanonicalCellRange318.sum_fibres (X.code z)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  let F := ∑ x∈fibre (X.code z) r,∏ i : I,
     weightedSquare α R χ (oldSite X z ((x.val:ℤ)+1) i).natAbs
  change F/(X.n:ℝ)=((X.width z r:ℝ)/(X.n:ℝ))*(F/(X.width z r:ℝ))
  by_cases h : X.width z r=0
  · have he : fibre (X.code z) r=∅ := Finset.card_eq_zero.mp h
    have hF : F=0 := by simp only [F,he,Finset.sum_empty]
    simp only [hF,zero_div,mul_zero]
  · have hL : (X.width z r:ℝ)≠0 := by exact_mod_cast h
    have hN : (X.n:ℝ)≠0 := by exact_mod_cast X.npos.ne'
    field_simp [hN,hL] <;> ring

theorem oldCell_bound (α R : ℝ) (χ : ℝ→ℝ)
    (hR : 1<R) (hα : 0≤α) (hα' : α≤1) (hχ : ∀ t>1,χ t=0)
    (B : ℝ) (hB : ∀ t,|χ t|≤B) (z : X.OldGrid) (r : X.Keys) :
    |oldCell X α R χ z r|≤(Real.log R*(2*R*B)^2)^Fintype.card I := by
  have h0 : 0≤(Real.log R*(2*R*B)^2)^Fintype.card I :=
    pow_nonneg (mul_nonneg (Real.log_nonneg hR.le) (sq_nonneg _)) _
  by_cases h : X.width z r=0
  · simpa only [oldCell,h,Nat.cast_zero,div_zero,abs_zero] using h0
  · have hL : (0:ℝ)<X.width z r := by exact_mod_cast (Nat.pos_of_ne_zero h)
    rw [oldCell,abs_div,abs_of_nonneg hL.le,div_le_iff₀ hL]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _x∈fibre (X.code z) r,
          (Real.log R*(2*R*B)^2)^Fintype.card I := by
        apply Finset.sum_le_sum
        intro x _
        apply ActualTZOrdinaryCutoffEnvelope318.product_le α R χ _ _ hR hα hα' B hB hχ
        intro i
        apply Int.natAbs_pos.mpr
        have hr := (residue_range X.n X.npos ((x.val:ℤ)+1+X.off z i)).1
        have hW : (0:ℤ)<(primorial X.y:ℤ) := by exact_mod_cast primorial_pos X.y
        have hb : (0:ℤ)<(X.base i:ℤ) := by
          exact_mod_cast (show 0<X.base i by have h:= (X.base_unit i).1; omega)
        unfold oldSite
        exact (add_pos (mul_pos hW (zero_lt_one.trans_le hr)) hb).ne'
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul,Context.width]
        ring

theorem exact_boundary_error (α R : ℝ) (χ : ℝ→ℝ) (hR : 1<R) (hα : 0≤α) (hα' : α≤1)
    (hχ : ∀ t>1,χ t=0) (B : ℝ) (hB : ∀ t,|χ t|≤B) :
    |original X α R χ-clipped X α R χ|≤
      (Real.log R*(2*R*B)^2)^Fintype.card I*lostBound X := by
  let A := (Real.log R*(2*R*B)^2)^Fintype.card I
  let w := fun z r=>wrapMass X.n X.width z r-X.theta z r
  have hA : 0≤A := pow_nonneg (mul_nonneg (Real.log_nonneg hR.le) (sq_nonneg _)) _
  have hW (z : X.OldGrid) (r : X.Keys) : 0≤w z r := sub_nonneg.mpr (X.theta_le_original z r)
  have he : avg X (wrapMass X.n X.width) (oldCell X α R χ) -
      avg X X.theta (oldCell X α R χ)=avg X w (oldCell X α R χ) := by
    simp only [avg,w,sub_mul,Finset.sum_sub_distrib,mul_sub]
  have H := ActualTZNestedWeightedError318.sub_bound (mass X) w (oldCell X α R χ) (fun _ _=>0) A
    (fun _=>by unfold mass; positivity) hW
    (fun z r _=>by simpa only [sub_zero] using oldCell_bound X α R χ hR hα hα' hχ B hB z r)
  simp only [mul_zero,Finset.sum_const_zero,sub_zero] at H
  change |avg X w (oldCell X α R χ)|≤_ at H
  rw [original_eq,clipped,he]
  exact H.trans (mul_le_mul_of_nonneg_left (X.lost_mass_bound) hA)

theorem exact_interval_error (α R : ℝ) (χ : ℝ→ℝ) (hR : 1<R)
    (hχ : ∀ t>1,χ t=0) (B : ℝ) (hB : ∀ t,|χ t|≤B) :
    |clipped X α R χ-gridMain X α R χ|≤intervalError X α R B := by
  have hB0 : 0≤B := (abs_nonneg _).trans (hB 0)
  have h0 : 0≤intervalError X α R B := by
    unfold intervalError
    have hn : 0<(X.n:ℝ) := by exact_mod_cast X.npos
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg (by positivity) _)
      (div_nonneg (pow_nonneg hB0 _) (Real.rpow_pos_of_pos hn _).le))
  exact ActualTZNestedWeightedError318.unit_sub_bound (mass X) X.theta
    (oldCell X α R χ) (mainCell X α R χ) (intervalError X α R B)
    (fun _=>by unfold mass; positivity) (fun z r=>(X.theta_bounds z r).1) h0
    (fun z r h=>retained_error X α R χ z r h hR hχ B hB)
    X.mass_total_le

end ActualTZSharedXDivisorAverage318
