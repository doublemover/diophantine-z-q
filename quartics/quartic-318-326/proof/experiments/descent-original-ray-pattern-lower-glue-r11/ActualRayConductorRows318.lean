module
public import ActualRayPeriodicRectangle318
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Fin
public section
noncomputable section
namespace ActualRayConductorRows318

open scoped BigOperators
open ActualRayPeriodicRectangle318

/-- Canonical digit reconstruction, zero-based internally. A positive
physical base residue uses b.val+1 in both sides, not a different b. -/
def digits (W E : ℕ) (hW : 0<W) : Fin W × Fin E ≃ Fin (W*E) where
  toFun z := ⟨z.1.val+W*z.2.val,by
    calc
      z.1.val+W*z.2.val < W+W*z.2.val := Nat.add_lt_add_right z.1.isLt _
      _ = (z.2.val+1)*W := by ring
      _ ≤ E*W := Nat.mul_le_mul_right W (Nat.succ_le_of_lt z.2.isLt)
      _ = W*E := Nat.mul_comm _ _⟩
  invFun z := (⟨z.val%W,Nat.mod_lt _ hW⟩,
    ⟨z.val/W,(Nat.div_lt_iff_lt_mul hW).2 (by simpa only [Nat.mul_comm] using z.isLt)⟩)
  left_inv z := by
    apply Prod.ext
    · apply Fin.ext
      change (z.1.val+W*z.2.val)%W=z.1.val
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt z.1.isLt]
    · apply Fin.ext
      change (z.1.val+W*z.2.val)/W=z.2.val
      rw [Nat.add_mul_div_left _ _ hW,Nat.div_eq_of_lt z.1.isLt,zero_add]
  right_inv z := by
    apply Fin.ext
    exact Nat.mod_add_div z.val W

theorem digits_apply (W E : ℕ) (hW : 0<W) (b : Fin W) (x : Fin E) :
    (digits W E hW (b,x)).val=b.val+W*x.val := by rfl

theorem digits_apply_positive (W E : ℕ) (hW : 0<W) (b : Fin W) (x : Fin E) :
    (digits W E hW (b,x)).val+1=(b.val+1)+W*x.val := by
  rw [digits_apply]
  omega

theorem lcm_mul (W F : ℕ) : W*(W.lcm F/W)=W.lcm F := by
  rw [Nat.mul_comm W,Nat.div_mul_cancel (Nat.dvd_lcm_left W F)]

theorem divides_row_period (W F : ℕ) : F∣W*(W.lcm F/W) := by
  rw [lcm_mul]
  exact Nat.dvd_lcm_right W F

/-- Actual table of bounded periodic means: W is the original squarefree
wheel, F the fixed conductor, and no row label b or c is changed. F
need not divide W. -/
@[expose] def fold (g : ℕ→ℕ→ℝ) (F W b c : ℕ) (i j : ℕ) : ℝ :=
  g ((b+W*i)%F) ((c+W*j)%F)

theorem folded_period (g : ℕ→ℕ→ℝ) (F W b c E : ℕ) (h : F∣W*E) :
    Periods E (fold g F W b c) := by
  obtain ⟨k,hk⟩ := h
  constructor
  · intro i j
    unfold fold
    rw [Nat.mul_add,←Nat.add_assoc,hk,Nat.add_mul_mod_self_left]
  · intro i j
    unfold fold
    -- Do not accidentally reassociate the unchanged first row digit.
    have H : (c+W*(j+E))%F=(c+W*j)%F := by
      rw [Nat.mul_add,←Nat.add_assoc,hk,Nat.add_mul_mod_self_left]
    rw [H]

theorem fixed_conductor_row_error (g : ℕ→ℕ→ℝ) (F W b c : ℕ)
    (hW : 0<W) (hF : 0<F) (a z n m : ℕ) (A : ℝ)
    (hval : ∀ i j, 0≤g i j ∧ g i j≤A) :
    let E := W.lcm F/W
    |rectangle (fold g F W b c) a z n m-(n:ℝ)*(m:ℝ)*
        mean (fold g F W b c) E|≤(E:ℝ)*((n:ℝ)+(m:ℝ))*A := by
  let E := W.lcm F/W
  have hWE : W*E=W.lcm F := lcm_mul W F
  have hE : 0<E := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hp : 0<W.lcm F := Nat.lcm_pos hW hF
    rw [←hWE,hz,mul_zero] at hp
    exact (lt_irrefl 0) hp
  exact rectangle_mean_error (fold g F W b c) E hE
    (folded_period g F W b c E (divides_row_period W F)) a z n m A
    (fun i j => hval _ _)


/-- Finite evaluation of the all-means contribution. The positive
physical base residue is (b+1); the step residue is zero-based.
K is the given compatible-row mask (or weight), unchanged at every
inner x,j. Periods are evaluated at the fixed conductor F, not at W. -/
theorem folded_block_sum (g : ℕ→ℕ→ℝ) (F W E : ℕ) (hW : 0<W)
    (K : Fin W → Fin W → ℝ) :
    (∑ b : Fin W, ∑ c : Fin W, K b c *
      rectangle (fold g F W (b.val+1) c.val) 0 0 E E) =
    ∑ U : Fin (W*E), ∑ V : Fin (W*E),
      K ((digits W E hW).symm U).1 ((digits W E hW).symm V).1 *
        g ((U.val+1)%F) (V.val%F) := by
  let e := digits W E hW
  let G (U V : Fin (W*E)) :=
    K (e.symm U).1 (e.symm V).1*g ((U.val+1)%F) (V.val%F)
  have hLabels (b c : Fin W) (x y : Fin E) :
      G (e (b,x)) (e (c,y)) =
        K b c * fold g F W (b.val+1) c.val x.val y.val := by
    change K (e.symm (e (b,x))).1 (e.symm (e (c,y))).1 *
      g (((e (b,x)).val+1)%F) ((e (c,y)).val%F) = _
    simp only [Equiv.symm_apply_apply,e,fold]
    rw [digits_apply_positive,digits_apply]
  have hrect (b c : Fin W) :
      rectangle (fold g F W (b.val+1) c.val) 0 0 E E =
        ∑ x : Fin E, ∑ y : Fin E, fold g F W (b.val+1) c.val x.val y.val := by
    simp only [rectangle,line,Nat.zero_add]
    let H : ℕ → ℕ → ℝ := fold g F W (b.val+1) c.val
    change (∑ i ∈ Finset.range E, ∑ j ∈ Finset.range E, H i j) =
      ∑ x : Fin E, ∑ y : Fin E, H x.val y.val
    calc
      _ = ∑ i ∈ Finset.range E, ∑ y : Fin E, H i y.val := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Fin.sum_univ_eq_sum_range (H i) E).symm
      _ = _ := (Fin.sum_univ_eq_sum_range (fun i => ∑ y : Fin E, H i y.val) E).symm
  calc
    (∑ b : Fin W, ∑ c : Fin W, K b c *
       rectangle (fold g F W (b.val+1) c.val) 0 0 E E) =
        ∑ b : Fin W, ∑ c : Fin W, ∑ x : Fin E, ∑ y : Fin E,
          G (e (b,x)) (e (c,y)) := by
      simp only [hrect,Finset.mul_sum,hLabels]
    _ = ∑ b : Fin W, ∑ x : Fin E, ∑ c : Fin W, ∑ y : Fin E,
          G (e (b,x)) (e (c,y)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ z : Fin W × Fin E, ∑ z' : Fin W × Fin E, G (e z) (e z') := by
      simp only [Fintype.sum_prod_type]
    _ = _ := by
      change (∑ z : Fin W × Fin E, ∑ z' : Fin W × Fin E, G (e z) (e z')) =
        ∑ U : Fin (W*E), ∑ V : Fin (W*E), G U V
      calc
        _ = ∑ z : Fin W × Fin E, ∑ V : Fin (W*E), G (e z) V := by
          apply Finset.sum_congr rfl
          intro z _
          exact e.sum_comp (G (e z))
        _ = _ := e.sum_comp (fun U => ∑ V : Fin (W*E), G U V)

/-- Sum the error over only the occupied compatible rows. Independent
start coordinates are allowed for each row. This is a finite bound,
not an Artin or polynomial prime estimate. -/
theorem selected_row_error {ι : Type*} (S : Finset ι)
    (g : ℕ→ℕ→ℝ) (F W : ℕ) (hW : 0<W) (hF : 0<F)
    (b c a z : ι→ℕ) (n m : ℕ) (A : ℝ)
    (hval : ∀ i j, 0≤g i j ∧ g i j≤A) :
    let E := W.lcm F/W
    |(∑ j ∈ S, rectangle (fold g F W (b j) (c j)) (a j) (z j) n m)-
       (n:ℝ)*(m:ℝ)*(∑ j ∈ S, mean (fold g F W (b j) (c j)) E)|≤
      (S.card:ℝ)*((E:ℝ)*((n:ℝ)+(m:ℝ))*A) := by
  let E := W.lcm F/W
  let f (j : ι) := fold g F W (b j) (c j)
  let H (j : ι) := rectangle (f j) (a j) (z j) n m-(n:ℝ)*(m:ℝ)*mean (f j) E
  change |(∑ j ∈ S, rectangle (f j) (a j) (z j) n m)-
       (n:ℝ)*(m:ℝ)*(∑ j ∈ S, mean (f j) E)|≤_
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    |∑ j ∈ S, H j| ≤ ∑ j ∈ S, |H j| := Finset.abs_sum_le_sum_abs H S
    _ ≤ ∑ _j ∈ S, (E:ℝ)*((n:ℝ)+(m:ℝ))*A := by
      apply Finset.sum_le_sum
      intro j _
      exact fixed_conductor_row_error g F W (b j) (c j) hW hF (a j) (z j) n m A hval
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,E]

end ActualRayConductorRows318
