module
public import Mathlib
import all Mathlib.Data.Fin.Tuple.Basic
public section
noncomputable section
namespace ActualTZReflectionIteration318
open scoped BigOperators

abbrev Vertex (a : ℕ) := Fin a→Bool

@[expose] def mirror {a : ℕ} {R : Type*} (j : Fin a) (b : Bool)
    (P : Vertex a→R) (ω : Vertex a) : R :=
  P (Function.update ω j b)

def splicePrefix {a m : ℕ} (bits : Vertex m) (ω : Vertex a) : Vertex a :=
  fun i => if h : i.val<m then bits ⟨i.val,h⟩ else ω i

private theorem next_update {a m : ℕ} (hm : m<a) (bits : Vertex m)
    (ω : Vertex a) (b : Bool) :
    Function.update (splicePrefix bits ω) ⟨m,hm⟩ b = splicePrefix (Fin.snoc bits b) ω := by
  funext i
  by_cases hi : i.val<m
  · have hd : i≠(⟨m,hm⟩ : Fin a) := by
      intro he
      have h := congrArg Fin.val he
      omega
    rw [Function.update_of_ne hd]
    simpa only [splicePrefix,dif_pos hi,dif_pos (Nat.lt_succ_of_lt hi)] using
      (Fin.snoc_castSucc b bits ⟨i.val,hi⟩).symm
  · by_cases he : i.val=m
    · have H : i=(⟨m,hm⟩ : Fin a) := Fin.ext he
      subst i
      rw [Function.update_self]
      simpa only [splicePrefix,dif_pos (Nat.lt_succ_self m)] using (Fin.snoc_last b bits).symm
    · have h' : ¬i.val<m+1 := by omega
      have hd : i≠(⟨m,hm⟩ : Fin a) := fun h => he (congrArg Fin.val h)
      rw [Function.update_of_ne hd]
      simp only [splicePrefix,dif_neg hi,dif_neg h']

private theorem prod_snoc {m : ℕ} (G : Vertex (m+1)→ℝ) :
    (∏ b : Bool, ∏ u : Vertex m, G (Fin.snoc u b)) = ∏ v : Vertex (m+1), G v := by
  let e := Fin.snocEquiv (fun _ : Fin (m+1) => Bool)
  calc
    _ = ∏ t : Bool×Vertex m, G (e t) := by rw [Fintype.prod_prod_type] <;> rfl
    _ = _ := e.prod_comp G

/-- Every one-axis Cauchy–Schwarz inequality is iterated once per
coordinate, keeping the full 2^m list of reflections as a product. -/
theorem prefix_bound {a : ℕ} {R : Type*} (M : (Vertex a→R)→ℝ)
    (hStep : ∀ (j : Fin a) (P : Vertex a→R),
      |M P|^2≤ |M (mirror j true P)| * |M (mirror j false P)|) :
    ∀ m≤a, ∀ P : Vertex a→R,
      |M P|^(2^m:ℕ)≤∏ u : Vertex m, |M (fun ω => P (splicePrefix u ω))| := by
  intro m
  induction m with
  | zero =>
      intro _ P
      simp only [pow_zero,pow_one,splicePrefix,Nat.not_lt_zero,dif_neg,
        Finset.prod_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin]
  | succ m ih =>
      intro hma P
      have hm : m<a := by omega
      let j : Fin a := ⟨m,hm⟩
      let C (b : Bool) := ∏ u : Vertex m, |M (fun ω => mirror j b P (splicePrefix u ω))|
      have hC (b : Bool) : 0≤C b := Finset.prod_nonneg fun _ _ => abs_nonneg _
      have hi (b : Bool) : |M (mirror j b P)|^(2^m:ℕ)≤C b := ih hm.le _
      have hp : (2^(m+1):ℕ)=2*2^m := by rw [pow_succ,mul_comm]
      rw [hp,pow_mul]
      calc
        _ ≤ (|M (mirror j true P)| * |M (mirror j false P)|)^(2^m:ℕ) :=
          pow_le_pow_left₀ (sq_nonneg _) (hStep j P) _
        _ ≤ C true*C false := by
          rw [mul_pow]
          exact mul_le_mul (hi _) (hi _) (pow_nonneg (abs_nonneg _) _) (hC _)
        _ = ∏ b : Bool, ∏ u : Vertex m, |M (fun ω => P (splicePrefix (Fin.snoc u b) ω))| := by
          rw [Fintype.prod_bool]
          simp only [C,mirror,j,next_update hm]
        _ = _ := prod_snoc _

/-- Once all axes are reflected the function family at each leaf is
the same single constant vertex-family, not a new average. -/
theorem full_bound {a : ℕ} {R : Type*} (M : (Vertex a→R)→ℝ)
    (hStep : ∀ (j : Fin a) (P : Vertex a→R),
      |M P|^2≤ |M (mirror j true P)| * |M (mirror j false P)|)
    (P : Vertex a→R) :
    |M P|^(2^a:ℕ)≤∏ u : Vertex a,|M (fun _ => P u)| := by
  have h (u ω : Vertex a) : splicePrefix u ω=u := by
    funext i
    simp only [splicePrefix,dif_pos i.isLt]
  simpa only [h] using prefix_bound M hStep a le_rfl P

end ActualTZReflectionIteration318
