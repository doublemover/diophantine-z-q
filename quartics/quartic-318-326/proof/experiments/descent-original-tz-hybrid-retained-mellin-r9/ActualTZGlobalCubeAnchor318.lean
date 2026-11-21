module
public import ActualTZFiniteBoxes318
public import ActualTZOldProductAverage318
public import ActualTZOneAxisLocalDual318
import all ActualTZFiniteBoxes318
public section
noncomputable section
namespace ActualTZGlobalCubeAnchor318
open scoped BigOperators
open ActualTZFiniteBoxes318 ActualPointedCyclicPairing318 ActualTZOldProductAverage318
open ActualTZOneAxisLocalDual318 (prob_swap)
variable {n a J : ℕ}

abbrev Ends (a J : ℕ) := (Fin a→Fin J)×(Fin a→Fin J)

@[expose] def zero (a : ℕ) : Vertex a := fun _=>false

/-- Toggle all axes on which the chosen anchor is true. -/
@[expose] def vertices (b : Vertex a) : Vertex a≃Vertex a where
  toFun w i := if b i then !(w i) else w i
  invFun w i := if b i then !(w i) else w i
  left_inv w := by funext i; cases H : b i <;> simp [H]
  right_inv w := by funext i; cases H : b i <;> simp [H]

/-- Swap the ordered endpoint pair on just those same axes. -/
@[expose] def endpoints (b : Vertex a) : Ends a J≃Ends a J where
  toFun z := (fun i=>if b i then z.2 i else z.1 i,fun i=>if b i then z.1 i else z.2 i)
  invFun z := (fun i=>if b i then z.2 i else z.1 i,fun i=>if b i then z.1 i else z.2 i)
  left_inv z := by
    apply Prod.ext <;> funext i <;> cases H : b i <;> simp [H]
  right_inv z := by
    apply Prod.ext <;> funext i <;> cases H : b i <;> simp [H]

@[expose] def off (q : ℕ) (z : Ends a J) (w : Vertex a) : ℤ :=
  ActualTZFiniteBoxes318.shift (fun _=>(q:ℤ)) z.1 z.2 w

theorem vertices_zero (b : Vertex a) : vertices b (zero a)=b := by
  funext i
  cases H : b i <;> simp [vertices,zero,H]

theorem off_zero (q : ℕ) (z : Ends a J) : off q z (zero a)=0 := by
  simp only [off,ActualTZFiniteBoxes318.shift,zero,Bool.false_eq_true,if_false,Finset.sum_const_zero]

theorem off_reanchor (q : ℕ) (z : Ends a J) (b w : Vertex a) :
    off q z (vertices b w)-off q z b=off q (endpoints b z) w := by
  unfold off ActualTZFiniteBoxes318.shift
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hv : vertices b w i=(if b i then !(w i) else w i) := rfl
  have h₁ : (endpoints b z).1 i=(if b i then z.2 i else z.1 i) := rfl
  have h₂ : (endpoints b z).2 i=(if b i then z.1 i else z.2 i) := rfl
  rw [hv,h₁,h₂]
  cases H : b i <;> cases T : w i <;> simp [H,T] <;> ring

@[expose] def mixedMean (hn : 0<n) (q : ℕ) (F : Vertex a→Fin n→ℝ) : ℝ :=
  prob (fun x=>prob (fun z : Ends a J=>∏ w : Vertex a,F w (move hn (off q z w) x)))

/-- Exact anchor change in the original global q[J] cube.
All q[J] difference multiplicities are unchanged. The only
x is translated once, depending on the old ordered pair. -/
theorem reanchor (hn : 0<n) (q : ℕ) (F : Vertex a→Fin n→ℝ) (b : Vertex a) :
    mixedMean (J:=J) hn q F=mixedMean (J:=J) hn q (F ∘ vertices b) := by
  unfold mixedMean
  rw [prob_swap,prob_swap (fun x z=>∏ w : Vertex a,(F ∘ vertices b) w (move hn (off q z w) x))]
  let H (z : Ends a J) := prob (fun x=>∏ w : Vertex a,(F ∘ vertices b) w (move hn (off q z w) x))
  calc
    _ = prob (H ∘ endpoints b) := by
      congr 1
      funext z
      let G (x : Fin n) := ∏ w : Vertex a,F w (move hn (off q z w) x)
      calc
        _ = prob (G ∘ translation hn (-off q z b)) := (permute _ G).symm
        _ = _ := by
          congr 1
          funext x
          simp only [G,H,Function.comp_apply,translation_apply,move_add]
          rw [←(vertices b).prod_comp (fun w=>F w (move hn (-off q z b+off q z w) x))]
          apply Finset.prod_congr rfl
          intro w _
          rw [add_comm (-off q z b), ←sub_eq_add_neg,off_reanchor]
    _ = _ := permute _ H

end ActualTZGlobalCubeAnchor318
