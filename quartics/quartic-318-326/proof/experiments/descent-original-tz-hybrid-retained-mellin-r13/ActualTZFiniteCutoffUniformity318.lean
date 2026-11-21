module
public import Mathlib
public section
noncomputable section
namespace ActualTZFiniteCutoffUniformity318
open Filter
open scoped BigOperators Topology
variable {J : Type*} [Fintype J]

theorem joint_nat (P : J→ℕ→Prop)
    (h : ∀ j,∃ n : ℕ,∀ m≥n,P j m) :
    ∃ n : ℕ,∀ m≥n,∀ j,P j m := by
  classical
  choose L hL using h
  let n := Finset.univ.sup L
  refine ⟨n,?_⟩
  intro m hm j
  have H : L j≤n := Finset.le_sup (f:=L) (Finset.mem_univ j)
  exact hL j m (H.trans hm)

/-- A finite shape-index ledger: y0 before every y, the N threshold
after fixed y and ε but BEFORE the arbitrary actual mask. A single
nonnegative error e(y) tending to zero dominates all mask errors. -/
theorem finite_rate (P : J→ℕ→ℕ→ℝ→Prop) (e : J→ℕ→ℝ)
    (he : ∀ j,Tendsto (e j) atTop (𝓝 0)) (h0 : ∀ j y,0≤e j y)
    (hP : ∀ j y N {u v},u≤v→P j y N u→P j y N v)
    (h : ∀ j,∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,P j y N (e j y+ε)) :
    ∃ E : ℕ→ℝ,Tendsto E atTop (𝓝 0) ∧ (∀ y,0≤E y) ∧
      ∃ y₀ : ℕ,∀ y≥y₀,∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,∀ j,P j y N (E y+ε) := by
  classical
  let E (y : ℕ) := ∑ j : J,e j y
  have hSum (S : Finset J) : Tendsto (fun y=>∑ j∈S,e j y) atTop (𝓝 0) := by
    induction S using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))
    | @insert j S hj ih =>
        simpa only [Finset.sum_insert hj,zero_add] using (he j).add ih
  have hE : Tendsto E atTop (𝓝 0) := hSum Finset.univ
  have hEn (y : ℕ) : 0≤E y := Finset.sum_nonneg (fun j _=>h0 j y)
  have hEs (j : J) (y : ℕ) : e j y≤E y :=
    Finset.single_le_sum (fun k _=>h0 k y) (Finset.mem_univ j)
  choose L hL using h
  let y₀ := Finset.univ.sup L
  refine ⟨E,hE,hEn,y₀,?_⟩
  intro y hy ε hε
  apply joint_nat
  intro j
  have H : L j≤y₀ := Finset.le_sup (f:=L) (Finset.mem_univ j)
  obtain ⟨N₀,hN⟩ := hL j y (H.trans hy) ε hε
  exact ⟨N₀,fun N hN' => hP j y N (add_le_add_right (hEs j y) _) (hN N hN')⟩

end ActualTZFiniteCutoffUniformity318
