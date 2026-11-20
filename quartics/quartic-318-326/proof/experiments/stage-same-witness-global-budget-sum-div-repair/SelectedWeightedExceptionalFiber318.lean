module
public import SelectedExceptionalDualEffectivity318
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public section
noncomputable section
open scoped BigOperators
open SelectedExceptionalDualEffectivity318

namespace SelectedWeightedExceptionalFiber318

/-- A positive intersection of distinct components. -/
abbrev edge {ι : Type*} (Q : ι → ι → ℝ) (i j : ι) : Prop :=
  i ≠ j ∧ 0 < Q i j

section Cut
variable {ι : Type*} [Fintype ι]

/-- Connectivity through the full fiber gives a path in the selected
exceptional block up to, but not including, its first genuine exit. -/
theorem first_exit (P : ι → Prop) (A : ι → ι → Prop)
    {i k : ι} (h : Relation.ReflTransGen A i k) (hi : P i) (hk : ¬P k) :
    ∃ j : Subtype P,
      Relation.ReflTransGen (fun u v : Subtype P => A u.1 v.1) ⟨i,hi⟩ j ∧
      ∃ t : ι, ¬P t ∧ A j.1 t := by
  classical
  revert hi
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun v _ => ∀ hv : P v, ∃ j : Subtype P,
      Relation.ReflTransGen (fun u v : Subtype P => A u.1 v.1) ⟨v,hv⟩ j ∧
      ∃ t : ι, ¬P t ∧ A j.1 t) h ?_ ?_
  · intro h'
    exact (hk h').elim
  · intro v w hvw _ ih hv
    by_cases hw : P w
    · obtain ⟨j,hj,t,ht,hjt⟩ := ih hw
      exact ⟨j,hj.head hvw,t,ht,hjt⟩
    · exact ⟨⟨v,hv⟩,Relation.ReflTransGen.refl,w,hw,hvw⟩

/-- Weight of the explicitly nonexceptional part of the special fiber
against the selected component, not a residual divisor of M/dj. -/
@[expose] def cutWeight (P : ι → Prop) [DecidablePred P]
    (Q : ι → ι → ℝ) (m : ι → ℝ) (i : Subtype P) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => ¬P j), Q i.1 j * m j

theorem cut_nonneg (P : ι → Prop) [DecidablePred P] (Q : ι → ι → ℝ) (m : ι → ℝ)
    (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j) (weights : ∀ i, 0 < m i) :
    ∀ i : Subtype P, 0 ≤ cutWeight P Q m i := by
  intro i
  unfold cutWeight
  apply Finset.sum_nonneg
  intro j hj
  have h' : ¬P j := (Finset.mem_filter.mp hj).2
  have hne : (i:ι) ≠ j := fun h => h' (h ▸ i.2)
  exact mul_nonneg (offDiag i.1 j hne) (weights j).le

theorem cut_pos (P : ι → Prop) [DecidablePred P] (Q : ι → ι → ℝ) (m : ι → ℝ)
    (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j) (weights : ∀ i, 0 < m i)
    (i : Subtype P) (j : ι) (hj : ¬P j) (hij : edge Q i.1 j) :
    0 < cutWeight P Q m i := by
  have hle : Q i.1 j * m j ≤ cutWeight P Q m i := by
    unfold cutWeight
    apply Finset.single_le_sum
    · intro t ht
      have ht' : ¬P t := (Finset.mem_filter.mp ht).2
      have hne : (i:ι) ≠ t := fun h => ht' (h ▸ i.2)
      exact mul_nonneg (offDiag i.1 t hne) (weights t).le
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  exact (mul_pos hij.2 (weights j)).trans_le hle

/-- A single true noncontracted component in a connected full fiber is
enough. The exiting edge, not merely existence elsewhere, supplies the
strict positive cut term in each exceptional block. -/
theorem boundary_reachable (P : ι → Prop) [DecidablePred P]
    (Q : ι → ι → ℝ) (m : ι → ℝ)
    (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j) (weights : ∀ i, 0 < m i)
    (k : ι) (hk : ¬P k)
    (connected : ∀ i : Subtype P, Relation.ReflTransGen (edge Q) i.1 k) :
    ∀ i : Subtype P, ∃ j : Subtype P,
      Relation.ReflTransGen (fun u v : Subtype P => edge Q u.1 v.1) i j ∧
      0 < cutWeight P Q m j := by
  intro i
  obtain ⟨j,hj,t,ht,hExit⟩ := first_exit P (edge Q) (connected i) i.2 hk
  exact ⟨j,hj,cut_pos P Q m offDiag weights j t ht hExit⟩

end Cut

section Quadratic
variable {ι : Type*} [Fintype ι]

@[expose] def edgeEnergy (Q : ι → ι → ℝ) (m z : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i j * m i * m j * (z i-z j)^2

@[expose] def cutEnergy (b m z : ι → ℝ) : ℝ :=
  ∑ i, b i * m i * (z i)^2

/-- Full double sums count edges twice. The half in this literal
weighted Laplacian identity prevents an extra intersection factor. -/
theorem weighted_identity (Q : ι → ι → ℝ) (m b z : ι → ℝ)
    (symm : ∀ i j, Q i j = Q j i)
    (row : ∀ i, (∑ j, Q i j * m j) = -b i) :
    pairing Q (fun i => m i*z i) = -(edgeEnergy Q m z)/2 - cutEnergy b m z := by
  let L := ∑ i, ∑ j, Q i j * m i * m j * (z i)^2
  let R := ∑ i, ∑ j, Q i j * m i * m j * (z j)^2
  let C := ∑ i, ∑ j, Q i j * m i * m j * z i * z j
  have hL : L = -cutEnergy b m z := by
    calc
      L = ∑ i, (m i * (z i)^2)*(∑ j, Q i j*m j) := by
        unfold L
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -cutEnergy b m z := by
        unfold cutEnergy
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [row i]
        ring
  have hR : R = L := by
    calc
      R = ∑ i, ∑ j, Q j i * m j * m i * (z i)^2 := by
        unfold R
        exact Finset.sum_comm
      _ = L := by
        unfold L
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [symm j i]
        ring
  have hC : C = pairing Q (fun i => m i*z i) := by
    unfold C pairing
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hE : edgeEnergy Q m z = L + R - 2*C := by
    calc
      edgeEnergy Q m z = ∑ i, ∑ j,
          Q i j * m i * m j * (z i)^2 + Q i j * m i * m j * (z j)^2 -
          2*(Q i j * m i * m j * z i * z j) := by
        unfold edgeEnergy
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = L + R - 2*C := by
        simp only [L,R,C,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]
  linarith only [hL,hR,hC,hE]

private theorem equal_along_path (Q : ι → ι → ℝ) (z : ι → ℝ)
    (equal_step : ∀ i j, edge Q i j → z i = z j)
    {i j : ι} (h : Relation.ReflTransGen (edge Q) i j) : z i = z j := by
  induction h with
  | refl => rfl
  | tail _ hStep ih => exact ih.trans (equal_step _ _ hStep)

/-- Each connected exceptional component must touch the complement.
A component of the graph with no such edge would retain a zero mode. -/
theorem negative_definite (Q : ι → ι → ℝ) (m b : ι → ℝ)
    (symm : ∀ i j, Q i j = Q j i) (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (weights : ∀ i, 0 < m i) (cut : ∀ i, 0 ≤ b i)
    (row : ∀ i, (∑ j, Q i j*m j) = -b i)
    (reach : ∀ i, ∃ j, Relation.ReflTransGen (edge Q) i j ∧ 0 < b j) :
    ∀ v : ι → ℝ, v ≠ 0 → pairing Q v < 0 := by
  intro v hv
  let z := fun i => v i / m i
  have hzrep (i : ι) : m i*z i = v i := by
    dsimp only [z]
    rw [mul_comm,div_mul_cancel₀ _ (weights i).ne']
  have hrep : (fun i => m i*z i) = v := funext hzrep
  have hid := weighted_identity Q m b z symm row
  rw [hrep] at hid
  have hEdge (i j : ι) : 0 ≤ Q i j*m i*m j*(z i-z j)^2 := by
    by_cases h : i = j
    · subst j
      simp only [sub_self,pow_two,zero_mul,mul_zero,le_refl]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (offDiag i j h) (weights i).le) (weights j).le)
        (sq_nonneg _)
  have hCut (i : ι) : 0 ≤ b i*m i*(z i)^2 :=
    mul_nonneg (mul_nonneg (cut i) (weights i).le) (sq_nonneg _)
  have hE : 0 ≤ edgeEnergy Q m z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hEdge i j
  have hB : 0 ≤ cutEnergy b m z := Finset.sum_nonneg fun i _ => hCut i
  by_contra hnot
  have hpos : 0 ≤ pairing Q v := le_of_not_gt hnot
  have hE0 : edgeEnergy Q m z = 0 := by linarith only [hid,hpos,hE,hB]
  have hB0 : cutEnergy b m z = 0 := by linarith only [hid,hpos,hE,hB]
  have hzm (i j : ι) (hij : edge Q i j) : z i = z j := by
    have h₁ : Q i j*m i*m j*(z i-z j)^2 ≤
        ∑ t, Q i t*m i*m t*(z i-z t)^2 :=
      Finset.single_le_sum (fun t _ => hEdge i t) (Finset.mem_univ j)
    have h₂ : (∑ t, Q i t*m i*m t*(z i-z t)^2) ≤ edgeEnergy Q m z :=
      Finset.single_le_sum (fun s _ => Finset.sum_nonneg fun t _ => hEdge s t)
        (Finset.mem_univ i)
    have hle := h₁.trans (h₂.trans_eq hE0)
    by_contra hne
    have hp : 0 < (z i-z j)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    exact (not_lt_of_ge hle) (mul_pos (mul_pos (mul_pos hij.2 (weights i)) (weights j)) hp)
  have hzb (i : ι) (hi : 0 < b i) : z i = 0 := by
    have h₁ : b i*m i*(z i)^2 ≤ cutEnergy b m z :=
      Finset.single_le_sum (fun s _ => hCut s) (Finset.mem_univ i)
    have hle := h₁.trans_eq hB0
    by_contra hne
    exact (not_lt_of_ge hle) (mul_pos (mul_pos hi (weights i)) (sq_pos_of_ne_zero hne))
  apply hv
  funext i
  obtain ⟨j,hpath,hj⟩ := reach i
  have hz : z i = 0 := (equal_along_path Q z hzm hpath).trans (hzb j hj)
  rw [← hzrep i,hz,mul_zero]

end Quadratic

section FullFiber
variable {ι : Type*} [Fintype ι]

/-- Restrict the actual principal-fiber row to the exceptional subset;
the cutoff term is the nonexceptional fiber multiplicity, not the
nonexceptional coefficient of the rational dual section. -/
theorem restricted_fiber_row (P : ι → Prop) [DecidablePred P]
    (Q : ι → ι → ℝ) (m : ι → ℝ)
    (principal : ∀ i, (∑ j, Q i j*m j) = 0) (i : Subtype P) :
    (∑ j : Subtype P, Q i.1 j.1*m j.1) = -cutWeight P Q m i := by
  have ha := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι) P
    (fun j => Q i.1 j*m j)
  have hin : (∑ j ∈ Finset.univ.filter P, Q i.1 j*m j) =
      ∑ j : Subtype P, Q i.1 j.1*m j.1 :=
    Finset.sum_subtype _ (fun j => by simp) _
  rw [hin,principal i.1] at ha
  change (∑ j : Subtype P, Q i.1 j.1*m j.1) + cutWeight P Q m i = 0 at ha
  linarith only [ha]

/-- Exact producer of negative definiteness from a full principal
fiber and a path from each exceptional component to a noncontracted
component. This contains no canonical-nef or section-effectivity input. -/
theorem restricted_negative_definite (P : ι → Prop) [DecidablePred P]
    (Q : ι → ι → ℝ) (m : ι → ℝ)
    (symm : ∀ i j, Q i j = Q j i) (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (weights : ∀ i, 0 < m i)
    (principal : ∀ i, (∑ j, Q i j*m j) = 0)
    (k : ι) (hk : ¬P k)
    (connected : ∀ i : Subtype P, Relation.ReflTransGen (edge Q) i.1 k) :
    ∀ v : Subtype P → ℝ, v ≠ 0 →
      pairing (fun i j : Subtype P => Q i.1 j.1) v < 0 := by
  let Qe : Subtype P → Subtype P → ℝ := fun i j => Q i.1 j.1
  have he : ∀ i : Subtype P, ∃ j : Subtype P,
      Relation.ReflTransGen (edge Qe) i j ∧ 0 < cutWeight P Q m j := by
    intro i
    obtain ⟨j,hj,hb⟩ := boundary_reachable P Q m offDiag weights k hk connected i
    have hmon : (fun u v : Subtype P => edge Q u.1 v.1) ≤ edge Qe := by
      intro u v h
      exact ⟨fun h' => h.1 (congrArg Subtype.val h'),h.2⟩
    exact ⟨j,Relation.ReflTransGen.mono hmon i j hj,hb⟩
  exact negative_definite Qe (fun i => m i.1) (cutWeight P Q m)
    (fun i j => symm i.1 j.1)
    (fun i j h => offDiag i.1 j.1 (fun h' => h (Subtype.ext h')))
    (fun i => weights i.1) (cut_nonneg P Q m offDiag weights)
    (restricted_fiber_row P Q m principal) he

end FullFiber
end SelectedWeightedExceptionalFiber318

#print axioms SelectedWeightedExceptionalFiber318.first_exit
#print axioms SelectedWeightedExceptionalFiber318.boundary_reachable
#print axioms SelectedWeightedExceptionalFiber318.weighted_identity
#print axioms SelectedWeightedExceptionalFiber318.negative_definite
#print axioms SelectedWeightedExceptionalFiber318.restricted_fiber_row
#print axioms SelectedWeightedExceptionalFiber318.restricted_negative_definite
