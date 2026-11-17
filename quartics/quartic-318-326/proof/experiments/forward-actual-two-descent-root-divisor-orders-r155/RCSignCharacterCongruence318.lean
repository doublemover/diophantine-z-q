module
public import RCFiniteBinaryCongruence318
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public section
noncomputable section
namespace RCSignCharacterCongruence318
open scoped BigOperators
open MvPolynomial RCBooleanDigitPolynomial318

abbrev Cube (b : ℕ) := Fin b → ZMod 2

def linear {b : ℕ} (g : Cube b) : MvPolynomial (Fin b) (ZMod 2) :=
  ∑ i, C (g i) * X i

def sign {b : ℕ} (g x : Cube b) : ℤ :=
  (-1) ^ (∑ i, g i * x i).val

def sumCharacter {b : ℕ} (W : List (Cube b)) (x : Cube b) : ℤ :=
  (W.map fun g => sign g x).sum

theorem linear_degree {b : ℕ} (g : Cube b) : (linear g).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem eval_linear {b : ℕ} (g x : Cube b) :
    eval x (linear g) = ∑ i, g i * x i := by simp [linear]

theorem linear_zero {b : ℕ} (g : Cube b) : eval (0 : Cube b) (linear g) = 0 := by
  simp [eval_linear]

/-- The exact integral sign-sum identity is the transport from the binary
count polynomial to actual character evaluations. -/
theorem sumCharacter_eq_count {b : ℕ} (W : List (Cube b)) (x : Cube b) :
    sumCharacter W x = (W.length : ℤ) - 2 * activeCount x (W.map linear) := by
  induction W with
  | nil => simp [sumCharacter, activeCount]
  | cons g W ih =>
      have cases_two : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases cases_two (eval x (linear g)) with h | h
      · simp only [eval_linear] at h
        simp [sumCharacter, List.map_cons, activeCount, eval_linear, sign, h] at ih ⊢
        omega
      · simp only [eval_linear] at h
        simp [sumCharacter, List.map_cons, activeCount, eval_linear, sign, h] at ih ⊢
        omega

/-- The original binary-congruence conclusion for every finite list of
integral sign characters, allowing arbitrary repetitions. No coefficient
bound enters the dimension estimate. -/
theorem exists_nonzero_list_congruence (b r M : ℕ)
    (W : Fin r → List (Cube b)) (hsize : r * (2 ^ M - 1) < b) :
    ∃ x : Cube b, x ≠ 0 ∧
      ∀ i, (2 ^ M : ℤ) ∣ sumCharacter (W i) x - (W i).length := by
  obtain ⟨x,hx,hdiv⟩ := RCFiniteBinaryCongruence318.exists_nonzero_count_congruence
    b r M (fun i => (W i).map linear)
    (by
      intro i Q hQ
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hQ
      exact linear_degree g)
    (by
      intro i Q hQ
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp hQ
      exact linear_zero g)
    hsize
  refine ⟨x,hx,fun i => ?_⟩
  obtain ⟨a,ha⟩ := hdiv i
  refine ⟨-2 * (a : ℤ), ?_⟩
  rw [sumCharacter_eq_count, ha]
  push_cast
  ring

def expandWeights {b : ℕ} (a : Cube b → ℕ) : List (Cube b) → List (Cube b)
  | [] => []
  | g :: W => List.replicate (a g) g ++ expandWeights a W

theorem sumCharacter_expandWeights {b : ℕ} (a : Cube b → ℕ)
    (W : List (Cube b)) (x : Cube b) :
    sumCharacter (expandWeights a W) x =
      (W.map fun g => (a g : ℤ) * sign g x).sum := by
  induction W with
  | nil => simp [expandWeights, sumCharacter]
  | cons g W ih =>
      simpa [expandWeights, sumCharacter, nsmul_eq_mul] using
        congrArg (fun z : ℤ => (a g : ℤ) * sign g x + z) ih

theorem length_expandWeights {b : ℕ} (a : Cube b → ℕ) (W : List (Cube b)) :
    (expandWeights a W).length = (W.map a).sum := by
  induction W with
  | nil => rfl
  | cons g W ih => simp [expandWeights, ih]

/-- Explicit coefficient-weighted version over an arbitrary finite list
of group elements. Passing a complete enumeration gives the finite group
ring statement; integer/residue coefficients are reduced to these weights. -/
theorem exists_nonzero_weighted_congruence (b r M : ℕ)
    (G : List (Cube b)) (a : Fin r → Cube b → ℕ)
    (hsize : r * (2 ^ M - 1) < b) :
    ∃ x : Cube b, x ≠ 0 ∧ ∀ i,
      (2 ^ M : ℤ) ∣ (G.map fun g => (a i g : ℤ) * sign g x).sum -
        ((G.map (a i)).sum : ℕ) := by
  obtain ⟨x,hx,h⟩ := exists_nonzero_list_congruence b r M
    (fun i => expandWeights (a i) G) hsize
  refine ⟨x,hx,fun i => ?_⟩
  simpa only [sumCharacter_expandWeights, length_expandWeights] using h i

end RCSignCharacterCongruence318
