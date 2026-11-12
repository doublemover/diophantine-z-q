module
public import CanonicalQuarticCharacter318
public section
noncomputable section
namespace QuarticJacobiIntegral318
open CanonicalJacobiTrace318
open scoped BigOperators
set_option maxHeartbeats 1000000

@[expose] def Gaussian (z : ℂ) : Prop := ∃ a b : ℤ, z=(a:ℂ)+(b:ℂ)*Complex.I

lemma gaussian_zero : Gaussian 0 := ⟨0,0,by norm_num⟩
lemma gaussian_add {z w : ℂ} (hz : Gaussian z) (hw : Gaussian w) : Gaussian (z+w) := by
  obtain ⟨a,b,rfl⟩ := hz
  obtain ⟨c,d,rfl⟩ := hw
  exact ⟨a+c,b+d,by push_cast; ring⟩
lemma gaussian_mul {z w : ℂ} (hz : Gaussian z) (hw : Gaussian w) : Gaussian (z*w) := by
  obtain ⟨a,b,rfl⟩ := hz
  obtain ⟨c,d,rfl⟩ := hw
  refine ⟨a*c-b*d,a*d+b*c,?_⟩
  push_cast
  linear_combination (b:ℂ)*(d:ℂ)*Complex.I_sq

lemma gaussian_sum {T : Type*} (s : Finset T) (f : T → ℂ)
    (hf : ∀ t∈s, Gaussian (f t)) : Gaussian (∑ t∈s, f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gaussian_zero
  | @insert t s ht ih =>
    rw [Finset.sum_insert ht]
    exact gaussian_add (hf t (Finset.mem_insert_self t s))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

/-- Every fourth root of unity has literal integer Gaussian coordinates. -/
lemma gaussian_fourth_root (z : ℂ) (hz : z^4=1) : Gaussian z := by
  have he : (z^2-1)*(z^2+1)=0 := by linear_combination hz
  rcases mul_eq_zero.mp he with h|h
  · have he' : (z-1)*(z+1)=0 := by linear_combination h
    rcases mul_eq_zero.mp he' with h'|h'
    · have heq : z=1 := by linear_combination h'
      rw [heq]; exact ⟨1,0,by norm_num⟩
    · have heq : z= -1 := by linear_combination h'
      rw [heq]; exact ⟨-1,0,by norm_num⟩
  · have he' : (z-Complex.I)*(z+Complex.I)=0 := by
      linear_combination h-Complex.I_sq
    rcases mul_eq_zero.mp he' with h'|h'
    · have heq : z=Complex.I := by linear_combination h'
      rw [heq]; exact ⟨0,1,by norm_num⟩
    · have heq : z= -Complex.I := by linear_combination h'
      rw [heq]; exact ⟨0,-1,by norm_num⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma quartic_value (ψ : MulChar F ℂ) (hfour : ψ^4=1) (x : F) : Gaussian (ψ x) := by
  by_cases hx : x=0
  · rw [hx,map_zero]; exact gaussian_zero
  · apply gaussian_fourth_root
    have he := congrArg (fun χ : MulChar F ℂ => χ x) hfour
    rw [MulChar.pow_apply' ψ (by decide : (4:ℕ)≠0),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)] at he
    exact he

/-- The actual Jacobi sum lies in Z[i] by closure of its actual summands;
no integer coordinates are supplied as input. -/
theorem jacobi_integral (ψ : MulChar F ℂ) (hfour : ψ^4=1) :
    Gaussian (jacobiSum ψ quadraticComplex) := by
  unfold jacobiSum
  apply gaussian_sum
  intro x hx
  apply gaussian_mul (quartic_value ψ hfour x)
  exact ⟨quadraticChar F (1-x),0,by rw [quadraticComplex_apply]; simp⟩

end QuarticJacobiIntegral318
