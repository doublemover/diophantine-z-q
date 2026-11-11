module
public import PELPrimitiveIntegerCoordinates318
public section
noncomputable section
namespace PELPrimitiveRationalCoordinates318
open PELPrincipalOrderCoordinates318 PELPrimitiveIntegerCoordinates318
open scoped BigOperators
set_option maxHeartbeats 1600000

theorem primitive_rational (r : Fin 4 → ℚ) (hr : r≠0) :
    ∃ (q : ℚ) (a z : Coordinates),q≠0 ∧ (∀ i,r i=q*(a i:ℚ)) ∧ ∑ i : Fin 4,z i*a i=1 := by
  let D : ℕ := (r 0).den*(r 1).den*(r 2).den*(r 3).den
  let A : Coordinates := ![
    (r 0).num*(r 1).den*(r 2).den*(r 3).den,
    (r 1).num*(r 0).den*(r 2).den*(r 3).den,
    (r 2).num*(r 0).den*(r 1).den*(r 3).den,
    (r 3).num*(r 0).den*(r 1).den*(r 2).den]
  have hDpos : 0<D := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (r 0).den_pos (r 1).den_pos)
    (r 2).den_pos) (r 3).den_pos
  have hD : (D:ℚ)≠0 := by exact_mod_cast hDpos.ne'
  have hclear (i : Fin 4) : (D:ℚ)*r i=(A i:ℚ) := by
    fin_cases i
    · dsimp [D,A]; push_cast; rw [←Rat.mul_den_eq_num (r 0)]; ring
    · dsimp [D,A]; push_cast; rw [←Rat.mul_den_eq_num (r 1)]; ring
    · dsimp [D,A]; push_cast; rw [←Rat.mul_den_eq_num (r 2)]; ring
    · dsimp [D,A]; push_cast; rw [←Rat.mul_den_eq_num (r 3)]; ring
  have hA : A≠0 := by
    intro hz
    apply hr
    funext i
    have he : (D:ℚ)*r i=0 := by simpa [hz] using hclear i
    exact (mul_eq_zero.mp he).resolve_left hD
  obtain ⟨g,a,z,hg,ha,hprim⟩ := primitive_coordinates A hA
  have hgQ : (g:ℚ)≠0 := by exact_mod_cast hg
  refine ⟨(g:ℚ)/(D:ℚ),a,z,div_ne_zero hgQ hD,?_,hprim⟩
  intro i
  have he : (D:ℚ)*r i=(g:ℚ)*(a i:ℚ) := by
    rw [hclear i,ha i]
    push_cast <;> rfl
  apply mul_left_cancel₀ hD
  calc
    (D:ℚ)*r i=(g:ℚ)*(a i:ℚ) := he
    _ = (D:ℚ)*((g:ℚ)/(D:ℚ)*(a i:ℚ)) := by field_simp [hD]
end PELPrimitiveRationalCoordinates318
