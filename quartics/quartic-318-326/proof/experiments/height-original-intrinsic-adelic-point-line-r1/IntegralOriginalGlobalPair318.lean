module
public import IntegralOriginalBicanonicalRestrictions318
public section
noncomputable section
namespace IntegralOriginalGlobalPair318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open IntegralOriginalBicanonicalRestrictions318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- All five literal integral formulas, viewed on the original complete
rational cover using the actual scheme and ring comparison maps. -/
@[expose] def localQ (n : Fin 2) : (i : Option (Fin 4)) →
    Γ(tensor c,ContactGlobalBicanonical318.opens c i)
  | some i => (tensor c).presheaf.map (homOfLE (branchLE c i)).op (branchQ c i n)
  | none => (tensor c).presheaf.map (homOfLE (infinityLE c)).op (infinityQ c n)

theorem local_eq_restriction (n : Fin 2) (i : Option (Fin 4)) :
    localQ c n i =
      (tensor c).presheaf.map
        (homOfLE (show ContactGlobalBicanonical318.opens c i≤⊤ from le_top)).op (originalQ c n) := by
  cases i
  · exact infinity_restriction c n
  · exact branch_restriction c _ n

/-- Compatibility is equality of genuine section restrictions on full
intersections, already identified with the same original global section. -/
theorem compatible (n : Fin 2) :
    TopCat.Presheaf.IsCompatible (tensor c).presheaf
      (ContactGlobalBicanonical318.opens c) (localQ c n) := by
  intro i j
  rw [local_eq_restriction,local_eq_restriction]
  have hL := congrArg (fun f => f (originalQ c n))
    ((tensor c).presheaf.map_comp
      (homOfLE (show ContactGlobalBicanonical318.opens c i≤⊤ from le_top)).op
      (homOfLE (show ContactGlobalBicanonical318.opens c i ⊓ ContactGlobalBicanonical318.opens c j ≤
        ContactGlobalBicanonical318.opens c i from inf_le_left)).op)
  have hR := congrArg (fun f => f (originalQ c n))
    ((tensor c).presheaf.map_comp
      (homOfLE (show ContactGlobalBicanonical318.opens c j≤⊤ from le_top)).op
      (homOfLE (show ContactGlobalBicanonical318.opens c i ⊓ ContactGlobalBicanonical318.opens c j ≤
        ContactGlobalBicanonical318.opens c j from inf_le_right)).op)
  exact hL.symm.trans hR

/-- Genuine global gluing of the transported integral chart formulas inside
the original intrinsic bicanonical sheaf. No rank-one replacement is used. -/
@[expose] def fromIntegralFormulas (n : Fin 2) : Γ(tensor c,⊤) :=
  ModuleGlobalSections318.gluedTop (tensor c) (ContactGlobalBicanonical318.opens c)
    (ContactGlobalBicanonical318.cover c) (localQ c n) (compatible c n)

/-- The resulting global sections are exactly J² times the ORIGINAL q0/q1.
This is sheaf uniqueness on the entire original cover, not generic equality. -/
theorem original_identity (n : Fin 2) : fromIntegralFormulas c n = originalQ c n := by
  have h := Classical.choose_spec
    (TopCat.Sheaf.existsUnique_gluing'
      (⟨(tensor c).presheaf,(tensor c).isSheaf⟩ :
        TopCat.Sheaf AddCommGrpCat (ContactGlobalSmooth318.Model c))
      (ContactGlobalBicanonical318.opens c) ⊤ (fun _ => homOfLE le_top)
      (ContactGlobalBicanonical318.cover c) (localQ c n) (compatible c n))
  exact (h.2 (originalQ c n) (fun i => (local_eq_restriction c n i).symm)).symm

theorem original_q0 : fromIntegralFormulas c 0 =
    (VerticalSection318.J^2 : ℤ) • ContactGlobalBicanonical318.q0 c := by
  rw [original_identity]
  all_goals simp only [originalQ,ite_true]

theorem original_q1 : fromIntegralFormulas c 1 =
    (VerticalSection318.J^2 : ℤ) • ContactGlobalBicanonical318.q1 c := by
  rw [original_identity]
  all_goals simp only [originalQ,show (1 : Fin 2)≠0 by decide,ite_false]
end IntegralOriginalGlobalPair318
