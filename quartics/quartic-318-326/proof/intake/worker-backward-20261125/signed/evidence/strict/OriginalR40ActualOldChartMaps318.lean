module
public import OriginalNodeRingMaps318
public section
noncomputable section

/-!
The literal coordinate morphisms extracted from the R40 central and
outer chart sources. The qualified names and map values are the old
ones. A recovered Proj atlas must import this common owner, and its
actual `chart_base` and `old_reads` must compare these same maps to
the localization charts. No identification with Proj is asserted here.
-/

namespace OriginalThickCentralReesChart318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R]
variable (q : R) (d : ℕ)

abbrev O := Node (q^(d+2))
abbrev P := Node (q^d)
abbrev x := xAxis (q^(d+2))
abbrev y := yAxis (q^(d+2))
abbrev w := algebraMap R (O q d) q
abbrev I := Ideal.span ({x q d,y q d,w q d} : Set (O q d))
theorem hw : w q d ∈ I q d := Ideal.subset_span (by simp)

theorem base_relation :
    (algebraMap R (P q d) q * yAxis (q^d)) *
      (algebraMap R (P q d) q * xAxis (q^d)) =
        algebraMap R (P q d) (q^(d+2)) := by
  let a := algebraMap R (P q d) q
  calc
    _ = yAxis (q^d) * xAxis (q^d) * a^2 := by
      change (a*yAxis (q^d))*(a*xAxis (q^d)) = _
      rw [pow_two]
      ac_rfl
    _ = algebraMap R (P q d) (q^d * q^2) := by
      rw [node_relation, map_mul]
      exact congrArg (algebraMap R (P q d) (q^d) * ·) ((map_pow (algebraMap R (P q d)) q 2).symm)
    _ = _ := congrArg (algebraMap R (P q d)) (pow_add q d 2).symm

/-- The old affine coordinates map to q times the two genuine central
parameters, on this exact reduced-thickness node. -/
@[expose] def oldToNew : O q d →ₐ[R] P q d :=
  eval (q^(d+2)) (algebraMap R (P q d) q * xAxis (q^d))
    (algebraMap R (P q d) q * yAxis (q^d)) (base_relation q d)

end OriginalThickCentralReesChart318

namespace OriginalThickOuterReesChart318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalThickCentralReesChart318 (O x y w I)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R]
variable (q : R) (d : ℕ) (ε : Bool)

abbrev a := if ε then x q d else y q d
abbrev b := if ε then y q d else x q d
theorem a_mem : a q d ε ∈ I q d := by cases ε <;> apply Ideal.subset_span <;> simp
theorem b_mem : b q d ε ∈ I q d := by cases ε <;> apply Ideal.subset_span <;> simp

abbrev P := Node q

theorem old_relation :
    (algebraMap R (P q) q)^(d+1) * yAxis q * xAxis q =
      algebraMap R (P q) (q^(d+2)) := by
  rw [mul_assoc,node_relation]
  exact (pow_succ _ _).symm.trans (map_pow (algebraMap R (P q)) q _).symm

/-- The old axial pair is reordered coherently when choosing the other
outer chart, over the same old node, not a second model. -/
@[expose] def oldToOuter : O q d →ₐ[R] P q :=
  if ε then eval (q^(d+2)) (xAxis q) ((algebraMap R (P q) q)^(d+1) * yAxis q)
      (old_relation q d)
  else eval (q^(d+2)) ((algebraMap R (P q) q)^(d+1) * yAxis q) (xAxis q)
      ((mul_comm _ _).trans (old_relation q d))

theorem old_a : oldToOuter q d ε (a q d ε) = xAxis q := by
  cases ε
  · exact eval_y _ _ _ ((mul_comm _ _).trans (old_relation q d))
  · exact eval_x _ _ _ (old_relation q d)

theorem old_b : oldToOuter q d ε (b q d ε) = (algebraMap R (P q) q)^(d+1) * yAxis q := by
  cases ε
  · exact eval_x _ _ _ ((mul_comm _ _).trans (old_relation q d))
  · exact eval_y _ _ _ (old_relation q d)

end OriginalThickOuterReesChart318

#print axioms OriginalThickCentralReesChart318.oldToNew
#print axioms OriginalThickOuterReesChart318.oldToOuter
#print axioms OriginalThickOuterReesChart318.old_a
#print axioms OriginalThickOuterReesChart318.old_b
