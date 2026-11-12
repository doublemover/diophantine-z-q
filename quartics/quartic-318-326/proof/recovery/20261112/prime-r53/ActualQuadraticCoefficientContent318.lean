module
public import ActualInertCoverageResidues318
public section
noncomputable section
namespace ActualQuadraticCoefficientContent318
open ClearedContactForms318 ContactPatternSupport318
variable {labels : Fin 4→ℤ} (C : Clearing labels)
/-- Content of the literal fifteen coefficients, including duplicates
and the three old zero coefficients. No coefficient is normalized away. -/
@[expose] def content : ℕ := Finset.univ.gcd (fun i => (C.coefficient i).natAbs)
lemma unit_base (u w : ℤ) (q : ℕ)
    (hr : ∀ i : Fin 3×Fin 5,(row C u w i.1 i.2:ZMod q)=1) : (u:ZMod q)=1 := by
  have he:=hr (0,0)
  simpa only [row,ActualContactZeroCoefficient318.zero_value] using he
/-- A common inert divisor will be confined to coefficient content OR
the translated primitive defect gcd(u-1,w), not gcd(u,w). -/
theorem support (u w : ℤ) (q : ℕ) [Fact q.Prime]
    (hr : ∀ i : Fin 3×Fin 5,(row C u w i.1 i.2:ZMod q)=1) :
    q∣content C ∨ q∣Nat.gcd (u-1).natAbs w.natAbs := by
  have hu:=unit_base C u w q hr
  by_cases hw : (w:ZMod q)=0
  · right
    apply Nat.dvd_gcd
    · have hz : ((u-1:ℤ):ZMod q)=0 := by simp [hu]
      simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd (u-1) q).mp hz)
    · simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd w q).mp hw)
  · left
    apply Finset.dvd_gcd
    intro i _
    have hz := QuadraticPatternUnitResidues318.difference q u w (C.coefficient i)
      (C.coefficient (0,0)) (hr i) (hr (0,0))
    have hk : (C.coefficient i:ZMod q)=0 := by
      simpa only [ActualContactZeroCoefficient318.coefficient_zero,Int.cast_zero] using hz.resolve_right hw
    simpa using Int.natAbs_dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (C.coefficient i) q).mp hk)
lemma separated_step (u w : ℤ) (q : ℕ) [Fact q.Prime]
    (hr : ∀ i : Fin 3×Fin 5,(row C u w i.1 i.2:ZMod q)=1)
    (i : Fin 3×Fin 5) (hi : (C.coefficient i:ZMod q)≠0) :
    (w:ZMod q)=0 ∧ (u:ZMod q)=1 := by
  exact QuadraticPatternUnitResidues318.separated q u w (C.coefficient i)
    (C.coefficient (0,0)) (hr i) (hr (0,0))
    (by simpa only [ActualContactZeroCoefficient318.coefficient_zero,Int.cast_zero] using hi)
/-- With nonzero step and one nonzero coefficient the support is FINITE.
No bound independent of the same pair's w is inferred. -/
lemma bounded (u w : ℤ) (hw : w≠0) (q : ℕ) [Fact q.Prime]
    (hr : ∀ i : Fin 3×Fin 5,(row C u w i.1 i.2:ZMod q)=1)
    (i : Fin 3×Fin 5) (hi : C.coefficient i≠0) :
    q≤max (C.coefficient i).natAbs w.natAbs := by
  have hd:=QuadraticPatternUnitResidues318.divisor_support q u w (C.coefficient i)
    (C.coefficient (0,0)) (hr i) (hr (0,0))
  rw [ActualContactZeroCoefficient318.coefficient_zero,sub_zero] at hd
  rcases hd with hk|hw'
  · exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hi) hk).trans (le_max_left _ _)
  · exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hw) hw').trans (le_max_right _ _)
end ActualQuadraticCoefficientContent318
