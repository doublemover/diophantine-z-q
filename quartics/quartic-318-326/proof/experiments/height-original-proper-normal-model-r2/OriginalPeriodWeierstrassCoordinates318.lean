module
public import OriginalComplexPeriodPair318
public section
noncomputable section
namespace OriginalPeriodWeierstrassCoordinates318
open OriginalComplexPeriodPair318 ComplexAffineFreeTranslation318
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Descend an actually periodic function through the original full
period relation; no analytic or algebraic quotient comparison is supplied. -/
@[expose] def descend (f : ℂ→ℂ) (hf : ∀ z (a : L),f (z+a.val)=f z) : Torus L→ℂ :=
  Quotient.lift f (by
    intro z w he
    have hq : (QuotientAddGroup.mk' L) z=(QuotientAddGroup.mk' L) w := Quotient.sound he
    have hm : z-w∈L := by
      apply (QuotientAddGroup.eq_zero_iff).mp
      change (QuotientAddGroup.mk' L) (z-w)=0
      rw [map_sub]
      exact sub_eq_zero.mpr hq
    have hh := hf w ⟨z-w,hm⟩
    have hz : w+(z-w)=z := by abel
    simpa only [hz] using hh)

@[expose] def x : Torus L→ℂ := descend L (pair L).weierstrassP (fun z a =>
  (pair L).weierstrassP_add_coe z ⟨a.val,(pair_mem L a.val).mpr a.property⟩)
@[expose] def y : Torus L→ℂ := descend L (pair L).derivWeierstrassP (fun z a =>
  (pair L).derivWeierstrassP_add_coe z ⟨a.val,(pair_mem L a.val).mpr a.property⟩)

lemma x_projection (z : ℂ) : x L (projection L z)=(pair L).weierstrassP z := rfl
lemma y_projection (z : ℂ) : y L (projection L z)=(pair L).derivWeierstrassP z := rfl

/-- The actual descended coordinates satisfy the Weierstrass cubic at
EVERY nonorigin point. The origin is excluded honestly: library junk
values at lattice poles are not used as affine points. -/
theorem cubic (q : Torus L) (hq : q≠0) :
    y L q ^ 2=4*x L q ^ 3-(pair L).g₂*x L q-(pair L).g₃ := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L q
  rw [x_projection,y_projection]
  apply (pair L).derivWeierstrassP_sq z
  intro hz
  apply hq
  exact (QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L z).mp hz)

/-- The coefficients are the genuine lattice-sum invariants of the SAME
full period lattice, not the published target invariants supplied as data. -/
@[expose] def affinePoint (q : {q : Torus L // q≠0}) :
    {p : ℂ×ℂ // p.2^2=4*p.1^3-(pair L).g₂*p.1-(pair L).g₃} :=
  ⟨(x L q.val,y L q.val),cubic L q.val q.property⟩
end OriginalPeriodWeierstrassCoordinates318
