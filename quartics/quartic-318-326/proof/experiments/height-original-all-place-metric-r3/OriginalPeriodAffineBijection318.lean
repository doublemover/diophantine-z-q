module
public import OriginalPeriodCubicSurjectivity318
public import WeierstrassPairInjective318
public section
noncomputable section
namespace OriginalPeriodAffineBijection318
open OriginalPeriodWeierstrassCoordinates318 OriginalComplexPeriodPair318
open ComplexAffineFreeTranslation318
set_option maxHeartbeats 2200000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- The existing original Weierstrass-pair separation theorem applies to
this SAME whole period lattice, not a finite-index lattice of a new torus. -/
theorem affinePoint_injective : Function.Injective (affinePoint L) := by
  intro q r he
  apply Subtype.ext
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk'_surjective L q.val
  obtain ⟨w,hw⟩ := QuotientAddGroup.mk'_surjective L r.val
  have hzl : z∉(pair L).lattice := by
    intro h
    exact q.property (hz.symm.trans ((QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L z).mp h)))
  have hwl : w∉(pair L).lattice := by
    intro h
    exact r.property (hw.symm.trans ((QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L w).mp h)))
  have hx := congrArg (fun p => p.val.1) he
  have hy := congrArg (fun p => p.val.2) he
  change x L q.val=x L r.val at hx
  change y L q.val=y L r.val at hy
  rw [←hz,←hw,x_projection] at hx
  rw [←hz,←hw,y_projection] at hy
  have hp := (WeierstrassPairInjective318.pair_eq_iff_sub_mem (pair L) z w hzl hwl).mp ⟨hx,hy⟩
  have hq : (QuotientAddGroup.mk' L) (w-z)=0 :=
    (QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L (w-z)).mp hp)
  rw [map_sub,hz,hw] at hq
  exact (sub_eq_zero.mp hq).symm

/-- Exact set-level equivalence to the whole actual affine period cubic.
No algebraic morphism or analytic structure is transported through it. -/
@[expose] def equivalence : {q : Torus L // q≠0} ≃
    {p : ℂ×ℂ // p.2^2=4*p.1^3-(pair L).g₂*p.1-(pair L).g₃} :=
  Equiv.ofBijective (affinePoint L)
    ⟨affinePoint_injective L,OriginalPeriodCubicSurjectivity318.affinePoint_surjective L⟩
end OriginalPeriodAffineBijection318
