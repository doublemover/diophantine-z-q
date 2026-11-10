module
public import PELOriginalExactDoubledLattice318
public section
noncomputable section
namespace PELOriginalDoubledPeriodSums318
open PELOriginalExactDoubledLattice318 OriginalComplexPeriodPair318
variable (i:Fin 4)

/-- Reindex the ENTIRE genuine original period sum by multiplication2.
The inverse is division2 because source_mem_iff proves exact full lattice
equality, not only inclusion or equal rank. -/
@[expose] def latticeEquiv : (pair (TargetLattice i)).lattice≃(pair (SourceLattice i)).lattice where
  toFun a:=⟨2*(a:ℂ),(pair_mem (SourceLattice i) _).mpr
    ((source_mem_iff i _).mpr ⟨⟨a.val,(pair_mem (TargetLattice i) _).mp a.property⟩,rfl⟩)⟩
  invFun b:=⟨(b:ℂ)/2,by
    apply (pair_mem (TargetLattice i) _).mpr
    obtain ⟨a,ha⟩:=(source_mem_iff i b.val).mp
      ((pair_mem (SourceLattice i) _).mp b.property)
    rw [ha]
    have he:(2*(a:ℂ))/2=(a:ℂ):=by ring
    rw [he]
    exact a.property⟩
  left_inv a:=by
    apply Subtype.ext
    dsimp
    ring
  right_inv b:=by
    apply Subtype.ext
    dsimp
    ring
lemma latticeEquiv_value (a:(pair (TargetLattice i)).lattice) :
    (latticeEquiv i a:ℂ)=2*(a:ℂ):=rfl

/-- Actual full G sums scale by2^{-n}. No sample, truncated sum or
assumed invariance under an arbitrary finite-index lattice is involved. -/
theorem G_scale (n:ℕ) :
    (pair (SourceLattice i)).G n=((2:ℂ)^n)⁻¹*(pair (TargetLattice i)).G n := by
  unfold PeriodPair.G
  rw [←(latticeEquiv i).tsum_eq]
  calc
    _ = ∑' a:(pair (TargetLattice i)).lattice,((2:ℂ)^n)⁻¹*((a:ℂ)^n)⁻¹ := by
      apply tsum_congr
      intro a
      rw [latticeEquiv_value,mul_pow,mul_inv_rev,mul_comm]
    _ = _ := by rw [tsum_mul_left]
lemma g2_scale : (pair (SourceLattice i)).g₂=(pair (TargetLattice i)).g₂/16 := by
  rw [PeriodPair.g₂,PeriodPair.g₂,G_scale]
  norm_num <;> ring
lemma g3_scale : (pair (SourceLattice i)).g₃=(pair (TargetLattice i)).g₃/64 := by
  rw [PeriodPair.g₃,PeriodPair.g₃,G_scale]
  norm_num <;> ring
lemma native_A_scale : OriginalPeriodProjectiveModel318.A (SourceLattice i)=
    OriginalPeriodProjectiveModel318.A (TargetLattice i)/16 := by
  rw [OriginalPeriodProjectiveModel318.A,OriginalPeriodProjectiveModel318.A,g2_scale]
  ring
lemma native_B_scale : OriginalPeriodProjectiveModel318.B (SourceLattice i)=
    OriginalPeriodProjectiveModel318.B (TargetLattice i)/64 := by
  rw [OriginalPeriodProjectiveModel318.B,OriginalPeriodProjectiveModel318.B,g3_scale]
  ring
end PELOriginalDoubledPeriodSums318
