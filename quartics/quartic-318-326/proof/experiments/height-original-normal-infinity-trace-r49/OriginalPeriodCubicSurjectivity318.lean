module
public import WeierstrassActualCubicSurjectivity318
public section
noncomputable section
namespace OriginalPeriodCubicSurjectivity318
open OriginalPeriodWeierstrassCoordinates318 OriginalComplexPeriodPair318
open ComplexAffineFreeTranslation318
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- The actual nonorigin torus maps ONTO the entire actual lattice-sum
affine cubic, not merely a selected family of points. This is surjectivity
only; injectivity and full scheme algebraization are separate claims. -/
theorem affinePoint_surjective : Function.Surjective (affinePoint L) := by
  rintro ⟨⟨a,b⟩,hc⟩
  obtain ⟨z,hz,hx,hy⟩ := WeierstrassActualCubicSurjectivity318.exists_cubic_point (pair L) a b hc
  have hq : projection L z≠0 := by
    intro h
    exact hz ((pair_mem L z).mpr ((QuotientAddGroup.eq_zero_iff).mp h))
  refine ⟨⟨projection L z,hq⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · exact hy
end OriginalPeriodCubicSurjectivity318

namespace PELOriginalCubicSurjectivity318
open PELOriginalInvolutionTower318 PELOriginalWeierstrassCoordinates318
open PELOriginalUniformizationOnly318 ComplexAffineFreeTranslation318
set_option maxHeartbeats 2600000
variable (i : Fin 4) (L : AddSubgroup ℂ) [DiscreteTopology L]
variable (u : InvolutionBase i ≃ₜ Torus L)
local instance : CompactSpace (Torus L) := quotient_compact i L u

/-- Actual original involution points, excluding the specified origin,
produce every affine point of its genuine period cubic under the original
uniformization. No cubic-point existence hypothesis remains. -/
theorem original_cubic_point (a b : ℂ)
    (hc : b^2=4*a^3-(PELOriginalWeierstrassCoordinates318.periods i L u).g₂*a-
      (PELOriginalWeierstrassCoordinates318.periods i L u).g₃) :
    ∃ p : InvolutionBase i,p≠origin i L u ∧
      originalX i L u p=a ∧ originalY i L u p=b := by
  obtain ⟨q,hq⟩ := OriginalPeriodCubicSurjectivity318.affinePoint_surjective L ⟨(a,b),hc⟩
  refine ⟨u.symm q.val,?_,?_,?_⟩
  · intro he
    exact q.property (u.symm.injective he)
  · have hh := congrArg (fun p => p.val.1) hq
    simpa only [originalX,u.apply_symm_apply,OriginalPeriodWeierstrassCoordinates318.affinePoint] using hh
  · have hh := congrArg (fun p => p.val.2) hq
    simpa only [originalY,u.apply_symm_apply,OriginalPeriodWeierstrassCoordinates318.affinePoint] using hh
end PELOriginalCubicSurjectivity318
