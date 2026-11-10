module
public import NormalizedLegendreAllFibers318
public import PELOriginalFourBranchAlgebraicTarget318
public import PELOriginalNormalizedDoubleCover318
public section
noncomputable section
namespace PELOriginalCommonLegendreBase318
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalNormalizedDoubleCover318 PELOriginalFourBranchAlgebraicTarget318
open ProjectiveLineComplexSchemePoints318
open scoped OnePoint

/-- The actual original analytic cover now lands in the SAME genuine
homogeneous Proj Scheme-point target as the actual Legendre projection.
The map is induced by the old quotient and the actual algebraic target
normalization, not a choice of fiber matching. -/
@[expose] def originalProjection (i:Fin 4) (x:CharacterBase i) : SchemePoints:=
  normalizedPoint i (toMaximal i x)

lemma original_projection_coordinate (i:Fin 4) (x:CharacterBase i) :
    originalProjection i x=spherePoint (normalizedMap i x):=
  exact_normalized_point i (toMaximal i x)

@[expose] def originalFiberEquiv (i:Fin 4) (z:OnePoint ℂ) :
    {x:CharacterBase i // originalProjection i x=spherePoint z} ≃
      {x:CharacterBase i // normalizedMap i x=z} where
  toFun x:=⟨x.val,spherePoint_bijective.1
    ((original_projection_coordinate i x.val).symm.trans x.property)⟩
  invFun x:=⟨x.val,(original_projection_coordinate i x.val).trans
    (congrArg spherePoint x.property)⟩
  left_inv x:=rfl
  right_inv x:=rfl

/-- Complete original fibers at the FINAL Scheme-valued base, not just at
an auxiliary sphere, remain one at exactly the four actual marked values
and two at every other point. -/
theorem original_all_fibers (i:Fin 4) (q:SchemePoints) :
    Nat.card {x:CharacterBase i // originalProjection i x=q}=
      if q=chartPoint 0 0 ∨ q=chartPoint 1 0 ∨ q=chartPoint 1 1 ∨
        q=chartPoint 1 (branchParameter i) then 1 else 2 := by
  classical
  obtain ⟨z,rfl⟩:=spherePoint_bijective.2 q
  rw [Nat.card_congr (originalFiberEquiv i z),all_fibers]
  simp only [←spherePoint_infty,←spherePoint_coe,spherePoint_bijective.1.eq_iff]

/-- Both actual projections are onto the SAME actual base, with the
original parameter. This is a common-base theorem, NOT a cover isomorphism.
The remaining task is a compatible analytic sheet comparison across cuts. -/
theorem both_surjective (i:Fin 4) : Function.Surjective (originalProjection i) ∧
    Function.Surjective (NormalizedLegendreFiniteProjection318.project (branchParameter i)) := by
  constructor
  · intro q
    obtain ⟨z,rfl⟩:=spherePoint_bijective.2 q
    obtain ⟨x,hx⟩:=PELOriginalNormalizedDoubleCover318.surjective i z
    exact ⟨x,(original_projection_coordinate i x).trans (congrArg spherePoint hx)⟩
  · exact NormalizedLegendreAllFibers318.scheme_projection_surjective _
end PELOriginalCommonLegendreBase318
