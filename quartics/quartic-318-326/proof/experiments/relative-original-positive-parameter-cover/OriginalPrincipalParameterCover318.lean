module
public import OriginalPrincipalAffineFrames318
public import OriginalAffineParameterPullback318
public section
noncomputable section
namespace OriginalPrincipalParameterCover318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (R A S : CommRingCat.{u}) [Algebra R A] [Algebra R S]
  (L : Line (Spec A))
local notation "AS" => OriginalAffineParameterSquare318.source R A S
abbrev Index := OriginalPrincipalAffineFrames318.Index A L
abbrev chart (r : Index A L) := OriginalAffineParameterSquare318.target R A
  (OriginalPrincipalAffineFrames318.ring A L r) S (OriginalPrincipalAffineFrames318.arrow A L r)
abbrev arrow (r : Index A L) : AS ⟶ chart R A S L r :=
  OriginalAffineParameterSquare318.chartMap R A _ S (OriginalPrincipalAffineFrames318.arrow A L r)

instance chart_open (r : Index A L) : IsOpenImmersion (Spec.map (arrow R A S L r)) :=
  OriginalAffineParameterPullback318.chart_open R A _ S _

/-- The PRODUCED principal frames continue to cover the literal
parameter-extended original affine chart. The proof uses the actual
Cartesian square and exact inverse-image identity. -/
theorem covers (x : Spec AS) : ∃ r : Index A L, ∃ y : Spec (chart R A S L r),
    Spec.map (arrow R A S L r) y=x := by
  let i := OriginalAffineParameterSquare318.sourceMap R A S
  obtain ⟨r,y,hy⟩ := OriginalPrincipalAffineFrames318.covers A L (Spec.map i x)
  have hx : x ∈ (Spec.map (arrow R A S L r)).opensRange := by
    rw [OriginalAffineParameterPullback318.chart_range]
    change Spec.map i x ∈ Set.range (Spec.map (OriginalPrincipalAffineFrames318.arrow A L r))
    exact ⟨y,hy⟩
  exact ⟨r,hx⟩
end OriginalPrincipalParameterCover318
