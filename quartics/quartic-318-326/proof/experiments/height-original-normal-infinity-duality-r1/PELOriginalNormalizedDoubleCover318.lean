module
public import PELOriginalFourBranchCoordinate318
public import PELOriginalCharacterProjection318
public import NormalizedLegendreProjectiveModel318
public section
noncomputable section
namespace PELOriginalNormalizedDoubleCover318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalCharacterTopologicalAtlas318 PELOriginalCharacterComplexAtlas318
open PELOriginalFourBranchCoordinate318 PELOriginalCharacterBranches318
open ComplexSphereCharts318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold
local instance : ChartedSpace ℂ PELOriginalMaximalQuotient318.MaximalBase:=
  PELMaximalTopologicalAtlas318.maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω PELOriginalMaximalQuotient318.MaximalBase:=
  PELMaximalComplexAtlas318.maximal_manifold

/-- The actual original character map in the genuinely constructed
normalized coordinate. Its domain remains the original index-eight quotient. -/
@[expose] def normalizedMap : CharacterBase i→OnePoint ℂ:=coordinate i∘toMaximal i
lemma holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (normalizedMap i):=
  (coordinate_biholomorphic i).1.comp (PELOriginalCharacterProjection318.toMaximal_holomorphic i)
lemma surjective : Function.Surjective (normalizedMap i):=
  (coordinate i).surjective.comp (toMaximal_surjective i)
lemma continuous : Continuous (normalizedMap i):=
  (coordinate i).continuous.comp (toMaximal_continuous i)
lemma proper : IsProperMap (normalizedMap i):=by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨continuous i,?_,?_⟩
  · intro S hS
    exact (hS.isCompact.image (continuous i)).isClosed
  · intro q
    exact (isClosed_singleton.preimage (continuous i)).isCompact

/-- Actual WHOLE fibers before and after the target coordinate change. -/
@[expose] def fiberEquiv (q:PELOriginalMaximalQuotient318.MaximalBase) :
    {x:CharacterBase i // normalizedMap i x=coordinate i q}≃
      {x:CharacterBase i // toMaximal i x=q} where
  toFun x:=⟨x.val,(coordinate i).injective x.property⟩
  invFun x:=⟨x.val,congrArg (coordinate i) x.property⟩
  left_inv x:=rfl
  right_inv x:=rfl

lemma original_fiber_alternatives (q:PELOriginalMaximalQuotient318.MaximalBase) :
    Nat.card {x:CharacterBase i // toMaximal i x=q}=1 ∨
    Nat.card {x:CharacterBase i // toMaximal i x=q}=2 := by
  obtain ⟨x,rfl⟩:=PELOriginalMaximalQuotient318.projection_surjective q
  rw [fiber_card]
  split_ifs <;> simp

/-- Exact original map has one point over precisely infinity,zero,one,
and its constructed fourth parameter; EVERY other full fiber has two. -/
theorem all_fibers (z:OnePoint ℂ) :
    Nat.card {x:CharacterBase i // normalizedMap i x=z}=
      if z=∞ ∨ z=(0:ℂ) ∨ z=(1:ℂ) ∨ z=(branchParameter i:ℂ) then 1 else 2 := by
  classical
  obtain ⟨q,rfl⟩:=(coordinate i).surjective z
  rw [Nat.card_congr (fiberEquiv i q)]
  have he:=actual_branch_values i q
  change Nat.card {x:CharacterBase i // toMaximal i x=q}=1 ↔ _ at he
  split_ifs with h
  · exact he.mpr h
  · rcases original_fiber_alternatives i q with hh|hh
    · exact False.elim (h (he.mp hh))
    · exact hh

/-- The candidate algebraic target is now a REAL smooth proper projective
scheme using the constructed original fourth branch coordinate. This does
NOT assert that matching branch sets alone identifies the double covers. -/
abbrev legendreModel:=NormalizedLegendreProjectiveModel318.model (branchParameter i)
abbrev legendreStructure:=NormalizedLegendreProjectiveModel318.structure (branchParameter i)
theorem legendre_smooth : AlgebraicGeometry.Smooth (legendreStructure i):=
  NormalizedLegendreProjectiveModel318.smooth _ (branchParameter_nonexceptional i).1
    (branchParameter_nonexceptional i).2
theorem legendre_proper : AlgebraicGeometry.IsProper (legendreStructure i):=
  NormalizedLegendreProjectiveModel318.proper _
theorem legendre_equation (t y:ℂ) :
    (NormalizedLegendreProjectiveModel318.curve (branchParameter i)).toAffine.Equation
      (t-NormalizedLegendreProjectiveModel318.shift (branchParameter i)) y ↔
        y^2=t*(t-1)*(t-branchParameter i):=
  NormalizedLegendreProjectiveModel318.curve_equation _ t y
end PELOriginalNormalizedDoubleCover318
