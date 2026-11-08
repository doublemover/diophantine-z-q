module
public import LiteralKernelOpenClosed318
public section
noncomputable section
namespace LiteralKernelFiniteRange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

lemma range_comp_of_isIso {X Y Z:Scheme.{u}} (f:X ⟶ Y) [IsIso f] (g:Y ⟶ Z) :
    Set.range (f ≫ g)=Set.range g := by
  change Set.range (g ∘ f)=Set.range g
  have hs : Set.range f=Set.univ := Set.range_eq_univ.mpr f.homeomorph.surjective
  rw [Set.range_comp,hs,Set.image_univ]

variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

lemma intoGlobal_range : Set.range (LiteralKernelOpenClosed318.intoGlobal N)=
    (pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)) ⁻¹'
      Set.range (WeierstrassGluing318.finiteChart A B) := by
  rw [←(LiteralKernelOpenClosed318.isPullback N).isoPullback_hom_fst,range_comp_of_isIso]
  exact IsOpenImmersion.range_pullbackFst (WeierstrassGluing318.finiteChart A B)
    (pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))

/-- Exact image of the original rank-eight component in the actual global
kernel: precisely the inverse image of the whole finite curve chart. -/
theorem canonical_range : Set.range (ThreeTorsionTriplingFiber318.toFiber A B hD)=
    (pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)) ⁻¹'
      Set.range (WeierstrassGluing318.finiteChart A B) := by
  rw [LiteralKernelOpenClosed318.canonical_eq,range_comp_of_isIso,intoGlobal_range]
end LiteralKernelFiniteRange318
