module
public import ReducedSchemePointFactorization318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace ReducedSourceClosedLift318
open AlgebraicGeometry CategoryTheory
variable {X Y Z : Scheme} (i : X ⟶ Z) (g : Y ⟶ Z)
  [IsClosedImmersion i] [IsReduced Y] [QuasiCompact g]

/-- A reduced SOURCE factors through any actual closed subscheme whose
underlying support contains its image. The target closed subscheme may
have nilpotents or multiplicities; its full kernel ideal is retained. -/
theorem kernel_le (h : Set.range g ⊆ Set.range i) : i.ker ≤ g.ker := by
  have hs : g.ker.support ≤ i.ker.support := by
    change (g.ker.support : Set Z) ⊆ (i.ker.support : Set Z)
    rw [g.support_ker,i.support_ker]
    exact closure_mono h
  have he := Scheme.IdealSheafData.vanishingIdeal_antimono hs
  rw [Scheme.IdealSheafData.vanishingIdeal_support,
    Scheme.IdealSheafData.vanishingIdeal_support,
    ReducedSchemePointFactorization318.kernel_radical g] at he
  exact (Scheme.IdealSheafData.le_radical i.ker).trans he
@[expose] def lift (h : Set.range g ⊆ Set.range i) : Y ⟶ X :=
  IsClosedImmersion.lift i g (kernel_le i g h)
@[reassoc] lemma lift_fac (h : Set.range g ⊆ Set.range i) : lift i g h≫i=g :=
  IsClosedImmersion.lift_fac i g (kernel_le i g h)
end ReducedSourceClosedLift318
