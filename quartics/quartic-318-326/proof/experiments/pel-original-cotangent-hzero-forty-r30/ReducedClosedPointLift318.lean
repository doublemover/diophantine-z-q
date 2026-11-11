module
public import ReducedSchemePointFactorization318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace ReducedClosedPointLift318
open AlgebraicGeometry CategoryTheory
variable {X Y Z : Scheme} (i : X ⟶ Z) (g : Y ⟶ Z)
  [IsClosedImmersion i] [IsReduced X] [IsReduced Y] [QuasiCompact g]
/-- A range inclusion into an ACTUAL reduced closed subscheme implies
inclusion of the actual kernel ideal sheaves. No replacement by the
reduction of that subscheme occurs. -/
theorem kernel_le (h : Set.range g ⊆ Set.range i) : i.ker ≤ g.ker := by
  have hs : g.ker.support ≤ i.ker.support := by
    change (g.ker.support : Set Z) ⊆ (i.ker.support : Set Z)
    rw [g.support_ker,i.support_ker]
    exact closure_mono h
  have he := Scheme.IdealSheafData.vanishingIdeal_antimono hs
  rw [Scheme.IdealSheafData.vanishingIdeal_support,
    Scheme.IdealSheafData.vanishingIdeal_support,
    ReducedSchemePointFactorization318.kernel_radical i,
    ReducedSchemePointFactorization318.kernel_radical g] at he
  exact he
@[expose] def lift (h : Set.range g ⊆ Set.range i) : Y ⟶ X :=
  IsClosedImmersion.lift i g (kernel_le i g h)
@[reassoc] theorem lift_fac (h : Set.range g ⊆ Set.range i) : lift i g h ≫ i = g :=
  IsClosedImmersion.lift_fac i g (kernel_le i g h)
end ReducedClosedPointLift318
