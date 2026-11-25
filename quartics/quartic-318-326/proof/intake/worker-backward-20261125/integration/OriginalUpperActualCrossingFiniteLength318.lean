module
public import OriginalUpperActualFibreCrossingIdeal318
public import Mathlib.RingTheory.HopkinsLevitzki

public section
noncomputable section
namespace OriginalUpperActualCrossingFiniteLength318

open AlgebraicGeometry TopologicalSpace Order
open OriginalUpperActualFibreComponents318 (C)
open OriginalUpperActualFibreIncidence318 (common)
open OriginalUpperActualFibreCrossingIdeal318 (cross cross_dim_zero length)

universe u
variable {X Z : Scheme.{u}} [IsIntegral X] (s : X ⟶ Z) (p : Z)
variable (E F : C s p) (x : X) (hx : x ∈ common s p E F)
local notation "A" => X.presheaf.stalk x
local notation "B" => A ⧸ cross s p E F x hx
variable [noeth : IsNoetherianRing (X.presheaf.stalk x)]

/-- Finiteness of the actual ordinary-stalk intersection quotient's
length. This route does not require a split point or a chosen simple
local node chart. Optional: Hopkins–Levitzki stock is not installed. -/
include noeth in
theorem length_not_infty (different : E ≠ F) (closed : IsClosed ({p} : Set Z))
    (vertical : s (genericPoint X) ≠ p) (dim : ∀ y : X, coheight y ≤ 2) :
    length s p E F x hx ≠ ⊤ := by
  letI : Ring.KrullDimLE 0 B := cross_dim_zero s p E F x hx different closed vertical dim
  letI : IsArtinianRing B := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  change Module.length A B ≠ ⊤
  rw [Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end OriginalUpperActualCrossingFiniteLength318

#print axioms OriginalUpperActualCrossingFiniteLength318.length_not_infty
