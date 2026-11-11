module
public import VaryingWordChartGluing318
public import CyclicQuotientFiniteFlat318
public section
noncomputable section
namespace VaryingNormalizedUniversalFamily318
open AlgebraicGeometry CategoryTheory VaryingNormalizedWordFrame318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
@[expose] def frame := framed R A ι w N (VaryingNormalizedWordOverlap318.universal R A ι w)
abbrev quotient := (N ⊗[R] A) ⧸ ideal (frame R A ι w).action (frame R A ι w).marked
@[expose] def basis : Basis ι N (quotient R A ι w) :=
  CyclicQuotientKernel318.quotientBasis (frame R A ι w).action (frame R A ι w).marked
    (VaryingSourceWordQuotient318.standardBasis ι N) (frame R A ι w).cyclic

/-- The universal quotient has exactly the original chosen source-word
images as its basis, not an arbitrary rank witness. -/
lemma basis_word (j : ι) : basis R A ι w j=
    Ideal.Quotient.mk (ideal (frame R A ι w).action (frame R A ι w).marked)
      ((1 : N) ⊗ₜ[R] (w j).prod) := by
  apply (CyclicQuotientKernel318.quotientEquiv (frame R A ι w).action
    (frame R A ι w).marked (frame R A ι w).cyclic).injective
  rw [CyclicQuotientKernel318.quotientBasis_image,CyclicQuotientKernel318.quotientEquiv_mk]
  change (VaryingSourceWordQuotient318.standardBasis ι N) j=
    evaluation (frame R A ι w).action (frame R A ι w).marked ((1 : N) ⊗ₜ[R] (w j).prod)
  rw [normalized R A ι w N (VaryingNormalizedWordOverlap318.universal R A ι w) j]
  exact congrFun (Basis.coe_ofEquivFun (LinearEquiv.refl N (ι → N))) j

abbrev family : Scheme := CyclicQuotientFiniteFlat318.scheme (frame R A ι w).action (frame R A ι w).marked
abbrev intoSource : family R A ι w ⟶ Spec (CommRingCat.of (N ⊗[R] A)) :=
  CyclicQuotientFiniteFlat318.into (frame R A ι w).action (frame R A ι w).marked
abbrev projection : family R A ι w ⟶ VaryingNormalizedOverlapScheme318.chart R A ι w :=
  CyclicQuotientFiniteFlat318.projection (frame R A ι w).action (frame R A ι w).marked
instance closed : IsClosedImmersion (intoSource R A ι w) := inferInstance
instance finite : IsFinite (projection R A ι w) :=
  CyclicQuotientFiniteFlat318.finite (frame R A ι w).action (frame R A ι w).marked
    (VaryingSourceWordQuotient318.standardBasis ι N) (frame R A ι w).cyclic
instance flat : Flat (projection R A ι w) :=
  CyclicQuotientFiniteFlat318.flat (frame R A ι w).action (frame R A ι w).marked
    (VaryingSourceWordQuotient318.standardBasis ι N) (frame R A ι w).cyclic
end VaryingNormalizedUniversalFamily318
