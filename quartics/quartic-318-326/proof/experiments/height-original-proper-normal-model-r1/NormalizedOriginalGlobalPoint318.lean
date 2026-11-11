module
public import NormalizedWholeScaleProjection318
public import NormalizedOriginalFinitePoint318
public section
noncomputable section
namespace NormalizedOriginalGlobalPoint318
open Polynomial CategoryTheory AlgebraicGeometry IntegralSourceBranches318
open NormalizedWholeGluing318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type*) [Field K] (c : Fin 4 → Kˣ) (d s : Fin 4 → K)
  (hs : ∀ i,s i≠0) (hc : ∀ i,(c i:K)=d i*(s i)^2)

/-- The generic whole proper models before and after the actual local
square normalization are globally isomorphic, with every signed multiplier
and the original projective contact coordinate retained. -/
@[expose] def comparison : scheme K d (contacts K) ≅ scheme K (fun i => (c i:K)) (contacts K) :=
  NormalizedWholeScaleScheme318.modelIso K (fun i => (c i:K)) d (contacts K)
    (fun i => Units.mk0 (s i) (hs i)) hc

theorem comparison_over_line : (comparison K c d s hs hc).hom ≫
    NormalizedWholeProjection318.projection K (fun i => (c i:K)) (contacts K)=
      NormalizedWholeProjection318.projection K d (contacts K) :=
  NormalizedWholeScaleProjection318.over_projective_line K (fun i => (c i:K)) d (contacts K)
    (fun i => Units.mk0 (s i) (hs i)) hc

variable (t : K) (y : Fin 4 → K)
  (hy : ∀ i,(y i)^2=(c i:K)*(t-contacts K i))

/-- The original whole-source field point is the image of its normalized
field point under the actual global comparison. The proof uses equality of
whole ring maps, not merely equality of the projective t coordinate. These
are the possibly singular four-root models, not a claimed smooth normalization. -/
theorem original_point :
    Spec.map (CommRingCat.ofHom
      (DVRNormalizedFiniteOrder318.pointMap K d (contacts K) t (fun i => y i/s i)
        (NormalizedOriginalFinitePoint318.normalized_roots K c d s hs hc t y hy))) ≫
      finiteChart K d (contacts K) ≫ (comparison K c d s hs hc).hom=
    Spec.map (CommRingCat.ofHom (IntegralValuativeChartPoints318.finiteMap K c t y hy)) ≫
      finiteChart K (fun i => (c i:K)) (contacts K) := by
  change Spec.map (CommRingCat.ofHom _) ≫
    (finiteChart K d (contacts K) ≫ NormalizedWholeScaleScheme318.forward K
      (fun i => (c i:K)) d (contacts K) (fun i => Units.mk0 (s i) (hs i)) hc)=_
  rw [NormalizedWholeScaleScheme318.finite_forward,←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((DVRNormalizedFiniteOrder318.pointMap K d (contacts K) t (fun i => y i/s i)
      (NormalizedOriginalFinitePoint318.normalized_roots K c d s hs hc t y hy)).comp
      (NormalizedOriginalFinitePoint318.sourceEquiv K c d s hs hc).toRingHom)) ≫ _ = _
  rw [NormalizedOriginalFinitePoint318.source_point]
end NormalizedOriginalGlobalPoint318
