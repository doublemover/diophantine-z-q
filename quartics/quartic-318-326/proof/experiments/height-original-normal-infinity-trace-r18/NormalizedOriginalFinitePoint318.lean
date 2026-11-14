module
public import FourRootIndividualScales318
public import DVRNormalizedFiniteOrder318
public import IntegralValuativeChartPoints318
public section
noncomputable section
namespace NormalizedOriginalFinitePoint318
open Polynomial IntegralSourceBranches318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type*) [Field K] (c : Fin 4 → Kˣ) (d s : Fin 4 → K)
  (hs : ∀ i,s i≠0) (hc : ∀ i,(c i:K)=d i*(s i)^2)
abbrev NormalizedOrder := DVRNormalizedFiniteOrder318.Order K d (contacts K)
@[expose] def scaleUnit (i : Fin 4) : K[X]ˣ :=
  Units.map Polynomial.C.toMonoidHom (Units.mk0 (s i) (hs i))

include hc in
theorem coefficient_relation (i : Fin 4) :
    coefficient K c i=DVRNormalizedFiniteOrder318.coefficient K d (contacts K) i*
      (scaleUnit K s hs i:K[X])^2 := by
  change C (c i:K)*(X-C (contacts K i))=
    (C (d i)*(X-C (contacts K i)))*(C (s i))^2
  rw [hc i,map_mul,map_pow]
  ring

/-- The normalized finite generic order is the SAME original four-root
source after the four specified square scalings; the whole polynomial base,
including the original t coordinate, is fixed by the algebra equivalence. -/
@[expose] def sourceEquiv : SourceOrder K c ≃ₐ[K[X]] NormalizedOrder K d :=
  FourRootIndividualScales318.four _ _ (scaleUnit K s hs)
    (coefficient_relation K c d s hs hc)

theorem sourceEquiv_polynomial (p : K[X]) :
    sourceEquiv K c d s hs hc (algebraMap K[X] (SourceOrder K c) p)=
      algebraMap K[X] (NormalizedOrder K d) p :=
  (sourceEquiv K c d s hs hc).commutes p

theorem sourceEquiv_root (i : Fin 4) :
    sourceEquiv K c d s hs hc (FourRootOrderSigns318.generator (coefficient K c) i)=
      algebraMap K[X] (NormalizedOrder K d) (C (s i))*
        FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient K d (contacts K)) i := by
  have h := FourRootIndividualScales318.four_generator
    (DVRNormalizedFiniteOrder318.coefficient K d (contacts K)) (coefficient K c)
    (scaleUnit K s hs) (coefficient_relation K c d s hs hc) i
  simpa only [Algebra.smul_def] using h

variable (t : K) (y : Fin 4 → K)
  (hy : ∀ i,(y i)^2=(c i:K)*(t-contacts K i))
include hs hc hy in
theorem normalized_roots (i : Fin 4) : (y i/s i)^2=d i*(t-contacts K i) :=
  DVRNormalizedContactPoint318.root_relation _ _ _ _ _ _ (hs i) (hc i) (hy i)

/-- Equality of the ENTIRE original point map under the actual order
isomorphism. This checks every polynomial coefficient and every signed root,
not only squareclasses or the projective coordinate. -/
theorem source_point :
    (DVRNormalizedFiniteOrder318.pointMap K d (contacts K) t (fun i => y i/s i)
      (normalized_roots K c d s hs hc t y hy)).comp
        (sourceEquiv K c d s hs hc).toRingHom=
      IntegralValuativeChartPoints318.finiteMap K c t y hy := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change DVRNormalizedFiniteOrder318.pointMap K d (contacts K) t (fun i => y i/s i)
        (normalized_roots K c d s hs hc t y hy)
        (sourceEquiv K c d s hs hc (algebraMap K[X] (SourceOrder K c) (C r)))=_
      rw [sourceEquiv_polynomial,DVRNormalizedFiniteOrder318.pointMap_polynomial,
        IntegralValuativeChartPoints318.finiteMap_polynomial]
    · change DVRNormalizedFiniteOrder318.pointMap K d (contacts K) t (fun i => y i/s i)
        (normalized_roots K c d s hs hc t y hy)
        (sourceEquiv K c d s hs hc (algebraMap K[X] (SourceOrder K c) X))=_
      rw [sourceEquiv_polynomial,DVRNormalizedFiniteOrder318.pointMap_polynomial,
        IntegralValuativeChartPoints318.finiteMap_polynomial]
  · intro i
    change DVRNormalizedFiniteOrder318.pointMap K d (contacts K) t (fun i => y i/s i)
      (normalized_roots K c d s hs hc t y hy)
      (sourceEquiv K c d s hs hc (FourRootOrderSigns318.generator (coefficient K c) i))=_
    rw [sourceEquiv_root,map_mul,DVRNormalizedFiniteOrder318.pointMap_polynomial,
      Polynomial.eval_C,DVRNormalizedFiniteOrder318.pointMap_root,
      IntegralValuativeChartPoints318.finiteMap_generator]
    exact DVRNormalizedContactPoint318.original_root _ _ (hs i)
end NormalizedOriginalFinitePoint318
