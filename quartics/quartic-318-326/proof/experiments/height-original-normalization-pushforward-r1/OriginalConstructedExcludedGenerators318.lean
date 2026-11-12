module
public import OriginalZoomFiberLattice318
public import OriginalContactBicanonicalExtension318
public section
noncomputable section
namespace OriginalConstructedExcludedGenerators318
open NumberField OriginalPointFinitePlaceRoots318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i : Fin 4)
abbrev t := OriginalContactAllPrimeNeighborhood318.coordinate u v
abbrev hn := RationalContactPoint318.parameters_ne_of_forms c u v hf

/-- The previously external excluded-place generator input is constructed
from the actual integral fiber coefficients of the original pair on the
produced smooth point neighborhoods. The Hodge/KS compatibility of these
local lattices remains a separate, explicit global comparison problem. -/
@[expose] def generators : OriginalExcludedPlaceData318.ExcludedGenerators
    c (t u v) (hn c u v hf) i where
  generator b := OriginalZoomFiberLattice318.generator c (t u v) (hn c u v hf) i b.val
    (OriginalContactAllPrimeNeighborhood318.data c u v b.val)
    (OriginalContactAllPrimeNeighborhood318.input c u v hf b.val)
  nonzero b := OriginalZoomFiberLattice318.generator_ne c (t u v) (hn c u v hf) i b.val
    (OriginalContactAllPrimeNeighborhood318.data c u v b.val)
    (OriginalContactAllPrimeNeighborhood318.input c u v hf b.val)
  original_mem b n := OriginalZoomFiberLattice318.original_mem c (t u v) (hn c u v hf) i b.val
    (OriginalContactAllPrimeNeighborhood318.data c u v b.val)
    (OriginalContactAllPrimeNeighborhood318.input c u v hf b.val) n

theorem excluded_bound (b : OriginalExcludedPlaceData318.BadPlace c (t u v)) (n : Fin 2) :
    b.val (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
      ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*
        OriginalExcludedPlaceData318.excludedNorm c (t u v) (hn c u v hf) i
          (generators c u v hf i) b≤1 :=
  OriginalExcludedPlaceData318.excluded_bound c (t u v) (hn c u v hf) i
    (generators c u v hf i) b n
end OriginalConstructedExcludedGenerators318
