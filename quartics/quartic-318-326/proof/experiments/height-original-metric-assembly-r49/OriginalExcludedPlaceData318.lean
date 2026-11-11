module
public import OriginalGoodLatticeFrameChange318
public section
noncomputable section
namespace OriginalExcludedPlaceData318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
/-- Exactly the finite places excluded by the proved arithmetic model. -/
@[expose] def BadPlace := {v : FinitePlace (K c t) // v (denominator c:K c t)≠1}
instance badPlace_finite : Finite (BadPlace c t) :=
  (ContactFinitePlaceBaseMap318.excluded_places_finite (K:=K c t) c).to_subtype

variable (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
/-- The remaining excluded-place input is explicit and finite: specified
nonzero local lattice generators containing the two ORIGINAL sections.
This record does not claim these generators have been constructed from a
bad-prime model or satisfy the later Hodge/KS lattice identification. -/
structure ExcludedGenerators where
  generator : BadPlace c t → K c t
  nonzero : ∀ b, generator b≠0
  original_mem : ∀ (b : BadPlace c t) (n : Fin 2),
    (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)∈
        FinitePlacePrincipalLattice318.lattice b.val (generator b)

variable (B : ExcludedGenerators c t hn i)
@[expose] def excludedNorm (b : BadPlace c t) : ℝ := (b.val (B.generator b))⁻¹
theorem excludedNorm_pos (b : BadPlace c t) : 0<excludedNorm c t hn i B b :=
  inv_pos.mpr (b.val.pos (B.nonzero b))
theorem excluded_bound (b : BadPlace c t) (n : Fin 2) :
    b.val (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*excludedNorm c t hn i B b≤1 :=
  (FinitePlacePrincipalLattice318.mem_iff_norm b.val _ (B.nonzero b) _).mp (B.original_mem b n)
end OriginalExcludedPlaceData318
