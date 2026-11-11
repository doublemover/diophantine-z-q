module
public import OriginalZoomIntegralFiber318
public import OriginalExcludedPlaceData318
public section
noncomputable section
namespace OriginalZoomFiberLattice318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j,RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)

/-- The unique field scalar taking the actual nonzero integral q0 fiber
coefficient to the ORIGINAL scaled q0 value. This constructs a local
principal lattice, not an identification with the global Hodge lattice. -/
@[expose] def generator : K c t := ContactBicanonicalPointHeight318.a0 c t hn i /
  algebraMap (V c t w) (K c t) (OriginalZoomIntegralFiber318.b0 c t w D I)

theorem generator_ne : generator c t hn i w D I≠0 :=
  div_ne_zero (ContactBicanonicalPointHeight318.a0_ne c t hn i)
    (OriginalZoomIntegralFiber318.field_b0_ne c t w D I)

theorem original0 : algebraMap (V c t w) (K c t) (OriginalZoomIntegralFiber318.b0 c t w D I)*
    generator c t hn i w D I=ContactBicanonicalPointHeight318.a0 c t hn i := by
  unfold generator
  field_simp [OriginalZoomIntegralFiber318.field_b0_ne c t w D I]

theorem original1 : algebraMap (V c t w) (K c t) (OriginalZoomIntegralFiber318.b1 c t w D I)*
    generator c t hn i w D I=ContactBicanonicalPointHeight318.a1 c t hn i := by
  rw [OriginalZoomIntegralFiber318.field_ratio,mul_assoc,original0,
    ContactBicanonicalPointHeight318.ratio]

theorem original_mem (n : Fin 2) :
    (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)∈
        FinitePlacePrincipalLattice318.lattice w (generator c t hn i w D I) := by
  fin_cases n
  · exact (FinitePlacePrincipalLattice318.mem_iff w _ _).mpr
      ⟨OriginalZoomIntegralFiber318.b0 c t w D I,original0 c t hn i w D I⟩
  · exact (FinitePlacePrincipalLattice318.mem_iff w _ _).mpr
      ⟨OriginalZoomIntegralFiber318.b1 c t w D I,original1 c t hn i w D I⟩

/-- Both original section bounds use the exact SAME actual integral
fiber-generated local lattice, at every place including2 and collisions. -/
theorem original_norm_bound (n : Fin 2) :
    w (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*
        (w (generator c t hn i w D I))⁻¹≤1 :=
  (FinitePlacePrincipalLattice318.mem_iff_norm w _ (generator_ne c t hn i w D I) _).mp
    (original_mem c t hn i w D I n)
end OriginalZoomFiberLattice318
