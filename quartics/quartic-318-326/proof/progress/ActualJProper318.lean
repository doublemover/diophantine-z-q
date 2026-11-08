module
public import ActualJSurjective318
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public section
noncomputable section
namespace ActualJProper318
open Function Topology AllCuspFilling318 AllCuspInfinity318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318 QuotientJ318
set_option maxHeartbeats 0

/-- Exact identification of compact finite-j inverse images in the actual
open curve and its already-constructed all-cusp compactification. -/
lemma finite_preimage_image (N : ℕ) (hN : 5≤N) (K : Set ℂ) :
    original N hN '' ((jMap N) ⁻¹' K)=
      (jInfinity N hN) ⁻¹' ((fun z:ℂ => (z:OnePoint ℂ)) '' K) := by
  ext p
  constructor
  · rintro ⟨b,hb,rfl⟩
    rw [Set.mem_preimage,jInfinity_original]
    exact ⟨jMap N b,hb,rfl⟩
  · intro hp
    rcases original_or_cusp N hN p with ⟨b,rfl⟩|⟨c,rfl⟩
    · rw [Set.mem_preimage,jInfinity_original] at hp
      obtain ⟨z,hz,he⟩ := hp
      refine ⟨b,?_,rfl⟩
      change jMap N b∈K
      rwa [←OnePoint.coe_injective he]
    · rw [Set.mem_preimage,jInfinity_cusp] at hp
      obtain ⟨z,_,he⟩ := hp
      exact False.elim (OnePoint.coe_ne_infty z he)

/-- Genuine j on the actual noncompact fine-level quotient has compact
preimages of compact sets. Cusps cannot enter a finite-j inverse image. -/
theorem compact_preimage (N : ℕ) (hN : 5≤N) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact ((jMap N) ⁻¹' K) := by
  letI := AllCuspCompact318.filled_compactSpace N hN
  apply (original_openEmbedding N hN).isEmbedding.isCompact_iff.mpr
  rw [finite_preimage_image N hN K]
  exact (jInfinity_continuous N hN).isProperMap.isCompact_preimage
    (hK.image OnePoint.continuous_coe)

/-- Actual topological properness of genuine j, derived rather than supplied
as a modular comparison hypothesis. -/
theorem proper (N : ℕ) (hN : 5≤N) : IsProperMap (jMap N) :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨HolomorphicQuotientJ318.jMap_continuous N hN,fun _ hK => compact_preimage N hN hK⟩

/-- Every genuine finite j-fiber on the actual analytic quotient is compact. -/
theorem compact_fiber (N : ℕ) (hN : 5≤N) (z : ℂ) : IsCompact ((jMap N) ⁻¹' {z}) :=
  (proper N hN).isCompact_preimage isCompact_singleton

end ActualJProper318
