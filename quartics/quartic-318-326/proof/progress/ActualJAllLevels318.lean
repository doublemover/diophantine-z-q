module
public import GammaOneLevelMap318
public section
noncomputable section
namespace ActualJAllLevels318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318 QuotientJ318 GammaOneLevelMap318
set_option maxHeartbeats 0

lemma preimage_eq_image {N M : ℕ} (h : N∣M) (K : Set ℂ) :
    (jMap N) ⁻¹' K=forget h '' ((jMap M) ⁻¹' K) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p,rfl⟩ := forget_surjective h q
    exact ⟨p,by simpa only [Set.mem_preimage,j_forget] using hq,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,j_forget] using hp

/-- Compact finite-j inverse images for every positive level, including
levels with elliptic stabilizers. The high-level result descends through an
actual continuous surjective level-forgetting map. -/
theorem compact_preimage (N : ℕ) [NeZero N] {K : Set ℂ} (hK : IsCompact K) :
    IsCompact ((jMap N) ⁻¹' K) := by
  have hN : 0<N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 5≤5*N := by omega
  let hd : N∣5*N := dvd_mul_left N 5
  rw [preimage_eq_image hd K]
  exact (ActualJProper318.compact_preimage (5*N) hM hK).image (forget_continuous hd)

lemma continuous_j (N : ℕ) : Continuous (jMap N) := by
  apply continuous_quot_lift
  exact QuotientJ318.j_holomorphic.continuous

/-- Genuine j is topologically proper at every positive level. -/
theorem proper (N : ℕ) [NeZero N] : IsProperMap (jMap N) :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨continuous_j N,fun _ hK => compact_preimage N hK⟩

/-- Every genuine quotient j-fiber is finite at every positive level. -/
theorem finite_fiber (N : ℕ) [NeZero N] (z : ℂ) : ((jMap N) ⁻¹' {z}).Finite :=
  (compact_preimage N isCompact_singleton).finite (ActualJFinite318.discrete_fiber N z)

end ActualJAllLevels318
