module
public import PELOriginalCM210NativePrimeResidue318
public import Mathlib.RingTheory.Ideal.Maps
public section
noncomputable section
namespace PELOriginalCM210PrimeIdealTransport318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210PrimeReduction318 PELOriginalCM210NativePrimeResidue318
variable (p:ℕ) (hp:(p:ℤ)∣210)
lemma map_kernel : Ideal.map integerEquiv.toRingHom (kernel p hp)=nativeIdeal p hp := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    exact (image_mem p hp z).mpr hz
  · intro z hz
    obtain ⟨x,rfl⟩ := integerEquiv.surjective z
    exact Ideal.mem_map_of_mem integerEquiv.toRingHom ((image_mem p hp x).mp hz)
lemma map_principal : Ideal.map integerEquiv.toRingHom (Ideal.span ({(p:R)}:Set R))=
    Ideal.span ({(p:O)}:Set O) := by
  rw [Ideal.map_span,Set.image_singleton,map_natCast]
end PELOriginalCM210PrimeIdealTransport318
