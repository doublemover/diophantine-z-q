module
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace NormalitySpanDescent318
open scoped nonZeroDivisors
set_option maxHeartbeats 500000
variable {R:Type*} [CommRing R] [IsDomain R]

/-- Normality descends from any family of principal opens spanning the unit
ideal. No normality of the original domain is assumed. -/
theorem of_principal_cover {ι:Type*} (d:ι→R)
    (hs:Ideal.span (Set.range d)=⊤)
    (hn:∀i,IsIntegrallyClosed (Localization.Away (d i))) : IsIntegrallyClosed R:=by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  obtain ⟨i,hi⟩:∃i,d i∉p:=by
    by_contra! h
    have hle:Ideal.span (Set.range d)≤p:=Ideal.span_le.mpr (by
      rintro _ ⟨i,rfl⟩
      exact h i)
    rw [hs] at hle
    exact (Ideal.IsPrime.ne_top (inferInstance : p.IsPrime)) (top_le_iff.mp hle)
  let S:=Localization.Away (d i)
  let T:=Localization.AtPrime p
  have hle:Submonoid.powers (d i)≤p.primeCompl:=Submonoid.powers_le.mpr hi
  have hreg:Submonoid.powers (d i)≤R⁰:=hle.trans p.primeCompl_le_nonZeroDivisors
  letI:IsDomain S:=IsLocalization.isDomain_of_le_nonZeroDivisors S hreg
  letI:IsIntegrallyClosed S:=hn i
  letI:Algebra S T:=IsLocalization.localizationAlgebraOfSubmonoidLe S T
    (Submonoid.powers (d i)) p.primeCompl hle
  letI:IsScalarTower R S T:=IsLocalization.localization_isScalarTower_of_submonoid_le
    S T (Submonoid.powers (d i)) p.primeCompl hle
  letI:IsLocalization (p.primeCompl.map (algebraMap R S)) T:=
    IsLocalization.isLocalization_of_submonoid_le S T (Submonoid.powers (d i)) p.primeCompl hle
  apply isIntegrallyClosed_of_isLocalization T (p.primeCompl.map (algebraMap R S))
  rintro _ ⟨y,hy,rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  simpa only [map_zero] using (IsLocalization.injective S hreg).ne
    (mem_nonZeroDivisors_iff_ne_zero.mp (p.primeCompl_le_nonZeroDivisors hy))
end NormalitySpanDescent318
