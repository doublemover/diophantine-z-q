module
public import ContactKummerCover318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace ContactKummerOpenDomain318
set_option maxHeartbeats 400000
open scoped TensorProduct
open ContactKummerOrder318

/-- Localizing the actual domain order, not selecting a generic component,
proves that the entire finite-etale contact cover is a domain. -/
theorem open_domain (c:Fin 4→ℚˣ) : IsDomain (OpenOrder c) := by
  letI:IsDomain (SourceOrder c):=source_domain c
  letI:Module.Free R (SourceOrder c):=(source_finite_free c).2
  have hi:Function.Injective (algebraMap R (SourceOrder c)):=
    FaithfulSMul.algebraMap_injective R (SourceOrder c)
  have hd:algebraMap R (SourceOrder c) denominator≠0 := by
    simpa only [map_zero] using hi.ne denominator_ne_zero
  letI:IsLocalization.Away (algebraMap R (SourceOrder c) denominator)
      (SourceOrder c⊗[R]OpenBase) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (SourceOrder c)
        (Submonoid.powers denominator)) (SourceOrder c⊗[R]OpenBase))
  letI:IsDomain (SourceOrder c⊗[R]OpenBase):=
    IsLocalization.Away.isDomain (SourceOrder c⊗[R]OpenBase) hd
  let e:OpenOrder c≃+*(SourceOrder c⊗[R]OpenBase):=
    (openBaseChange c).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm R OpenBase (SourceOrder c)).toRingEquiv
  exact Function.Injective.isDomain e e.injective

end ContactKummerOpenDomain318
