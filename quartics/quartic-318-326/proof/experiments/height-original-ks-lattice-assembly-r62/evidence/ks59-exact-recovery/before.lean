module
public import FourRootOrderOpenMaps318
public import Mathlib.Algebra.Module.Torsion.Free
public section
noncomputable section
namespace FourRootOrderLocalizationMaps318
open scoped TensorProduct
variable {A T C : Type*} [CommRing A] [CommRing T] [CommRing C] [Algebra A T]
variable (a : Fin 4 → A)
variable (e : FourRootOrder318.Order (fun i => algebraMap A T (a i)) ≃+* C)

/-- The actual base-change map followed by the displayed target equivalence. -/
@[expose] def map : FourRootOrder318.Order a →+* C :=
  e.toRingHom.comp
    ((FourRootOrder318.baseChange a T).toRingHom.comp
      (Algebra.TensorProduct.includeRight : FourRootOrder318.Order a →ₐ[A]
        T ⊗[A] FourRootOrder318.Order a).toRingHom)
@[expose] def sourceAlgebra : Algebra (FourRootOrder318.Order a) C :=
  (map a e).toAlgebra

/-- Compare over the SOURCE order, not merely over the localized coefficient
ring. This pins the exact algebra needed for the localization predicate. -/
@[expose] def localizedEquiv :
    letI := sourceAlgebra a e
    FourRootOrder318.Order a ⊗[A] T ≃ₐ[FourRootOrder318.Order a] C := by
  letI := sourceAlgebra a e
  exact { ((Algebra.TensorProduct.comm A (FourRootOrder318.Order a) T).toRingEquiv.trans
      (FourRootOrder318.baseChange a T).toRingEquiv).trans e with
    commutes' := by intro z; rfl }

theorem localization (x : A) [IsLocalization.Away x T] :
    letI := sourceAlgebra a e
    IsLocalization.Away (algebraMap A (FourRootOrder318.Order a) x) C := by
  letI := sourceAlgebra a e
  letI : IsLocalization.Away (algebraMap A (FourRootOrder318.Order a) x)
      (FourRootOrder318.Order a ⊗[A] T) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid (FourRootOrder318.Order a) (Submonoid.powers x))
        (FourRootOrder318.Order a ⊗[A] T))
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap A (FourRootOrder318.Order a) x)) (localizedEquiv a e)

/-- The scalar being inverted is regular because the ACTUAL four-root
order is free over its domain coefficient ring. The order need not already
be known to be a domain. -/
theorem scalar_regular [IsDomain A] (x : A) (hx : x ≠ 0) :
    algebraMap A (FourRootOrder318.Order a) x ∈ nonZeroDivisors (FourRootOrder318.Order a) := by
  letI : Module.Free A (FourRootOrder318.Order a) := (FourRootOrder318.finite_free a).2
  rw [mem_nonZeroDivisors_iff_left]
  intro z hz
  have hz' : x • z = 0 :=
    (IsScalarTower.algebraMap_smul (FourRootOrder318.Order a) x z).symm.trans hz
  exact (smul_eq_zero.mp hz').resolve_left hx

theorem map_injective [IsDomain A] (x : A) (hx : x ≠ 0) [IsLocalization.Away x T] :
    Function.Injective (map a e) := by
  letI := sourceAlgebra a e
  letI := localization a e x
  exact IsLocalization.injective C (Submonoid.powers_le.mpr (scalar_regular a x hx))

end FourRootOrderLocalizationMaps318
