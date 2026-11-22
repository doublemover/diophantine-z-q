module

public import SelectedActualLocalizedNormalizationSameField318
public import SelectedNormalizedEtaleDJ318
public import EtaleNormalization318

public section
noncomputable section

open scoped Polynomial TensorProduct
open SelectedActualLocalizedNormalizationSameField318

namespace SelectedActualMonicOrdinaryNormalizationComparison318

variable {R A B O K F : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing O]
  [Field K] [Field F] [Algebra R A] [Algebra R B] [Algebra R O] [Algebra R F]
  [Algebra A O] [Algebra B O] [Algebra A F] [Algebra B F] [Algebra O F] [Algebra A K]
  [IsScalarTower R A O] [IsScalarTower R B O] [IsScalarTower R A F]
  [IsScalarTower R B F] [IsScalarTower A O F] [IsScalarTower B O F]
  [IsIntegralClosure B R F] [Algebra.IsIntegral R B]
  [IsFractionRing A K] [IsIntegrallyClosed A]

/-- The complex ordinary monic quotient is compared to the
existing localization of the finite normalization in the original
whole field. Its finite and étale properties are derived from
the monic equation and derivative unit, and the comparison is
checked on all values in that same field, in particular the
original marked monic root. -/
theorem ordinary_monic_compares_in_the_whole_field
    (M : Submonoid R) [IsLocalization M A]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) O]
    (p : A[X]) (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (E : (AdjoinRoot p ⊗[A] K) ≃ₐ[A] F) :
    ∃ e : AdjoinRoot p ≃ₐ[A] O,
      ∀ z : AdjoinRoot p, algebraMap O F (e z) = E (z ⊗ₜ[A] (1 : K)) := by
  let C := AdjoinRoot p
  let G := C ⊗[A] K
  let j : C →+* F := E.toRingHom.comp (algebraMap C G)
  letI : Algebra C F := j.toAlgebra
  letI : IsScalarTower A C F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A F a = E (algebraMap C G (algebraMap A C a))
    exact (E.commutes a).symm.trans
      (congrArg E (IsScalarTower.algebraMap_apply A C G a))
  letI : Module.Finite A C := hp.finite_adjoinRoot
  letI : Algebra.Etale A C := SelectedNormalizedEtaleDJ318.etale_of_derivative p hp hd
  letI : IsIntegralClosure C A G :=
    EtaleNormalization318.smooth_finite_integralClosure (R := A) (S := C) (K := K)
  letI : IsIntegralClosure C A F := by
    constructor
    · exact E.injective.comp (IsIntegralClosure.algebraMap_injective C A G)
    · intro y
      constructor
      · intro hy
        obtain ⟨z,hz⟩ := (IsIntegralClosure.isIntegral_iff
          (A := C) (R := A) (B := G)).mp (hy.map E.symm.toAlgHom)
        refine ⟨z,?_⟩
        change E (algebraMap C G z) = y
        exact (congrArg E hz).trans (E.apply_symm_apply y)
      · rintro ⟨z,rfl⟩
        exact ((IsIntegralClosure.isIntegral_iff (A := C) (R := A) (B := G)).mpr
          ⟨z,rfl⟩).map E.toAlgHom
  obtain ⟨e,he⟩ := comparison_preserves_the_whole_field
    (R := R) (A := A) (B := B) (O := O) (F := F) (C := C) M
  refine ⟨e,?_⟩
  intro z
  exact (he z).trans (congrArg E (Algebra.TensorProduct.algebraMap_apply z))

end SelectedActualMonicOrdinaryNormalizationComparison318

#print axioms SelectedActualMonicOrdinaryNormalizationComparison318.ordinary_monic_compares_in_the_whole_field
