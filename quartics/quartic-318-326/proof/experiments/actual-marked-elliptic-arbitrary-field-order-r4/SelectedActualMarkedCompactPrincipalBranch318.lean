module

public import SelectedActualLiteralMarkedOrdinaryNormalization318
public import SelectedActualMarkedTensorOrdinaryIntoWhole318
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Maps

public section
noncomputable section

open Polynomial
open scoped Polynomial TensorProduct
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexGenericChartClosures318 (polynomial)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra)
open SelectedActualLiteralMarkedOrdinaryNormalization318
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedTensorOrdinaryIntoWhole318

namespace SelectedActualMarkedCompactPrincipalBranch318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

/-- Localize the very marked period character in the ordinary root ring.
Its matching prime of the finite-J normal order is obtained by actual
contraction, and avoids the old denominator. The two local rings are
identified with the same prescribed values in the actual whole K. -/
theorem actual_marked_compact_branch
    (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p)))
    (hRoots : fullRootSet N p) (t : SelectedActualComplexWholeRootField318.Period) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    let F := K N p
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    let T := B F
    let W := O F
    let C := OrdinaryRoot N p
    let Q := RingHom.ker (atPeriod N p hRoots t)
    letI : Q.IsPrime := RingHom.ker_isPrime _
    ∃ (α : W →+* F) (e : C ≃ₐ[Base] W),
      α.comp (algebraMap T W) = algebraMap T F ∧
      (∀ z : C, α (e z) = intoWhole N p z) ∧
      let χW := (atPeriod N p hRoots t).comp e.symm.toRingHom
      let P₀ := (RingHom.ker χW).comap (algebraMap T W)
      ∃ hP₀ : P₀.IsPrime,
        let L := @Localization.AtPrime T _ P₀ hP₀
        algebraMap ℂ[X] T denominator ∉ P₀ ∧
        ∃ (loc : Localization.AtPrime Q ≃+* L) (β : L →+* F),
          (∀ b : T, β (algebraMap T L b) = algebraMap T F b) ∧
          ∀ z : C, β (loc (algebraMap C (Localization.AtPrime Q) z)) = intoWhole N p z := by
  letI : Field (K N p) := (whole_isField N p hf).toField
  let F := K N p
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  let T := B F
  let W := O F
  let C := OrdinaryRoot N p
  let Q := RingHom.ker (atPeriod N p hRoots t)
  letI : Q.IsPrime := RingHom.ker_isPrime _
  let U := Localization.AtPrime Q
  obtain ⟨α,e,hα,he⟩ := actual_literal_ordinary_normalization N p hp hd hf
  have hSame (z : C) : α (e z) = intoWhole N p z :=
    (he z).trans (literalWholeTensor_eq_intoWhole N p z)
  let χ := atPeriod N p hRoots t
  let χW : W →+* ℂ := χ.comp e.symm.toRingHom
  let QW := RingHom.ker χW
  letI : QW.IsPrime := RingHom.ker_isPrime _
  let P₀ := QW.comap (algebraMap T W)
  letI hP₀ : P₀.IsPrime := Ideal.comap_isPrime _ QW
  let L := Localization.AtPrime P₀
  let M : Submonoid T := Algebra.algebraMapSubmonoid T (Submonoid.powers denominator)
  let dT : T := algebraMap ℂ[X] T denominator
  have hdM : dT ∈ M := ⟨denominator,Submonoid.mem_powers denominator,rfl⟩
  have hAway : dT ∉ P₀ := by
    intro h
    have hz : χW (algebraMap T W dT) = 0 := h
    exact ((IsLocalization.map_units W (⟨dT,hdM⟩ : M)).map χW).ne_zero hz
  have hQ : QW.comap e.toRingHom = Q := by
    apply Ideal.ext
    intro a
    change χ (e.symm (e a)) = 0 ↔ χ a = 0
    rw [e.symm_apply_apply]
  have hMEquiv : Q.primeCompl.map e.toRingEquiv.toMonoidHom = QW.primeCompl := by
    rw [← hQ]
    exact RingEquiv.map_primeCompl_comap_eq e.toRingEquiv QW
  let V := Localization.AtPrime QW
  letI : Algebra T V := Algebra.compHom V (algebraMap T W)
  letI : IsScalarTower T W V := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization.AtPrime V P₀ :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M V QW
  let eW : U ≃+* V := IsLocalization.ringEquivOfRingEquiv U V e.toRingEquiv hMEquiv
  let eT : L ≃ₐ[T] V := IsLocalization.algEquiv P₀.primeCompl L V
  let loc : U ≃+* L := eW.trans eT.symm.toRingEquiv
  have hαi : Function.Injective α := by
    intro r s h
    apply e.symm.injective
    apply intoWhole_injective N p hp
    calc
      intoWhole N p (e.symm r) = α (e (e.symm r)) := (hSame (e.symm r)).symm
      _ = α (e (e.symm s)) := by simpa only [e.apply_symm_apply] using h
      _ = intoWhole N p (e.symm s) := hSame (e.symm s)
  have hInv (s : QW.primeCompl) : IsUnit (α s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hn
    have hz : (s : W) = 0 := hαi (hn.trans (map_zero α).symm)
    have hz' : (s : W) ∈ QW := hz.symm ▸ QW.zero_mem
    exact (Ideal.mem_primeCompl_iff.mp s.property) hz'
  let αloc : V →+* F := IsLocalization.lift hInv
  let β : L →+* F := αloc.comp eT.toAlgHom.toRingHom
  have hL (w : W) : αloc (algebraMap W V w) = α w := IsLocalization.lift_eq hInv w
  have hT (b : T) : algebraMap T V b = algebraMap W V (algebraMap T W b) :=
    IsScalarTower.algebraMap_apply T W V b
  have hW (z : C) : eW (algebraMap C U z) = algebraMap W V (e z) :=
    IsLocalization.ringEquivOfRingEquiv_eq hMEquiv z
  refine ⟨α,e,hα,hSame,hP₀,hAway,loc,β,?_,?_⟩
  · intro b
    change αloc (eT (algebraMap T L b)) = algebraMap T F b
    rw [eT.commutes,hT,hL]
    exact RingHom.congr_fun hα b
  · intro z
    change αloc (eT (eT.symm (eW (algebraMap C U z)))) = _
    rw [eT.apply_symm_apply,hW,hL]
    exact hSame z

end SelectedActualMarkedCompactPrincipalBranch318

#print axioms SelectedActualMarkedCompactPrincipalBranch318.actual_marked_compact_branch
