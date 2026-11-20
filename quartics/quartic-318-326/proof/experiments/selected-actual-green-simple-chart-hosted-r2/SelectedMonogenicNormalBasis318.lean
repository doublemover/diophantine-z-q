module
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Minpoly.Field
public section
noncomputable section
open Polynomial
open scoped TensorProduct

namespace SelectedMonogenicNormalBasis318

variable {R C : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [CommRing C] [Algebra R C] [Module.Flat R C] [Module.Finite R C]

/-- Gauss descent for the actual element of the actual generic tensor
algebra. The generic algebra need not be a field, domain, or connected. -/
theorem monic_kernel (x : C) :
    ∃ p : R[X], p.Monic ∧ ∀ q : R[X], aeval x q = 0 ↔ p ∣ q := by
  let K := FractionRing R
  let F := K ⊗[R] C
  let i : C →ₐ[R] F := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (A := K) (B := C) (IsFractionRing.injective R K)
  let y := i x
  have hyR : IsIntegral R y := (IsIntegral.of_finite R x).map i
  have hy : IsIntegral K y := hyR.tower_top
  have hlift (q : R[X]) :
      aeval y (q.map (algebraMap R K)) = i (aeval x q) := by
    rw [aeval_map_algebraMap]
    exact Polynomial.aeval_algHom_apply i x q
  obtain ⟨p,hp⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (minpoly.monic hyR)
    (minpoly.dvd_map_of_isScalarTower R K y)
  rw [(minpoly.monic hy).leadingCoeff,C_1,mul_one] at hp
  have hf : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hm : p.Monic := (hf.monic_map_iff (p := p)).2 (hp.symm ▸ minpoly.monic hy)
  refine ⟨p,hm,?_⟩
  intro q
  constructor
  · intro hq
    have hd : minpoly K y ∣ q.map (algebraMap R K) := by
      apply minpoly.dvd K y
      rw [hlift,hq,map_zero]
    have hzero : (q %ₘ p).map (algebraMap R K) = 0 := by
      rw [Polynomial.map_modByMonic _ hm]
      apply (modByMonic_eq_zero_iff_dvd (hm.map (algebraMap R K))).mpr
      rwa [hp]
    have hzero' : q %ₘ p = 0 :=
      Polynomial.map_injective _ hf (hzero.trans (Polynomial.map_zero _).symm)
    exact (modByMonic_eq_zero_iff_dvd hm).mp hzero'
  · intro hq
    have hd : minpoly K y ∣ q.map (algebraMap R K) := by
      rw [← hp]
      exact Polynomial.map_dvd _ hq
    have hz : aeval y (q.map (algebraMap R K)) = 0 :=
      (minpoly.dvd_iff (A := K) (x := y)).mp hd
    rw [hlift,← map_zero i] at hz
    exact hi hz

/-- If the same coordinate generates, the monic kernel gives its actual
root algebra and hence an honest global powers basis; no basis is input. -/
theorem monic_presentation (x : C) (hgen : Function.Surjective (aeval x : R[X] →ₐ[R] C)) :
    ∃ p : R[X], p.Monic ∧ ∃ e : AdjoinRoot p ≃ₐ[R] C, e (AdjoinRoot.root p) = x := by
  obtain ⟨p,hp,hker⟩ := monic_kernel (R := R) (C := C) x
  have hz : aeval x p = 0 := (hker p).mpr dvd_rfl
  let h : AdjoinRoot p →ₐ[R] C := AdjoinRoot.liftAlgHom p (Algebra.ofId _ _) x hz
  have hmk (q : R[X]) : h (AdjoinRoot.mk p q) = aeval x q :=
    AdjoinRoot.liftAlgHom_mk _ _ _ _ _
  have hinj : Function.Injective h := by
    apply (injective_iff_map_eq_zero h).mpr
    intro a ha
    obtain ⟨q,rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hmk] at ha
    exact AdjoinRoot.mk_eq_zero.mpr ((hker q).mp ha)
  have hsur : Function.Surjective h := by
    intro b
    obtain ⟨q,rfl⟩ := hgen b
    exact ⟨AdjoinRoot.mk p q,hmk q⟩
  exact ⟨p,hp,AlgEquiv.ofBijective h ⟨hinj,hsur⟩,AdjoinRoot.liftAlgHom_root _ _ _ _⟩

theorem exists_powers (x : C) (hgen : Function.Surjective (aeval x : R[X] →ₐ[R] C)) :
    ∃ pb : PowerBasis R C, pb.gen = x := by
  obtain ⟨p,hp,e,he⟩ := monic_presentation x hgen
  exact ⟨(AdjoinRoot.powerBasis' hp).map e,he⟩

end SelectedMonogenicNormalBasis318

#print axioms SelectedMonogenicNormalBasis318.monic_kernel
#print axioms SelectedMonogenicNormalBasis318.exists_powers
