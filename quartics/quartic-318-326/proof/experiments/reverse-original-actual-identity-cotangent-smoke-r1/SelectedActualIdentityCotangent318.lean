module
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section

namespace SelectedActualIdentityCotangent318

open TensorProduct
open scoped TensorProduct

variable {R B T : Type*} [CommRing R] [CommRing B] [CommRing T]
variable [Algebra R B] [Algebra R T]

/-- The identity of the actual affine neighborhood is a retraction.
Use its augmentation, not an arbitrary free rank-two module. -/
def baseAug (ε : B →ₐ[R] R) : T ⊗[R] B →ₐ[T] T :=
  Algebra.TensorProduct.lift (AlgHom.id T T) ((Algebra.ofId R T).comp ε)
    (fun _ _ => mul_comm _ _)

@[simp]
theorem baseAug_tmul (ε : B →ₐ[R] R) (t : T) (b : B) :
    baseAug (T:=T) ε (t ⊗ₜ[R] b) = t * algebraMap R T (ε b) := by
  simp [baseAug]

/-- Conormal of the actual zero section on the global affine open. -/
abbrev I (ε : B →ₐ[R] R) : Ideal B := RingHom.ker ε.toRingHom

abbrev extendedIdeal (T : Type*) [CommRing T] [Algebra R T] (ε : B →ₐ[R] R) :
    Ideal (T ⊗[R] B) :=
  (I ε).map (Algebra.TensorProduct.includeRight.toRingHom : B →+* T ⊗[R] B)

private theorem subtract_identity_mem (ε : B →ₐ[R] R) (x : T ⊗[R] B) :
    x - ((baseAug (T:=T) ε x) ⊗ₜ[R] (1:B)) ∈ extendedIdeal T ε := by
  induction x with
  | zero =>
      simp only [map_zero,zero_tmul,sub_zero,Ideal.zero_mem]
  | add x y hx hy =>
      rw [map_add,add_tmul,add_sub_add_comm]
      exact (extendedIdeal T ε).add_mem hx hy
  | tmul t b =>
      have hb : b - algebraMap R B (ε b) ∈ I ε :=
        RingHom.mem_ker.mpr (by simp)
      have hm := (extendedIdeal T ε).mul_mem_left (t ⊗ₜ[R] (1:B)) <|
        Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight.toRingHom :
          B →+* T ⊗[R] B) hb
      change (t ⊗ₜ[R] (1:B)) * ((1:T) ⊗ₜ[R] (b-algebraMap R B (ε b))) ∈
        extendedIdeal T ε at hm
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,tmul_sub] at hm
      have hc : t ⊗ₜ[R] algebraMap R B (ε b) =
          (t*algebraMap R T (ε b)) ⊗ₜ[R] (1:B) := by
        calc
          _ = t ⊗ₜ[R] (ε b • (1:B)) := by simp [Algebra.smul_def]
          _ = (ε b • t) ⊗ₜ[R] (1:B) := (TensorProduct.smul_tmul _ _ _).symm
          _ = _ := by simp [Algebra.smul_def,mul_comm]
      rwa [hc,←baseAug_tmul] at hm

/-- Base-changing the actual zero section extends its ideal. No
flatness is needed for this split augmentation identity. -/
theorem ker_baseAug (ε : B →ₐ[R] R) :
    RingHom.ker (baseAug (T:=T) ε).toRingHom = extendedIdeal T ε := by
  apply le_antisymm
  · intro x hx
    have h : baseAug (T:=T) ε x = 0 := RingHom.mem_ker.mp hx
    simpa only [h,zero_tmul,sub_zero] using subtract_identity_mem ε x
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    have h : ε b = 0 := RingHom.mem_ker.mp hb
    change baseAug (T:=T) ε ((1:T) ⊗ₜ[R] b) = 0
    simp [h]

/-- Hence the cotangent at the same actual identity, after any flat
base change, is the base change of this very conormal module. -/
def identityBaseChange (ε : B →ₐ[R] R) [Module.Flat R T] :
    T ⊗[R] (I ε).Cotangent ≃ₗ[T] (RingHom.ker (baseAug (T:=T) ε).toRingHom).Cotangent := by
  rw [ker_baseAug]
  exact Ideal.tensorCotangentEquiv R T (I ε)

def restrictCotangent (ε : B →ₐ[R] R) [Module.Flat R T] :
    (I ε).Cotangent →ₗ[R] (RingHom.ker (baseAug (T:=T) ε).toRingHom).Cotangent :=
  (identityBaseChange (T:=T) ε).toLinearMap.restrictScalars R ∘ₗ
    TensorProduct.mk R T (I ε).Cotangent 1

/-- In particular the restriction of this actual identity cotangent
to each fine arithmetic open is the genuine module localization. -/
theorem isLocalized_restrict (ε : B →ₐ[R] R) [Module.Flat R T]
    (S : Submonoid R) [IsLocalization S T] :
    IsLocalizedModule S (restrictCotangent (T:=T) ε) :=
  (isLocalizedModule_iff_isBaseChange S T _).mpr <|
    (TensorProduct.isBaseChange R (I ε).Cotangent T).comp
      (IsBaseChange.ofEquiv (identityBaseChange (T:=T) ε))

end SelectedActualIdentityCotangent318

#print axioms SelectedActualIdentityCotangent318.ker_baseAug
#print axioms SelectedActualIdentityCotangent318.isLocalized_restrict
