module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
The actual localization of the proof constants C at the contraction of
the old structural component q. Replace C by C_p before taking the
structural localization without changing the local ring or its inputs.
-/
@[expose] public section
noncomputable section

open scoped TensorProduct

namespace OriginalStructuralLocalConstantsCut318

universe u
variable {V C U : Type u} [CommRing V] [CommRing C] [CommRing U]
  [Algebra V C] [Algebra V U]

abbrev N (V C U : Type u) [CommRing V] [CommRing C] [CommRing U]
    [Algebra V C] [Algebra V U] := C ⊗[V] U

variable (q : Ideal (N V C U)) [q.IsPrime]

abbrev p := q.comap (algebraMap C (N V C U))

instance primeP : (p q).IsPrime := Ideal.IsPrime.comap _ inferInstance

abbrev B := Localization.AtPrime (p q)

local instance algebraVB : Algebra V (B q) :=
  ((algebraMap C (B q)).comp (algebraMap V C)).toAlgebra

local instance towerVCB : IsScalarTower V C (B q) :=
  IsScalarTower.of_algebraMap_eq' rfl

abbrev middle := B q ⊗[C] N V C U

attribute [local instance] Algebra.TensorProduct.rightAlgebra

abbrev sub := Algebra.algebraMapSubmonoid (N V C U) (p q).primeCompl

instance localizesMiddle : IsLocalization (sub q) (middle q) :=
  IsLocalization.tensorRight (S := N V C U) (A := B q) (p q).primeCompl

theorem below : sub q ≤ q.primeCompl := by
  rintro _ ⟨c, hc, rfl⟩
  exact hc

private theorem disj : Disjoint (sub q : Set (N V C U)) (q : Set (N V C U)) :=
  Set.disjoint_left.mpr fun _ hx hq => below q hx hq

abbrev midPrime := q.map (algebraMap (N V C U) (middle q))

instance midIsPrime : (midPrime q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (sub q) (middle q) q inferInstance (disj q)

theorem midContraction :
    (midPrime q).comap (algebraMap (N V C U) (middle q)) = q :=
  IsLocalization.under_map_of_isPrime_disjoint (sub q) (middle q) inferInstance (disj q)

abbrev localMiddle := Localization.AtPrime (midPrime q)

local instance directAlgebra : Algebra (N V C U) (localMiddle q) :=
  ((algebraMap (middle q) (localMiddle q)).comp
    (algebraMap (N V C U) (middle q))).toAlgebra

local instance directTower : IsScalarTower (N V C U) (middle q) (localMiddle q) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem exactLocalization : IsLocalization.AtPrime (localMiddle q) q := by
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (sub q) (T := localMiddle q) (midPrime q)
  have he : ((midPrime q).comap (algebraMap (N V C U) (middle q))).primeCompl =
      q.primeCompl := by
    ext x
    change x ∉ (midPrime q).comap _ ↔ x ∉ q
    rw [midContraction q]
  exact he ▸ h

def throughMiddle : Localization.AtPrime q ≃ₐ[N V C U] localMiddle q := by
  letI := exactLocalization q
  exact IsLocalization.algEquiv q.primeCompl _ _

abbrev actual := B q ⊗[V] U

def combine : middle q ≃ₐ[B q] actual q :=
  Algebra.TensorProduct.cancelBaseChange V C (B q) (B q) U

theorem combine_tensor (b : B q) (c : C) (a : U) :
    combine q (b ⊗ₜ[C] (c ⊗ₜ[V] a)) = (c • b) ⊗ₜ[V] a := by
  rw [combine, Algebra.TensorProduct.cancelBaseChange_tmul]

abbrev actualPrime := (midPrime q).comap (combine q).symm.toRingHom

instance actualIsPrime : (actualPrime q).IsPrime := Ideal.IsPrime.comap _ inferInstance

private theorem mid_to_actual :
    midPrime q = (actualPrime q).comap (combine q).toRingHom := by
  ext s
  change s ∈ midPrime q ↔ (combine q).symm (combine q s) ∈ midPrime q
  rw [AlgEquiv.symm_apply_apply]

/-- Ring on which R4 reads the derivative and the exact same ring on
which one first specializes the proof constants at their true prime. -/
def structuralLocal :
    Localization.AtPrime q ≃+* Localization.AtPrime (actualPrime q) :=
  (throughMiddle q).toRingEquiv.trans <|
    Localization.localRingEquiv (midPrime q) (actualPrime q) (combine q).toRingEquiv
      (mid_to_actual q)

theorem structuralLocal_on_base (x : N V C U) :
    structuralLocal q (algebraMap (N V C U) (Localization.AtPrime q) x) =
      algebraMap (actual q) (Localization.AtPrime (actualPrime q))
        (combine q ((1 : B q) ⊗ₜ[C] x)) := by
  change Localization.localRingHom (midPrime q) (actualPrime q) (combine q).toRingHom
    (mid_to_actual q) (throughMiddle q (algebraMap (N V C U) (Localization.AtPrime q) x)) = _
  rw [(throughMiddle q).commutes]
  change Localization.localRingHom (midPrime q) (actualPrime q) (combine q).toRingHom
    (mid_to_actual q) (algebraMap (middle q) (localMiddle q) ((1 : B q) ⊗ₜ[C] x)) = _
  exact Localization.localRingHom_to_map _ _ _ _ _

theorem structuralLocal_on_original (c : C) (a : U) :
    structuralLocal q (algebraMap (N V C U) (Localization.AtPrime q) (c ⊗ₜ[V] a)) =
      algebraMap (actual q) (Localization.AtPrime (actualPrime q))
        ((algebraMap C (B q) c) ⊗ₜ[V] a) := by
  rw [structuralLocal_on_base, combine_tensor, Algebra.smul_def, mul_one]

def constantsOnOldLocal : B q →+* Localization.AtPrime q :=
  Localization.localRingHom (p q) q (algebraMap C (N V C U)) rfl

/-- This is equality on the whole proof DVR, not just on C. In
particular its actual auxiliary uniformizer maps compatibly. -/
theorem allLocalConstants :
    (structuralLocal q).toRingHom.comp (constantsOnOldLocal q) =
      (algebraMap (actual q) (Localization.AtPrime (actualPrime q))).comp
        (algebraMap (B q) (actual q)) := by
  apply IsLocalization.ringHom_ext (p q).primeCompl
  ext c
  change structuralLocal q (constantsOnOldLocal q (algebraMap C (B q) c)) =
    algebraMap (actual q) (Localization.AtPrime (actualPrime q))
      ((algebraMap C (B q) c) ⊗ₜ[V] (1 : U))
  rw [constantsOnOldLocal, Localization.localRingHom_to_map]
  change structuralLocal q (algebraMap (N V C U) (Localization.AtPrime q)
    (c ⊗ₜ[V] (1 : U))) = _
  exact structuralLocal_on_original q c 1

end OriginalStructuralLocalConstantsCut318

#print axioms OriginalStructuralLocalConstantsCut318.midContraction
#print axioms OriginalStructuralLocalConstantsCut318.exactLocalization
#print axioms OriginalStructuralLocalConstantsCut318.structuralLocal_on_original
#print axioms OriginalStructuralLocalConstantsCut318.allLocalConstants
