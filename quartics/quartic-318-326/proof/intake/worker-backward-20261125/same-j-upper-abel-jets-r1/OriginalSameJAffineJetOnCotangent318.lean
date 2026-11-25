module
public import OriginalSameJRetainedAffineJet318
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift

@[expose] public section
noncomputable section

open Algebra
open scoped TensorProduct

namespace OriginalSameJAffineJetOnCotangent318
open OriginalSameJRetainedAffineJet318 (Jet abelJet)

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The full augmentation is not separately chosen. It is the
ε=0 restriction of this very scheme-valued point. -/
def augment (j : A →ₐ[k] Jet k) : A →ₐ[k] k :=
  (TrivSqZeroExt.fstHom k k k).comp j

abbrev augmentAlgebra (j : A →ₐ[k] Jet k) : Algebra A k :=
  (augment j).toRingHom.toAlgebra

theorem augmentTower (j : A →ₐ[k] Jet k) :
    letI : Algebra A k := augmentAlgebra j
    IsScalarTower k A k := by
  let : Algebra A k := augmentAlgebra j
  exact IsScalarTower.of_algebraMap_eq fun c => ((augment j).commutes c).symm

def derivation (j : A →ₐ[k] Jet k) :
    letI : Algebra A k := augmentAlgebra j
    Derivation k A k := by
  let : Algebra A k := augmentAlgebra j
  refine { toFun := fun a => (j a).snd
           map_add' := ?_
           map_smul' := ?_
           map_one_eq_zero' := ?_
           leibniz' := ?_ }
  · intro a b
    change (j (a+b)).snd = (j a).snd + (j b).snd
    rw [map_add, TrivSqZeroExt.snd_add]
  · intro c a
    change (j (c • a)).snd = c • (j a).snd
    rw [map_smul, TrivSqZeroExt.snd_smul]
  · change (j 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  · intro a b
    change (j (a*b)).snd = (j a).fst * (j b).snd + (j b).fst * (j a).snd
    simp only [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, smul_eq_mul]

/-- Whole Kähler functional, not only its values on selected
uniformizers. The module is the pointed affine algebraic Ω fibre. -/
def cotangent (j : A →ₐ[k] Jet k) :
    letI : Algebra A k := augmentAlgebra j
    k ⊗[A] Ω[A⁄k] →ₗ[k] k := by
  let : Algebra A k := augmentAlgebra j
  let : IsScalarTower k A k := augmentTower j
  exact (derivation j).liftKaehlerDifferential.liftBaseChange k

theorem reads_d (j : A →ₐ[k] Jet k) (a : A) :
    letI : Algebra A k := augmentAlgebra j
    cotangent j ((1:k) ⊗ₜ[A] KaehlerDifferential.D k A a) = (j a).snd := by
  let : Algebra A k := augmentAlgebra j
  let : IsScalarTower k A k := augmentTower j
  change (derivation j).liftKaehlerDifferential.liftBaseChange k
    ((1:k) ⊗ₜ[A] KaehlerDifferential.D k A a) = _
  calc
    _ = (derivation j).liftKaehlerDifferential (KaehlerDifferential.D k A a) :=
      LinearMap.liftBaseChange_one_tmul k (derivation j).liftKaehlerDifferential
        (KaehlerDifferential.D k A a)
    _ = (derivation j) a := Derivation.liftKaehlerDifferential_comp_D _ _
    _ = (j a).snd := rfl

variable {B : Type*} [CommRing B] [Algebra k B]
variable (F : B →ₐ[k] A) (j : A →ₐ[k] Jet k)

/-- The exact marked cotangent read on the J chart via its actual
Abel pullback of affine regular functions. -/
theorem abel_reads_d (b : B) :
    letI : Algebra B k := augmentAlgebra (abelJet F j)
    cotangent (abelJet F j) ((1:k) ⊗ₜ[B] KaehlerDifferential.D k B b) =
      (j (F b)).snd := reads_d (abelJet F j) b

end OriginalSameJAffineJetOnCotangent318

#print axioms OriginalSameJAffineJetOnCotangent318.derivation
#print axioms OriginalSameJAffineJetOnCotangent318.reads_d
#print axioms OriginalSameJAffineJetOnCotangent318.abel_reads_d
