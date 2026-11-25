module
public import OriginalActualKSCoboundary318
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.Tactic.Abel

/-!
Extend actual affine gauge derivations to the genuine affine overlaps.
Open restrictions are formally étale; the canonical Kähler tensor
comparison yields a unique derivation and a commuting square for the
actual square-zero chart algebra maps.
-/
@[expose] public section
noncomputable section

open scoped TensorProduct
open TrivSqZeroExt
open KaehlerDifferential

namespace OriginalActualKSEtaleRestriction318
open OriginalActualKSCotangentOverlap318 OriginalActualKSCoboundary318

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra.FormallyEtale A B]

def extendForm (d : Derivation R A A) : Ω[B⁄R] →ₗ[B] B :=
  (((TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap.comp
    (d.liftKaehlerDifferential.baseChange B)).comp
    (tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap)

def extend (d : Derivation R A A) : Derivation R B B :=
  (extendForm (B:=B) d).compDer (D R B)

theorem on_actual_restriction (d : Derivation R A A) (a : A) :
    extend (B:=B) d (algebraMap A B a) = algebraMap A B (d a) := by
  change extendForm (B:=B) d (D R B (algebraMap A B a)) = _
  simp only [extendForm,LinearMap.comp_apply,LinearEquiv.coe_coe,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.baseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def,mul_one]

/-- Different chart choices cannot enlarge derivations on an actual
open intersection. Injectivity follows on all symbols by the true
formally-étale cotangent tensor isomorphism. -/
theorem unique_on_actual_restriction (d e : Derivation R B B)
    (h : ∀ a : A, d (algebraMap A B a)=e (algebraMap A B a)) : d=e := by
  have he : (d.liftKaehlerDifferential.restrictScalars A).comp
      (KaehlerDifferential.map R R A B) =
      (e.liftKaehlerDifferential.restrictScalars A).comp
      (KaehlerDifferential.map R R A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    change d.liftKaehlerDifferential (KaehlerDifferential.map R R A B (D R A a)) =
      e.liftKaehlerDifferential (KaehlerDifferential.map R R A B (D R A a))
    simpa only [KaehlerDifferential.map_D,Derivation.liftKaehlerDifferential_comp_D]
      using h a
  have hw (w : Ω[A⁄R]) :
      d.liftKaehlerDifferential (KaehlerDifferential.map R R A B w) =
        e.liftKaehlerDifferential (KaehlerDifferential.map R R A B w) :=
    LinearMap.congr_fun he w
  let E := tensorKaehlerEquivOfFormallyEtale R A B
  have ht (z : B ⊗[A] Ω[A⁄R]) :
      d.liftKaehlerDifferential (E z) = e.liftKaehlerDifferential (E z) := by
    refine TensorProduct.inductionOn (motive := fun z =>
      d.liftKaehlerDifferential (E z) = e.liftKaehlerDifferential (E z)) z ?_ ?_
    · intro b w
      change d.liftKaehlerDifferential (tensorKaehlerEquivOfFormallyEtale R A B
        (b ⊗ₜ[A] w)) = e.liftKaehlerDifferential
          (tensorKaehlerEquivOfFormallyEtale R A B (b ⊗ₜ[A] w))
      simp only [tensorKaehlerEquivOfFormallyEtale_apply,mapBaseChange_tmul,map_smul,hw]
    · intro z₁ z₂ h₁ h₂
      simp only [map_add,h₁,h₂]
  apply Derivation.ext
  intro b
  simpa only [LinearEquiv.apply_symm_apply,Derivation.liftKaehlerDifferential_comp_D] using
    ht (E.symm (D R B b))

/-- The actual coefficient ring pullback on a trivialized overlap. -/
def sqRestriction (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    Sq A →ₐ[R] Sq B where
  toFun x := inl (algebraMap A B x.fst) + inr (algebraMap A B x.snd)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext <;> simp [op_smul_eq_smul,smul_eq_mul]
  commutes' r := by
    simp only [TrivSqZeroExt.algebraMap_eq_inl',fst_inl,snd_inl,map_zero,inr_zero,
      add_zero,IsScalarTower.algebraMap_apply R A B]

@[simp] theorem sqRestriction_fst (x : Sq A) :
    (sqRestriction R A B x).fst=algebraMap A B x.fst := by
  change (inl (algebraMap A B x.fst) + inr (algebraMap A B x.snd) : Sq B).fst=_
  simp

@[simp] theorem sqRestriction_snd (x : Sq A) :
    (sqRestriction R A B x).snd=algebraMap A B x.snd := by
  change (inl (algebraMap A B x.fst) + inr (algebraMap A B x.snd) : Sq B).snd=_
  simp

/-- These are actual ring arrows on the overlap, not just commuting
differential matrices. With genuine affine restrictions, this is the
covariance needed to glue corrected local infinitesimal charts. -/
theorem shear_restricts (d : Derivation R A A) :
    (shear (extend (B:=B) d)).comp (sqRestriction R A B) =
      (sqRestriction R A B).comp (shear d) := by
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · simp only [AlgHom.comp_apply,shear_fst,sqRestriction_fst]
  · simp only [AlgHom.comp_apply,shear_snd,sqRestriction_fst,sqRestriction_snd,
      map_add,on_actual_restriction]

theorem extend_neg (d : Derivation R A A) :
    extend (B:=B) (-d) = -extend (B:=B) d := by
  apply unique_on_actual_restriction (A:=A)
  intro a
  simp only [on_actual_restriction,Derivation.neg_apply,map_neg]

section CorrectBothLegs
variable {C : Type*} [CommRing C] [Algebra R C] [Algebra C B] [IsScalarTower R C B]
  [Algebra.FormallyEtale C B]

/-- On the two literal restriction arrows into one actual overlap, a
vanishing deformation class gives the *same* correction on both scheme
legs. This is before applying Spec contravariantly and gluing. -/
theorem corrected_overlap_legs (F : Sq B →ₐ[R] Sq B)
    (red : ∀ x : Sq B, (F x).fst=x.fst)
    (base : F (epsilon B)=epsilon B)
    (di : Derivation R A A) (dj : Derivation R C C)
    (boundary : difference (constantLift R B) (backLift F red) =
      extend (B:=B) dj-extend (B:=B) di) :
    (sqRestriction R A B).comp (shear (-di)) =
      (shear (-(extend (B:=B) di))).comp (sqRestriction R A B) ∧
    F.comp ((sqRestriction R C B).comp (shear (-dj))) =
      (shear (-(extend (B:=B) di))).comp (sqRestriction R C B) := by
  have hl := (shear_restricts (B:=B) (-di)).symm
  have hr := (shear_restricts (B:=B) (-dj)).symm
  rw [extend_neg] at hl hr
  refine ⟨hl,?_⟩
  rw [hr,recover_actual_chart_map F red base,boundary,←AlgHom.comp_assoc,shear_add]
  have h : extend (B:=B) dj-extend (B:=B) di + -(extend (B:=B) dj) =
      -(extend (B:=B) di) := by abel
  rw [h]

end CorrectBothLegs

end OriginalActualKSEtaleRestriction318

#print axioms OriginalActualKSEtaleRestriction318.on_actual_restriction
#print axioms OriginalActualKSEtaleRestriction318.unique_on_actual_restriction
#print axioms OriginalActualKSEtaleRestriction318.shear_restricts
#print axioms OriginalActualKSEtaleRestriction318.corrected_overlap_legs
