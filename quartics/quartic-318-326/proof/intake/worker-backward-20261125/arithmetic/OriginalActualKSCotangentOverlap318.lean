module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
Actual first-order Kodaira–Spencer overlap coefficient on a split affine
chart of the original marked deformation. The input maps are actual
algebra sections of reduction in the same overlap ring. No assumption
of odd residue characteristic or analytic torus coordinates.
-/
@[expose] public section
noncomputable section

open TrivSqZeroExt

namespace OriginalActualKSCotangentOverlap318

abbrev Sq (A : Type*) := TrivSqZeroExt A A

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A local trivialization restricted to the common actual affine
overlap sends each function to a lift of that same reduced function. -/
structure Lift (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] where
  arrow : A →ₐ[R] Sq A
  reduced : ∀ a, (arrow a).fst = a

def epsilon (A : Type*) [CommRing A] : Sq A := inr (1 : A)

def difference (s t : Lift R A) : Derivation R A A where
  toLinearMap :=
    { toFun := fun a => (t.arrow a).snd - (s.arrow a).snd
      map_add' := by
        intro a b
        simp only [map_add, snd_add]
        abel
      map_smul' := by
        intro r a
        simp only [map_smul, snd_smul, smul_sub, RingHom.id_apply] }
  map_one_eq_zero' := by simp
  leibniz' := by
    intro a b
    change (t.arrow (a*b)).snd - (s.arrow (a*b)).snd =
      a • ((t.arrow b).snd - (s.arrow b).snd) +
        b • ((t.arrow a).snd - (s.arrow a).snd)
    simp only [map_mul,snd_mul,s.reduced,t.reduced,op_smul_eq_smul,smul_eq_mul]
    ring

def overlap (s t : Lift R A) : Ω[A⁄R] →ₗ[A] A :=
  (difference s t).liftKaehlerDifferential

/-- The sign is the ordered local lift t−s, not its inverse. -/
theorem on_differential (s t : Lift R A) (a : A) :
    overlap s t (KaehlerDifferential.D R A a) = (t.arrow a).snd - (s.arrow a).snd := by
  exact Derivation.liftKaehlerDifferential_comp_D (difference s t) a

theorem actual_difference (s t : Lift R A) (a : A) :
    t.arrow a - s.arrow a = inr (overlap s t (KaehlerDifferential.D R A a)) := by
  apply TrivSqZeroExt.ext
  · simp [t.reduced,s.reduced]
  · rw [snd_sub,snd_inr,on_differential]

section ActualReducedCotangent

attribute [local instance] TrivSqZeroExt.algebraBase

local instance sqTower : IsScalarTower R (Sq A) A where
  smul_assoc r x a := by
    change (r • x).fst * a = r • (x.fst * a)
    rw [fst_smul,Algebra.smul_mul_assoc]

/-- This coefficient is read from the real absolute cotangent of
the first-order algebra, viewed at its reduced fibre. -/
def reducedEpsilonDerivation : Derivation R (Sq A) A where
  toLinearMap := (TrivSqZeroExt.sndHom A A).restrictScalars R
  map_one_eq_zero' := rfl
  leibniz' := by
    intro x y
    change (x*y).snd = x.fst*y.snd + y.fst*x.snd
    simp only [snd_mul,op_smul_eq_smul,smul_eq_mul]

def reducedEpsilonFunctional : Ω[(Sq A)⁄R] →ₗ[Sq A] A :=
  (reducedEpsilonDerivation (R := R) (A := A)).liftKaehlerDifferential

theorem epsilon_reads_one :
    reducedEpsilonFunctional (R := R) (A := A)
      (KaehlerDifferential.D R (Sq A) (epsilon A)) = 1 := by
  exact Derivation.liftKaehlerDifferential_comp_D
    (reducedEpsilonDerivation (R := R) (A := A)) (epsilon A)

/-- Actual differential connecting map: difference of the two *lifted*
Kähler symbols, followed by the actual reduced dε coefficient. -/
theorem from_absolute_differentials (s t : Lift R A) (a : A) :
    reducedEpsilonFunctional (R := R) (A := A)
      (KaehlerDifferential.D R (Sq A) (t.arrow a) -
        KaehlerDifferential.D R (Sq A) (s.arrow a)) =
      overlap s t (KaehlerDifferential.D R A a) := by
  rw [on_differential]
  calc
    _ = reducedEpsilonFunctional (R := R) (A := A)
          (KaehlerDifferential.D R (Sq A) (t.arrow a)) -
        reducedEpsilonFunctional (R := R) (A := A)
          (KaehlerDifferential.D R (Sq A) (s.arrow a)) := map_sub _ _ _
    _ = _ := by
      rw [reducedEpsilonFunctional,Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D]
      rfl

end ActualReducedCotangent

/-- The actual three lift differences add in the Kähler Hom group.
This is the cocycle sign on a common overlap. -/
theorem overlap_cocycle (s t u : Lift R A) :
    overlap s t + overlap t u = overlap s u := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change overlap s t (KaehlerDifferential.D R A a) +
    overlap t u (KaehlerDifferential.D R A a) = overlap s u (KaehlerDifferential.D R A a)
  rw [on_differential,on_differential,on_differential]
  abel

theorem change_trivializations (s t s' t' : Lift R A) :
    overlap s' t' = overlap s t + overlap t t' - overlap s s' := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change overlap s' t' (KaehlerDifferential.D R A a) =
    overlap s t (KaehlerDifferential.D R A a) +
      overlap t t' (KaehlerDifferential.D R A a) -
      overlap s s' (KaehlerDifferential.D R A a)
  simp only [on_differential]
  abel

section SameActualMap
variable {B : Type*} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable (F : Sq A →ₐ[R] Sq B)

/-- An actual map of first-order affine charts preserves the nilpotent
coefficient according to its reduced map, irrespective of how its
constant sections were trivialized. -/
theorem literal_epsilon_map (hε : F (epsilon A) = epsilon B)
    (hr : ∀ x : Sq A, (F x).fst = algebraMap A B x.fst) (a : A) :
    F (inr a) = inr (algebraMap A B a) := by
  have he : (inr a : Sq A) = epsilon A * inl a := by
    rw [epsilon,inr_mul_inl]
    congr 1
    rw [op_smul_eq_smul,smul_eq_mul,mul_one]
  rw [he,map_mul,hε]
  apply TrivSqZeroExt.ext
  · simp [epsilon]
  · simp only [epsilon,snd_mul,fst_inr,snd_inr,
      op_smul_eq_smul,smul_eq_mul,zero_mul,zero_add,mul_one,hr,fst_inl]

/-- This compares the connecting class on the literal same
[11]/[3] marked germ whenever its actual affine arrow preserves the
structural T+ε direction and actual local lifts are transported. -/
theorem same_marked_symbol (hε : F (epsilon A) = epsilon B)
    (hr : ∀ x : Sq A, (F x).fst = algebraMap A B x.fst)
    (s t : Lift R A) (s' t' : Lift R B)
    (hs : ∀ a, F (s.arrow a) = s'.arrow (algebraMap A B a))
    (ht : ∀ a, F (t.arrow a) = t'.arrow (algebraMap A B a)) (a : A) :
    overlap s' t' (KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a)) =
      algebraMap A B (overlap s t (KaehlerDifferential.D R A a)) := by
  rw [KaehlerDifferential.map_D]
  apply (inr_injective (R := B))
  rw [← actual_difference s' t',← ht,← hs,← map_sub,actual_difference s t,
    literal_epsilon_map F hε hr]

/-- Whole true cotangent transport, not only agreement on selected
coordinates. The symbols span by the universal property of Ω. -/
theorem same_marked_cotangent (hε : F (epsilon A) = epsilon B)
    (hr : ∀ x : Sq A, (F x).fst = algebraMap A B x.fst)
    (s t : Lift R A) (s' t' : Lift R B)
    (hs : ∀ a, F (s.arrow a) = s'.arrow (algebraMap A B a))
    (ht : ∀ a, F (t.arrow a) = t'.arrow (algebraMap A B a)) :
    ((overlap s' t').restrictScalars A).comp (KaehlerDifferential.map R R A B) =
      (Algebra.linearMap A B).comp (overlap s t) := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  exact same_marked_symbol F hε hr s t s' t' hs ht a

end SameActualMap

section LiteralIsomorphism
variable {B : Type*} [CommRing B] [Algebra R B]

/-- In the actual isomorphic affine germ one transports the chosen local
section by conjugation, not by postulating equality with a second choice. -/
def throughGerm (f : A ≃ₐ[R] B) (F : Sq A ≃ₐ[R] Sq B)
    (hr : ∀ x : Sq A, (F x).fst = f x.fst) (s : Lift R A) : Lift R B where
  arrow := F.toAlgHom.comp (s.arrow.comp f.symm.toAlgHom)
  reduced b := by
    change (F (s.arrow (f.symm b))).fst=b
    rw [hr,s.reduced,AlgEquiv.apply_symm_apply]

theorem throughGerm_reads (f : A ≃ₐ[R] B) (F : Sq A ≃ₐ[R] Sq B)
    (hr : ∀ x : Sq A, (F x).fst = f x.fst) (s : Lift R A) (a : A) :
    (throughGerm f F hr s).arrow (f a) = F (s.arrow a) := by
  change F (s.arrow (f.symm (f a))) = F (s.arrow a)
  rw [AlgEquiv.symm_apply_apply]

theorem same_isomorphic_germ (f : A ≃ₐ[R] B) (F : Sq A ≃ₐ[R] Sq B)
    (hr : ∀ x : Sq A, (F x).fst = f x.fst)
    (hε : F (epsilon A) = epsilon B) (s t : Lift R A) (a : A) :
    overlap (throughGerm f F hr s) (throughGerm f F hr t)
      (KaehlerDifferential.D R B (f a)) =
      f (overlap s t (KaehlerDifferential.D R A a)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq
    (fun r => (f.commutes r).symm)
  have h := same_marked_symbol F.toAlgHom hε hr s t
    (throughGerm f F hr s) (throughGerm f F hr t)
    (fun x => (throughGerm_reads f F hr s x).symm)
    (fun x => (throughGerm_reads f F hr t x).symm) a
  rw [KaehlerDifferential.map_D] at h
  exact h

end LiteralIsomorphism
end OriginalActualKSCotangentOverlap318

#print axioms OriginalActualKSCotangentOverlap318.from_absolute_differentials
#print axioms OriginalActualKSCotangentOverlap318.overlap_cocycle
#print axioms OriginalActualKSCotangentOverlap318.change_trivializations
#print axioms OriginalActualKSCotangentOverlap318.same_marked_symbol
#print axioms OriginalActualKSCotangentOverlap318.same_isomorphic_germ
#print axioms OriginalActualKSCotangentOverlap318.same_marked_cotangent
