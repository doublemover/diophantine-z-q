module
public import NormalizedCofactorFirstOrder318
public section
noncomputable section
namespace NormalizedCofactorAlgebraJet318
open Polynomial
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  (d a : Fin 4 → R) (T : S) (z : Fin 4 → S)
  (hz : ∀ i,(z i)^2=algebraMap R S (d i)*(T-algebraMap R S (a i)))
local notation "A" => DVRNormalizedFiniteOrder318.Order R d a
local notation "p" => DVRNormalizedFiniteOrder318.coefficient R d a
local notation "dS" => fun i => algebraMap R S (d i)

include hz in
/-- Integral cofactor jet in an arbitrary actual R-algebra target, not only
at a number-field point. No domain, inverse or unit hypothesis is needed. -/
theorem root_relation (i : Fin 4) :
    NormalizedCofactorFirstOrder318.rootJet S dS z i^2=
      Polynomial.aeval (NormalizedCofactorFirstOrder318.parameter S T z) (p i) := by
  simp only [DVRNormalizedFiniteOrder318.coefficient,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X]
  rw [pow_two]
  apply TrivSqZeroExt.ext
  · change z i*z i=algebraMap R S (d i)*(T-algebraMap R S (a i))
    exact (pow_two (z i)).symm.trans (hz i)
  · change z i*NormalizedCofactorFirstOrder318.slope S dS z i+
      NormalizedCofactorFirstOrder318.slope S dS z i*z i=
      algebraMap R S (d i)*(NormalizedCofactorFirstOrder318.factor S z-0)+
        0*(T-algebraMap R S (a i))
    rw [NormalizedCofactorFirstOrder318.cofactor_relation]
    ring

@[expose] def lift : A →ₐ[R] TrivSqZeroExt S S := by
  letI : Algebra R[X] (TrivSqZeroExt S S) :=
    (Polynomial.aeval (NormalizedCofactorFirstOrder318.parameter S T z)).toRingHom.toAlgebra
  let F := IntegralRootPointMaps318.fourMap p
    (NormalizedCofactorFirstOrder318.rootJet S dS z) (root_relation R S d a T z hz)
  exact { F.toRingHom with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply R R[X] A]
      change F (algebraMap R[X] A (C r))=algebraMap R _ r
      exact (F.commutes (C r)).trans (Polynomial.aeval_C _ _) }

theorem lift_polynomial (q : R[X]) :
    lift R S d a T z hz (algebraMap R[X] A q)=
      Polynomial.aeval (NormalizedCofactorFirstOrder318.parameter S T z) q := by
  letI : Algebra R[X] (TrivSqZeroExt S S) :=
    (Polynomial.aeval (NormalizedCofactorFirstOrder318.parameter S T z)).toRingHom.toAlgebra
  exact (IntegralRootPointMaps318.fourMap p
    (NormalizedCofactorFirstOrder318.rootJet S dS z) (root_relation R S d a T z hz)).commutes q

theorem lift_root (i : Fin 4) :
    lift R S d a T z hz (FourRootOrderSigns318.generator p i)=
      NormalizedCofactorFirstOrder318.rootJet S dS z i := by
  letI : Algebra R[X] (TrivSqZeroExt S S) :=
    (Polynomial.aeval (NormalizedCofactorFirstOrder318.parameter S T z)).toRingHom.toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator p
    (NormalizedCofactorFirstOrder318.rootJet S dS z) (root_relation R S d a T z hz) i

/-- Whole projection compatibility with the specified actual algebra map. -/
theorem projection (f : A →ₐ[R] S)
    (hf : ∀ q : R[X],f (algebraMap R[X] A q)=Polynomial.aeval T q)
    (hr : ∀ i,f (FourRootOrderSigns318.generator p i)=z i) (x : A) :
    (lift R S d a T z hz x).fst=f x := by
  have h : (TrivSqZeroExt.fstHom R S S).toRingHom.comp (lift R S d a T z hz).toRingHom=f.toRingHom := by
    apply IntegralRootPointMaps318.four_ringHom_ext
    · apply RingHom.ext
      intro q
      change (lift R S d a T z hz (algebraMap R[X] A q)).fst=f (algebraMap R[X] A q)
      rw [lift_polynomial,hf]
      exact (Polynomial.aeval_algHom_apply (TrivSqZeroExt.fstHom R S S)
        (NormalizedCofactorFirstOrder318.parameter S T z) q).symm
    · intro i
      change (lift R S d a T z hz (FourRootOrderSigns318.generator p i)).fst=_
      rw [lift_root,hr]
      rfl
  exact RingHom.congr_fun h x
end NormalizedCofactorAlgebraJet318
