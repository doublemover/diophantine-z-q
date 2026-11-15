module
public import IntegralRootPointMaps318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace FourRootFirstOrderPoint318
open Polynomial
variable (V K : Type*) [CommRing V] [Field K] [Algebra V K]

@[expose] def parameter (t : K) : TrivSqZeroExt K K := (t,1)

@[expose] def rootJet (z b : K) : TrivSqZeroExt K K := (z,b/(2*z))

theorem rootJet_square [CharZero K] (z b : K) (hz : z≠0) :
    rootJet K z b ^ 2 = (z^2,b) := by
  rw [pow_two]
  apply TrivSqZeroExt.ext
  · change z*z=z^2
    ring
  · change z*(b/(2*z))+(b/(2*z))*z=b
    field_simp [hz]
    <;> ring

variable (p : Fin 4 → V[X]) (t : K) (z : Fin 4 → TrivSqZeroExt K K)
  (hz : ∀ i,(z i)^2=Polynomial.aeval (parameter K t) (p i))

/-- The actual entire four-root order maps into first-order scalars. The base
coordinate is t+epsilon; the source is not replaced by a quotient or open set. -/
@[expose] def lift : FourRootOrder318.Order p →ₐ[V] TrivSqZeroExt K K := by
  letI : Algebra V[X] (TrivSqZeroExt K K) :=
    (Polynomial.aeval (parameter K t)).toRingHom.toAlgebra
  let F := IntegralRootPointMaps318.fourMap p z hz
  exact { F.toRingHom with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply V V[X] (FourRootOrder318.Order p)]
      change F (algebraMap V[X] (FourRootOrder318.Order p) (C r))=algebraMap V _ r
      exact (F.commutes (C r)).trans (Polynomial.aeval_C _ _) }

theorem lift_polynomial (q : V[X]) :
    lift V K p t z hz (algebraMap V[X] (FourRootOrder318.Order p) q)=
      Polynomial.aeval (parameter K t) q := by
  letI : Algebra V[X] (TrivSqZeroExt K K) :=
    (Polynomial.aeval (parameter K t)).toRingHom.toAlgebra
  exact (IntegralRootPointMaps318.fourMap p z hz).commutes q

theorem lift_root (i : Fin 4) :
    lift V K p t z hz (FourRootOrderSigns318.generator p i)=z i := by
  letI : Algebra V[X] (TrivSqZeroExt K K) :=
    (Polynomial.aeval (parameter K t)).toRingHom.toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator p z hz i

/-- Projection is the specified original whole point: equality checks the
entire polynomial base and all four signed roots, not only the parameter. -/
theorem projection_eq (f : FourRootOrder318.Order p →+* K)
    (hf : ∀ q : V[X],f (algebraMap V[X] (FourRootOrder318.Order p) q)=Polynomial.aeval t q)
    (hr : ∀ i,f (FourRootOrderSigns318.generator p i)=(z i).fst) :
    (TrivSqZeroExt.fstHom V K K).toRingHom.comp (lift V K p t z hz).toRingHom=f := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · apply RingHom.ext
    intro q
    change (lift V K p t z hz (algebraMap V[X] (FourRootOrder318.Order p) q)).fst=
      f (algebraMap V[X] (FourRootOrder318.Order p) q)
    rw [lift_polynomial,hf]
    exact (Polynomial.aeval_algHom_apply (TrivSqZeroExt.fstHom V K K) (parameter K t) q).symm
  · intro i
    change (lift V K p t z hz (FourRootOrderSigns318.generator p i)).fst=
      f (FourRootOrderSigns318.generator p i)
    rw [lift_root,hr]
end FourRootFirstOrderPoint318
