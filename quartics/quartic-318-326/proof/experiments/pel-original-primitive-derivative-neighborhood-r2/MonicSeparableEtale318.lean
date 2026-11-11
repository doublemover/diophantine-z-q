module
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace MonicSeparableEtale318
variable {R : Type*} [CommRing R]

/-- A monic separable equation over the actual coefficient ring gives
an etale WHOLE quotient. Separability here is a Bezout identity in R[X],
not merely separability after passing to a fraction field. -/
theorem etale (Q : Polynomial R) (hm : Q.Monic) (hs : Q.Separable) :
    Algebra.Etale R (AdjoinRoot Q) := by
  obtain ⟨a,b,hab⟩ := (Polynomial.separable_def' Q).mp hs
  let P : StandardEtalePair R :=
    { f := Q
      monic_f := hm
      g := 1
      cond := ⟨b,a,0,by simpa only [pow_zero,mul_comm,add_comm] using hab⟩ }
  let u : AdjoinRoot Q ≃ₐ[AdjoinRoot Q]
      Localization.Away (AdjoinRoot.mk Q (1 : Polynomial R)) :=
    IsLocalization.atUnit (AdjoinRoot Q) _ (AdjoinRoot.mk Q 1) (by simp)
  let e : P.Ring ≃ₐ[R] AdjoinRoot Q :=
    P.equivAwayAdjoinRoot.trans (u.symm.restrictScalars R)
  exact Algebra.Etale.of_equiv e

/-- A whole-ring equivalence fixing the GIVEN coefficient map transports
etaleness with precisely that coefficient algebra structure. -/
theorem of_ringEquiv {A : Type*} [CommRing A] (g : R →+* A)
    (Q : Polynomial R) (hm : Q.Monic) (hs : Q.Separable)
    (e : AdjoinRoot Q ≃+* A)
    (he : ∀ r : R, e (AdjoinRoot.of Q r) = g r) :
    @Algebra.Etale R A _ _ g.toAlgebra := by
  letI : Algebra R A := g.toAlgebra
  letI : Algebra.Etale R (AdjoinRoot Q) := etale Q hm hs
  let ea : AdjoinRoot Q ≃ₐ[R] A := { e with commutes' := he }
  exact Algebra.Etale.of_equiv ea
end MonicSeparableEtale318
