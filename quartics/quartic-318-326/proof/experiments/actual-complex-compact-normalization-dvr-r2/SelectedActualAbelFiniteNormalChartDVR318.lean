module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.Algebra.Polynomial.FieldDivision

public section

open Polynomial Set CategoryTheory AlgebraicGeometry

namespace SelectedActualAbelFiniteNormalChartDVR318

universe u

private theorem dedekind_of_finite_normal_polynomial_chart
    (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k[X] B] [Module.Finite k[X] B] [IsIntegrallyClosed B] :
    IsDedekindDomain B := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite k[X] B
  letI : Ring.DimensionLEOne B := Ring.DimensionLEOne.of_isIntegral k[X] B
  letI : IsDedekindRing B := ⟨inferInstance, inferInstance, inferInstance⟩
  exact inferInstance

/-- On an actual finite normal affine chart of a polynomial line, a
nongeneric original scheme point has a DVR stalk. The local ring is
the original stalk, not an unrelated copy of a localized ring. -/
theorem original_stalk_isDVR_of_finite_normal_chart
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U)
    [Algebra k[X] Γ(X, U)] [Module.Finite k[X] Γ(X, U)]
    [IsIntegrallyClosed Γ(X, U)]
    (x : X) (hx : x ∈ U) (hn : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  letI : Nonempty U := ⟨⟨x,hx⟩⟩
  letI : IsDedekindDomain Γ(X, U) :=
    dedekind_of_finite_normal_polynomial_chart k Γ(X, U)
  have hg : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      exact ⟨x, hx⟩)
  let p := hU.primeIdealOf ⟨x,hx⟩
  let q := hU.primeIdealOf ⟨genericPoint X,hg⟩
  letI : p.asIdeal.IsPrime := p.isPrime
  have hq : q.asIdeal = ⊥ := by
    change (hU.primeIdealOf ⟨genericPoint X,hg⟩).asIdeal = ⊥
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] <;> rfl
  have hp : p.asIdeal ≠ ⊥ := by
    intro hz
    have hEq : p = q := by
      apply PrimeSpectrum.ext
      exact hz.trans hq.symm
    have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x,hx⟩
    have hqg : hU.fromSpec q = genericPoint X :=
      hU.fromSpec_primeIdealOf ⟨genericPoint X,hg⟩
    exact hn (hpx.symm.trans ((congrArg hU.fromSpec hEq).trans hqg))
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x,hx⟩
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    Γ(X, U) hp (X.presheaf.stalk x)

/-- Applying the same fixed pair of compact affine charts supplies
the DVRs at *all* original nongeneric points, including under infinity.
The base line map is the one carried by each actual chart algebra. -/
theorem original_stalk_isDVR_from_two_charts
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (U : Fin 2 → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (cover : (⊤ : X.Opens) ≤ iSup U)
    [∀ i, Algebra k[X] Γ(X, U i)] [∀ i, Module.Finite k[X] Γ(X, U i)]
    (normal : ∀ i, IsIntegrallyClosed Γ(X, U i))
    (x : X) (hn : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have htop : x ∈ (⊤ : X.Opens) := by simp
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (cover htop)
  letI : IsIntegrallyClosed Γ(X, U i) := normal i
  exact original_stalk_isDVR_of_finite_normal_chart k X (U i) (hU i) x hi hn

end SelectedActualAbelFiniteNormalChartDVR318

#print axioms SelectedActualAbelFiniteNormalChartDVR318.original_stalk_isDVR_of_finite_normal_chart
#print axioms SelectedActualAbelFiniteNormalChartDVR318.original_stalk_isDVR_from_two_charts
