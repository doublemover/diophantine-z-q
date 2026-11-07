module
public import GlobalCuspEnergy318
public import SourceNonCMHeight318
public section
noncomputable section
namespace GlobalEnergyJacobian318
open NumberField SourceJacobianBound318 SourceNonCMHeight318 ActualLogWeight318
variable (K X : Type*) [Field K] [NumberField K] [MeasurableSpace X]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {g i d N : ℕ}

/-- The concrete Jacobian bound now derives the complete local analytic
input from global normalized differential-energy measures.  Finite geometric
and Arakelov identifications remain named, unchanged inputs. -/
theorem jacobian_quadratic
    (D : GlobalCuspEnergy318.Data K X g i N)
    (F : FiniteData ι κ (2^128 + i) d N)
    (A : ArakelovIdentifications K D.toCusp F)
    (hg : 2 ≤ g) (hi : i ≤ g^3 + 1) (hgd : g ≤ d) (hN : 1 ≤ N) :
    A.hGR ≤ 2^11 * (d : ℝ)^2 * (Real.log (6*d*N))^2 :=
  SourceNonCMHeight318.jacobian_quadratic K D.toCusp F A hg hi hgd hN

/-- Exact adopted exponent after the actual index and level estimates. -/
theorem jacobian_49_over_8
    (D : GlobalCuspEnergy318.Data K X g i N)
    (F : FiniteData ι κ (2^128 + i) d N)
    (A : ArakelovIdentifications K D.toCusp F)
    (hg : 2 ≤ g) (hi : i ≤ g^3 + 1) (hgd : g ≤ d) (hN : 1 ≤ N)
    (R : ℝ) (hR : 1 ≤ R)
    (hindex : (d : ℝ) < 2^14 * C * R^((97 : ℝ)/32))
    (hlevel : (N : ℝ) ≤ C * R^2) :
    A.hGR < 2^65 * C^2 * R^((49 : ℝ)/8) :=
  SourceNonCMHeight318.jacobian_49_over_8 K D.toCusp F A hg hi hgd hN R hR hindex hlevel

end GlobalEnergyJacobian318
#print axioms GlobalEnergyJacobian318.jacobian_quadratic
#print axioms GlobalEnergyJacobian318.jacobian_49_over_8
