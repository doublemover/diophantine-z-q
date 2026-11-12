module
public import IntegralFourRootNormalizationConductor318
public import IntegralTwoChartNormalization318
public section
noncomputable section
namespace IntegralNormalizationConductorChart318
open AlgebraicGeometry CategoryTheory Polynomial IntegralDistinctContactOpen318
universe u

/-- Keep the ACTUAL normalization chart when its original source map
has been identified with a concrete polynomial-chart factorization. -/
@[expose] def sectionsEquivOfFactor {P B : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : P ⟶ B) (j : Spec P ⟶ Y) [IsOpenImmersion j]
    (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f=Spec.map φ ≫ j) :
    letI := φ.hom.toAlgebra
    Γ(f.normalization,f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) ≃+* integralClosure P B := by
  subst f
  exact NormalChart318.sectionsEquiv φ j

variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)]
local notation "N" => arithmeticDenominator R d
local notation "B" => OpenOrder R a d
local instance : Module.Finite (Base R a d) B := (finite_free_etale R a d).1
local instance : Algebra.Etale (Base R a d) B := (finite_free_etale R a d).2.2

/-- The polynomial scalar used by the canonical proper-normal model
is exactly the scalar used by the conductor/codifferent calculation. -/
lemma scalarMap_eq :
    IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B=algebraMap R[X] B := by
  ext p
  exact (IsScalarTower.algebraMap_apply R[X] (Base R a d) B p).symm

/-- The actual ring of sections of the finite chart of the original
canonical normalization is its concrete integral closure, with precisely
the polynomial scalar map checked above. No replacement model is chosen. -/
@[expose] def finiteChartClosureEquiv :
    letI := (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B).toAlgebra
    IntegralTwoChartNormalization318.chartRing R a N B 1 ≃+* integralClosure R[X] B := by
  letI := (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B).toAlgebra
  change Γ((IntegralTwoChartNormalization318.coverMap R a N B).normalization,
    (IntegralTwoChartNormalization318.coverMap R a N B).fromNormalization ⁻¹ᵁ
      (JLineAtlas318.chart R 1 ''ᵁ ⊤)) ≃+* integralClosure R[X] B
  exact sectionsEquivOfFactor
    (CommRingCat.ofHom (IntegralReciprocalNormalClosures318.finitePolynomialMap R a N B))
    (JLineAtlas318.chart R 1) (IntegralTwoChartNormalization318.coverMap R a N B)
    (IntegralTwoChartNormalization318.finite_factor R a N B)
end IntegralNormalizationConductorChart318
