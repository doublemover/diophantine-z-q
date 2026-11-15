module
public import NormalizedOrderFiniteDual318
public import NormalizedSourceConormalRelations318
public import Mathlib.RingTheory.Kaehler.Polynomial
public section
noncomputable section
namespace NormalizedFiniteProjectionCotangent318
variable (V : Type*) [CommRing V] (d a : Fin 4 → V)
local notation "P" => Polynomial V
local notation "A" => DVRNormalizedFiniteOrder318.Order V d a
local notation "D" => KaehlerDifferential.D V A

/-- The ACTUAL finite-projection dual with values in the genuine base
coordinate differentials, not merely a free coefficient target. -/
abbrev ProjectionDual := A →ₗ[P] KaehlerDifferential V P

@[expose] def finiteDual : A ≃ₗ[P] ProjectionDual V d a :=
  (NormalizedOrderFiniteDual318.normalizedPerfect V d a).trans
    (KaehlerDifferential.polynomialEquiv V).symm.congrRight

theorem finiteDual_apply (x y : A) :
    finiteDual V d a x y=(KaehlerDifferential.polynomialEquiv V).symm
      (NormalizedOrderFiniteDual318.normalizedPerfect V d a x y) := rfl

theorem finiteDual_mul (x y z : A) :
    finiteDual V d a (x*y) z=finiteDual V d a x (y*z) := by
  rw [finiteDual_apply,finiteDual_apply]
  exact congrArg (KaehlerDifferential.polynomialEquiv V).symm
    (NormalizedOrderFiniteDual318.perfect_mul P
      (DVRNormalizedFiniteOrder318.coefficient V d a) x y z)

/-- The generator literally takes values in multiples of the ACTUAL dT
on the polynomial base; no formal symbol is substituted for this module. -/
theorem generator_base_differential (y : A) :
    finiteDual V d a 1 y=
      NormalizedOrderFiniteDual318.normalizedPerfect V d a 1 y •
        KaehlerDifferential.D V P Polynomial.X := by
  rw [finiteDual_apply,KaehlerDifferential.polynomialEquiv_symm]

/-- A constructed cofactor class from the WHOLE native source cotangent
module into the actual finite-projection dual. Identification with the
relative curve dualizing fundamental class is still a separate theorem. -/
@[expose] def differentialClass (η : KaehlerDifferential V A) : ProjectionDual V d a :=
  finiteDual V d a (NormalizedSourceConormalRelations318.contraction V d a η)

theorem differentialClass_add (η θ : KaehlerDifferential V A) :
    differentialClass V d a (η+θ)=differentialClass V d a η+differentialClass V d a θ := by
  unfold differentialClass
  rw [map_add,map_add]

/-- Full source-algebra equivariance through the actual multiplication
precomposition action on Hom_P(A,Ω_{P/V}), without hiding a module choice. -/
theorem differentialClass_balance (x y : A) (η : KaehlerDifferential V A) :
    differentialClass V d a (x • η) y=differentialClass V d a η (x*y) := by
  unfold differentialClass
  rw [(NormalizedSourceConormalRelations318.contraction V d a).map_smul]
  change finiteDual V d a (x*NormalizedSourceConormalRelations318.contraction V d a η) y=_
  rw [mul_comm x,finiteDual_mul]

theorem differentialClass_coordinate :
    differentialClass V d a (D (NormalizedCofactorSourceDerivation318.coordinate V d a))=
      finiteDual V d a (NormalizedCofactorFirstOrder318.factor A
        (NormalizedCofactorSourceDerivation318.roots V d a)) := by
  unfold differentialClass
  rw [NormalizedSourceConormalRelations318.contraction_coordinate]

theorem differentialClass_root (i : Fin 4) :
    differentialClass V d a (D (NormalizedCofactorSourceDerivation318.roots V d a i))=
      finiteDual V d a (NormalizedCofactorFirstOrder318.slope A
        (fun j => algebraMap V A (d j)) (NormalizedCofactorSourceDerivation318.roots V d a) i) := by
  unfold differentialClass
  rw [NormalizedSourceConormalRelations318.contraction_root]
end NormalizedFiniteProjectionCotangent318
