module
public import NormalizedCofactorSourceDerivation318
public section
noncomputable section
namespace NormalizedSourceConormalRelations318
open NormalizedCofactorSourceDerivation318
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
local notation "A" => DVRNormalizedFiniteOrder318.Order R d a
local notation "D" => KaehlerDifferential.D R A

/-- The ACTUAL universal-differential relation in Ω_{A/R}, derived from
its quadratic quotient equation. It is not a numerical tangent equation. -/
theorem quadratic_conormal (i : Fin 4) :
    (2*roots R d a i) • D (roots R d a i)=
      algebraMap R A (d i) • D (coordinate R d a) := by
  have h := congrArg D (roots_square R d a i)
  rw [pow_two,Derivation.leibniz (KaehlerDifferential.D R A),Derivation.leibniz (KaehlerDifferential.D R A),map_sub,Derivation.map_algebraMap (KaehlerDifferential.D R A),Derivation.map_algebraMap (KaehlerDifferential.D R A),
    sub_zero,smul_zero,add_zero] at h
  calc
    (2*roots R d a i) • D (roots R d a i)=
        roots R d a i • D (roots R d a i)+roots R d a i • D (roots R d a i) := by
      rw [two_mul]
      exact add_smul (roots R d a i) (roots R d a i)
        ((KaehlerDifferential.D R A) (roots R d a i))
    _=algebraMap R A (d i) • D (coordinate R d a) := h

/-- The native universal cotangent contraction from the actual source
cofactor derivation. No dualizing-line identification is built into its type. -/
@[expose] def contraction : KaehlerDifferential R A →ₗ[A] A :=
  (derivation R d a).liftKaehlerDifferential

theorem contraction_D (x : A) : contraction R d a (D x)=derivation R d a x :=
  Derivation.liftKaehlerDifferential_comp_D (derivation R d a) x

theorem contraction_coordinate : contraction R d a (D (coordinate R d a))=
    NormalizedCofactorFirstOrder318.factor A (roots R d a) := by
  rw [contraction_D,derivation_coordinate]

theorem contraction_root (i : Fin 4) : contraction R d a (D (roots R d a i))=
    NormalizedCofactorFirstOrder318.slope A (fun j => algebraMap R A (d j))
      (roots R d a) i := by
  rw [contraction_D,derivation_root]

/-- Applying the constructed contraction to the true conormal relation
retains the full Jacobian factor, even at nonunit twists and primes over2. -/
theorem contraction_conormal (i : Fin 4) :
    (2*roots R d a i)*NormalizedCofactorFirstOrder318.slope A
      (fun j => algebraMap R A (d j)) (roots R d a) i=
      algebraMap R A (d i)*NormalizedCofactorFirstOrder318.factor A (roots R d a) := by
  have h := congrArg (contraction R d a) (quadratic_conormal R d a i)
  rw [(contraction R d a).map_smul,(contraction R d a).map_smul,
    contraction_root,contraction_coordinate] at h
  exact h
end NormalizedSourceConormalRelations318
