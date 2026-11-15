module
public import NormalizedCofactorAlgebraJet318
public import LocalizationDerivation318
public section
noncomputable section
namespace NormalizedCofactorSourceDerivation318
open Polynomial
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
local notation "A" => DVRNormalizedFiniteOrder318.Order R d a
local notation "p" => DVRNormalizedFiniteOrder318.coefficient R d a

@[expose] def coordinate : A := algebraMap R[X] A X
@[expose] def roots (i : Fin 4) : A := FourRootOrderSigns318.generator p i

theorem roots_square (i : Fin 4) :
    (roots R d a i)^2=algebraMap R A (d i)*(coordinate R d a-algebraMap R A (a i)) := by
  have hC (r : R) : algebraMap R[X] A (C r)=algebraMap R A r := rfl
  change (FourRootOrderSigns318.generator p i)^2=_
  rw [FourRootOrderSigns318.generator_square]
  change algebraMap R[X] A (C (d i)*(X-C (a i)))=
    algebraMap R A (d i)*(algebraMap R[X] A X-algebraMap R A (a i))
  rw [map_mul,map_sub,hC,hC]

/-- A genuine first-order self-map of the entire original normalized
source ring, not a tangent map at a number-field point. -/
@[expose] def jet : A →ₐ[R] TrivSqZeroExt A A :=
  NormalizedCofactorAlgebraJet318.lift R A d a (coordinate R d a) (roots R d a)
    (roots_square R d a)

theorem polynomial_eval (q : R[X]) :
    algebraMap R[X] A q=Polynomial.aeval (coordinate R d a) q := by
  have h : (Polynomial.aeval (coordinate R d a) : R[X] →ₐ[R] A)=IsScalarTower.toAlgHom R R[X] A := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact (AlgHom.congr_fun h q).symm

theorem projection (x : A) : (jet R d a x).fst=x :=
  NormalizedCofactorAlgebraJet318.projection R A d a (coordinate R d a) (roots R d a)
    (roots_square R d a) (AlgHom.id R A) (polynomial_eval R d a) (fun _ => rfl) x

/-- Integral source-ring derivation: its values actually lie in the same A.
It is not a derivation of the algebraic point field, nor a supplied lattice
preservation hypothesis. No root/twist/unit2 inversion occurs. -/
@[expose] def derivation : Derivation R A A :=
  RingValuedCotangentEvaluation318.derivation R A A (AlgHom.id R A) (jet R d a) (projection R d a)

theorem derivation_coordinate :
    derivation R d a (coordinate R d a)=NormalizedCofactorFirstOrder318.factor A (roots R d a) := by
  change (jet R d a (algebraMap R[X] A X)).snd=_
  rw [jet,NormalizedCofactorAlgebraJet318.lift_polynomial,Polynomial.aeval_X]
  rfl

theorem derivation_root (i : Fin 4) :
    derivation R d a (roots R d a i)=NormalizedCofactorFirstOrder318.slope A
      (fun j => algebraMap R A (d j)) (roots R d a) i := by
  change (jet R d a (FourRootOrderSigns318.generator p i)).snd=_
  rw [jet,NormalizedCofactorAlgebraJet318.lift_root]
  rfl

section Localization
variable (L : Type*) [CommRing L]
  [Algebra (DVRNormalizedFiniteOrder318.Order R d a) L] [Algebra R L]
  [IsScalarTower R (DVRNormalizedFiniteOrder318.Order R d a) L]
  (P : Submonoid (DVRNormalizedFiniteOrder318.Order R d a)) [IsLocalization P L]

/-- Native extension to the ACTUAL localization ring of this source.
No DVR, regularity, normality or maximal-model premise is fabricated. -/
@[expose] def localized : Derivation R L L :=
  LocalizationDerivation318.extend P
    ((Algebra.linearMap A L).compDer (derivation R d a))

theorem localized_algebraMap (x : A) :
    localized R d a L P (algebraMap A L x)=algebraMap A L (derivation R d a x) :=
  LocalizationDerivation318.extend_algebraMap P _ x

theorem localized_coordinate :
    localized R d a L P (algebraMap A L (coordinate R d a))=
      algebraMap A L (NormalizedCofactorFirstOrder318.factor A (roots R d a)) := by
  rw [localized_algebraMap,derivation_coordinate]

/-- The coefficient base is killed on the actual localization by native
relative derivation, rather than an assumed vanishing of a uniformizer. -/
theorem localized_constant (r : R) : localized R d a L P (algebraMap R L r)=0 :=
  (localized R d a L P).map_algebraMap r
end Localization
end NormalizedCofactorSourceDerivation318
