module
public import FourRootCharacterAffineScheme318
public import PELOriginalActualCharacterFields318
public section
noncomputable section
namespace PELOriginalWholeCharacterOrders318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalActualCharacterFields318
open PELOriginalCharacterQuotient318 PELOriginalMaximalQuotient318
open OriginalContactInertiaBasis318
open FourRootCharacterPolynomialOrder318
local instance independentFact:
    Fact (QuadraticTower318.Independent (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩

/-- Four literal whole cubic orders in the original omitted-character
order105,70,42,30, before any unproved rational branch identification. -/
abbrev Cubic (i:Fin 4):=Order branches (omitted i)
abbrev CharacterField (i:Fin 4):=PELOriginalActualCharacterFields318.field i
@[expose] def morphism (i:Fin 4):FourRootGluedScheme318.finiteScheme branches⟶
    FourRootCharacterAffineScheme318.characterScheme branches (omitted i):=
  FourRootCharacterAffineScheme318.morphism branches branches_injective
    (omitted i) (omitted_nonempty i)
theorem finite (i:Fin 4):IsFinite (morphism i):=
  FourRootCharacterAffineScheme318.finite branches branches_injective _ _

/-- Explicit literal polynomial; the original coefficients remain the
actual geometric branch coordinates, not the manuscript constants. -/
lemma cubic_equation (i:Fin 4):radicand branches (omitted i)=
    ∏j:Fin 3,Polynomial.X-Polynomial.C
      (branches (SourceTwistArithmetic318.complement i j)):=by
  rw [radicand,omitted_eq]
  fin_cases i <;> simp [FourRootAffineTensorPresentation318.radicand,
    SourceTwistArithmetic318.complement,Fin.prod_univ_succ] <;> ring

/-- The map annihilates exactly the already identified original analytic
character kernel at the whole affine scheme level, on all original labels. -/
theorem original_deck_square (i:Fin 4) (g:Labels) (hg:g∈(character i).ker):
    FourRootSchemeSignAction318.finiteMap branches (basis g)≫morphism i=morphism i:=by
  apply FourRootCharacterAffineScheme318.deck_square
  rw [complementary_product]
  exact (PELOriginalContactCharacterIdentity318.field_kernel_iff (F:=ℂ) i g).mp hg

/-- Exact kernel, now on the whole actual cubic-to-source ring map,
with original analytic labels retained in both directions. -/
theorem original_ring_kernel (i:Fin 4) (g:Labels):
    (FourRootCoordinateRingSigns318.finiteEnd branches (basis g)).comp
      (FourRootCharacterAffineScheme318.coordinateMap branches branches_injective
        (omitted i) (omitted_nonempty i))=
      FourRootCharacterAffineScheme318.coordinateMap branches branches_injective
        (omitted i) (omitted_nonempty i) ↔ g∈(character i).ker:=by
  rw [FourRootCharacterAffineScheme318.invariant_iff,complementary_product]
  exact (PELOriginalContactCharacterIdentity318.field_kernel_iff (F:=ℂ) i g).symm

/-- The specified fraction field of the literal cubic order is precisely
its actual character fixed field, and not a newly chosen elliptic field. -/
theorem fraction_field (i:Fin 4):
    letI:Algebra (Cubic i) (CharacterField i):=
      (embedding branches branches_injective (omitted i) (omitted_nonempty i)).toAlgebra
    IsFractionRing (Cubic i) (CharacterField i):=
  fractionField branches branches_injective (omitted i) (omitted_nonempty i)

theorem degree_eight (i:Fin 4):Module.finrank (CharacterField i)
    (KummerTensorField318.Raw (FourRootActualGenericField318.parameter branches))=8:=
  FourRootCharacterWholeAffineMap318.relative_degree branches branches_injective _ _

/-- All genuine source algebra points have the literal original omitted
root product as their character coordinate, without excluding branches. -/
lemma every_finite_point (i:Fin 4)
    (f:FourRootAffineCoordinateRing318.Ring branches→ₐ[ℂ]ℂ):
    (f.comp (FourRootCharacterAffineScheme318.coordinateMap branches branches_injective
      (omitted i) (omitted_nonempty i)))
      (AdjoinRoot.root (QuadraticPresentation318.polynomial (radicand branches (omitted i))))=
      ∏k∈omitted i,f (FourRootAffineCoordinateRing318.coordinate branches (some k)):=
  FourRootCharacterAffineScheme318.point_root branches branches_injective _ _ f
end PELOriginalWholeCharacterOrders318
