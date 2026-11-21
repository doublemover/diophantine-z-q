module
public import SelectedOriginalCompactOverlapIdentity318
public import SelectedRationalGenericFromComplex318
import Mathlib.Algebra.Module.Rat
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedRationalGenericFromComplex318 SelectedOriginalGenericChartClosures318
open SelectedOriginalGenericCompactNormal318

namespace SelectedRationalRootCompactInstall318

/-- The full rational generic root algebra of the same original p.
The definition does not take a factor or select a complex embedding. -/
abbrev RootField (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :=
  AdjoinRoot (p.map (rationalGenericMap N))

/-- The polynomial quotient's native scalar action. Its coefficient map is
the composite through the same rational function field. Keeping this action,
rather than rebuilding it from the ring homomorphism, matches the chart tower. -/
@[expose] def rationalAlgebra (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    Algebra ℚ (RootField N p) := by
  letI : Algebra ℚ QJ := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  exact AdjoinRoot.instAlgebra (S := ℚ) (p.map (rationalGenericMap N))

private abbrev nativeJAlgebra (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    Algebra QJ (RootField N p) :=
  AdjoinRoot.instAlgebra (S := QJ) (p.map (rationalGenericMap N))

private theorem nativeTower (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    @IsScalarTower ℚ QJ (RootField N p)
      (RatFunc.instAlgebraOfPolynomial ℚ ℚ).toSMul
      (nativeJAlgebra N p).toSMul (rationalAlgebra N p).toSMul :=
  @IsScalarTower.of_algebraMap_eq' ℚ QJ (RootField N p)
    inferInstance inferInstance inferInstance
    (RatFunc.instAlgebraOfPolynomial ℚ ℚ) (nativeJAlgebra N p) (rationalAlgebra N p) (by rfl)

private theorem native_rat_smul (r : ℚ) (z : QJ) :
    r • z = algebraMap ℚ[X] QJ (Polynomial.C r) * z := by
  induction z using RatFunc.induction_on with
  | _ a b _ =>
    rw [←RatFunc.div_smul r a b,Polynomial.smul_eq_C_mul,map_mul,mul_div_assoc]

private theorem native_rat_assoc (r : ℚ) (s z : QJ) : (r • s) • z = r • (s • z) := by
  rw [smul_eq_mul (r • s) z,smul_eq_mul s z,
    native_rat_smul r s,native_rat_smul r (s*z),mul_assoc]

theorem rationalTower (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    letI : Algebra ℚ (RootField N p) := rationalAlgebra N p
    IsScalarTower ℚ QJ (RootField N p) := by
  constructor
  intro r s z
  induction z using AdjoinRoot.induction_on with
  | _ a =>
    have ha : (r • s) • a = r • (s • a) := by
      apply Polynomial.ext
      intro i
      simp only [Polynomial.coeff_smul]
      refine (native_rat_assoc r s (a.coeff i)).trans ?_
      -- The polynomial coefficient law sees the action projected from a module.
      -- Both rational actions are unique on this same additive group.
      let v : QJ := s • a.coeff i
      let A : Algebra ℚ QJ := RatFunc.instAlgebraOfPolynomial ℚ ℚ
      let U : Module ℚ QJ := @Algebra.toModule ℚ QJ _ _ A
      let V : Module ℚ QJ := inferInstance
      first
      | exact congrArg (fun W : Module ℚ QJ =>
          @SMul.smul ℚ QJ W.toDistribMulAction.toDistribSMul.toSMul r v)
          (Subsingleton.elim U V)
      | exact congrArg (fun W : Algebra ℚ QJ => @SMul.smul ℚ QJ W.toSMul r v)
          (Subsingleton.elim A (DivisionRing.toRatAlgebra : Algebra ℚ QJ))
    rw [AdjoinRoot.smul_mk,AdjoinRoot.smul_mk,AdjoinRoot.smul_mk,ha]

/-- Actual compact normalization of the whole rational generic root
algebra, now a field. This keeps the originally specified projective
J-line and the standard two chart orders, not a stand-in compact curve. -/
@[expose] def compact (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hf : IsField (RootField N p)) : Scheme := by
  letI : Field (RootField N p) := hf.toField
  exact model (RootField N p)

@[expose] def compactJ (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hf : IsField (RootField N p)) : compact N p hf ⟶ ProjectiveJLine318.scheme ℚ := by
  letI : Field (RootField N p) := hf.toField
  exact modelMap (RootField N p)

theorem original_degree (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hp : p.Monic) : Module.finrank QJ (RootField N p) = p.natDegree := by
  change Module.finrank QJ (AdjoinRoot (p.map (rationalGenericMap N))) = _
  rw [Module.finrank_eq_card_basis
    (AdjoinRoot.powerBasis' (hp.map (rationalGenericMap N))).basis, Fintype.card_fin]
  change (p.map (rationalGenericMap N)).natDegree = p.natDegree
  exact hp.natDegree_map (rationalGenericMap N)

/-- No new trace bound is assumed: monic powers give finiteness of
the whole generic field extension and characteristic zero supplies
separability for the already-proved two-chart trace construction. -/
theorem compact_properties (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hp : p.Monic) (hf : IsField (RootField N p)) :
    IsFinite (compactJ N p hf) ∧
    IsProper (compactJ N p hf ≫ ProjectiveJLine318.structureMap ℚ) ∧
    IsIntegral (compact N p hf) ∧
    ∀ x : compact N p hf, IsIntegrallyClosed ((compact N p hf).presheaf.stalk x) := by
  let K := RootField N p
  let aJ : Algebra QJ K := nativeJAlgebra N p
  letI aQ : Algebra ℚ K := rationalAlgebra N p
  let tQ : @IsScalarTower ℚ QJ K (RatFunc.instAlgebraOfPolynomial ℚ ℚ).toSMul
      aJ.toSMul aQ.toSMul := nativeTower N p
  letI fK : Field K := hf.toField
  letI hfin : FiniteDimensional QJ K := (hp.map (rationalGenericMap N)).finite_adjoinRoot
  let hsep : Algebra.IsSeparable QJ K := inferInstance
  exact ⟨@model_finite K fK aJ aQ tQ hfin hsep,
    @model_proper K fK aJ aQ tQ hfin hsep, model_integral K,
    @normal_stalk K fK aJ aQ tQ hfin hsep⟩

end SelectedRationalRootCompactInstall318

#print axioms SelectedRationalRootCompactInstall318.original_degree
#print axioms SelectedRationalRootCompactInstall318.compact_properties
