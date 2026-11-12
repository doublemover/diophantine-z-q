module
public import IntegralNormalPointCenter318
public import OriginalAllPlaceNormalizedData318
public section
noncomputable section
namespace OriginalAllPlaceNormalModel318
open Polynomial NumberField CategoryTheory AlgebraicGeometry
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open IntegralDistinctContactOpen318
set_option maxHeartbeats 1400000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
abbrev contacts := IntegralSourceBranches318.contacts (V c t w)
abbrev SourceOpenRing := OpenOrder (V c t w) (contacts c t w) D.coefficients

/-- Normality and properness are asserted of one actual scheme over the
actual finite-place integer ring. This record deliberately has no regularity
or dualizing/Hodge identification field. -/
structure Realization where
  scheme : Scheme
  projection : scheme ⟶ ProjectiveJLine318.scheme (V c t w)
  finite_projection : IsFinite projection
  integral : IsIntegral scheme
  noetherian : AlgebraicGeometry.IsNoetherian scheme
  normal_stalk : ∀ x : scheme, IsIntegrallyClosed (scheme.presheaf.stalk x)
  source : Spec (CommRingCat.of (SourceOpenRing c t w D)) ⟶ scheme
  source_open : IsOpenImmersion source
  source_dense : IsDominant source
  source_projection : source ≫ projection =
    Spec.map (CommRingCat.ofHom (IntegralReciprocalNormalClosures318.finitePolynomialMap
      (V c t w) (contacts c t w) (arithmeticDenominator (V c t w) D.coefficients)
      (SourceOpenRing c t w D))) ≫ JLineAtlas318.chart (V c t w) 1
  fieldPoint : SourceOpenRing c t w D →+* K c t
  field_polynomial : ∀ p : (V c t w)[X], fieldPoint
    (algebraMap (Base (V c t w) (contacts c t w) D.coefficients) (SourceOpenRing c t w D)
      (algebraMap (V c t w)[X] (Base (V c t w) (contacts c t w) D.coefficients) p)) =
        Polynomial.aeval (t : K c t) p
  field_roots : ∀ i, fieldPoint (FourRootOrderSigns318.generator
    (fun j => algebraMap (V c t w)[X] (Base (V c t w) (contacts c t w) D.coefficients)
      (DistinctContactIntegralDomain318.coefficient (V c t w) (contacts c t w) D.coefficients j)) i) =
        D.normalizedRoots i
  whole_source : fieldPoint.comp (IntegralNormalSourcePoint318.sourceInclusion
      (V c t w) (contacts c t w) D.coefficients) =
    NormalizedGenericChartMaps318.finiteMap (V c t w) (K c t) D.coefficients
      (contacts c t w) (t : K c t) D.normalizedRoots D.root_equation
  center : Spec (CommRingCat.of (V c t w)) ⟶ scheme
  center_base : center ≫ projection ≫ ProjectiveJLine318.structureMap (V c t w) = 𝟙 _
  center_generic : Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫ center =
    Spec.map (CommRingCat.ofHom fieldPoint) ≫ source

/-- The twists need not be units. Their literal exponent-zero-or-one
normalizations remain nonzero at every finite place. -/
theorem coefficients_ne_zero (i : Fin 4) : D.coefficients i ≠ 0 :=
  mul_ne_zero (D.unit i).ne_zero (pow_ne_zero _ D.irreducible.ne_zero)

theorem contacts_injective : Function.Injective (contacts c t w) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [contacts,IntegralSourceBranches318.contacts] at h ⊢

/-- This produces the proper normal model and its actual center at EVERY
finite place, without excluding 2, 3, 5 or 7 or assuming separated reduction.
The noncontact condition is on the original rational point only. -/
theorem exists_realization (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0) :
    Nonempty (Realization c t w D) := by
  let R := V c t w
  let F := K c t
  let a : Fin 4 → R := contacts c t w
  let d : Fin 4 → R := D.coefficients
  let B := SourceOpenRing c t w D
  have hd : ∀ i, d i ≠ 0 := coefficients_ne_zero c t w D
  have hdF : ∀ i, algebraMap R F (d i) ≠ 0 := fun i => by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne (hd i)
  have hz : ∀ i, D.normalizedRoots i ≠ 0 := fun i =>
    div_ne_zero (RationalFourRootFiber318.root_ne_zero _ i (hn i)) (D.multiplier_ne i)
  have hcontact : ∀ i, (t : F)-algebraMap R F (a i) ≠ 0 := by
    intro i hi
    have h := D.root_equation i
    change (D.normalizedRoots i)^2=algebraMap R F (d i)*((t : F)-algebraMap R F (a i)) at h
    rw [hi,mul_zero] at h
    exact pow_ne_zero 2 (hz i) h
  have ht : (t : F) ≠ 0 := by
    simpa only [a, contacts, IntegralSourceBranches318.contacts, Matrix.cons_val_zero,
      map_zero, sub_zero] using hcontact 0
  letI : IsDomain B := open_domain R a d F (IsFractionRing.injective R F)
    (contacts_injective c t w) hd
  letI : Module.Finite (Base R a d) B := (finite_free_etale R a d).1
  letI : Algebra.Etale (Base R a d) B := (finite_free_etale R a d).2.2
  have hN := arithmeticDenominator_ne_zero R d hd
  let f := IntegralNormalSourcePoint318.openMap R F a d (t : F) hdF ht hcontact
    D.normalizedRoots D.root_equation
  obtain ⟨g,hg,hgb⟩ := IntegralNormalPointCenter318.exists_center R F a d
    (t : F) hdF ht hcontact D.normalizedRoots D.root_equation hN
  refine ⟨{
    scheme := IntegralTwoChartNormalization318.model R a (arithmeticDenominator R d) B
    projection := IntegralTwoChartNormalization318.modelMap R a (arithmeticDenominator R d) B
    finite_projection := IntegralTwoChartNormalization318.normalization_finite R a _ B hN
    integral := IntegralTwoChartNormalization318.model_integral R a _ B
    noetherian := IntegralTwoChartNormalization318.noetherian_model R a _ B hN
    normal_stalk := IntegralTwoChartNormalization318.normal_stalk R a _ B hN
    source := IntegralTwoChartNormalization318.sourceOpen R a _ B
    source_open := IntegralTwoChartNormalization318.sourceOpen_open R a _ B
    source_dense := IntegralTwoChartNormalization318.sourceOpen_dense R a _ B
    source_projection := (IntegralTwoChartNormalization318.factorization R a _ B).trans
      (IntegralTwoChartNormalization318.finite_factor R a _ B)
    fieldPoint := f
    field_polynomial := ?_
    field_roots := IntegralNormalSourcePoint318.openMap_root R F a d (t : F) hdF ht hcontact
      D.normalizedRoots D.root_equation
    whole_source := IntegralNormalSourcePoint318.full_source_point R F a d (t : F) hdF ht hcontact
      D.normalizedRoots D.root_equation
    center := g
    center_base := hgb
    center_generic := hg }⟩
  intro p
  exact (IntegralNormalSourcePoint318.openMap_base R F a d (t : F) hdF ht hcontact
    D.normalizedRoots D.root_equation _).trans
    (IntegralNormalSourcePoint318.baseEvaluation_polynomial R F a d (t : F) hdF ht hcontact p)

/-- The original rational point and its finite place alone produce the
normalization data AND a proper normal model center. The prior raw-model
center is not used as a regularity or normalization certificate. -/
theorem exists_original_realization
    (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0) :
    ∃ D : Data c t w, Nonempty (Realization c t w D) := by
  obtain ⟨D,_,_,_⟩ := OriginalAllPlaceNormalizedData318.exists_center c t w
  exact ⟨D,exists_realization c t w D hn⟩

namespace Realization
variable (M : Realization c t w D)
@[expose] def structureMap : M.scheme ⟶ Spec (CommRingCat.of (V c t w)) :=
  M.projection ≫ ProjectiveJLine318.structureMap (V c t w)
theorem proper : IsProper M.structureMap := by
  letI := M.finite_projection
  unfold structureMap
  infer_instance

/-- Recover the same original signed source value after its chosen square
normalization, not just the original root squareclass. -/
theorem original_signed_root (i : Fin 4) : D.multiplier i *
    M.fieldPoint (FourRootOrderSigns318.generator
      (fun j => algebraMap (V c t w)[X] (Base (V c t w) (contacts c t w) D.coefficients)
        (DistinctContactIntegralDomain318.coefficient (V c t w) (contacts c t w) D.coefficients j)) i) =
      RationalContactPoint318.sourcePoint c t
        (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) := by
  rw [M.field_roots]
  exact D.original_signed_root i
end Realization
end OriginalAllPlaceNormalModel318
