module
public import FiniteFamilyAvoidanceNaturality318
public import VaryingProjectiveQuotientFamily318
public section
noncomputable section
namespace VaryingQuotientAvoidance318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingProjectiveQuotientEquiv318
open FiniteFamilyAvoidanceOpen318 FiniteFamilyAvoidanceFactor318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
local notation "q" => VaryingWordGlobalOriginalMap318.original R A ι
variable (U : (Spec (CommRingCat.of A)).Opens)
/-- Actual open subparameter of the represented affine quotient scheme
where the WHOLE original quotient is supported in U. -/
abbrev parameterOpen := locus π q U
variable (S : Type u) [CommRing S] [Algebra R S] (I : ProjectiveIdeal R A ι S)
local notation "x" => equivalence R A ι S I
local notation "Q" => VaryingWholeIdealFamily318.family R A S I.val
@[expose] def original : Q ⟶ Spec (CommRingCat.of A) :=
  VaryingWholeIdealFamily318.into R A S I.val ≫ VaryingSourceCoefficientPullback318.original R A S
@[reassoc] lemma comparison_original : (VaryingProjectiveQuotientFamily318.comparison R A ι S I).hom ≫
    VaryingParameterPointFamily318.intoFamily R A ι S x ≫ q=original R A ι S I := by
  rw [← VaryingParameterPointFamily318.into_original,← Category.assoc,
    VaryingProjectiveQuotientFamily318.comparison_into]
  rfl
/-- The open represents support of the literal FULL quotient family,
through its actual original-source comparison, not only its matrix frame. -/
lemma supported_iff_original : Supported π q U x.val ↔ ∀ z : Q,original R A ι S I z∈U := by
  let e := VaryingProjectiveQuotientFamily318.comparison R A ι S I
  constructor
  · intro h z
    have he := congrArg (fun k : Q ⟶ Spec (CommRingCat.of A) => k z)
      (comparison_original R A ι S I)
    exact he ▸ h (e.hom z)
  · intro h z
    have h' := h (e.inv z)
    have he := congrArg (fun k : Q ⟶ Spec (CommRingCat.of A) => k (e.inv z))
      (comparison_original R A ι S I)
    rw [← he] at h'
    have hz : e.hom (e.inv z)=z :=
      congrArg (fun k : VaryingParameterPointFamily318.family R A ι S x ⟶
        VaryingParameterPointFamily318.family R A ι S x => k z) e.inv_hom_id
    change q (VaryingParameterPointFamily318.intoFamily R A ι S x (e.hom (e.inv z)))∈U at h'
    rw [hz] at h'
    exact h'
@[expose] def classify_supported (h : ∀ z : Q,original R A ι S I z∈U) :
    Spec (CommRingCat.of S) ⟶ (parameterOpen R A ι U).toScheme :=
  factor π q U x.val ((supported_iff_original R A ι U S I).mpr h)
@[reassoc] lemma classify_supported_into (h : ∀ z : Q,original R A ι S I z∈U) :
    classify_supported R A ι U S I h ≫ (parameterOpen R A ι U).ι=x.val :=
  factor_into π q U x.val _
end VaryingQuotientAvoidance318
