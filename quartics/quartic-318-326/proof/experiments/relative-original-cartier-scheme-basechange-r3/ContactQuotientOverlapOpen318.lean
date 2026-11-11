module
public import ContactQuotientOverlapNaturality318
public import VaryingQuotientAvoidance318
public section
noncomputable section
namespace ContactQuotientOverlapOpen318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
/-- Literal inverse image of the other original source chart. -/
@[expose] def sourceOpen : (Spec (ring c a)).Opens := (original c a) ⁻¹ᵁ (original c b).opensRange
/-- Genuine open subscheme of the first affine quotient PARAMETER
scheme, defined by avoidance of the whole universal finite family. -/
abbrev parameterOpen := VaryingQuotientAvoidance318.parameterOpen ℚ (ring c a) (Fin n) (sourceOpen c a b)
local notation "π" => VaryingWordGlobalFamilyProjection318.projection ℚ (ring c a) (Fin n)
local notation "q" => VaryingWordGlobalOriginalMap318.original ℚ (ring c a) (Fin n)
variable (S : CommRingCat.{0}) [Algebra ℚ S]
lemma supported_iff_universal (I : Ideal c a S n) : Supported c a b S n I ↔
    FiniteFamilyAvoidanceFactor318.Supported π q (sourceOpen c a b)
      (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I).val := by
  rw [VaryingQuotientAvoidance318.supported_iff_original,
    ContactQuotientSourceSupport318.supported_iff]
  rfl
/-- ALL rational-structure-preserving affine test maps into the actual
open subscheme, independently of the chart-transfer function. -/
abbrev Point := {f : Spec S ⟶ (parameterOpen c a b n).toScheme //
  f ≫ (parameterOpen c a b n).ι ≫ VaryingWordParameterStructure318.structureMap ℚ (ring c a) (Fin n)=
    VaryingSourceCoefficientPullback318.base ℚ S}
@[expose] def underlying (x : Point c a b n S) : VaryingParameterPoint318.Point ℚ (ring c a) (Fin n) S :=
  ⟨x.val ≫ (parameterOpen c a b n).ι,by simpa only [Category.assoc] using x.property⟩
@[expose] def classify (I : ContactQuotientOverlapEquiv318.Overlap c a b S n) : Point c a b n S := by
  let x := VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I.val
  let h := (supported_iff_universal c a b n S I.val).mp I.property
  refine ⟨FiniteFamilyAvoidanceFactor318.factor π q (sourceOpen c a b) x.val h,?_⟩
  rw [← Category.assoc,FiniteFamilyAvoidanceFactor318.factor_into]
  exact x.property
lemma classify_underlying (I : ContactQuotientOverlapEquiv318.Overlap c a b S n) :
    underlying c a b n S (classify c a b n S I)=
      VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I.val := by
  apply Subtype.ext
  exact FiniteFamilyAvoidanceFactor318.factor_into _ _ _ _ _
end ContactQuotientOverlapOpen318
