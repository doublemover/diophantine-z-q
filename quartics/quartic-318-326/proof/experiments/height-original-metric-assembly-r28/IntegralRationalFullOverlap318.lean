module
public import IntegralFullOverlapLocalization318
public import SourceOpenFractionField318
public section
noncomputable section
namespace IntegralRationalFullOverlap318
open Polynomial
open IntegralSourceBranches318 IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Expose the original composite on abstract carriers, before specializing
large nested localization instances. -/
private theorem polynomial_source_apply {R A T : Type*}
    [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [Algebra R[X] A]
    [IsScalarTower R R[X] A] (f : A →ₐ[R] T) (p : R[X]) :
    (f.comp (IsScalarTower.toAlgHom R R[X] A)) p = f (algebraMap R[X] A p) := rfl

variable (c : Fin 4 → ℚˣ)

/-- The rational specialization is literally the original four-root source
presentation, with each ordered radicand unchanged. -/
theorem coefficient_eq (i : Fin 4) : coefficient ℚ c i =
    ContactKummerOrder318.coefficient c i := rfl

@[expose] def sourceEquiv : SourceOrder ℚ c ≃ₐ[ℚ[X]] ContactKummerOrder318.SourceOrder c := by
  change FourRootOrder318.Order (ContactKummerOrder318.coefficient c) ≃ₐ[ℚ[X]]
    FourRootOrder318.Order (ContactKummerOrder318.coefficient c)
  exact AlgEquiv.refl

theorem quartic_eq : IntegralBranchBicanonical318.quartic ℚ =
    ContactKummerOrder318.denominator := rfl

theorem sourceEquiv_quartic :
    sourceEquiv c (IntegralFullOverlapLocalization318.sourceQuartic ℚ c) =
      SourceOpenFractionField318.d c := by
  rw [IntegralFullOverlapLocalization318.sourceQuartic,AlgEquiv.commutes,quartic_eq]
  rfl

@[expose] def originalRestriction : SourceOrder ℚ c →+* ContactKummerOrder318.OpenOrder c :=
  (SourceOpenFractionField318.orderToOpen c).comp (sourceEquiv c).toRingHom
@[expose] def originalAlgebra : Algebra (SourceOrder ℚ c) (ContactKummerOrder318.OpenOrder c) :=
  (originalRestriction c).toAlgebra
local instance : Algebra (SourceOrder ℚ c) (Overlap ℚ c) :=
  IntegralFullOverlapLocalization318.sourceAlgebra ℚ c
local instance : Algebra (SourceOrder ℚ c) (ContactKummerOrder318.OpenOrder c) := originalAlgebra c

/-- The comparison is forced by the universal property for the SAME quartic
and SAME original source restriction, not selected by a field isomorphism. -/
theorem original_localization :
    IsLocalization.Away (IntegralFullOverlapLocalization318.sourceQuartic ℚ c)
      (ContactKummerOrder318.OpenOrder c) := by
  letI : Algebra (ContactKummerOrder318.SourceOrder c) (ContactKummerOrder318.OpenOrder c) :=
    (SourceOpenFractionField318.orderToOpen c).toAlgebra
  haveI : IsLocalization.Away
      (sourceEquiv c (IntegralFullOverlapLocalization318.sourceQuartic ℚ c))
      (ContactKummerOrder318.OpenOrder c) := by
    rw [sourceEquiv_quartic]
    exact SourceOpenFractionField318.open_isLocalization c
  exact LocalizationSourceTransport318.away (sourceEquiv c).toRingEquiv
    (IntegralFullOverlapLocalization318.sourceQuartic ℚ c) (fun _ => rfl)

@[expose] def overlapEquiv : Overlap ℚ c ≃ₐ[SourceOrder ℚ c] ContactKummerOrder318.OpenOrder c := by
  letI := IntegralFullOverlapLocalization318.whole_localization ℚ c
  letI := original_localization c
  exact IsLocalization.algEquiv
    (Submonoid.powers (IntegralFullOverlapLocalization318.sourceQuartic ℚ c)) _ _

@[simp] theorem overlapEquiv_source (a : SourceOrder ℚ c) :
    overlapEquiv c (sourceMap ℚ c a) =
      SourceOpenFractionField318.orderToOpen c (sourceEquiv c a) :=
  (overlapEquiv c).commutes a

/-- Every original polynomial is preserved, hence the original contact
coordinate and all four labeled branch parameters are preserved together. -/
theorem overlapEquiv_polynomial (p : ℚ[X]) :
    overlapEquiv c (IntegralAllBranchOverlapMaps318.polynomialMap ℚ c p) =
      algebraMap ContactKummerOrder318.OpenBase (ContactKummerOrder318.OpenOrder c)
        (algebraMap ℚ[X] ContactKummerOrder318.OpenBase p) := by
  rw [IntegralAllBranchOverlapMaps318.polynomialMap, polynomial_source_apply,
    overlapEquiv_source, AlgEquiv.commutes,
    SourceOpenFractionField318.orderToOpen_on_polynomial]

/-- The same equivalence also respects the existing rational scalar actions. -/
@[expose] def overlapEquivRat : Overlap ℚ c ≃ₐ[ℚ] ContactKummerOrder318.OpenOrder c :=
  { (overlapEquiv c).toRingEquiv with
    commutes' := by
      intro q
      exact RingHom.map_rat_algebraMap (overlapEquiv c).toRingHom q }

/-- The actual existing common overlap embeds in the original Kummer field. -/
@[expose] def originalFieldEmbedding : Overlap ℚ c →+* SourceFractionField318.L c :=
  (SourceOpenFractionField318.openEmbedding c).comp (overlapEquiv c).toRingHom

theorem originalFieldEmbedding_injective : Function.Injective (originalFieldEmbedding c) :=
  (SourceOpenFractionField318.openEmbedding_injective c).comp (overlapEquiv c).injective

theorem originalFieldEmbedding_source (a : SourceOrder ℚ c) :
    originalFieldEmbedding c (sourceMap ℚ c a) =
      ContactKummerOrder318.embedding c (sourceEquiv c a) := by
  change SourceOpenFractionField318.openEmbedding c (overlapEquiv c (sourceMap ℚ c a)) = _
  rw [overlapEquiv_source,SourceOpenFractionField318.openEmbedding_on_order]
end IntegralRationalFullOverlap318
