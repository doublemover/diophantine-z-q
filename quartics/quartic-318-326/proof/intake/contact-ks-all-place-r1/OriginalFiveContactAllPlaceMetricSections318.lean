module

public import OriginalLiteralFiveContactAllFinite318
public import OriginalFiveContactExactArchRead318
public import Mathlib.Algebra.Ring.ULift

@[expose] public section
noncomputable section

namespace OriginalFiveContactAllPlaceMetricSections318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open SectionHeight318 PeterssonSectionNorm318
open OriginalRetainedComplexZeroByPasting318 (specOf spec_comp)
open OriginalThreeElevenNamedProperCentres318 OriginalFineArithmeticPlaceSwitch318
open OriginalLiteralFiveContactAllFinite318 OriginalYuanAllFinitePlaces318

universe u x

/-- The generic base is the literal ℚ-localization of the full 33
arithmetic model; the universe lift only transports the fixed ℚ. -/
def fullRatBase : FullBase →+* ULift.{u} ℚ :=
  (ULift.ringEquiv.symm.toRingHom : ℚ →+* ULift.{u} ℚ).comp (oldFullBase (E:=ℚ))

variable {E : Type u} [Field E] [NumberField E]
variable (B : OriginalFineBases.{u}) (m : CommonMark (E:=E) B)

def ratInHeld : ULift.{u} ℚ →+* E :=
  (Rat.castHom E).comp ULift.ringEquiv.toRingHom

theorem full_base_same :
    (ratInHeld (E:=E)).comp fullRatBase.{u}=oldFullBase (E:=E) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (33:ℤ))
  ext z
  change Rat.castHom E (oldFullBase (E:=ℚ) (algebraMap ℤ FullBase z)) =
    oldFullBase (E:=E) (algebraMap ℤ FullBase z)
  simp only [oldFullBase, IsLocalization.Away.lift_eq, map_intCast]

abbrev genericFull := pullback B.pFull (specOf fullRatBase.{u})

/-- Its first projection is the whole retained mark, not a point
picked using equality of the `T` coordinate on another sheet. -/
def genericMark : Spec (CommRingCat.of E) ⟶ genericFull B :=
  pullback.lift m.P33 (specOf (ratInHeld (E:=E))) (by
    rw [m.over, spec_comp, full_base_same])

theorem genericMark_read :
    genericMark B m ≫ pullback.fst B.pFull (specOf fullRatBase.{u})=m.P33 :=
  pullback.lift_fst _ _ _

def complexField (w : InfinitePlace E) : E →+* ULift.{u} ℂ :=
  (ULift.ringEquiv.symm.toRingHom : ℂ →+* ULift.{u} ℂ).comp w.embedding

variable {Z : Scheme.{u}} (coarse : genericFull B ⟶ Z)

/-- Given the actual canonical characteristic-zero forget, specialize
the very same marked scheme arrow at the relevant embedding. -/
def complexMark (w : InfinitePlace E) : Spec (CommRingCat.of (ULift.{u} ℂ)) ⟶ Z :=
  specOf (complexField w) ≫ genericMark B m ≫ coarse

variable {X : Type x} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable (analytify : (Spec (CommRingCat.of (ULift.{u} ℂ)) ⟶ Z) → X)

/-- No separately supplied map from infinite places to points. -/
def analyticMark (w : InfinitePlace E) : X := analytify (complexMark B m coarse w)

variable (H C : FrameNorms E) (u₀ v : ℤ) (hYuan : ℝ)
variable (forms : ∀ i : Fin 5, ContactRadical318.forms u₀ v i ≠ 0)
variable {H₀ C₀ : Type u}
  [AddCommGroup H₀] [AddCommGroup C₀] [Module E H₀] [Module E C₀]
variable {HL CL : Lane → Type u}
  [∀ n, AddCommGroup (HL n)] [∀ n, AddCommGroup (CL n)]
  [∀ n, Module E (HL n)] [∀ n, Module E (CL n)]
variable (h₀ : H₀ ≃ₗ[E] E) (c₀ : C₀ ≃ₗ[E] E)
variable (hT : ∀ n, HL n ≃ₗ[E] H₀) (cT : ∀ n, CL n ≃ₗ[E] C₀)
variable (Ψ : H₀ →ₗ[E] C₀)

theorem scalar_nonzero
    (archIsometry : ∀ w : InfinitePlace E, w (k h₀ c₀ Ψ) * C.arch w = H.arch w ^ 2) :
    k h₀ c₀ Ψ ≠ 0 := by
  intro hz
  let w : InfinitePlace E := Classical.choice (inferInstance : Nonempty (InfinitePlace E))
  have e := archIsometry w
  rw [hz, map_zero, zero_mul] at e
  exact (pow_ne_zero 2 (H.arch_pos w).ne') e.symm

/-- Exact R369→R377→arch-r5 composition on the one full marked model.
  The finite bounds and image are computed from the true local charts
  on its proper prolongations; the archimedean read uses the same
  marked point under the fixed embedding. The numerical integral
  bound, coefficient ratio, and nonzero raw scalar are conclusions.
  `archIsometry` is still the norm theorem for the same actual raw Ψ. -/
def sections
    (affineData : ∀ w, charts B m H C (literalT u₀ v) h₀ c₀ hT cT Ψ w)
    (degree : H.normalizedDegree = hYuan)
    (D : GlobalSectionNorm318.Data X)
    (chart : ∀ w : InfinitePlace E, D.kind (analyticMark B m coarse analytify w) =
      SourceMetricCharts318.Chart.regular (w.embedding (literalT u₀ v))
        (OriginalFiveContactExactArchRead318.off_contact u₀ v w forms))
    (normRead : ∀ w : InfinitePlace E, C.arch w =
      quadraticNorm (D.hyperbolic (analyticMark B m coarse analytify w) (0,0))
        (BicanonicalCharts318.q0 LiteralMetricExtension318.contacts
          (w.embedding (literalT u₀ v))))
    (archIsometry : ∀ w : InfinitePlace E, w (k h₀ c₀ Ψ) * C.arch w = H.arch w^2) :
    RefinedContactRealization318.MetricSections E u₀ v hYuan := by
  let F := from_original_pair B m H C h₀ c₀ hT cT Ψ u₀ v forms affineData
  exact OriginalFiveContactExactArchRead318.sections u₀ v C H hYuan
    (k h₀ c₀ Ψ) (scalar_nonzero H C h₀ c₀ Ψ archIsometry) degree D
    (analyticMark B m coarse analytify)
    (fun w => OriginalFiveContactExactArchRead318.at_regular u₀ v C D w
      (analyticMark B m coarse analytify w) forms (chart w) (normRead w))
    F.paid F.images archIsometry

end OriginalFiveContactAllPlaceMetricSections318

#print axioms OriginalFiveContactAllPlaceMetricSections318.full_base_same
#print axioms OriginalFiveContactAllPlaceMetricSections318.genericMark_read
#print axioms OriginalFiveContactAllPlaceMetricSections318.scalar_nonzero
#print axioms OriginalFiveContactAllPlaceMetricSections318.sections
