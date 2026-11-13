module
public import IntegralNormalReciprocalForms318
public import OriginalNormalDualSheafSections318
public section
noncomputable section
namespace OriginalNormalDualDifferential318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "F" => IntegralDistinctContactOpen318.Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N
local notation "S" => OriginalNormalDualSheafSections318.Sections c t w D
local notation "π" => AffineFiniteDualSheafAdjunction318.projection P N

/-- Every actual affine dual-sheaf section has an actual source form,
not just a scalar labeled a differential. -/
@[expose] def sourceForm (s : S) : KaehlerDifferential R B :=
  IntegralNormalTraceForms318.form R a d
    ⟨OriginalNormalDualSheafSections318.coefficient c t w D s,
      OriginalNormalDualSheafSections318.coefficient_mem c t w D s⟩

lemma source_coefficient (s : S) : IntegralNormalSourceDifferentialFrame318.frame R a d
    (sourceForm c t w D s)=OriginalNormalDualSheafSections318.coefficient c t w D s :=
  IntegralNormalTraceForms318.coefficient R a d _

/-- Tensor specialization uses exactly the original field point, with
its algebra installed explicitly. It is not Omega of the number field. -/
@[expose] def pointForm (s : S) : OriginalNormalSourceCotangent318.Fiber c t w D M := by
  letI : Algebra B (K c t) := M.fieldPoint.toAlgebra
  exact (1:K c t) ⊗ₜ[B] sourceForm c t w D s

lemma point_coefficient (s : S) :
    OriginalNormalSourceCotangent318.frame c t w D M (pointForm c t w D M s)=
      OriginalNormalDualSheafSections318.value c t w D M s := by
  letI : Algebra B (K c t) := M.fieldPoint.toAlgebra
  change FramedCotangentFiber318.frame R B (K c t)
    (IntegralNormalSourceDifferentialFrame318.frame R a d)
      ((1:K c t) ⊗ₜ[B] sourceForm c t w D s)=_
  rw [FramedCotangentFiber318.frame_tmul,source_coefficient,mul_one]
  rfl

lemma original_coordinate_unit : M.fieldPoint
    (IntegralNormalReciprocalForms318.coordinateUnit R a d:B)=(t:K c t) := by
  rw [IntegralNormalReciprocalForms318.coordinateUnit_value]
  exact OriginalNormalSourceCotangent318.original_coordinate c t w D M

/-- Exact coefficient transition of the same form at the same signed
point: the infinity coefficient is -t squared times the finite one. -/
theorem reciprocal_point_coefficient (s : S) :
    M.fieldPoint (IntegralNormalReciprocalForms318.reciprocalFrame R a d
      (sourceForm c t w D s))=
      -(t:K c t)^2*OriginalNormalDualSheafSections318.value c t w D M s := by
  change M.fieldPoint (-(IntegralNormalReciprocalForms318.coordinateUnit R a d:B)^2*
    IntegralNormalSourceDifferentialFrame318.frame R a d (sourceForm c t w D s))=_
  rw [source_coefficient,map_mul,map_neg,map_pow,original_coordinate_unit]
  rfl

/-- Actual original-chart duality with genuine polynomial differentials.
Its projection is the predecessor's finite map into SAME proper normal M. -/
@[expose] def homEquiv (Q : ModuleCat N) :
    (tilde Q ⟶ IntegralNormalTraceSheafDuality318.traceSheaf R a d) ≃
      ((Scheme.Modules.pushforward π).obj (tilde Q) ⟶
        tilde (R:=CommRingCat.of P) (ModuleCat.of P (KaehlerDifferential R P))) := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  exact IntegralNormalDifferentialDuality318.homEquiv R a d (coefficients_ne_zero c t w D) Q

/-- The proved integral estimate applies to actual cotangent-fiber forms,
with its raw-different correction retained. No Hodge/regularity premise. -/
theorem corrected_pairing (ht : w (t:K c t) ≤ 1) (s : S) (q : K c t)
    (hq : q ∈ OriginalNormalCenterDualImage318.dual c t w D M) :
    w (q*(OriginalNormalizationDifferentValue318.differentValue c t w D M*
      OriginalNormalSourceCotangent318.frame c t w D M (pointForm c t w D M s))) ≤ 1 := by
  rw [point_coefficient]
  exact OriginalNormalDualSheafSections318.corrected_pairing c t w D M ht s q hq
end OriginalNormalDualDifferential318
