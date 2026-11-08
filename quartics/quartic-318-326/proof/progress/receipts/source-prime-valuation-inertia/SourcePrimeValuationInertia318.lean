module
public import SourceValuationFullInertia318
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public section
noncomputable section
namespace SourcePrimeValuationInertia318
open ContactKummerOrder318 Polynomial IsDedekindDomain
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
local instance sourceDedekind:IsDedekindDomain (SourceOrder c):=SourceBranchValuation318.source_dedekind c
variable (Q:Ideal (SourceOrder c)) [Q.IsPrime]
abbrev k:=Q.ResidueField
local instance residueBase:Algebra R (k c Q):=
  ((algebraMap (SourceOrder c) (k c Q)).comp (algebraMap R (SourceOrder c))).toAlgebra
local instance residueRat:Algebra ℚ (k c Q):=
  ((algebraMap (SourceOrder c) (k c Q)).comp (algebraMap ℚ (SourceOrder c))).toAlgebra
local instance baseTower:IsScalarTower R (SourceOrder c) (k c Q):=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=SourceOrder c) (A:=k c Q) (fun _=>rfl)
local instance ratTower:IsScalarTower ℚ R (k c Q):=by
  apply IsScalarTower.of_algebraMap_eq
  intro q
  change algebraMap (SourceOrder c) (k c Q) (algebraMap ℚ (SourceOrder c) q)=
    algebraMap (SourceOrder c) (k c Q) (algebraMap R (SourceOrder c) (algebraMap ℚ R q))
  rw [IsScalarTower.algebraMap_apply ℚ R (SourceOrder c)]

/-- Canonical field-valued point of every actual source prime. -/
@[expose] def residuePoint:SourceOrder c→ₐ[R]k c Q:=IsScalarTower.toAlgHom R (SourceOrder c) (k c Q)
lemma kernel_exact:SourceBranchResidueInertia318.prime c (residuePoint c Q)=Q:=
  Ideal.ker_algebraMap_residueField Q

variable (i:Fin 4)
    (hc:algebraMap R (SourceOrder c) (X-C (LinearContactSquareclass318.contacts i))∈Q)
include hc
lemma residue_contact:algebraMap R (k c Q) X=
    algebraMap ℚ (k c Q) (LinearContactSquareclass318.contacts i):=by
  have h:=Ideal.algebraMap_residueField_eq_zero.mpr hc
  change algebraMap R (k c Q) (X-C (LinearContactSquareclass318.contacts i))=0 at h
  rw [map_sub] at h
  apply sub_eq_zero.mp
  exact h

/-- The valuation inside the original full field at this exact prime. -/
@[expose] abbrev valuationRing:ValuationSubring (L c):=
  SourceBranchValuation318.valuationRing c (residuePoint c Q) i (residue_contact c Q i hc)

theorem actual_prime:(SourceBranchValuation318.place c (residuePoint c Q) i
    (residue_contact c Q i hc)).asIdeal=Q:=kernel_exact c Q

/-- Every source prime above the literal finite contact is covered, with
no supplied field-valued point or residue-field embedding. -/
theorem inertia_card:Nat.card ((valuationRing c Q i hc).inertiaSubgroup K)=2:=
  SourceValuationFullInertia318.inertia_card c (residuePoint c Q) i (residue_contact c Q i hc)
end SourcePrimeValuationInertia318
