module
public import ActualTwoDescentFullLocalClassRestriction318
public section
noncomputable section
namespace ActualTwoDescentActualShaDefinition318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentSquareClassFieldMap318
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Actual full elliptic local cohomology vanishes at EVERY place. -/
def EverywhereLocallyTrivial (n : ℚ) (hn : n ≠ 0) (z : continuousFullCocycles n hn) : Prop :=
  fullClassHom ((algebraMap ℚ ℝ) n) (field_map_ne_zero _ hn)
      (fullCocycleRestriction (algebraMap ℚ ℝ) n hn z)=0 ∧
  ∀ (p : ℕ) [Fact p.Prime], fullClassHom ((algebraMap ℚ (ℚ_[p])) n) (field_map_ne_zero _ hn)
      (fullCocycleRestriction (algebraMap ℚ (ℚ_[p])) n hn z)=0

/-- Genuine Tate-Shafarevich subgroup of ACTUAL full elliptic H1: continuous classes with zero actual restriction at all places. -/
def actualSha (n : ℚ) (hn : n ≠ 0) : AddSubgroup (H1 (fullEllipticRep n hn)) where
  carrier := {x | ∃ z : continuousFullCocycles n hn, fullClassHom n hn z=x ∧ EverywhereLocallyTrivial n hn z}
  zero_mem' := ⟨0,map_zero _,by constructor <;> simp [EverywhereLocallyTrivial,map_zero]⟩
  add_mem' := by
    rintro x y ⟨z,rfl,hzR,hzp⟩ ⟨w,rfl,hwR,hwp⟩
    refine ⟨z+w,map_add _ _ _,?_,?_⟩
    · rw [map_add,map_add,hzR,hwR,zero_add]
    · intro p _
      rw [map_add,map_add,hzp p,hwp p,zero_add]
  neg_mem' := by
    rintro x ⟨z,rfl,hzR,hzp⟩
    refine ⟨-z,map_neg _ _,?_,?_⟩
    · rw [map_neg,map_neg,hzR,neg_zero]
    · intro p _
      rw [map_neg,map_neg,hzp p,neg_zero]

/-- The actual2-torsion of this actual full elliptic Sha, not a renamed Selmer quotient. -/
def actualShaTwo (n : ℚ) (hn : n ≠ 0) : Subgroup (Multiplicative (H1 (fullEllipticRep n hn))) where
  carrier := {x | x.toAdd ∈ actualSha n hn ∧ x^2=1}
  one_mem' := ⟨(actualSha n hn).zero_mem,one_pow 2⟩
  mul_mem' := by
    rintro x y ⟨hx,hx2⟩ ⟨hy,hy2⟩
    exact ⟨(actualSha n hn).add_mem hx hy,by rw [mul_pow,hx2,hy2,one_mul]⟩
  inv_mem' := by
    rintro x ⟨hx,hx2⟩
    exact ⟨(actualSha n hn).neg_mem hx,by rw [inv_pow,hx2,inv_one]⟩

end ActualTwoDescentActualShaDefinition318
