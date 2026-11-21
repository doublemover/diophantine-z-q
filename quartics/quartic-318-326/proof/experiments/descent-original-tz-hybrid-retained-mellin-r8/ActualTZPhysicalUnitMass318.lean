module
public import ActualTZSharedXDivisorAverage318
import all ActualTZSharedXDivisorAverage318
import all ActualTZLiteralPhysicalWrapCarrier318
import all ActualTZLiteralWrapClipping318
public section
noncomputable section
namespace ActualTZPhysicalUnitMass318
open scoped BigOperators
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZSharedXDivisorAverage318
open ActualTZLiteralWrapClipping318 ActualTZRelabelPhysicalGrid318

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable {S : ActualTZJointPolynomialForms318.Terminal m a b} (X : Context S I)

/-- Total original grid × shared-x probability; no strip cutoff
is present. Used to recover the removed mass with error ≤lostBound. -/
theorem full_unit :
    (∑ z : X.OldGrid,mass X z*(∑ r : X.Keys,wrapMass X.n X.width z r))=1 := by
  have hN : (X.n:ℝ)≠0 := by exact_mod_cast X.npos.ne'
  have hR (z : X.OldGrid) : (∑ r : X.Keys,wrapMass X.n X.width z r)=1 := by
    unfold wrapMass
    rw [←Finset.sum_div,←Nat.cast_sum,X.width_total,div_self hN]
  simp only [hR,mul_one,mass]
  exact_mod_cast ActualTZExactZeroIntegerGrid318.uniform_one (len m a j X.M X.M₀)
    (fun i=>X.Mpos.trans_le (len_ge X.M X.M₀ X.fine_le i))

theorem defect_le : |retainedMass X-1|≤lostBound X := by
  have h0 : retainedMass X≤1 := X.mass_total_le
  rw [abs_of_nonpos (sub_nonpos.mpr h0),neg_sub]
  have h :
      1-retainedMass X=
        ∑ z : X.OldGrid,mass X z*(∑ r : X.Keys,(wrapMass X.n X.width z r-X.theta z r)) := by
    simp only [Finset.sum_sub_distrib,mul_sub,full_unit,retainedMass]
  rw [h]
  exact X.lost_mass_bound

/-- Flat finite product index used by the angular kernel, with
identical grid and wrap marginal, not a new Cartesian choice of x. -/
theorem flatten (F : X.OldGrid→X.Keys→ℝ) :
    (∑ zr : X.OldGrid×X.Keys,(mass X zr.1*X.theta zr.1 zr.2)*F zr.1 zr.2) =
      avg X X.theta F := by
  simp only [Fintype.sum_prod_type,avg,Finset.mul_sum,mul_assoc]

theorem flatten_one :
    (∑ zr : X.OldGrid×X.Keys,mass X zr.1*X.theta zr.1 zr.2)=retainedMass X := by
  simp only [Fintype.sum_prod_type,retainedMass,Finset.mul_sum]

end ActualTZPhysicalUnitMass318
