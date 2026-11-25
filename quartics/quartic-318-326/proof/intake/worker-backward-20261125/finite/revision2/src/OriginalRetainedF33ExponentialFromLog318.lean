module
public import OriginalLocalNormalizedExponentialContinuation318
public import OriginalRetainedF33ExponentialQuotient318

@[expose] public section
noncomputable section

namespace OriginalRetainedF33ExponentialFromLog318
open AlgebraicGeometry CategoryTheory
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedF33ExponentialQuotient318
open OriginalLocalNormalizedExponentialContinuation318
open scoped CategoryTheory.Obj CategoryTheory.MonObj Topology
attribute [local instance] Over.cartesianMonoidalCategory

variable {A₃₃ Y₃₃:Scheme} (a₃₃:A₃₃⟶Y₃₃) [GrpObj (Over.mk a₃₃)]
  {E:Type} [Field E] (σ:E→+*ℂ) (P:Spec (CommRingCat.of E)⟶Y₃₃)
local notation "F" => fiber a₃₃ (specOf σ≫P)
local notation "TC" => Spec (CommRingCat.of ℂ)
local notation "G" => Points a₃₃ σ P
local notation "J" => Additive G

/-- The existing abelian surface is commutative. This adds no new
operations on its represented points: only the existing group
operations and their commutativity theorem. -/
instance commOnActualPoints [IsCommMonObj F] : AddCommGroup J where
  __ := inferInstanceAs (AddGroup J)
  add_comm x y :=
    (isMulCommutative_iff.mp
      ((isCommMonObj_iff_isMulCommutative F).mp ‹IsCommMonObj F› (Over.mk (𝟙 TC))))
      x.toMul y.toMul

variable [IsCommMonObj F] (r:ℝ) (hr:0<r) (loc:V→J)
  (at_zero:loc 0=0) (add_on_ball:∀z w:V,‖z‖<r→‖w‖<r→‖z+w‖<r→loc (z+w)=loc z+loc w)

/-- The actual exponential produced from the inverse of the local
logarithm of the very same marked analytic abelian surface. -/
def actualExp : Tangent→+J :=
  continueExp r hr loc at_zero add_on_ball

theorem reads_actual_local (z:Tangent) (hz:‖z‖<r):
    actualExp a₃₃ σ P r hr loc at_zero add_on_ball z=loc z :=
  continueExp_local r hr loc at_zero add_on_ball z hz

theorem unique_of_actual_germ (e:Tangent→+J)
    (he:∀z:Tangent,‖z‖<r→e z=loc z):
    actualExp a₃₃ σ P r hr loc at_zero add_on_ball=e :=
  continueExp_unique r hr loc at_zero add_on_ball e he

variable [TopologicalSpace J] [IsTopologicalAddGroup J] [PreconnectedSpace J]

/-- Genuine analytic local openness suffices; the continuous
surjective additive exponential on the full actual point group
is produced without an analytic-isomorphism hypothesis. -/
theorem actualExp_surjective (localOpen:loc '' {z:Tangent | ‖z‖<r}∈𝓝 (0:J)):
    Function.Surjective (actualExp a₃₃ σ P r hr loc at_zero add_on_ball) :=
  actual_exp_surjective a₃₃ σ P _ (continueExp_near r hr loc at_zero add_on_ball localOpen)

omit [PreconnectedSpace J] in
theorem actualExp_continuous (localContinuous:ContinuousAt loc (0:Tangent)):
    Continuous (actualExp a₃₃ σ P r hr loc at_zero add_on_ball) :=
  continuous_of_continuousAt_zero _
    (continueExp_continuousAt r hr loc at_zero add_on_ball localContinuous)

end OriginalRetainedF33ExponentialFromLog318
