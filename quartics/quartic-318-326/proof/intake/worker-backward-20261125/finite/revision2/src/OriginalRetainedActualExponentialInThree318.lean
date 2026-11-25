module
public import OriginalRetainedF33ExponentialQuotient318

@[expose] public section
noncomputable section

namespace OriginalRetainedActualExponentialInThree318
open AlgebraicGeometry CategoryTheory Limits
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedComplexPointFromE318
open OriginalRetainedComplexPointsOverEEquiv318 OriginalRetainedF33ExponentialQuotient318
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {A₃₃ A₃ Y₃₃ Y₃:Scheme} (a₃₃:A₃₃⟶Y₃₃) (a₃:A₃⟶Y₃)
  (forget:Y₃₃⟶Y₃) (u₀:A₃₃⟶A₃) (cart:IsPullback u₀ a₃₃ a₃ forget)
  [GrpObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
  {L E:Type} [Field L] [Field E] (i:L→+*E) (σ:E→+*ℂ)
  (P:Spec (CommRingCat.of E)⟶Y₃₃) (x3:Spec (CommRingCat.of L)⟶Y₃)
  (named:specOf i≫x3=P≫forget)
local notation "TC" => Spec (CommRingCat.of ℂ)
local notation "F3" => fiber a₃ (specOf (σ.comp i)≫x3)
local notation "Pts" => Points a₃₃ σ P
local notation "φ" => Iso.hom (complex a₃₃ a₃ forget u₀ cart i σ P x3 named)

variable (exp:Tangent→+Additive Pts)

/-- This is the unique E-read of the single actual exponential p.
It uses the same E-fibre and selected complex place as the R119 arrow. -/
def arithmeticRead (z:Tangent):Over.mk (specOf σ)⟶fiber a₃₃ P :=
  readOverE a₃₃ P (specOf σ) (exp z).toMul

local notation "q" => arithmeticRead a₃₃ σ P exp
local notation "R" => originalInThree a₃₃ a₃ forget u₀ cart i σ P x3 named q

theorem arithmeticRead_add (z w:Tangent):q (z+w)=q z*q w := by
  have h := congrArg Additive.toMul (exp.map_add z w)
  unfold arithmeticRead
  exact (congrArg (readOverE a₃₃ P (specOf σ)) h).trans
    (readOverE_mul a₃₃ P (specOf σ) (exp z).toMul (exp w).toMul)

include cart named in
/-- The full morphism at j3 is the actual input complex point
composed with the literal canonical marked [11] forget isomorphism. -/
theorem real_point_in_three (z:Tangent):
    R z=(exp z).toMul≫φ :=
  congrArg (fun p=>p≫φ) (lift_of_readOverE a₃₃ P (specOf σ) (exp z).toMul)

include cart named in
theorem true_x3_exp_add
    [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom] (z w:Tangent):
    R (z+w)=R z*R w :=
  original_full_add a₃₃ a₃ forget u₀ cart i σ P x3 named q
    (arithmeticRead_add a₃₃ σ P exp) z w

variable (periods:IntegralLabels→+Tangent)
  (frame:IntegralLabels≃+exp.ker)
  (four_labels:∀i₀:Fin 4,(frame (Pi.single i₀ 1):Tangent)=periods (Pi.single i₀ 1))

include cart named four_labels in
/-- Entire scheme points in the SAME selected original x3 fibre
coincide iff their difference is a genuine full integral period.
In particular, dropping the 11-level mark does not change the kernel. -/
theorem true_x3_eq_iff_integral (z w:Tangent):
    (R z).left=(R w).left ↔ ∃m:IntegralLabels,periods m=z-w := by
  have hj : R z=R w ↔ exp z=exp w := by
    rw [real_point_in_three a₃₃ a₃ forget u₀ cart i σ P x3 named exp z,
      real_point_in_three a₃₃ a₃ forget u₀ cart i σ P x3 named exp w]
    constructor
    · intro h
      exact Additive.toMul.injective ((cancel_mono φ).mp h)
    · intro h
      exact congrArg (fun p:Additive Pts=>p.toMul≫φ) h
  have hg : exp z=exp w ↔ z-w∈exp.ker := by
    change exp z=exp w ↔ exp (z-w)=0
    rw [map_sub,sub_eq_zero]
  have hk := exact_analytic_kernel a₃₃ σ P exp periods frame four_labels
  constructor
  · intro h
    have hker := hg.mp (hj.mp (Over.OverMorphism.ext h))
    rw [←hk] at hker
    exact hker
  · intro h
    have hker : z-w∈exp.ker := hk ▸ h
    exact congrArg (fun f:Over.mk (𝟙 TC)⟶F3=>f.left) (hj.mpr (hg.mpr hker))

/-- Any historically recorded q agreeing on the WHOLE original complex
point is the very same map. Agreement on T or selected scalar values
does not identify it. -/
theorem same_recorded_q (old:Tangent→(Over.mk (specOf σ)⟶fiber a₃₃ P))
    (whole:∀z,complexPoint a₃₃ P (specOf σ) (old z)=(exp z).toMul):
    q=old :=
  funext fun z=>readOverE_unique a₃₃ P (specOf σ) (exp z).toMul (old z) (whole z)

end OriginalRetainedActualExponentialInThree318
