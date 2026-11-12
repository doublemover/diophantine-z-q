module
public import PELArithmeticAdditionHolomorphy318
public section
noncomputable section
namespace PELArithmeticRelativeGroupLaws318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointRelativeAddition318 PELComplexPeriodSurface318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPrincipalThreeCovering318 PELArithmeticOriginalFibers318 PELArithmeticRelativeSum318
open PELArithmeticZeroSection318 PELArithmeticInversion318 PELArithmeticOrderEndomorphisms318
set_option maxHeartbeats 1600000
variable (τ : HalfPlane)

@[expose] def fiberAdd (p q : ArithmeticFiber τ) : ArithmeticFiber τ :=
  ⟨arithmeticAdd ⟨(p.val,q.val),p.property.trans q.property.symm⟩,
    (arithmeticAdd_over_base _).trans p.property⟩
@[expose] def fiberZero : ArithmeticFiber τ :=
  ⟨arithmeticZero (baseQuotient τ),arithmeticZero_section _⟩
@[expose] def fiberNeg (p : ArithmeticFiber τ) : ArithmeticFiber τ :=
  ⟨arithmeticNeg p.val,(arithmeticNeg_over_base p.val).trans p.property⟩

/-- The actual relative sum agrees with original surface addition on the
FULL original fiber. This fixes its group law, not just its zero and torsion. -/
theorem fiberAdd_original (p q : Surface τ) :
    fiberAdd τ (originalFiberEquiv τ p) (originalFiberEquiv τ q)=
      originalFiberEquiv τ (p+q) := by
  apply Subtype.ext
  change arithmeticAdd ⟨(totalQuotient (τ,fiberEquiv τ p),
    totalQuotient (τ,fiberEquiv τ q)),_⟩=totalQuotient (τ,fiberEquiv τ (p+q))
  rw [arithmeticAdd_square (τ,fiberEquiv τ p) (τ,fiberEquiv τ q) rfl]
  change totalQuotient (τ,fiberEquiv τ p+fiberEquiv τ q)=_
  rw [map_add]

theorem fiberZero_original : originalFiberEquiv τ 0=fiberZero τ := by
  apply Subtype.ext
  change totalQuotient (τ,fiberEquiv τ 0)=arithmeticZero (baseQuotient τ)
  rw [map_zero,arithmeticZero_square]
  all_goals rfl

theorem fiberNeg_original (p : Surface τ) :
    fiberNeg τ (originalFiberEquiv τ p)=originalFiberEquiv τ (-p) := by
  apply Subtype.ext
  exact original_fiber_neg τ p

theorem fiberAdd_assoc (p q r : ArithmeticFiber τ) :
    fiberAdd τ (fiberAdd τ p q) r=fiberAdd τ p (fiberAdd τ q r) := by
  obtain ⟨x,rfl⟩ := (originalFiberEquiv τ).surjective p
  obtain ⟨y,rfl⟩ := (originalFiberEquiv τ).surjective q
  obtain ⟨z,rfl⟩ := (originalFiberEquiv τ).surjective r
  simp only [fiberAdd_original,add_assoc]

theorem fiberAdd_comm (p q : ArithmeticFiber τ) : fiberAdd τ p q=fiberAdd τ q p := by
  obtain ⟨x,rfl⟩ := (originalFiberEquiv τ).surjective p
  obtain ⟨y,rfl⟩ := (originalFiberEquiv τ).surjective q
  simp only [fiberAdd_original,add_comm]

theorem fiberZero_add (p : ArithmeticFiber τ) : fiberAdd τ (fiberZero τ) p=p := by
  obtain ⟨x,rfl⟩ := (originalFiberEquiv τ).surjective p
  rw [←fiberZero_original,fiberAdd_original,zero_add]

theorem fiberAdd_zero (p : ArithmeticFiber τ) : fiberAdd τ p (fiberZero τ)=p := by
  rw [fiberAdd_comm,fiberZero_add]

theorem fiberNeg_add (p : ArithmeticFiber τ) : fiberAdd τ (fiberNeg τ p) p=fiberZero τ := by
  obtain ⟨x,rfl⟩ := (originalFiberEquiv τ).surjective p
  rw [fiberNeg_original,fiberAdd_original,neg_add_cancel,fiberZero_original]

/-- Every descended original order map is additive for the actual relative
sum; the claimed endomorphisms use precisely the same group law. -/
theorem fiberOrder_add (a : order) (p q : ArithmeticFiber τ) :
    fiberOrder τ a (fiberAdd τ p q)=fiberAdd τ (fiberOrder τ a p) (fiberOrder τ a q) := by
  obtain ⟨x,rfl⟩ := (originalFiberEquiv τ).surjective p
  obtain ⟨y,rfl⟩ := (originalFiberEquiv τ).surjective q
  simp only [fiberAdd_original,original_fiber_order,map_add]

/-- The τ-indexed laws cover every ACTUAL arithmetic base point, because
the original base quotient is surjective, not just a dense parameterization. -/
theorem every_base_point (b : ArithmeticBase) : ∃ τ : HalfPlane,baseQuotient τ=b :=
  baseQuotient_surjective b
end PELArithmeticRelativeGroupLaws318
