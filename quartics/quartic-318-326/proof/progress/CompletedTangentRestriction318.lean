module
public import CompletedAdditionRestrictions318
public import CompletedIteratedAddition318
public import TangentOpenScheme318
public section
noncomputable section
namespace CompletedTangentRestriction318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

/-- The actual nonvertical tangent chart restricts the actual completed addition. -/
theorem addition_restriction :
    TangentOpenScheme318.intoProduct A B ≫ CompletedAdditionRestrictions318.inputChart A B 0 0 ≫
      CompletedAddition318.addition A B hD =
    TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B := by
  rw [CompletedAdditionRestrictions318.inputChart_addition]
  change TangentOpenScheme318.intoProduct A B ≫ FiniteAdditionGluing318.addition A B hD = _
  exact FiniteAdditionGluing318.restriction A B hD 1

/-- The genuine finite diagonal has the genuine completed diagonal as its image. -/
theorem diagonal_into_completed {X:Scheme.{u}} (f:X⟶ShortAffineScheme318.scheme A B) :
    pullback.lift f f rfl ≫ CompletedAdditionRestrictions318.inputChart A B 0 0 =
      f ≫ WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.diagonal A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedAdditionRestrictions318.inputChart_fst,
      pullback.lift_fst_assoc,CompletedIteratedAddition318.diagonal_fst,Category.comp_id]
    rfl
  · simp only [Category.assoc,CompletedAdditionRestrictions318.inputChart_snd,
      pullback.lift_snd_assoc,CompletedIteratedAddition318.diagonal_snd,Category.comp_id]
    rfl

/-- An actual tangent-diagonal lift computes completed doubling for arbitrary Scheme tests. -/
theorem doubling_restriction {X:Scheme.{u}} (f:X⟶ShortAffineScheme318.scheme A B)
    (d:X⟶TangentOpenScheme318.tangentOpen A B)
    (hd:d≫TangentOpenScheme318.intoProduct A B=pullback.lift f f rfl) :
    f ≫ WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.doubling A B hD =
      d ≫ TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B := by
  have hd' : (d ≫ TangentOpenScheme318.intoProduct A B) ≫
      CompletedAdditionRestrictions318.inputChart A B 0 0 =
      f ≫ WeierstrassGluing318.finiteChart A B ≫ CompletedIteratedAddition318.diagonal A B :=
    (congrArg (fun k : X ⟶ TangentOpenScheme318.productScheme A B =>
      k ≫ CompletedAdditionRestrictions318.inputChart A B 0 0) hd).trans
        (diagonal_into_completed A B f)
  have he := congrArg (fun k => k ≫ CompletedAddition318.addition A B hD) hd'
  simpa only [Category.assoc,addition_restriction,CompletedIteratedAddition318.doubling] using he.symm
end CompletedTangentRestriction318
