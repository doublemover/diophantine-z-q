module
public import OriginalSchemeBranchReconstruction318
public import OriginalFiniteDeckDegree318
public import FiniteFlatGenericRank318
public section
noncomputable section
namespace OriginalQuotientRankFixed318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite p] [Flat p] [IsDominant p]
include p in
/-- The original quotient explicitly supplies its integral base. -/
lemma baseIntegral : IsIntegral (ProjectiveJLine318.scheme ℚ) :=
  OriginalProjectiveBaseIntegral318.integral p
/-- The original rational-coordinate algebra, under its constructed integral base. -/
@[expose] def actualBase : Algebra (RatFunc ℚ) Y.functionField := by
  letI := baseIntegral p
  exact OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ

/-- Generic degree is computed from the original morphism rank, retaining
the original base-generic map and its canonical polynomial chart coordinate. -/
lemma rank_eq_coordinate_degree (y : ProjectiveJLine318.scheme ℚ) :
    letI := baseIntegral p
    letI := actualBase p
    p.finrank y = Module.finrank (RatFunc ℚ) Y.functionField := by
  letI := baseIntegral p
  letI := actualBase p
  letI : Algebra (ProjectiveJLine318.scheme ℚ).functionField Y.functionField :=
    (DominantFunctionField318.map p).hom.toAlgebra
  have h := FiniteFlatGenericRank318.finrank_eq_generic_degree p y
  have hc : (algebraMap (ProjectiveJLine318.scheme ℚ).functionField Y.functionField).comp
      OriginalProjectiveFunctionCoordinate318.coordinate.symm.toRingHom =
      (RingEquiv.refl Y.functionField).toRingHom.comp
        (algebraMap (RatFunc ℚ) Y.functionField) := rfl
  exact h.trans (Algebra.finrank_eq_of_equiv_equiv
    OriginalProjectiveFunctionCoordinate318.coordinate.symm
    (RingEquiv.refl Y.functionField) hc).symm

variable (b : ArithmeticGroup → (Y ≅ Y))
  (bone : (b 1).hom = 𝟙 Y)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)
  (hb : Function.Injective (fun w => (b w).hom))
include bone bmul hover hb in
/-- One actual rank-sixteen fiber and the SAME sixteen faithful curve maps
supply the quotient fixed-function identity used by reconstruction. -/
theorem fixed (y : ProjectiveJLine318.scheme ℚ) (hrank : p.finrank y = 16)
    (x : Y.functionField) (hx : ∀ w, OriginalSchemeDeckFieldAction318.ringEquiv b w x = x) :
    letI := baseIntegral p
    ∃ r : RatFunc ℚ, (DominantFunctionField318.map p).hom
      (OriginalProjectiveFunctionCoordinate318.κ r) = x := by
  letI := baseIntegral p
  letI := actualBase p
  have hd : Module.finrank (RatFunc ℚ) Y.functionField = Nat.card ArithmeticGroup := by
    rw [← rank_eq_coordinate_degree p y, hrank]
    change 16 = Nat.card (Fin 4 → ZMod 2)
    norm_num [Nat.card_eq_fintype_card]
  exact OriginalFiniteDeckDegree318.fixed
    (OriginalSchemeDeckFieldAction318.representation p OriginalProjectiveFunctionCoordinate318.κ
      b bone bmul hover)
    (OriginalSchemeDeckFieldAction318.representation_injective p
      OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb) hd x hx
end OriginalQuotientRankFixed318
