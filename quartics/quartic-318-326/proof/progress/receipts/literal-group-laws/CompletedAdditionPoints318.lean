module
public import CompletedAdditionUnits318
public import AffineProductEvaluation318
public import FiniteAdditionPoints318
public section
noncomputable section
namespace CompletedAdditionPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical
open CompletedFieldPoints318 CompletedAdditionRestrictions318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
abbrev Points := SchemePoints (K:=K) A B
@[expose] def pointPair (p q:Points (K:=K) N) : Spec (CommRingCat.of K) ⟶
    pullback (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B) :=
  pullback.lift p.val q.val (p.property.trans q.property.symm)
@[reassoc] theorem pointPair_fst (p q:Points (K:=K) N) : pointPair N p q ≫ pullback.fst _ _=p.val := by simp [pointPair]
@[reassoc] theorem pointPair_snd (p q:Points (K:=K) N) : pointPair N p q ≫ pullback.snd _ _=q.val := by simp [pointPair]
@[expose] def sumPoint (p q:Points (K:=K) N) : Points (K:=K) N :=
  ⟨pointPair N p q ≫ CompletedAddition318.addition A B hD,by
    rw [Category.assoc,CompletedAddition318.addition_over_base,pointPair_fst_assoc]
    exact p.property⟩

theorem infinity_pair_left (q:Points (K:=K) N) : pointPair N (infinityPoint A B) q=
    q.val ≫ CompletedAdditionUnits318.leftUnit A B := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,CompletedAdditionUnits318.leftUnit_fst,←Category.assoc,q.property]
    rfl
  · rw [pointPair_snd,Category.assoc,CompletedAdditionUnits318.leftUnit_snd,Category.comp_id]
theorem infinity_pair_right (p:Points (K:=K) N) : pointPair N p (infinityPoint A B)=
    p.val ≫ CompletedAdditionUnits318.rightUnit A B := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,CompletedAdditionUnits318.rightUnit_fst,Category.comp_id]
  · rw [pointPair_snd,Category.assoc,CompletedAdditionUnits318.rightUnit_snd,←Category.assoc,p.property]
    rfl
@[simp] theorem sumPoint_infinity_left (q:Points (K:=K) N) : sumPoint N (infinityPoint A B) q=q := by
  apply Subtype.ext
  change pointPair N (infinityPoint A B) q ≫ CompletedAddition318.addition A B hD=q.val
  rw [infinity_pair_left,Category.assoc,CompletedAdditionUnits318.leftUnit_addition,Category.comp_id]
@[simp] theorem sumPoint_infinity_right (p:Points (K:=K) N) : sumPoint N p (infinityPoint A B)=p := by
  apply Subtype.ext
  change pointPair N p (infinityPoint A B) ≫ CompletedAddition318.addition A B hD=p.val
  rw [infinity_pair_right,Category.assoc,CompletedAdditionUnits318.rightUnit_addition,Category.comp_id]

@[expose] def finiteHom (p:AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    ShortAffineJacobian318.Ring A B →ₐ[OpenJModel318.Base N] K :=
  AffineProductEvaluation318.toAlgHom p.val p.property
@[simp] theorem map_finiteHom (p:AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    Spec.map (CommRingCat.ofHom (finiteHom N p).toRingHom)=p.val :=
  AffineProductEvaluation318.map_toAlgHom p.val p.property
@[expose] def finiteProductPoint (p q:AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    Spec (CommRingCat.of K) ⟶ RelativeChordScheme318.productScheme A B :=
  pullback.lift p.val q.val (p.property.trans q.property.symm)
theorem finite_pair (p q:AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    pointPair N (finiteInclusion A B p) (finiteInclusion A B q)=finiteProductPoint N p q ≫ inputChart A B 0 0 := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,inputChart_fst]
    change p.val ≫ WeierstrassGluing318.finiteChart A B=
      finiteProductPoint N p q ≫ pullback.fst _ _ ≫ WeierstrassGluing318.finiteChart A B
    simp [finiteProductPoint]
  · rw [pointPair_snd,Category.assoc,inputChart_snd]
    change q.val ≫ WeierstrassGluing318.finiteChart A B=
      finiteProductPoint N p q ≫ pullback.snd _ _ ≫ WeierstrassGluing318.finiteChart A B
    simp [finiteProductPoint]

theorem sumPoint_finite (p q:AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    sumPoint N (finiteInclusion A B p) (finiteInclusion A B q)=
      FiniteAdditionPoints318.outputSchemePoint N (AlgebraChartEvaluation318.pair (finiteHom N p) (finiteHom N q)) := by
  apply Subtype.ext
  change pointPair N (finiteInclusion A B p) (finiteInclusion A B q) ≫ CompletedAddition318.addition A B hD=_
  rw [finite_pair,Category.assoc,inputChart_addition]
  change finiteProductPoint N p q ≫ FiniteAdditionGluing318.addition A B hD=
    AlgebraChartEvaluation318.finite A B hD (finiteHom N p) (finiteHom N q)
  apply AffineProductEvaluation318.finite_evaluation
  · simpa [finiteProductPoint] using (map_finiteHom N p).symm
  · simpa [finiteProductPoint] using (map_finiteHom N q).symm

theorem finite_reading (p:AffineSchemeSolutions318.SchemePoints (K:=K) A B) :
    LiteralCompletedPoints318.fieldPointEquiv N (finiteInclusion A B p)=
      RelativeChordPoints318.pointOfHom N (finiteHom N p) := by
  apply FiniteAdditionPoints318.completed_finite_reading
  exact congrArg (fun f=>f ≫ WeierstrassGluing318.finiteChart A B) (map_finiteHom N p).symm

/-- Evaluation of the actual global Scheme morphism is genuine Mathlib point
addition, including the actual infinity section. -/
theorem actual_add (p q:Points (K:=K) N) :
    LiteralCompletedPoints318.fieldPointEquiv N (sumPoint N p q)=
      LiteralCompletedPoints318.fieldPointEquiv N p+LiteralCompletedPoints318.fieldPointEquiv N q := by
  classical
  rcases finite_or_infinity A B p with ⟨pf,rfl⟩ | rfl
  · rcases finite_or_infinity A B q with ⟨qf,rfl⟩ | rfl
    · rw [sumPoint_finite,finite_reading,finite_reading]
      have hf:(AlgebraChartEvaluation318.pair (finiteHom N pf) (finiteHom N qf)).comp
          (RelativeChordAlgebra318.leftPair A B)=finiteHom N pf := by
        apply AlgHom.ext
        exact AlgebraChartEvaluation318.pair_left _ _
      have hg:(AlgebraChartEvaluation318.pair (finiteHom N pf) (finiteHom N qf)).comp
          (RelativeChordAlgebra318.rightPair A B)=finiteHom N qf := by
        apply AlgHom.ext
        exact AlgebraChartEvaluation318.pair_right _ _
      have hh:=FiniteAdditionPoints318.actual_add N (AlgebraChartEvaluation318.pair (finiteHom N pf) (finiteHom N qf))
      rw [hf,hg] at hh
      exact hh
    · rw [sumPoint_infinity_right,LiteralCompletedPoints318.fieldPointEquiv_infinity,←WeierstrassCurve.Affine.Point.zero_def,add_zero]
  · rw [sumPoint_infinity_left,LiteralCompletedPoints318.fieldPointEquiv_infinity,←WeierstrassCurve.Affine.Point.zero_def,zero_add]

theorem sumPoint_assoc (p q r:Points (K:=K) N) :
    sumPoint N (sumPoint N p q) r=sumPoint N p (sumPoint N q r) := by
  apply (LiteralCompletedPoints318.fieldPointEquiv N).injective
  simp only [actual_add,add_assoc]
end CompletedAdditionPoints318
