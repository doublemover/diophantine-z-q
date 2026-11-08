module
public import CharacterSignAffine318
public section
noncomputable section
namespace CharacterBooleanAffine318
open SourceTwistArithmetic318 ContactKummerOrder318 CompletedCharacterInfinity318 CharacterSignAffine318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
/-- The actual complementary triple-root character, with all four labelled
source signs retained. -/
@[expose] def epsilon (i:Fin 4) (b:Fin 4→Bool):ℚ:=
  ∏j∈SourceCharacterFields318.complement i,if b j then -1 else 1
lemma epsilon_values (i:Fin 4) (b:Fin 4→Bool):epsilon i b=1∨epsilon i b=-1:=by
  have hs:∀s:Finset (Fin 4),(∏j∈s,if b j then (-1:ℚ) else 1)^2=1:=by
    intro s
    induction s using Finset.induction_on with
    | empty=>simp
    | @insert j s hj ih=>
      rw [Finset.prod_insert hj,mul_pow,ih,mul_one]
      cases hb:b j <;> simp [hb]
  exact sq_eq_one_iff.mp (hs _)
lemma epsilon_composition (i:Fin 4) (b d:Fin 4→Bool):
    epsilon i (fun j=>Bool.xor (b j) (d j))=epsilon i b*epsilon i d:=by
  unfold epsilon
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases hb:b j <;> cases hd:d j <;> simp [hb,hd]
@[expose] def sigma (b:Fin 4→Bool):L≃ₐ[RatFunc ℚ]L:=
  FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b
lemma sigma_rat (b:Fin 4→Bool) (q:ℚ):sigma b (algebraMap ℚ L q)=algebraMap ℚ L q:=
  (sigma b).toRingHom.map_rat_algebraMap q
lemma sigma_x (i:Fin 4) (b:Fin 4→Bool):sigma b (rawX i)=rawX i:=by
  rw [rawX_formula,map_mul,map_sub,sigma_rat,sigma_rat]
  rw [InfinityFieldCoordinates318.t,AlgEquiv.commutes]
lemma epsilon_field (i:Fin 4) (b:Fin 4→Bool):
    algebraMap (RatFunc ℚ) L (CharacterRoot318.sign (F:=RatFunc ℚ) (SourceCharacterFields318.complement i) b)=
      algebraMap ℚ L (epsilon i b):=by
  simp only [CharacterRoot318.sign,epsilon,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases hb:b j <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true,map_neg,map_one]
lemma sigma_y (i:Fin 4) (b:Fin 4→Bool):
    sigma b (rawY i)=algebraMap ℚ L (epsilon i b)*rawY i:=by
  rw [rawY_formula,map_mul,sigma_rat]
  change _*FourRootAutomorphisms318.signEquiv _ b _=_
  rw [CharacterRoot318.sign_action,epsilon_field]
  ring
lemma sigma_y_fixed_iff (i:Fin 4) (b:Fin 4→Bool):sigma b (rawY i)=rawY i↔epsilon i b=1:=by
  rw [sigma_y]
  constructor
  · intro h
    apply (algebraMap ℚ L).injective
    simpa only [map_one] using mul_right_cancel₀ (rawY_ne_zero i) (h.trans (one_mul (rawY i)).symm)
  · intro h
    rw [h,map_one,one_mul]
/-- Full affine equivariance through the literal coefficient map, with no
replacement of the original character-field embedding. -/
theorem positive_affine (i:Fin 4) (b:Fin 4→Bool) (h:epsilon i b=1):
    ((ContactGlobalSigns318.openEquiv units b).toAlgHom.restrictScalars ℚ).comp (openPublished i)=openPublished i:=by
  apply AffineEquationFunctor318.hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (openPublished i _))=_
    rw [SourceSignFieldComparison318.open_embedding,openPublished_embedding]
    exact sigma_x i b
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (openPublished i _))=_
    rw [SourceSignFieldComparison318.open_embedding,openPublished_embedding]
    exact (sigma_y_fixed_iff i b).mpr h

theorem negative_affine (i:Fin 4) (b:Fin 4→Bool) (h:epsilon i b=-1):
    ((ContactGlobalSigns318.openEquiv units b).toAlgHom.restrictScalars ℚ).comp (openPublished i)=
      (openPublished i).comp (ChartNegation318.affineNeg (publishedA i) (publishedB i)):=by
  apply AffineEquationFunctor318.hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (openPublished i _))=
      SourceOpenFractionField318.openEmbedding units (openPublished i (ChartNegation318.affineNeg _ _ _))
    rw [ChartNegation318.affineNeg_x,SourceSignFieldComparison318.open_embedding,openPublished_embedding]
    exact sigma_x i b
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units b (openPublished i _))=
      SourceOpenFractionField318.openEmbedding units (openPublished i (ChartNegation318.affineNeg _ _ _))
    rw [ChartNegation318.affineNeg_y,map_neg,map_neg,SourceSignFieldComparison318.open_embedding,openPublished_embedding]
    change sigma b (rawY i)=-rawY i
    rw [sigma_y,h,map_neg,map_one]
    exact neg_one_mul (rawY i)
end CharacterBooleanAffine318
