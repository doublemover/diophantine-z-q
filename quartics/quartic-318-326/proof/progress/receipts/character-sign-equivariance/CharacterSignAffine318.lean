module
public import SourceSignFieldComparison318
public import CompletedCharacterInfinity318
public import ChartNegation318
public section
noncomputable section
namespace CharacterSignAffine318
open SourceTwistArithmetic318 ContactKummerOrder318
open CompletedCharacterInfinity318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
@[expose] def sigma (j:Fin 4):L≃ₐ[RatFunc ℚ]L:=
  FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) (SourceCharacterFields318.flip j)
lemma sigma_rat (j:Fin 4) (q:ℚ):sigma j (algebraMap ℚ L q)=algebraMap ℚ L q:=
  (sigma j).toRingHom.map_rat_algebraMap q
lemma sigma_x (i j:Fin 4):sigma j (rawX i)=rawX i:=by
  rw [rawX_formula,map_mul,map_sub,sigma_rat,sigma_rat]
  rw [InfinityFieldCoordinates318.t,AlgEquiv.commutes]
lemma omitted_root (i:Fin 4):
    sigma i (CharacterRoot318.root (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i))=
      CharacterRoot318.root (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i):=by
  rw [sigma,CharacterRoot318.sign_action]
  have hs:CharacterRoot318.sign (F:=RatFunc ℚ) (SourceCharacterFields318.complement i)
      (SourceCharacterFields318.flip i)=1:=by
    apply Finset.prod_eq_one
    intro j hj
    simp only [SourceCharacterFields318.complement,Finset.mem_erase] at hj
    simp [SourceCharacterFields318.flip,hj.1]
  rw [hs,map_one,one_mul]
lemma omitted_y (i:Fin 4):sigma i (rawY i)=rawY i:=by
  rw [rawY_formula,map_mul,sigma_rat,omitted_root]
lemma other_y (i j:Fin 4) (hji:j≠i):sigma j (rawY i)=-rawY i:=by
  rw [rawY_formula,map_mul,sigma_rat]
  change _*FourRootAutomorphisms318.signEquiv _ (SourceCharacterFields318.flip j) _=_
  rw [SourceCharacterFields318.other_flip_negates units i j hji]
  exact mul_neg (algebraMap ℚ L (CubicInverseCoordinates318.yScale i:ℚ))
    (CharacterRoot318.root (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i))

@[expose] def openPublishedRing (i:Fin 4):Published i→+*OpenOrder units:=
  (SourceOpenFractionField318.orderToOpen units).comp (SourceCharacterAlgebra318.publishedToSource i).toRingHom
@[expose] def openPublished (i:Fin 4):Published i→ₐ[ℚ]OpenOrder units:=
  { openPublishedRing i with commutes':=by intro q;exact (openPublishedRing i).map_rat_algebraMap q }
lemma openPublished_embedding (i:Fin 4) (x:Published i):
    SourceOpenFractionField318.openEmbedding units (openPublished i x)=rawMap i x:=
  SourceOpenFractionField318.openEmbedding_on_order units _

/-- The omitted root flip fixes the exact entire published affine quotient map. -/
theorem omitted_affine (i:Fin 4):
    ((ContactGlobalSigns318.openEquiv units (SourceCharacterFields318.flip i)).toAlgHom.restrictScalars ℚ).comp (openPublished i)=
      openPublished i:=by
  apply AffineEquationFunctor318.hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units _ (openPublished i _))=_
    rw [SourceSignFieldComparison318.open_embedding,openPublished_embedding]
    exact sigma_x i i
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units _ (openPublished i _))=_
    rw [SourceSignFieldComparison318.open_embedding,openPublished_embedding]
    exact omitted_y i

/-- Every other root flip is the exact affine elliptic involution (x,y)↦(x,-y). -/
theorem other_affine (i j:Fin 4) (hji:j≠i):
    ((ContactGlobalSigns318.openEquiv units (SourceCharacterFields318.flip j)).toAlgHom.restrictScalars ℚ).comp (openPublished i)=
      (openPublished i).comp (ChartNegation318.affineNeg (publishedA i) (publishedB i)):=by
  apply AffineEquationFunctor318.hom_ext
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units _ (openPublished i _))=
      SourceOpenFractionField318.openEmbedding units (openPublished i (ChartNegation318.affineNeg _ _ _))
    rw [ChartNegation318.affineNeg_x,SourceSignFieldComparison318.open_embedding,
      openPublished_embedding]
    exact sigma_x i j
  · apply SourceOpenFractionField318.openEmbedding_injective units
    change SourceOpenFractionField318.openEmbedding units (ContactGlobalSigns318.openEquiv units _ (openPublished i _))=
      SourceOpenFractionField318.openEmbedding units (openPublished i (ChartNegation318.affineNeg _ _ _))
    rw [ChartNegation318.affineNeg_y,map_neg,map_neg,SourceSignFieldComparison318.open_embedding,
      openPublished_embedding]
    exact other_y i j hji
end CharacterSignAffine318
