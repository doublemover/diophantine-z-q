module
public import ContactOverlapAlgebraMaps318
public import SourceCharacterFields318
public section
noncomputable section
namespace InfinityCharacterUnits318
open Polynomial
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev Base:=InfinityOpenChart318.OpenBase c
abbrev Order:=InfinityOpenChart318.OpenOrder c
abbrev L:=InfinityFieldCoordinates318.L c
local instance actualField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance originalAlgebra : Algebra (Order c) (L c):=(InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance baseOriginalAlgebra : Algebra (Base c) (L c):=
  ((InfinityOpenFractionField318.openEmbedding c).comp (algebraMap (Base c) (Order c))).toAlgebra
local instance originalClosure : IsIntegralClosure (Order c) (Base c) (L c):=
  InfinityNormalChart318.actual_integralClosure c

lemma coefficient_image (j:Fin 3):
    algebraMap (Base c) (L c) (algebraMap ℚ[X] (Base c) (InfinityParameters318.coefficient c j))=
      InfinityFieldCoordinates318.ratio c j^2:=by
  change InfinityOpenFractionField318.openEmbedding c
    (algebraMap (Base c) (Order c) (algebraMap ℚ[X] (Base c) _))=_
  rw [ReciprocalInfinityNormalization318.openEmbedding_on_polynomial,
    InfinityParameters318.coefficient_shape]
  simp only [map_mul,map_sub,map_one,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
  exact (InfinityFieldCoordinates318.ratio_square c j).symm

lemma ratio_integral (j:Fin 3):IsIntegral (Base c) (InfinityFieldCoordinates318.ratio c j):=by
  apply IsIntegral.of_pow (n:=2) (by decide)
  rw [←coefficient_image]
  exact isIntegral_algebraMap

lemma ratio_exists (j:Fin 3):∃x:Order c,InfinityOpenFractionField318.openEmbedding c x=
    InfinityFieldCoordinates318.ratio c j:=
  (IsIntegralClosure.isIntegral_iff (A:=Order c) (R:=Base c) (B:=L c)).mp (ratio_integral c j)

/-- The unique original-field root ratio, constructed in the entire actual
infinity order by its already proved integral-closure property. -/
@[expose] def ratio (j:Fin 3):Order c:=Classical.choose (ratio_exists c j)
theorem ratio_embedding (j:Fin 3):InfinityOpenFractionField318.openEmbedding c (ratio c j)=
    InfinityFieldCoordinates318.ratio c j:=Classical.choose_spec (ratio_exists c j)

theorem ratio_square (j:Fin 3):(ratio c j)^2=
    algebraMap (Base c) (Order c) (algebraMap ℚ[X] (Base c) (InfinityParameters318.coefficient c j)):=by
  apply InfinityOpenFractionField318.openEmbedding_injective c
  rw [map_pow,ratio_embedding]
  exact (coefficient_image c j).symm

/-- Every original-field root ratio is a unit everywhere on this infinity
neighborhood, including above infinity itself. -/
theorem ratio_unit (j:Fin 3):IsUnit (ratio c j):=by
  have h:IsUnit ((ratio c j)^2):=by
    rw [ratio_square]
    exact (InfinityOpenChart318.coefficient_unit c j).map (algebraMap (Base c) (Order c))
  exact (isUnit_pow_iff (by decide:(2:ℕ)≠0)).mp h

@[expose] def indexedRatio : Fin 4→Order c:=Fin.cases 1 (ratio c)
theorem indexedRatio_unit (i:Fin 4):IsUnit (indexedRatio c i):=by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact isUnit_one
  · exact ratio_unit c j

theorem indexedRatio_embedding (i:Fin 4):
    InfinityOpenFractionField318.openEmbedding c (indexedRatio c i)=
      InfinityFieldCoordinates318.root c i/InfinityFieldCoordinates318.root c 0:=by
  refine Fin.cases ?_ (fun j=>?_) i
  · change InfinityOpenFractionField318.openEmbedding c 1=_
    rw [map_one,div_self (InfinityFieldCoordinates318.root_ne_zero c 0)]
  · exact ratio_embedding c j

@[expose] def ratioProduct (i:Fin 4):Order c:=
  ∏j∈SourceCharacterFields318.complement i,indexedRatio c j

theorem ratioProduct_unit (i:Fin 4):IsUnit (ratioProduct c i):=by
  apply IsUnit.prod_iff.mpr
  intro j hj
  exact indexedRatio_unit c j

lemma complement_card (i:Fin 4):(SourceCharacterFields318.complement i).card=3:=by
  fin_cases i <;> decide

/-- The actual complementary character root has its exact pole-three
normalization in the original field, with a unit coefficient on the whole
infinity order. This is the denominator needed for the completed quotient. -/
theorem character_normalization (i:Fin 4):
    (InfinityFieldCoordinates318.u c)^3*
      CharacterRoot318.root (SourceKummerField318.parameter c) (SourceCharacterFields318.complement i)=
    (algebraMap ℚ (L c) (c 0:ℚ))^3*
      InfinityOpenFractionField318.openEmbedding c (ratioProduct c i):=by
  have hf (j:Fin 4):InfinityFieldCoordinates318.u c*InfinityFieldCoordinates318.root c j=
      algebraMap ℚ (L c) (c 0:ℚ)*
        InfinityOpenFractionField318.openEmbedding c (indexedRatio c j):=by
    rw [indexedRatio_embedding]
    change (algebraMap ℚ (L c) (c 0:ℚ)/InfinityFieldCoordinates318.root c 0)*_=_
    ring
  have hp:=Finset.prod_congr (s₁:=SourceCharacterFields318.complement i)
    (s₂:=SourceCharacterFields318.complement i) rfl (fun j hj=>hf j)
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,complement_card,
    ratioProduct,map_prod,CharacterRoot318.root,InfinityFieldCoordinates318.root] using hp
end InfinityCharacterUnits318
