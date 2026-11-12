module
public import OpenDominantNormExistence318
public section
noncomputable section
namespace OpenDominantNorm318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (hY:NormalAffineBasis318.HasBasis Y)
@[expose] def value (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):Γ(Y,U):=
  Classical.choose (OpenDominantNormExistence318.exists_value f hY U s)
lemma value_embedding (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (value f hY U s)=
      Algebra.norm Y.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=
  Classical.choose_spec (OpenDominantNormExistence318.exists_value f hY U s)
@[expose] def nonemptyNorm (U:Y.Opens) [Nonempty U]:Γ(X,f⁻¹ᵁU)→*Γ(Y,U) where
  toFun:=value f hY U
  map_one':=by
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [value_embedding,map_one,map_one,map_one]
  map_mul' a b:=by
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [value_embedding,map_mul,map_mul,map_mul,value_embedding,value_embedding]
/-- Actual regular-function norm on every open, constructed by sheaf gluing
on a normal affine basis. The empty open has its unique section. -/
@[expose] def norm (U:Y.Opens):Γ(X,f⁻¹ᵁU)→*Γ(Y,U):=by
  classical
  exact if h:Nonempty U then @nonemptyNorm _ _ _ _ f _ _ hY U h else 1
lemma norm_embedding (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (norm f hY U s)=
      Algebra.norm Y.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=by
  classical
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  rw [norm,dif_pos (inferInstance:Nonempty U)]
  change Y.germToFunctionField U (value f hY U s)=_
  exact value_embedding f hY U s
lemma empty_subsingleton (U:Y.Opens) (h:¬Nonempty U):Subsingleton Γ(Y,U):=by
  have hu:U=⊥:=by
    apply le_antisymm _ bot_le
    intro x hx
    exact False.elim (h ⟨⟨x,hx⟩⟩)
  rw [hu]
  infer_instance
/-- Restriction compatibility on all actual opens, including empty ones. -/
lemma restrict {U V:Y.Opens} (i:U⟶V) (s:Γ(X,f⁻¹ᵁV)):
    Y.presheaf.map i.op (norm f hY V s)=
      norm f hY U (X.presheaf.map (homOfLE (f.preimage_mono i.le)).op s):=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:Nonempty V:=by obtain ⟨x⟩:=h;exact ⟨⟨x.1,i.le x.2⟩⟩
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Nonempty (f⁻¹ᵁV):=DominantFunctionField318.preimage_nonempty f V
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [AffineDominantNormRestriction318.germ_restrict,norm_embedding,norm_embedding,
      AffineDominantNormRestriction318.germ_restrict]
  · letI:=empty_subsingleton U h
    exact Subsingleton.elim _ _
/-- The all-open construction agrees with the previously constructed whole
normal-affine norm by its actual generic embedding. -/
lemma affine_eq (U:Y.Opens) [Nonempty U] [IsIntegrallyClosed Γ(Y,U)] (hU:IsAffineOpen U):
    norm f hY U=AffineDominantNorm318.norm f U hU:=by
  apply AffineDominantNorm318.unique
  intro s
  exact norm_embedding f hY U s
/-- Pullback followed by the all-open norm is the actual generic-degree power. -/
lemma pullback (U:Y.Opens) (s:Γ(Y,U)):
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    norm f hY U (f.app U s)=s^Module.finrank Y.functionField X.functionField:=by
  classical
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  by_cases h:Nonempty U
  · letI:=h
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    have hg:X.germToFunctionField (f⁻¹ᵁU) (f.app U s)=
        algebraMap Y.functionField X.functionField (Y.germToFunctionField U s):=by
      exact (congrArg (fun g:Γ(Y,U)⟶X.functionField=>g s)
        (DominantFunctionField318.map_germ f U)).symm
    apply Y.germToFunctionField_injective U
    rw [norm_embedding,hg,Algebra.norm_algebraMap,map_pow]
  · letI:=empty_subsingleton U h
    exact Subsingleton.elim _ _
end OpenDominantNorm318
