module
public import OpenDominantTraceExistence318
public section
noncomputable section
namespace OpenDominantTrace318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (hY:NormalAffineBasis318.HasBasis Y)
    (hfinite:letI:=AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
@[expose] def value (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):Γ(Y,U):=
  Classical.choose (OpenDominantTraceExistence318.exists_value f hY hfinite U s)
lemma value_embedding (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (value f hY hfinite U s)=
      Algebra.trace Y.functionField X.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=
  Classical.choose_spec (OpenDominantTraceExistence318.exists_value f hY hfinite U s)
@[expose] def nonemptyTrace (U:Y.Opens) [Nonempty U]:Γ(X,f⁻¹ᵁU)→+Γ(Y,U) where
  toFun:=value f hY hfinite U
  map_zero':=by
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [value_embedding,map_zero,map_zero,map_zero]
  map_add' a b:=by
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [value_embedding,map_add,map_add,map_add,value_embedding,value_embedding]
/-- Actual additive regular-function trace on every open, constructed by sheaf gluing
on a normal affine basis. The empty open has its unique section. -/
@[expose] def trace (U:Y.Opens):Γ(X,f⁻¹ᵁU)→+Γ(Y,U):=by
  classical
  exact if h:Nonempty U then @nonemptyTrace _ _ _ _ f _ _ hY hfinite U h else 0
lemma trace_embedding (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    Y.germToFunctionField U (trace f hY hfinite U s)=
      Algebra.trace Y.functionField X.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=by
  classical
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  rw [trace,dif_pos (inferInstance:Nonempty U)]
  change Y.germToFunctionField U (value f hY hfinite U s)=_
  exact value_embedding f hY hfinite U s
lemma empty_subsingleton (U:Y.Opens) (h:¬Nonempty U):Subsingleton Γ(Y,U):=by
  have hu:U=⊥:=by
    apply le_antisymm _ bot_le
    intro x hx
    exact False.elim (h ⟨⟨x,hx⟩⟩)
  rw [hu]
  infer_instance
/-- Restriction compatibility on all actual opens, including empty ones. -/
lemma restrict {U V:Y.Opens} (i:U⟶V) (s:Γ(X,f⁻¹ᵁV)):
    Y.presheaf.map i.op (trace f hY hfinite V s)=
      trace f hY hfinite U (X.presheaf.map (homOfLE (f.preimage_mono i.le)).op s):=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:Nonempty V:=by obtain ⟨x⟩:=h;exact ⟨⟨x.1,i.le x.2⟩⟩
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Nonempty (f⁻¹ᵁV):=DominantFunctionField318.preimage_nonempty f V
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [AffineDominantNormRestriction318.germ_restrict,trace_embedding,trace_embedding,
      AffineDominantNormRestriction318.germ_restrict]
  · letI:=empty_subsingleton U h
    exact Subsingleton.elim _ _
/-- The all-open construction agrees with the previously constructed whole
normal-affine trace by its actual generic embedding. -/
lemma affine_eq (U:Y.Opens) [Nonempty U] [IsIntegrallyClosed Γ(Y,U)] (hU:IsAffineOpen U):
    trace f hY hfinite U=AffineDominantTrace318.trace f U hU hfinite:=by
  ext s
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  apply Y.germToFunctionField_injective U
  rw [trace_embedding,AffineDominantTrace318.embedding]
/-- Pullback followed by transfer on every open, including the empty open. -/
lemma pullback (U:Y.Opens) (a:Γ(Y,U)):
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    trace f hY hfinite U (f.app U a)=Module.finrank Y.functionField X.functionField • a:=by
  classical
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  by_cases h:Nonempty U
  · letI:=h
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    apply Y.germToFunctionField_injective U
    rw [trace_embedding,map_nsmul]
    have hm:=congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a) (DominantFunctionField318.map_germ f U)
    change (DominantFunctionField318.map f) (Y.germToFunctionField U a)=
      X.germToFunctionField (f⁻¹ᵁU) (f.app U a) at hm
    rw [←hm]
    exact Algebra.trace_algebraMap (R:=Y.functionField) (S:=X.functionField) (Y.germToFunctionField U a)
  · letI:=empty_subsingleton U h
    exact Subsingleton.elim _ _
/-- Explicit O-linearity with the actual section pullback on every open. -/
lemma linearity (U:Y.Opens) (a:Γ(Y,U)) (s:Γ(X,f⁻¹ᵁU)):
    trace f hY hfinite U (f.app U a*s)=a*trace f hY hfinite U s:=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    apply Y.germToFunctionField_injective U
    rw [trace_embedding,(X.germToFunctionField (f⁻¹ᵁU)).hom.map_mul,
      (Y.germToFunctionField U).hom.map_mul,trace_embedding]
    have hm:=congrArg (fun g:Γ(Y,U)⟶X.functionField=>g a) (DominantFunctionField318.map_germ f U)
    change (DominantFunctionField318.map f) (Y.germToFunctionField U a)=
      X.germToFunctionField (f⁻¹ᵁU) (f.app U a) at hm
    rw [←hm]
    simpa only [Algebra.smul_def,Algebra.algebraMap_self,RingHom.id_apply,
      AffineDominantNorm318.fieldAlgebra,RingHom.algebraMap_toAlgebra] using
      (Algebra.trace Y.functionField X.functionField).map_smul
        (Y.germToFunctionField U a) (X.germToFunctionField (f⁻¹ᵁU) s)
  · letI:=empty_subsingleton U h
    exact Subsingleton.elim _ _
end OpenDominantTrace318
