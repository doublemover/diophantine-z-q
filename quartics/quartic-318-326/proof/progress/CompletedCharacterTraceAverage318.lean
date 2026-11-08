module
public import CompletedCharacterOpenTrace318
public section
noncomputable section
namespace CompletedCharacterTraceAverage318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318 Opposite
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i
/-- The rational scalar in each original section ring uses the actual
structural map to Spec Q and the original top-open restriction. -/
@[expose] def scalar (i:Fin 4) (U:(Target i).Opens):ℚ→+*Γ(Target i,U):=
  ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv≫
    (WeierstrassGluing318.structureMap (publishedA i) (publishedB i)).appTop≫
    (Target i).presheaf.map (homOfLE le_top).op).hom
lemma scalar_restrict (i:Fin 4) {U V:(Target i).Opens} (j:U⟶V) (q:ℚ):
    (Target i).presheaf.map j.op (scalar i V q)=scalar i U q:=by
  change (((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv≫
    (WeierstrassGluing318.structureMap (publishedA i) (publishedB i)).appTop≫
    (Target i).presheaf.map (homOfLE le_top).op≫(Target i).presheaf.map j.op):
      CommRingCat.of ℚ⟶Γ(Target i,U)) q=_
  rw [←Functor.map_comp]
  rfl
lemma generic_scalar (i:Fin 4) (U:(Target i).Opens) [Nonempty U] (q:ℚ):
    (Target i).germToFunctionField U (scalar i U q)=(q:(Target i).functionField):=by
  exact map_ratCast (((Target i).germToFunctionField U).hom.comp (scalar i U)) q
lemma eighth_mul (i:Fin 4) (U:(Target i).Opens):
    scalar i U (1/8)*(8:Γ(Target i,U))=1:=by
  have h:=congrArg (scalar i U) (by norm_num: (1/8:ℚ)*8=1)
  simpa only [map_mul,map_ofNat,map_one] using h
/-- Genuine trace divided by eight on all actual opens, including the empty one. -/
@[expose] def average (i:Fin 4) (U:(Target i).Opens):Γ(Model,completedMap i⁻¹ᵁU)→+Γ(Target i,U) where
  toFun s:=scalar i U (1/8)*CompletedCharacterOpenTrace318.trace i U s
  map_zero':=by rw [map_zero,mul_zero]
  map_add' a b:=by rw [map_add,mul_add]
lemma average_restrict (i:Fin 4) {U V:(Target i).Opens} (j:U⟶V)
    (s:Γ(Model,completedMap i⁻¹ᵁV)):
    (Target i).presheaf.map j.op (average i V s)=average i U
      (Model.presheaf.map (homOfLE ((completedMap i).preimage_mono j.le)).op s):=by
  change (Target i).presheaf.map j.op (scalar i V (1/8)*CompletedCharacterOpenTrace318.trace i V s)=_
  rw [map_mul,scalar_restrict,CompletedCharacterOpenTrace318.restrict]
  rfl
lemma average_pullback (i:Fin 4) (U:(Target i).Opens) (s:Γ(Target i,U)):
    average i U ((completedMap i).app U s)=s:=by
  change scalar i U (1/8)*CompletedCharacterOpenTrace318.trace i U ((completedMap i).app U s)=s
  rw [CompletedCharacterOpenTrace318.trace_pullback,←mul_assoc,eighth_mul,one_mul]
lemma average_linearity (i:Fin 4) (U:(Target i).Opens)
    (a:Γ(Target i,U)) (s:Γ(Model,completedMap i⁻¹ᵁU)):
    average i U ((completedMap i).app U a*s)=a*average i U s:=by
  change scalar i U (1/8)*CompletedCharacterOpenTrace318.trace i U ((completedMap i).app U a*s)=_
  rw [CompletedCharacterOpenTrace318.linearity]
  change scalar i U (1/8)*(a*CompletedCharacterOpenTrace318.trace i U s)=a*(scalar i U (1/8)*CompletedCharacterOpenTrace318.trace i U s)
  ring
lemma original_generic_average (i:Fin 4) (U:(Target i).Opens) [Nonempty U]
    (s:Γ(Model,completedMap i⁻¹ᵁU)):
    letI:Nonempty (completedMap i⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty (completedMap i) U
    letI:=CompletedCharacterDegree318.pullbackAlgebra i
    (Target i).germToFunctionField U (average i U s)=
      (8:(Target i).functionField)⁻¹*
      Algebra.trace (Target i).functionField Model.functionField
        (Model.germToFunctionField (completedMap i⁻¹ᵁU) s):=by
  change (Target i).germToFunctionField U (scalar i U (1/8)*CompletedCharacterOpenTrace318.trace i U s)=_
  rw [map_mul,CompletedCharacterOpenTrace318.original_generic_trace]
  congr 1
  rw [one_div]
  change (((Target i).germToFunctionField U).hom.comp (scalar i U)) ((8:ℚ)⁻¹)=_
  rw [map_inv₀,map_ofNat]
@[expose] def transfer (i:Fin 4):
    OpenTraceSheaf318.source (completedMap i)⟶OpenTraceSheaf318.target (Y:=Target i) where
  app U:=AddCommGrpCat.ofHom (average i U.unop)
  naturality U V j:=by
    ext s
    exact (average_restrict i j.unop s).symm
/-- The actual pullback of the normalized transfer is an idempotent
regular-function operator; no differential transfer is asserted. -/
@[expose] def projection (i:Fin 4) (U:(Target i).Opens):
    Γ(Model,completedMap i⁻¹ᵁU)→+Γ(Model,completedMap i⁻¹ᵁU):=
  ((completedMap i).app U).hom.toAddMonoidHom.comp (average i U)
lemma projection_twice (i:Fin 4) (U:(Target i).Opens) (s:Γ(Model,completedMap i⁻¹ᵁU)):
    projection i U (projection i U s)=projection i U s:=by
  change (completedMap i).app U (average i U ((completedMap i).app U (average i U s)))=_
  rw [average_pullback]
  rfl
lemma projection_eq_iff (i:Fin 4) (U:(Target i).Opens) (s:Γ(Model,completedMap i⁻¹ᵁU)):
    projection i U s=s ↔ ∃t:Γ(Target i,U),(completedMap i).app U t=s:=by
  constructor
  · intro h
    exact ⟨average i U s,h⟩
  · rintro ⟨t,rfl⟩
    change (completedMap i).app U (average i U ((completedMap i).app U t))=_
    rw [average_pullback]
end CompletedCharacterTraceAverage318
