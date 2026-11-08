module
public import CompletedCharacterDegree318
public import CompletedCharacterFinite318
public import CompletedRationalDedekind318
public import DedekindAffineFlat318
public import NormalAffineBasis318
public section
noncomputable section
namespace CompletedCharacterTraceBasis318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Model:=ContactGlobalSmooth318.Model units
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i
local instance finiteAffine (i:Fin 4):IsAffine (ShortAffineScheme318.scheme (publishedA i) (publishedB i)):=by
  change IsAffine (Spec (CommRingCat.of (ShortAffineJacobian318.Ring (publishedA i) (publishedB i))))
  infer_instance
@[expose] def chartOpen (i:Fin 4):Bool→(Target i).Opens
  | false=>(WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).opensRange
  | true=>(WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)).opensRange
lemma chart_affine (i:Fin 4) (b:Bool):IsAffineOpen (chartOpen i b):=by
  cases b
  · exact isAffineOpen_opensRange (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
  · exact isAffineOpen_opensRange (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i))
lemma discriminant_unit (i:Fin 4):IsUnit (-16*(4*(publishedA i)^3+27*(publishedB i)^2)):=
  isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (published_nonsingular i))
lemma chart_normal (i:Fin 4) (b:Bool):IsIntegrallyClosed Γ(Target i,chartOpen i b):=by
  cases b
  · letI:=CompletedRationalDedekind318.affine (publishedA i) (publishedB i) (discriminant_unit i)
    letI:=DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (ShortAffineJacobian318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
    change IsIntegrallyClosed Γ(Target i,(WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).opensRange)
    infer_instance
  · letI:=CompletedRationalDedekind318.infinity (publishedA i) (publishedB i) (discriminant_unit i)
    letI:=DedekindAffineFlat318.sections_dedekind
      (CommRingCat.of (InfinityChart318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i))
    change IsIntegrallyClosed Γ(Target i,(WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)).opensRange)
    infer_instance
lemma chart_cover (i:Fin 4) (x:Target i):∃b:Bool,x∈chartOpen i b:=by
  rcases WeierstrassGluing318.charts_cover (publishedA i) (publishedB i) x with h|h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩
lemma hasBasis (i:Fin 4):NormalAffineBasis318.HasBasis (Target i):=
  NormalAffineBasis318.of_cover (Target i) (chartOpen i) (chart_cover i) (chart_affine i) (chart_normal i)
/-- Finite dimension uses the actual original generic-stalk pullback. -/
lemma generic_finite (i:Fin 4):
    letI:=AffineDominantNorm318.fieldAlgebra (completedMap i)
    FiniteDimensional (Target i).functionField Model.functionField:=by
  letI:=AffineDominantNorm318.fieldAlgebra (completedMap i)
  apply Module.finite_of_finrank_pos
  rw [CompletedCharacterDegree318.actual_generic_degree_eight]
  norm_num
end CompletedCharacterTraceBasis318
