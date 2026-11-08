module
public import CompletedNormalizationBirational318
public import NormalAffineOpen318
public import CompletedRationalNormal318
public section
noncomputable section
namespace CompletedNormalizationIso318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterNormalizationJoin318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance originalIntegral (i:Fin 4):IsIntegral (SourceCharacterGlobal318.Model i):=
  SourceCharacterGlobal318.model_integral i
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance comparisonIntegral (i:Fin 4):IsIntegralHom (comparison i):=comparison_integral i
local instance comparisonSurjective (i:Fin 4):Surjective (comparison i):=comparison_surjective i
local instance comparisonGenericIso (i:Fin 4):IsIso (DominantFunctionField318.map (comparison i)):=
  CompletedNormalizationBirational318.comparison_generic_isIso i

/-- The existing canonical comparison is an isomorphism, using normality
of both entire actual charts and the actual generic-stalk pullback. -/
theorem comparison_isIso (i:Fin 4):IsIso (comparison i):=by
  have hD:IsUnit (-16*(4*(publishedA i)^3+27*(publishedB i)^2)):=
    isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (published_nonsingular i))
  letI:=CompletedRationalNormal318.affine (publishedA i) (publishedB i) hD
  letI:=CompletedRationalNormal318.infinity (publishedA i) (publishedB i) hD
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P:=MorphismProperty.isomorphisms Scheme)
  intro p
  rcases WeierstrassGluing318.charts_cover (publishedA i) (publishedB i) p with h|h
  · let U:=(WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact NormalAffineOpen318.restrict_isIso (comparison i)
      (CommRingCat.of (ShortAffineJacobian318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
  · let U:=(WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)).opensRange
    have hp:p∈U:=h
    letI:Nonempty U:=⟨⟨p,hp⟩⟩
    refine ⟨U,hp,?_⟩
    exact NormalAffineOpen318.restrict_isIso (comparison i)
      (CommRingCat.of (InfinityChart318.Ring (publishedA i) (publishedB i)))
      (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i))

/-- The relative cubic normalization and the literal completed Weierstrass
model, compared by the already constructed canonical morphism. -/
@[expose] def iso (i:Fin 4):SourceCharacterGlobal318.Model i≅Target i:=by
  letI:=comparison_isIso i
  exact asIso (comparison i)
@[simp] theorem iso_hom (i:Fin 4):(iso i).hom=comparison i:=rfl
@[reassoc] theorem iso_on_cubic (i:Fin 4):
    (SourceCharacterGlobal318.coverMap i).toNormalization≫(iso i).hom=
      CubicCompletedAffine318.embedding i:=comparison_on_cubic i
@[reassoc] theorem iso_over_t (i:Fin 4):
    (iso i).hom≫CompletedCharacterFinite318.targetTMap i=
      (SourceCharacterGlobal318.coverMap i).fromNormalization:=comparison_over_line i
@[reassoc] theorem actual_source_join (i:Fin 4):
    SourceCharacterGlobal318.globalMap i≫(iso i).hom=CompletedCharacterGlobal318.completedMap i:=
  original_global_join i
end CompletedNormalizationIso318
