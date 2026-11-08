module
public import FifthSignAffine318
public import FifthCompletedGlobal318
public import CompletedCharacterProper318
public import SchematicEqualityExtension318
public import GluedNegation318
public section
noncomputable section
namespace FifthSignGlobal318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 650000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def affineMap:ContactKummerCover318.cover units⟶ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom FifthSourceOverlap318.shortMap.toRingHom)
@[reassoc] theorem on_open:ContactProjectiveModel318.sourceOpen units≫FifthCompletedGlobal318.map=
    affineMap≫WeierstrassGluing318.finiteChart A B:=by
  rw [←ContactOverlapMaps318.source_square,Category.assoc,FifthCompletedGlobal318.on_finite,
    FifthSourceOverlap318.finite_restriction]
  rfl
lemma open_positive (b:Fin 4→Bool) (h:FifthSignAffine318.sign b=1):
    ContactGlobalSigns318.openMap units b≫affineMap=affineMap:=by
  unfold ContactGlobalSigns318.openMap affineMap
  rw [←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (FifthSignAffine318.positive b h))
lemma open_negative (b:Fin 4→Bool) (h:FifthSignAffine318.sign b=-1):
    ContactGlobalSigns318.openMap units b≫affineMap=affineMap≫GluedNegation318.finiteNeg A B:=by
  unfold ContactGlobalSigns318.openMap affineMap GluedNegation318.finiteNeg
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (FifthSignAffine318.negative b h))
local instance sourceIntegral:IsIntegral (ContactProjectiveModel318.model units):=
  (ContactGlobalProper318.proper_integral_extension units).2.1
local instance sourceOpenDominant:IsDominant (ContactProjectiveModel318.sourceOpen units):=
  ContactProjectiveModel318.sourceOpen_dense units
local instance sourceOpenDense:IsSchemeTheoreticallyDominant (ContactProjectiveModel318.sourceOpen units):=
  IsSchemeTheoreticallyDominant.of_isDominant (ContactProjectiveModel318.sourceOpen units)
lemma source_ext (f g:ContactGlobalSmooth318.Model units⟶WeierstrassGluing318.scheme A B)
    (hb:f≫WeierstrassGluing318.structureMap A B=g≫WeierstrassGluing318.structureMap A B)
    (ho:ContactProjectiveModel318.sourceOpen units≫f=ContactProjectiveModel318.sourceOpen units≫g):f=g:=by
  letI:=CubicClosedImmersion318.structure_separated A B
  exact SchematicEqualityExtension318.ext _ hb (ContactProjectiveModel318.sourceOpen units) ho
lemma signed_over_Q (b:Fin 4→Bool):
    (ContactGlobalSigns318.map units b≫FifthCompletedGlobal318.map)≫WeierstrassGluing318.structureMap A B=
      FifthCompletedGlobal318.map≫WeierstrassGluing318.structureMap A B:=by
  rw [Category.assoc,FifthCompletedGlobal318.over_Q]
  change ContactGlobalSigns318.map units b≫ContactProjectiveModel318.modelMap units≫ProjectiveJLine318.structureMap ℚ=_
  rw [←Category.assoc,ContactGlobalSigns318.over_line]
  rfl
/-- Every positive full-product sign fixes the whole actual fifth quotient map. -/
@[reassoc] theorem positive (b:Fin 4→Bool) (h:FifthSignAffine318.sign b=1):
    ContactGlobalSigns318.map units b≫FifthCompletedGlobal318.map=FifthCompletedGlobal318.map:=by
  apply source_ext _ _ (signed_over_Q b)
  rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,←Category.assoc,open_positive b h]
/-- Every negative full-product sign acts by actual completed elliptic negation,
including all finite branches and infinity points. -/
@[reassoc] theorem negative (b:Fin 4→Bool) (h:FifthSignAffine318.sign b=-1):
    ContactGlobalSigns318.map units b≫FifthCompletedGlobal318.map=
      FifthCompletedGlobal318.map≫GluedNegation318.negation A B:=by
  apply source_ext
  · simpa only [Category.assoc,GluedNegation318.negation_over_base] using signed_over_Q b
  · rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,←Category.assoc,open_negative b h,Category.assoc]
    rw [←Category.assoc (ContactProjectiveModel318.sourceOpen units) (FifthCompletedGlobal318.map),on_open]
    simp only [Category.assoc,GluedNegation318.finiteChart_negation]
@[expose] def targetAction (b:Fin 4→Bool):WeierstrassGluing318.scheme A B⟶WeierstrassGluing318.scheme A B:=by
  classical
  exact if FifthSignAffine318.sign b=-1 then GluedNegation318.negation A B else 𝟙 _
/-- The full Boolean source action, not only selected generator flips, has
the exact fifth-character quotient action. -/
@[reassoc] theorem equivariant (b:Fin 4→Bool):
    ContactGlobalSigns318.map units b≫FifthCompletedGlobal318.map=FifthCompletedGlobal318.map≫targetAction b:=by
  by_cases h:FifthSignAffine318.sign b=-1
  · rw [targetAction,if_pos h]
    exact negative b h
  · rw [targetAction,if_neg h,Category.comp_id]
    exact positive b ((FifthSignAffine318.sign_cases b).resolve_right h)
/-- Exact natural operation identity on every Scheme test, without reducing
tests or replacing the quotient by geometric labels. -/
theorem all_tests {T:Scheme} (f:T⟶ContactGlobalSmooth318.Model units) (b:Fin 4→Bool):
    (f≫ContactGlobalSigns318.map units b)≫FifthCompletedGlobal318.map=
      (f≫FifthCompletedGlobal318.map)≫targetAction b:=by
  rw [Category.assoc,equivariant,Category.assoc]
end FifthSignGlobal318
