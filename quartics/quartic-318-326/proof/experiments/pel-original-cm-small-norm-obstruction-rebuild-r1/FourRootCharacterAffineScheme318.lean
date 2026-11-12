module
public import FourRootCharacterWholeAffineMap318
public import FourRootSchemeSignAction318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace FourRootCharacterAffineScheme318
open AlgebraicGeometry CategoryTheory
open FourRootAffineTensorPresentation318 FourRootActualGenericField318 FourRootActualFractionField318
open FourRootCharacterPolynomialOrder318 FourRootCharacterWholeAffineMap318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (s:Finset (Fin 4)) (hs:s.Nonempty)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance polyTower:IsScalarTower ℂ P (A b):=
  IsScalarTower.of_algebraMap_eq (fun c=>(Polynomial.aeval_C _ c).symm)

@[expose] def coordinateMap:Order b s→ₐ[ℂ]A b:=(toSource b hb s hs).restrictScalars ℂ
abbrev characterScheme:Scheme:=Spec (CommRingCat.of (Order b s))
@[expose] def morphism:FourRootGluedScheme318.finiteScheme b⟶characterScheme b s:=
  Spec.map (CommRingCat.ofHom (coordinateMap b hb s hs).toRingHom)
@[expose] def projection:characterScheme b s⟶Spec (CommRingCat.of P):=
  Spec.map (CommRingCat.ofHom (algebraMap P (Order b s)))
@[expose] def structureMap:characterScheme b s⟶Spec (CommRingCat.of ℂ):=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Order b s)))

theorem finite:IsFinite (morphism b hb s hs):=
  (IsFinite.SpecMap_iff _).mpr (FourRootCharacterWholeAffineMap318.finite b hb s hs)

/-- The genuine finite character morphism commutes with the ORIGINAL
unshifted polynomial coordinate on the entire finite source scheme. -/
theorem base_square:morphism b hb s hs≫projection b s=
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toRingHom):=by
  rw [morphism,projection,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (toSource b hb s hs).comp_algebraMap

theorem over_complex:morphism b hb s hs≫structureMap b s=
    FourRootGluedScheme318.finiteBase b:=by
  rw [morphism,structureMap,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (coordinateMap b hb s hs).comp_algebraMap

/-- Every actual complex point, including finite ramification points,
uses the same root monomial. There is no generic nonvanishing premise. -/
lemma point_root (f:A b→ₐ[ℂ]ℂ):
    (f.comp (coordinateMap b hb s hs))
      (AdjoinRoot.root (QuadraticPresentation318.polynomial
        (FourRootCharacterPolynomialOrder318.radicand b s)))=
      ∏k∈s,f (FourRootAffineCoordinateRing318.coordinate b (some k)):=by
  change f (toSource b hb s hs _)=_
  rw [on_root]
  simp only [FourRootActualCharacterFields318.monomial,map_prod]

/-- The entire coordinate map is fixed by precisely the previously
specified character kernel; invariance is proved in the whole rings. -/
lemma invariant (g:FourBinaryCharacters318.Group)
    (hg:∏k∈s,FourBinaryCharacters318.coordinate (F:=ℂ) k g=1):
    (FourRootCoordinateRingSigns318.finiteEnd b g).comp (coordinateMap b hb s hs)=
      coordinateMap b hb s hs:=by
  apply AlgHom.ext
  intro x
  apply affineEmbedding_injective b
  change affineEmbedding b (FourRootCoordinateRingSigns318.finiteEnd b g
    (toSource b hb s hs x))=affineEmbedding b (toSource b hb s hs x)
  simp only [FourRootActualGenericSigns318.affineEmbedding_equivariant,embedding_square]
  have hfix:=
    (FourRootActualCharacterFields318.original_sign_mem_fixing_iff b hb s hs g).mpr hg
  exact (IntermediateField.mem_fixingSubgroup_iff.mp hfix)
    (embedding b hb s hs x) (embedding b hb s hs x).property

/-- Conversely, fixing the entire character coordinate map forces the
same character sign to be one. The literal nonzero generic root detects it. -/
lemma invariant_iff (g:FourBinaryCharacters318.Group):
    (FourRootCoordinateRingSigns318.finiteEnd b g).comp (coordinateMap b hb s hs)=
      coordinateMap b hb s hs ↔
      ∏k∈s,FourBinaryCharacters318.coordinate (F:=ℂ) k g=1:=by
  constructor
  · intro h
    have hm:=AlgHom.congr_fun h
      (AdjoinRoot.root (QuadraticPresentation318.polynomial
        (FourRootCharacterPolynomialOrder318.radicand b s)))
    change FourRootCoordinateRingSigns318.finiteEnd b g (toSource b hb s hs _)=
      toSource b hb s hs _ at hm
    simp only [on_root] at hm
    have he:=congrArg (affineEmbedding b) hm
    simp only [FourRootActualGenericSigns318.affineEmbedding_equivariant,
      FourRootActualCharacterFields318.affine_monomial] at he
    have hc:CharacterRoot318.sign (F:=K) s (FourBinaryCharacters318.signPattern g)=1:=
      (CharacterRoot318.sign_fixes_iff (parameter b) s _).mp he
    rw [FourRootActualCharacterFields318.actual_sign] at hc
    apply (algebraMap ℂ K).injective
    simpa only [map_one] using hc
  · exact invariant b hb s hs g

/-- This is an equality of genuine scheme morphisms, not only agreement
on complex points or on the function field. -/
theorem deck_square (g:FourBinaryCharacters318.Group)
    (hg:∏k∈s,FourBinaryCharacters318.coordinate (F:=ℂ) k g=1):
    FourRootSchemeSignAction318.finiteMap b g≫morphism b hb s hs=morphism b hb s hs:=by
  change Spec.map (CommRingCat.ofHom (FourRootCoordinateRingSigns318.finiteEnd b g).toRingHom)≫
    Spec.map (CommRingCat.ofHom (coordinateMap b hb s hs).toRingHom)=_
  rw [←Spec.map_comp]
  exact congrArg (fun f:Order b s→ₐ[ℂ]A b=>Spec.map (CommRingCat.ofHom f.toRingHom))
    (invariant b hb s hs g hg)
end FourRootCharacterAffineScheme318
