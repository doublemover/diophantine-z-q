module
public import PELOriginalCharacterRegularInvariants318
public import PELOriginalCharacterAffineQuotient318
public section
noncomputable section
namespace PELOriginalCharacterAffineDescent318
open PELOriginalCommonContactBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalCharacterAffineImage318 PELOriginalCharacterInvariantRing318
open PELOriginalCharacterRegularInvariants318
variable {T:Type*} [CommRing T]

/-- Valuewise invariance under the actual whole finite root-sign maps.
This is the exact affine-target descent condition, not a generic condition. -/
def Invariant (i:Fin 4) (f:T→+*Source):Prop:=
  ∀x:T,∀g:Labels,g∈(character i).ker →
    FourRootCoordinateRingSigns318.finiteEnd branches (basis g) (f x)=f x

@[expose] def liftInvariant (i:Fin 4) (f:T→+*Source) (hf:Invariant i f):
    T→+*invariantSubring i where
  toFun x:=⟨f x,(member_iff_original_kernel i (f x)).mpr (hf x)⟩
  map_zero':=Subtype.ext f.map_zero
  map_one':=Subtype.ext f.map_one
  map_add' x y:=Subtype.ext (f.map_add x y)
  map_mul' x y:=Subtype.ext (f.map_mul x y)

/-- The descended map uses the SAME old ordered target ring. -/
@[expose] def descend (i:Fin 4) (f:T→+*Source) (hf:Invariant i f):T→+*Order i:=
  (coordinateEquiv i).symm.toRingHom.comp (liftInvariant i f hf)

lemma factor (i:Fin 4) (f:T→+*Source) (hf:Invariant i f):
    (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom.comp
      (descend i f hf)=f:=by
  ext x
  have h:=congrArg Subtype.val ((coordinateEquiv i).apply_symm_apply (liftInvariant i f hf x))
  exact h

lemma unique (i:Fin 4) (f:T→+*Source) (hf:Invariant i f) (k:T→+*Order i)
    (hk:(PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom.comp k=f):
    k=descend i f hf:=by
  ext x
  apply PELOriginalOrderedCharacterSchemeMaps318.injective i
  exact (RingHom.congr_fun hk x).trans (RingHom.congr_fun (factor i f hf) x).symm

/-- Full affine ring descent for every test ring and every invariant map.
Via Spec this is the affine-target universal property of this chart;
no global arbitrary-scheme-target descent is asserted here. -/
theorem existsUnique_factor (i:Fin 4) (f:T→+*Source) (hf:Invariant i f):
    ∃!k:T→+*Order i,
      (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom.comp k=f:=
  ⟨descend i f hf,factor i f hf,fun k hk=>unique i f hf k hk⟩
end PELOriginalCharacterAffineDescent318
