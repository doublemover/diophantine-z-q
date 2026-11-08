module
public import ThreeTorsionOpenUniversal318
public import ThreeTorsionClosed318
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public section
noncomputable section
namespace ThreeTorsionRingCoequalizer318
open CategoryTheory CategoryTheory.Limits NonverticalDoubling318 ThreeTorsionAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma quotient_surjective : Function.Surjective (toTorsion A B hD):=by
  intro z
  obtain ⟨x,rfl⟩:=ThreeTorsionClosed318.coordinateMap_surjective A B hD z
  exact ⟨curveMap A B x,congrArg (fun f:Curve A B→ₐ[R]Ring A B hD=>f x)
    (toTorsion_curveMap A B hD)⟩

/-- The universal property also holds for arbitrary ring homomorphisms:
the test ring receives its base algebra structure through the given map. -/
lemma ring_existsUnique {S:Type} [CommRing S] (k:OpenRing A B→+*S)
    (hk:k.comp (double A B).toRingHom=k.comp (negative A B).toRingHom) :
    ∃! ψ:Ring A B hD→+*S,ψ.comp (toTorsion A B hD).toRingHom=k:=by
  letI:Algebra R S:=(k.comp (algebraMap R (OpenRing A B))).toAlgebra
  let kA:OpenRing A B→ₐ[R]S:={k with commutes':=fun _=>rfl}
  have hkA:kA.comp (double A B)=kA.comp (negative A B):=by
    apply AlgHom.toRingHom_injective
    exact hk
  obtain ⟨ψ,hψ,_⟩:=ThreeTorsionOpenUniversal318.existsUnique A B hD kA hkA
  have hψr:ψ.toRingHom.comp (toTorsion A B hD).toRingHom=k:=
    congrArg AlgHom.toRingHom hψ
  refine ⟨ψ.toRingHom,hψr,?_⟩
  intro χ hχ
  apply RingHom.ext
  intro z
  obtain ⟨y,rfl⟩:=quotient_surjective A B hD z
  exact congrArg (fun f:OpenRing A B→+*S=>f y) (hχ.trans hψr.symm)

abbrev curveObject:=CommRingCat.of (Curve A B)
abbrev openObject:=CommRingCat.of (OpenRing A B)
abbrev torsionObject:=CommRingCat.of (Ring A B hD)
@[expose] def doubling : curveObject A B⟶openObject A B:=CommRingCat.ofHom (double A B).toRingHom
@[expose] def negation : curveObject A B⟶openObject A B:=CommRingCat.ofHom (negative A B).toRingHom
@[expose] def quotient : openObject A B⟶torsionObject A B hD:=CommRingCat.ofHom (toTorsion A B hD).toRingHom
lemma condition : doubling A B≫quotient A B hD=negation A B≫quotient A B hD:=by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (NonverticalDoubling318.condition A B hD)
@[expose] def cofork : Cofork (doubling A B) (negation A B):=
  Cofork.ofπ (quotient A B hD) (condition A B hD)

/-- The actual localized coordinate quotient is a categorical coequalizer
in all commutative rings, not only a field-valued universal property. -/
@[expose] def isColimit : IsColimit (cofork A B hD):=by
  apply Cofork.IsColimit.ofExistsUnique
  intro s
  have hk:s.π.hom.comp (double A B).toRingHom=s.π.hom.comp (negative A B).toRingHom:=
    congrArg CommRingCat.Hom.hom s.condition
  obtain ⟨ψ,hψ,hunique⟩:=ring_existsUnique A B hD s.π.hom hk
  refine ⟨CommRingCat.ofHom ψ,CommRingCat.hom_ext hψ,?_⟩
  intro χ hχ
  apply CommRingCat.hom_ext
  exact hunique χ.hom (congrArg CommRingCat.Hom.hom hχ)
end ThreeTorsionRingCoequalizer318
