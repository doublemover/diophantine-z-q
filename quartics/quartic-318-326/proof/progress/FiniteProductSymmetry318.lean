module
public import FiniteAdditionCommutative318
public section
noncomputable section
namespace FiniteProductSymmetry318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

/-- The tensor swap is the actual symmetry of the relative finite-input product. -/
theorem transport_swap (A B:R) :
    Spec.map (CommRingCat.ofHom (FinitePairSwap318.swap A B).toRingHom) ≫
      (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv=
    (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv ≫
      (pullbackSymmetry (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)).hom := by
  dsimp only [ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
  apply pullback.hom_ext
  · rw [Category.assoc,pullbackSpecIso_inv_fst,Category.assoc,pullbackSymmetry_hom_comp_fst,
      pullbackSpecIso_inv_snd,←Spec.map_comp]
    congr 1
  · rw [Category.assoc,pullbackSpecIso_inv_snd,Category.assoc,pullbackSymmetry_hom_comp_snd,
      pullbackSpecIso_inv_fst,←Spec.map_comp]
    congr 1

/-- Commutativity as an equality of Scheme morphisms on the entire actual
relative finite-input fiber product, rather than only on field points. -/
theorem addition_commutative (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (pullbackSymmetry (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)).hom ≫
      FiniteAdditionGluing318.addition A B hD=FiniteAdditionGluing318.addition A B hD := by
  apply (cancel_epi (pullbackSpecIso R (ShortAffineJacobian318.Ring A B)
    (ShortAffineJacobian318.Ring A B)).inv).mp
  have hi : (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv ≫
      FiniteAdditionGluing318.addition A B hD=FiniteAdditionGluing318.coordinateAddition A B hD := by
    rw [FiniteAdditionGluing318.addition,Iso.inv_hom_id_assoc]
  rw [←Category.assoc,←transport_swap,Category.assoc,hi]
  exact FiniteAdditionCommutative318.coordinate_commutative A B hD
end FiniteProductSymmetry318
