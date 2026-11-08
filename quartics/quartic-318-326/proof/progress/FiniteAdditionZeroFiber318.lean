module
public import FiniteAdditionZero318
public section
noncomputable section
namespace FiniteAdditionZeroFiber318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
@[expose] def fiber : Scheme :=
  pullback (FiniteAdditionGluing318.addition A B hD) (WeierstrassGluing318.infinity A B)
@[expose] def toFiber : ShortAffineScheme318.scheme A B ⟶ fiber A B hD :=
  pullback.lift (FiniteInverseScheme318.antiDiagonal A B) (ShortAffineScheme318.structureMap A B)
    (FiniteInverseScheme318.antiDiagonal_addition A B hD)
@[expose] def fromFiber : fiber A B hD ⟶ ShortAffineScheme318.scheme A B :=
  pullback.fst _ _ ≫ pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)
@[reassoc] lemma toFiber_fst : toFiber A B hD ≫ pullback.fst _ _=FiniteInverseScheme318.antiDiagonal A B := by
  simp only [toFiber,pullback.lift_fst]
@[reassoc] lemma toFiber_snd : toFiber A B hD ≫ pullback.snd _ _=ShortAffineScheme318.structureMap A B := by
  simp only [toFiber,pullback.lift_snd]
@[reassoc] lemma fromFiber_base : fromFiber A B hD ≫ ShortAffineScheme318.structureMap A B=
    pullback.snd (FiniteAdditionGluing318.addition A B hD) (WeierstrassGluing318.infinity A B) := by
  have h:=congrArg (fun k=>k ≫ WeierstrassGluing318.structureMap A B)
    (pullback.condition (f:=FiniteAdditionGluing318.addition A B hD) (g:=WeierstrassGluing318.infinity A B))
  simpa only [fromFiber,Category.assoc,FiniteAdditionGluing318.addition_over_base,
    WeierstrassGluing318.infinity_section,Category.comp_id] using h

lemma fromFiber_antiDiagonal : fromFiber A B hD ≫ FiniteInverseScheme318.antiDiagonal A B=
    pullback.fst (FiniteAdditionGluing318.addition A B hD) (WeierstrassGluing318.infinity A B) := by
  apply Eq.symm
  apply (FiniteAdditionZero318.zero_iff_antiDiagonal A B hD _).mp
  rw [pullback.condition]
  exact (fromFiber_base_assoc A B hD (WeierstrassGluing318.infinity A B)).symm

/-- The actual finite-input addition zero-fiber is exactly the actual
anti-diagonal. Both inverse witnesses are explicit Scheme morphisms. -/
@[expose] def iso : ShortAffineScheme318.scheme A B ≅ fiber A B hD where
  hom := toFiber A B hD
  inv := fromFiber A B hD
  hom_inv_id := by
    simp only [fromFiber,←Category.assoc,toFiber_fst,FiniteInverseScheme318.antiDiagonal_fst]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,toFiber_fst,fromFiber_antiDiagonal,Category.id_comp]
    · simp only [Category.assoc,toFiber_snd,fromFiber_base,Category.id_comp]
end FiniteAdditionZeroFiber318
