module
public import FiniteZeroScheme318
public import FiniteInverseScheme318
public section
noncomputable section
namespace FiniteAdditionZero318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteZeroScheme318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[reassoc] lemma iso_first (A B:R) :
    (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫ first A B=
      pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) := by
  apply (cancel_epi (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv).mp
  dsimp only [ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
  rw [Iso.inv_hom_id_assoc,pullbackSpecIso_inv_fst]
  rfl
@[reassoc] lemma iso_second (A B:R) :
    (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫ second A B=
      pullback.snd (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) := by
  apply (cancel_epi (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv).mp
  dsimp only [ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
  rw [Iso.inv_hom_id_assoc,pullbackSpecIso_inv_snd]
  rfl
lemma first_base (A B:R) : first A B ≫ ShortAffineScheme318.structureMap A B=
    Spec.algebraMap R (RelativeChordAlgebra318.PairRing A B) := by
  dsimp only [first,ShortAffineScheme318.structureMap,Spec.algebraMap]
  rw [←Spec.map_comp]
  congr 1
@[reassoc] lemma iso_base (A B:R) :
    (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫
      Spec.algebraMap R (RelativeChordAlgebra318.PairRing A B)=
      pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        ShortAffineScheme318.structureMap A B := by
  rw [←first_base,←Category.assoc,iso_first]

/-- Full finite-input zero-sum criterion as equality of Scheme morphisms.
This is proved directly over every commutative base, including nilpotents,
without any associativity or cancellation premise. -/
theorem zero_iff {X:Scheme.{u}} (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (x:X ⟶ RelativeChordScheme318.productScheme A B) :
    x ≫ FiniteAdditionGluing318.addition A B hD=
      x ≫ pullback.fst _ _ ≫ ShortAffineScheme318.structureMap A B ≫ WeierstrassGluing318.infinity A B ↔
    x ≫ pullback.snd _ _=x ≫ pullback.fst _ _ ≫ negation A B := by
  constructor
  · intro h
    have hh:=coordinate_zero A B hD
      (x ≫ (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom)
      (by simpa only [Category.assoc,FiniteAdditionGluing318.addition,iso_base_assoc] using h)
    simpa only [Category.assoc,iso_first_assoc,iso_second] using hh
  · intro h
    have hx:x=(x ≫ pullback.fst _ _) ≫ FiniteInverseScheme318.antiDiagonal A B := by
      apply pullback.hom_ext
      · simp only [Category.assoc,FiniteInverseScheme318.antiDiagonal_fst,Category.comp_id]
      · simpa only [Category.assoc,FiniteInverseScheme318.antiDiagonal_snd,negation] using h
    calc
      x ≫ FiniteAdditionGluing318.addition A B hD =
          ((x ≫ pullback.fst _ _) ≫ FiniteInverseScheme318.antiDiagonal A B) ≫
            FiniteAdditionGluing318.addition A B hD := congrArg (fun k=>k ≫ _) hx
      _ = x ≫ pullback.fst _ _ ≫ ShortAffineScheme318.structureMap A B ≫
            WeierstrassGluing318.infinity A B := by
        rw [Category.assoc,FiniteInverseScheme318.antiDiagonal_addition,Category.assoc]

/-- The exact factorization through the actual finite anti-diagonal. -/
theorem zero_iff_antiDiagonal {X:Scheme.{u}} (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (x:X ⟶ RelativeChordScheme318.productScheme A B) :
    x ≫ FiniteAdditionGluing318.addition A B hD=
      x ≫ pullback.fst _ _ ≫ ShortAffineScheme318.structureMap A B ≫ WeierstrassGluing318.infinity A B ↔
    x=(x ≫ pullback.fst _ _) ≫ FiniteInverseScheme318.antiDiagonal A B := by
  rw [zero_iff]
  constructor
  · intro h
    apply pullback.hom_ext
    · simp only [Category.assoc,FiniteInverseScheme318.antiDiagonal_fst,Category.comp_id]
    · simpa only [Category.assoc,FiniteInverseScheme318.antiDiagonal_snd,negation] using h
  · intro h
    have hh:=congrArg (fun k=>k ≫ pullback.snd (ShortAffineScheme318.structureMap A B)
      (ShortAffineScheme318.structureMap A B)) h
    simpa only [Category.assoc,FiniteInverseScheme318.antiDiagonal_snd,negation] using hh
end FiniteAdditionZero318
