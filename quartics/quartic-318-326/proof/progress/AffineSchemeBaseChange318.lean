module
public import AffineBaseChange318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace AffineSchemeBaseChange318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ShortAffineJacobian318 AffineBaseChange318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual affine Scheme pullback is the literal changed-coefficient Scheme. -/
@[expose] def schemeIso (A B:R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (ShortAffineScheme318.structureMap A B) ≅
      ShortAffineScheme318.scheme (algebraMap R S A) (algebraMap R S B) :=
  pullbackSpecIso R S (Ring A B) ≪≫
    Scheme.Spec.mapIso (baseChangeEquiv (S:=S) A B).toRingEquiv.toCommRingCatIso.symm.op

/-- The inverse identification respects the actual base structure morphism. -/
theorem schemeIso_inv_base (A B:R) :
    (schemeIso (S:=S) A B).inv ≫ pullback.fst _ _ =
      ShortAffineScheme318.structureMap (algebraMap R S A) (algebraMap R S B) := by
  change Spec.map (CommRingCat.ofHom (forward (S:=S) A B).toRingHom) ≫
    (pullbackSpecIso R S (Ring A B)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst']
  rw [←Spec.map_comp]
  congr 1
  ext s
  exact (forward A B).commutes s

/-- The forward identification respects the actual base structure morphism. -/
theorem schemeIso_hom_base (A B:R) :
    (schemeIso (S:=S) A B).hom ≫
      ShortAffineScheme318.structureMap (algebraMap R S A) (algebraMap R S B)=
      pullback.fst _ _ := by
  rw [←schemeIso_inv_base A B, Iso.hom_inv_id_assoc]

/-- Actual base-changed literal family, not an assumed coefficient-model identification. -/
@[expose] def literalFiberIso (N:ℕ) (T:Type) [CommRing T]
    [Algebra (OpenJModel318.Base N) T] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) T)))
      (OpenJAffineScheme318.structureMap N) ≅
    ShortAffineScheme318.scheme
      (algebraMap (OpenJModel318.Base N) T (OpenJAffineScheme318.A N))
      (algebraMap (OpenJModel318.Base N) T (OpenJAffineScheme318.B N)) :=
  schemeIso (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end AffineSchemeBaseChange318
