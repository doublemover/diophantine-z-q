module
public import SimpleQuadraticEtalePoint318
public section
noncomputable section
namespace SimpleQuadraticEtaleUniversal318
open Polynomial SimpleQuadraticEtalePoint318
set_option maxHeartbeats 1200000
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (q : R) (z : S) (hz : z^2+z=algebraMap R S q) (hd : IsUnit (2*z+1))
@[expose] def rootLift : RootRing q →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (equation q) (Algebra.ofId R S) z (by
    change Polynomial.aeval z (X^2+(X-C q))=0
    simp only [map_add,map_pow,aeval_X,map_sub,aeval_C]
    linear_combination hz)

theorem rootLift_derivative : rootLift q z hz (derivativeValue q)=2*z+1 := by
  rw [derivativeValue,rootLift,AdjoinRoot.liftAlgHom_mk]
  simp [equation]
@[expose] def liftRing : EtaleRing q →+* S :=
  IsLocalization.Away.lift (derivativeValue q) (by rw [←rootLift_derivative q z hz] at hd; exact hd)
theorem liftRing_base (r : RootRing q) :
    liftRing q z hz hd (algebraMap (RootRing q) (EtaleRing q) r)=rootLift q z hz r :=
  IsLocalization.Away.lift_eq _ _ _
@[expose] def lift : EtaleRing q →ₐ[R] S where
  __ := liftRing q z hz hd
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (RootRing q) (EtaleRing q),liftRing_base]
    exact (rootLift q z hz).commutes r

theorem lift_root : lift q z hz hd (root q)=z := by
  change liftRing q z hz hd (algebraMap (RootRing q) (EtaleRing q) (AdjoinRoot.root (equation q)))=z
  rw [liftRing_base]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem hom_ext (f g : EtaleRing q →ₐ[R] S) (h : f (root q)=g (root q)) : f=g := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (derivativeValue q))
  have he : f.comp (IsScalarTower.toAlgHom R (RootRing q) (EtaleRing q)) =
      g.comp (IsScalarTower.toAlgHom R (RootRing q) (EtaleRing q)) := by
    apply AdjoinRoot.algHom_ext
    exact h
  exact congrArg AlgHom.toRingHom he
end SimpleQuadraticEtaleUniversal318
