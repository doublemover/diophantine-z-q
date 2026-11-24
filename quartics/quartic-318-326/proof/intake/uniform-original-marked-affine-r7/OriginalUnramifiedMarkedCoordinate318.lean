module
public import Mathlib.RingTheory.Unramified.Basic
public section
noncomputable section
namespace OriginalUnramifiedMarkedCoordinate318
open Polynomial
variable {V E:Type*} [CommRing V] [Field E] [Algebra V E]

/-- Genuine nonvanishing of the ordinary horizontal dT AFTER residue-field
evaluation (as opposed to nonvanishing only in a curve function field).
The source frame is the pullback primitive dualizing generator, which
agrees here with ordinary Kähler differentials. A ramified chart t=s² at
s=0 cannot supply formal unramifiedness of this particular coordinate. -/
theorem nonzero (e:KaehlerDifferential ℤ V≃ₗ[V]V) (T:V)
    (unr:letI := ((aeval T : ℤ[X]→ₐ[ℤ]V).toRingHom).toAlgebra
      Algebra.FormallyUnramified ℤ[X] V) :
    algebraMap V E (e (KaehlerDifferential.D ℤ V T))≠0 := by
  intro hz
  let : Algebra ℤ[X] V := ((aeval T:ℤ[X]→ₐ[ℤ]V).toRingHom).toAlgebra
  let : Algebra ℤ[X] E := ((algebraMap V E).comp (algebraMap ℤ[X] V)).toAlgebra
  let : IsScalarTower ℤ[X] V E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.FormallyUnramified ℤ[X] V := unr
  let f : KaehlerDifferential ℤ V →ₗ[V]E :=
    (Algebra.linearMap V E).comp e.toLinearMap
  let D : Derivation ℤ V E := f.compDer (KaehlerDifferential.D ℤ V)
  have hT:D T=0 := hz
  have kills (p:ℤ[X]):D (algebraMap ℤ[X] V p)=0 := by
    change D (aeval T p)=0
    rw [D.map_aeval,hT,smul_zero]
  let D' : Derivation ℤ[X] V E := {
    toFun:=D,map_add':=D.map_add,map_smul':=fun p x => by
      rw [Algebra.smul_def,D.leibniz,kills,smul_zero,add_zero,RingHom.id_apply]
      exact algebraMap_smul V p (D x)
    map_one_eq_zero':=D.map_one_eq_zero,leibniz':=D.leibniz }
  have allz (z:V):D z=0 := by
    change D' z=0
    rw [←D'.liftKaehlerDifferential_comp_D]
    rw [Subsingleton.elim (KaehlerDifferential.D ℤ[X] V z) 0,map_zero]
  have ef : f=(0:KaehlerDifferential ℤ V→ₗ[V]E) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    exact allz z
  have endeq := LinearMap.congr_fun ef (e.symm 1)
  change algebraMap V E (e (e.symm 1))=0 at endeq
  rw [e.apply_symm_apply,map_one] at endeq
  exact one_ne_zero endeq
end OriginalUnramifiedMarkedCoordinate318
