module
public import OddInfinityWholeModelMap318
public import NormalizedGenericPointExtension318
public section
noncomputable section
namespace SmoothInfinityModelPoint318
open Polynomial OddInfinityWholeModelMap318
variable (V : Type*) [CommRing V] (rho : V) (u : Fin 4 → Vˣ) (d a : Fin 4 → V)
  (ha : a 0=0) (hd : ∀ i,d i=(u i:V)*rho)
  (Z : V) (r : Fin 3 → Vˣ)
  (hr : ∀ j,(r j:V)^2=Polynomial.eval Z (OddInfinitySmoothChart318.coefficient V rho u a j))
local notation "Q" => OddInfinitySmoothChart318.coefficient V rho u a
local notation "C" => OddInfinitySmoothChart318.ModelRing V rho u a
local notation "e" => ThreePolynomialEtaleChart318.point V Q Z r hr
@[expose] def reciprocal : V := Polynomial.eval Z (OddInfinitySmoothChart318.reciprocal V rho u)
@[expose] def modelPoint : DVRNormalizedInfinityOrder318.Order V d a →+* V :=
  e.comp (sourceMap V rho u d a ha hd)
lemma point_s : e (s V rho u a)=reciprocal V rho u Z :=
  ThreePolynomialEtaleChart318.point_polynomial _ _ _ _ _ _
lemma point_scalarMap : e.comp (scalarMap V rho u a)=Polynomial.evalRingHom (reciprocal V rho u Z) := by
  apply Polynomial.ringHom_ext
  · intro v
    simp only [RingHom.comp_apply,scalarMap,coe_eval₂RingHom,eval₂_C,
      ThreePolynomialEtaleChart318.point_scalar,Polynomial.evalRingHom_apply,eval_C]
  · simp only [RingHom.comp_apply,scalarMap,coe_eval₂RingHom,eval₂_X,
      Polynomial.evalRingHom_apply,eval_X]
    exact point_s V rho u a Z r hr
lemma modelPoint_polynomial (p : V[X]) : modelPoint V rho u d a ha hd Z r hr
    (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V d a) p)=
      Polynomial.eval (reciprocal V rho u Z) p := by
  change e (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_polynomial]
  exact RingHom.congr_fun (point_scalarMap V rho u a Z r hr) p
lemma modelPoint_zero : modelPoint V rho u d a ha hd Z r hr
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) 0)=rho*Z := by
  change e (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_root]
  change e (algebraMap V C rho*z V rho u a)=_
  rw [map_mul,ThreePolynomialEtaleChart318.point_scalar]
  exact congrArg (rho*·) (ThreePolynomialEtaleChart318.point_coordinate V Q Z r hr)
lemma modelPoint_succ (j : Fin 3) : modelPoint V rho u d a ha hd Z r hr
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) j.succ)=
      rho*Z*(r j:V) := by
  change e (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_root]
  change e (algebraMap V C rho*z V rho u a*ratio V rho u a j)=_
  rw [map_mul,map_mul,ThreePolynomialEtaleChart318.point_scalar]
  change rho*e (ThreePolynomialEtaleChart318.coordinate V Q)*
    e (ThreeRootCoordinates318.generator _ j)=_
  rw [ThreePolynomialEtaleChart318.point_coordinate,ThreePolynomialEtaleChart318.point_root]
end SmoothInfinityModelPoint318
