module
public import IntegralZoomPointCoefficient318
public import IntegralContactZoomBaseChange318
public section
noncomputable section
namespace IntegralZoomFiberNaturality318
open IntegralContactZoomCoefficients318 IntegralZoomPointCoefficient318 IntegralContactZoomBaseChange318
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (d a : Fin 4 → R) (t : R) (m : Mode)

theorem commonValue_map : algebraMap R S (commonValue t d a m)=
    commonValue (algebraMap R S t) (mapped (S:=S) d) (mapped (S:=S) a) m := by
  cases m <;> simp only [commonValue,IntegralQuadraticPointZoom318.product,
    IntegralQuadraticPointZoom318.value,alpha,gamma,mapped,map_mul,map_prod,map_ofNat,
    map_add,map_pow,map_zero,map_neg]

theorem fiber0_map : algebraMap R S (fiber0 t d a m)=
    fiber0 (algebraMap R S t) (mapped (S:=S) d) (mapped (S:=S) a) m := by
  cases m with
  | finite => rw [finite_fiber0,finite_fiber0,commonValue_map]
  | reciprocal => rw [reciprocal_fiber0,reciprocal_fiber0,map_mul,map_pow,commonValue_map]

theorem fiber1_map : algebraMap R S (fiber1 t d a m)=
    fiber1 (algebraMap R S t) (mapped (S:=S) d) (mapped (S:=S) a) m := by
  cases m with
  | finite => rw [finite_fiber1,finite_fiber1,map_mul,fiber0_map]
  | reciprocal => rw [reciprocal_fiber1,reciprocal_fiber1,map_mul,map_pow,commonValue_map]
end IntegralZoomFiberNaturality318
