module
public import OddInfinityIntegralCoordinates318
public import ThreePolynomialEtaleChart318
public section
noncomputable section
namespace OddInfinitySmoothChart318
open Polynomial ThreePolynomialEtaleChart318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable (V : Type*) [CommRing V] (pi : V) (u : Fin 4 → Vˣ) (a : Fin 4 → V)
@[expose] def reciprocal : V[X] := C (pi*(↑(u 0)⁻¹ : V))*X^2
@[expose] def coefficient (j : Fin 3) : V[X] :=
  C ((u j.succ : V)*(↑(u 0)⁻¹ : V))*(1-C (a j.succ)*reciprocal V pi u)
abbrev ModelRing := Chart V (coefficient V pi u a)
@[expose] def reciprocalValue : ModelRing V pi u a :=
  polynomial V (coefficient V pi u a) (reciprocal V pi u)

variable [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]
  (hp : Irreducible pi) (ha : a 0=0) (w : V) (hw : w≠0) (hwn : ¬IsUnit w)
  (z : Fin 4 → V) (hz : ∀ i,(z i)^2=(u i : V)*pi*w*(1-a i*w))

/-- The common-odd reciprocal case yields a true smooth infinity chart
at every odd place, even when contact differences are nonunits. The
same distinguished signed root and all three signed ratios are retained. -/
theorem exists_smooth_center (h2 : IsUnit (2 : V)) :
    ∃ (Z : V) (r : Fin 3 → Vˣ)
      (hr : ∀ j,(r j : V)^2=Polynomial.eval Z (coefficient V pi u a j)),
      Z≠0 ∧ z 0=pi*Z ∧
      (∀ j : Fin 3,z j.succ=pi*Z*(r j : V)) ∧
      Algebra.Smooth V (ModelRing V pi u a) ∧
      point V (coefficient V pi u a) Z r hr (reciprocalValue V pi u a)=w := by
  obtain ⟨Z,r,hZ,hz0,hwZ,hzr,hr2⟩ :=
    OddInfinityIntegralCoordinates318.exists_coordinates V K pi hp u a ha w hw hwn z hz
  have hr (j : Fin 3) : (r j : V)^2=Polynomial.eval Z (coefficient V pi u a j) := by
    simp only [coefficient,reciprocal,eval_mul,eval_C,eval_sub,eval_one,eval_pow,eval_X]
    rw [←hwZ]
    exact hr2 j
  refine ⟨Z,r,hr,hZ,hz0,hzr,ThreePolynomialEtaleChart318.smooth V _ h2,?_⟩
  rw [reciprocalValue,point_polynomial]
  simpa only [reciprocal,eval_mul,eval_C,eval_pow,eval_X] using hwZ.symm

/-- Exact differential of the ORIGINAL reciprocal coordinate in the
actual Kaehler module. This retains its uniformizer square-coordinate
factor, rather than inferring differential regularity from point values. -/
theorem frame_reciprocal (h2 : IsUnit (2 : V)) :
    frame V (coefficient V pi u a) h2
      (KaehlerDifferential.D V _ (reciprocalValue V pi u a)) =
    polynomial V (coefficient V pi u a) (reciprocal V pi u).derivative :=
  frame_polynomial V _ h2 _
end OddInfinitySmoothChart318
