module
public import ActualOriginalCoordinateIndex318
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Constructions
public section
noncomputable section
namespace ActualOriginalTorusPeriodization318
open QuadricCRTAssembly318 ActualOriginalCoordinateIndex318
open ActualOriginalIntegerTiling318 ActualOriginalContinuousPeriodization318
open Topology
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def torusQuotient (x : Index → ℝ) : UnitAddTorus Index := fun i => (x i : UnitAddCircle)

lemma actual_torus_quotient_open : IsOpenQuotientMap torusQuotient := by
  change IsOpenQuotientMap (Pi.map (fun _ : Index => fun x : ℝ => (x : UnitAddCircle)))
  apply IsOpenQuotientMap.piMap
  intro i
  exact QuotientAddGroup.isOpenQuotientMap_mk

lemma actual_scalar_quotient_fiber (x y : ℝ) (h : (x : UnitAddCircle)=(y : UnitAddCircle)) :
    ∃ n : ℤ, x=(n : ℝ)+y := by
  have hz : ((x-y : ℝ) : UnitAddCircle)=0 := by rw [AddCircle.coe_sub,h,sub_self]
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp hz
  refine ⟨n,?_⟩
  simp only [zsmul_eq_mul,mul_one] at hn
  linarith

lemma actual_index_periodic (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (z : Index → ℤ) (x : Index → ℝ) :
    periodization f (coordinateEquiv ℝ (fun i => (z i : ℝ)+x i)) =
      periodization f (coordinateEquiv ℝ x) := by
  change periodization f (coordinateEquiv ℝ ((fun i => (z i : ℝ))+x)) = _
  rw [actual_coordinate_index_add,actual_coordinate_index_integer]
  exact actual_periodization_periodic f hf (coordinateEquiv ℤ z) (coordinateEquiv ℝ x)

/-- Equality of torus images gives an ACTUAL original integer
translation, so the produced periodization is constant on every fiber. -/
lemma actual_periodization_on_fibers (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (x y : Index → ℝ) (h : torusQuotient x=torusQuotient y) :
    periodization f (coordinateEquiv ℝ x)=periodization f (coordinateEquiv ℝ y) := by
  have hh (i : Index) : ∃ n : ℤ, x i=(n : ℝ)+y i :=
    actual_scalar_quotient_fiber (x i) (y i) (congrFun h i)
  choose z hz using hh
  have he : x=(fun i => (z i : ℝ)+y i) := funext hz
  rw [he]
  exact actual_index_periodic f hf z y

@[expose] def torusValue (f : C(Coordinates ℝ,ℂ)) (t : UnitAddTorus Index) : ℂ :=
  periodization f (coordinateEquiv ℝ (Function.surjInv actual_torus_quotient_open.surjective t))

lemma actual_torus_value_pullback (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (x : Index → ℝ) : torusValue f (torusQuotient x)=periodization f (coordinateEquiv ℝ x) := by
  unfold torusValue
  apply actual_periodization_on_fibers f hf
  exact Function.surjInv_eq actual_torus_quotient_open.surjective (torusQuotient x)

lemma actual_torus_value_continuous (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f) :
    Continuous (torusValue f) := by
  apply actual_torus_quotient_open.isQuotientMap.continuous_iff.mpr
  change Continuous (fun x : Index → ℝ => torusValue f (torusQuotient x))
  have he : (fun x : Index → ℝ => torusValue f (torusQuotient x)) =
      fun x => periodization f (coordinateEquiv ℝ x) := funext (actual_torus_value_pullback f hf)
  rw [he]
  exact (periodization f).continuous.comp (actual_coordinate_index_continuous ℝ)

/-- The same original periodization now genuinely descends to a
continuous function on the full five-dimensional unit torus. Its continuity
is proved through the open quotient, not through a discontinuous choice
of fundamental-domain representatives. -/
@[expose] def torusPeriodization (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f) :
    C(UnitAddTorus Index,ℂ) := ⟨torusValue f,actual_torus_value_continuous f hf⟩

lemma actual_torus_periodization_pullback (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f)
    (x : Index → ℝ) : torusPeriodization f hf (torusQuotient x)=periodization f (coordinateEquiv ℝ x) :=
  actual_torus_value_pullback f hf x

lemma actual_torus_periodization_zero (f : C(Coordinates ℝ,ℂ)) (hf : HasCompactSupport f) :
    torusPeriodization f hf 0 = ∑' z : Coordinates ℤ, f (integerEmbed z) := by
  have hz : torusQuotient 0=0 := by ext i; simp [torusQuotient]
  rw [←hz,actual_torus_periodization_pullback,actual_coordinate_index_zero,actual_periodization_apply f hf]
  simp only [add_zero]

end ActualOriginalTorusPeriodization318
