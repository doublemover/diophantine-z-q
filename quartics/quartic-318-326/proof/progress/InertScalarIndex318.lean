module
public import InertMembership318
public import InertScalarSource318
public section
namespace InertScalarIndex318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay
open CompressedOrientation318 ScalarSource318 InertLogHom318 InertMembership318
open ReciprocalDouble318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
variable (p:ℕ) [Fact p.Prime] (ns:¬∃x:ZMod p,x^2=2)
local notation "L" => InertCompletion318.Field p ns
local notation "φ" => InertCompletion318.embedding p ns
local notation "D0" => ArbitraryInertSeries318.sourceD p ns
local notation "d" => InertIntegers318.embedding p ns D0
local instance : DecidableEq L := Classical.decEq _

theorem int_norm (z:ℤ) : ‖(z:L)‖=‖(z:ℚ_[p])‖ := by
  simpa only [Rat.cast_intCast] using InertCompletion318.norm_ratCast p ns (z:ℚ)

/-- Actual literal-source scalar order-eight divisibility at an inert
 prime, after transport of the global integer labels to this actual curve.
 No logarithm, sign, formality or precision premise is retained. -/
theorem source_index_divisibility (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (rval:ℤ) (hr:ConcretePadic318.rationalPlace p (r w)=rval) (hpos:0<rval) (hodd:Odd rval)
    (P H Q tau:(E d).Point) (n c:ℤ)
    (hH:H=n • P+tau) (hQ:Q=c • P) (htau:(2:ℤ) • tau=0)
    (yH yQ:L) (hnsH:(E d).Nonsingular (1/φ (fH w)) yH)
    (hnsQ:(E d).Nonsingular (1/φ (fR w)) yQ)
    (hcoordH:H=Point.some _ yH hnsH) (hcoordQ:Q=Point.some _ yQ hnsQ) : (p:ℤ)^8∣c := by
  obtain ⟨hfH,hfR,hsmallH,hsmallR,hgain⟩:=
    InertScalarSource318.source_norm_bounds p ns hp S w source rval hr hpos hodd
  have curveH:yH^2=(1/φ (fH w))^3-d*(1/φ (fH w)) := by
    have he:=hnsH.1
    rw [equation_iff] at he
    simpa [E,sub_eq_add_neg] using he
  have curveQ:yQ^2=(1/φ (fR w))^3-d*(1/φ (fR w)) := by
    have he:=hnsQ.1
    rw [equation_iff] at he
    simpa [E,sub_eq_add_neg] using he
  have hmemH:H∈formalSubgroup p ns hp D0 := by
    rw [hcoordH]
    apply affine_mem p ns hp D0 _ yH (one_div_ne_zero hfH) curveH hnsH
    simpa only [one_div,inv_inv] using hsmallH
  have hmemQ:Q∈formalSubgroup p ns hp D0 := by
    rw [hcoordQ]
    apply affine_mem p ns hp D0 _ yQ (one_div_ne_zero hfR) curveQ hnsQ
    simpa only [one_div,inv_inv] using hsmallR
  have hLH:logHom p ns hp D0 ⟨H,hmemH⟩≠0 := by
    intro he
    have hh: (⟨H,hmemH⟩:formalSubgroup p ns hp D0)=0 := (logHom_zero_iff p ns hp D0 _).mp he
    have hz:H=0:=congrArg Subtype.val hh
    rw [hcoordH] at hz
    exact (Point.some_ne_zero hnsH) hz
  have hlogGain:‖logHom p ns hp D0 ⟨Q,hmemQ⟩‖≤
      ‖(p:ℚ_[p])‖^8*‖logHom p ns hp D0 ⟨H,hmemH⟩‖ := by
    apply reciprocal_gain p ns hp D0 ⟨H,hmemH⟩ ⟨Q,hmemQ⟩ _ yH _ yQ hnsH hnsQ hcoordH hcoordQ 8
    simpa only [one_div,inv_inv] using hgain
  exact TorsionSafeIndex318.torsion_safe_norm_divisibility
    (formalSubgroup p ns hp D0) (logHom p ns hp D0) p (int_norm p ns)
    P H Q tau n c hmemH hmemQ hH hQ htau hLH 8 hlogGain

end
end InertScalarIndex318
#print axioms InertScalarIndex318.source_index_divisibility
