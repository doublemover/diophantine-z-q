module
public import SquareCoordinateDifferential318
public section
noncomputable section
namespace ReciprocalCoordinateDifferential318
set_option maxHeartbeats 100000
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Universal differentiation of the actual reciprocal relation.
No division or cancellation at an omitted point is built into this statement. -/
theorem D_relation (t u : S) (c : R) (h : u^2*t=algebraMap R S c) :
    u^2 • KaehlerDifferential.D R S t =
      -(2*u*t) • KaehlerDifferential.D R S u := by
  have hd := congrArg (KaehlerDifferential.D R S) h
  simp only [pow_two,Derivation.leibniz,Derivation.map_algebraMap] at hd
  have he : (u*u) • KaehlerDifferential.D R S t +
      (2*u*t) • KaehlerDifferential.D R S u=0 := by
    calc
      _ = (u*u) • KaehlerDifferential.D R S t +
        t • (u • KaehlerDifferential.D R S u + u • KaehlerDifferential.D R S u) := by module
      _ = 0 := hd
  simpa only [pow_two,neg_smul] using eq_neg_of_add_eq_zero_left he
/-- Cancellation occurs only after supplying an actual inverse to u. -/
theorem D_of_inverse (t u v : S) (c : R) (hu : u*v=1)
    (h : u^2*t=algebraMap R S c) :
    KaehlerDifferential.D R S t =
      -(2*v*t) • KaehlerDifferential.D R S u := by
  have huv : v^2*u^2=1 := by
    calc
      _=(u*v)^2 := by ring
      _=1 := by rw [hu,one_pow]
  calc
    _=(1:S) • KaehlerDifferential.D R S t := (one_smul _ _).symm
    _=(v^2*u^2) • KaehlerDifferential.D R S t := by rw [huv]
    _=v^2 • (u^2 • KaehlerDifferential.D R S t) := (smul_smul _ _ _).symm
    _=v^2 • (-(2*u*t) • KaehlerDifferential.D R S u) := by rw [D_relation t u c h]
    _=-(2*v*t) • KaehlerDifferential.D R S u := by
      rw [smul_smul]
      congr 1
      calc
        _=-(2*v*t)*(u*v) := by ring
        _=-(2*v*t) := by rw [hu,mul_one]
end ReciprocalCoordinateDifferential318
