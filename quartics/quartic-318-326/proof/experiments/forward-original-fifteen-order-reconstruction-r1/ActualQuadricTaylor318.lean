module
public import ActualPrimitiveOptimizedPrimeBound318
public section
noncomputable section
namespace ActualQuadricTaylor318
open QuadricCRTAssembly318
set_option maxHeartbeats 16000000

@[expose] def translate {R : Type*} [CommRing R] (x h : Coordinates R) (m : R) : Coordinates R :=
  ((x.1.1+m*h.1.1,x.1.2+m*h.1.2),
    (x.2.1.1+m*h.2.1.1,x.2.1.2+m*h.2.1.2),x.2.2+m*h.2.2)
@[expose] def derivative {R : Type*} [CommRing R] (κ : R) (x h : Coordinates R) : R :=
  2*x.1.1*h.1.1+2*x.1.2*h.1.2-2*x.2.1.1*h.2.1.1-
    2*x.2.1.2*h.2.1.2-2*κ*x.2.2*h.2.2

/-- Exact quadratic Taylor identity on the ORIGINAL five-coordinate
form, with the true factor2 in every derivative coefficient. -/
theorem original_taylor {R : Type*} [CommRing R] (κ : R) (x h : Coordinates R) (m : R) :
    equation κ (translate x h m)=equation κ x+m*derivative κ x h+m^2*equation κ h := by
  dsimp [equation,translate,derivative]
  ring

@[expose] def vector {R : Type*} (x : Coordinates R) : Fin 5 → R :=
  ![x.1.1,x.1.2,x.2.1.1,x.2.1.2,x.2.2]
@[expose] def coordinateEquiv (R : Type*) : Coordinates R ≃ (Fin 5 → R) where
  toFun := vector
  invFun v := ((v 0,v 1),(v 2,v 3),v 4)
  left_inv x := rfl
  right_inv v := by funext i;fin_cases i <;> rfl
@[expose] def gradient {R : Type*} [CommRing R] (κ : R) (x : Coordinates R) : Fin 5 → R :=
  ![2*x.1.1,2*x.1.2,-2*x.2.1.1,-2*x.2.1.2,-2*κ*x.2.2]

lemma derivative_sum {R : Type*} [CommRing R] (κ : R) (x h : Coordinates R) :
    derivative κ x h=∑i : Fin 5,gradient κ x i*vector h i := by
  simp [derivative,gradient,vector,Fin.sum_univ_succ] <;> ring

/-- At a good odd prime, nonzero original residue means a nonzero
ACTUAL gradient coordinate. This supplies the pivot used by lifting. -/
theorem original_gradient_nonzero {F : Type*} [Field F] (κ : F) (hκ : κ≠0)
    (h2 : (2:F)≠0) (x : Coordinates F) (hx : x≠((0,0),(0,0),0)) :
    ∃i : Fin 5,gradient κ x i≠0 := by
  by_contra hh
  push_neg at hh
  have ha := hh 0
  have hb := hh 1
  have hc := hh 2
  have hd := hh 3
  have hw := hh 4
  have hna : x.1.1=0 := (mul_eq_zero.mp ha).resolve_left h2
  have hnb : x.1.2=0 := (mul_eq_zero.mp hb).resolve_left h2
  have hnc : x.2.1.1=0 := (mul_eq_zero.mp hc).resolve_left (neg_ne_zero.mpr h2)
  have hnd : x.2.1.2=0 := (mul_eq_zero.mp hd).resolve_left (neg_ne_zero.mpr h2)
  have hnw : x.2.2=0 := (mul_eq_zero.mp hw).resolve_left (mul_ne_zero (neg_ne_zero.mpr h2) hκ)
  apply hx
  exact Prod.ext (Prod.ext hna hnb) (Prod.ext (Prod.ext hnc hnd) hnw)

end ActualQuadricTaylor318
