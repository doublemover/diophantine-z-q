module
public import OriginalQuadraticEliminant318
public section
noncomputable section
namespace OriginalAffineSieveEliminants318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318 OriginalNormPointSieveTail318
open OriginalQuadraticEliminant318
set_option maxHeartbeats 4500000

@[expose] def affine (a d : Vector ℤ) (h : ℤ) : Vector ℤ := a+h • d
@[expose] def fA (side : Bool) (κ t : ℤ) (d : Vector ℤ) :=
  if side then κ*(t+2)*d.2.2^2-2*d.1*d.2.1 else κ*d.2.2^2
@[expose] def fB (side : Bool) (κ t : ℤ) (a d : Vector ℤ) :=
  if side then 2*κ*(t+2)*a.2.2*d.2.2-2*(a.1*d.2.1+d.1*a.2.1)
  else 2*κ*a.2.2*d.2.2
@[expose] def fC (side : Bool) (κ t : ℤ) (a : Vector ℤ) :=
  if side then P' κ t a else P κ t a
@[expose] def normEliminant (side : Bool) (κ t : ℤ) (a d : Vector ℤ)
    (coordinate : Bool) : ℤ :=
  let x := if coordinate then a.2.1 else a.1
  let dx := if coordinate then d.2.1 else d.1
  eliminant (fA side κ t d) (fB side κ t a d) (fC side κ t a)
    (dx^2) (2*x*dx) (x^2+t^2)

lemma actual_affine_polynomial (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (h : ℤ) :
    (if side then P' κ t (affine a d h) else P κ t (affine a d h))=
      fA side κ t d*h^2+fB side κ t a d*h+fC side κ t a := by
  cases side <;> simp [affine,fA,fB,fC,P,P',zsmul_eq_mul] <;> ring

lemma affine_norm_factor (t a d h : ℤ) :
    (a+h*d)^2+t^2=d^2*h^2+(2*a*d)*h+(a^2+t^2) := by ring

/-- EVERY actual prime obstruction on either original pair yields one
of the two explicit eliminant divisibilities on that same affine fiber.
No exclusion of leading-coefficient primes is inserted. -/
theorem obstruction_eliminates (side : Bool) (κ t : ℤ) (a d : Vector ℤ)
    (h : ℤ) (p : ℕ) (hp : p.Prime)
    (ho : pointObstruction side κ t (affine a d h) p) :
    (p:ℤ)∣normEliminant side κ t a d false ∨
      (p:ℤ)∣normEliminant side κ t a d true := by
  have hF := ho.1
  rw [actual_affine_polynomial] at hF
  have hD : (p:ℤ)∣(t^2+(a.1+h*d.1)^2)*(t^2+(a.2.1+h*d.2.1)^2) := by
    simpa [pointObstruction,D,affine,zsmul_eq_mul] using ho.2
  have hpi : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpi.dvd_mul.mp hD with hx|hz
  · left
    apply common_divisor _ _ _ _ _ _ h _ hF
    have he : t^2+(a.1+h*d.1)^2=d.1^2*h^2+(2*a.1*d.1)*h+(a.1^2+t^2) := by ring
    rw [he] at hx
    exact hx
  · right
    apply common_divisor _ _ _ _ _ _ h _ hF
    have he : t^2+(a.2.1+h*d.2.1)^2=d.2.1^2*h^2+(2*a.2.1*d.2.1)*h+(a.2.1^2+t^2) := by ring
    rw [he] at hz
    exact hz

end OriginalAffineSieveEliminants318
