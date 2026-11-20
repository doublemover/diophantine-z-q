module
public import ActualTwoDescentCloseSquare318
public section
noncomputable section
namespace ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]

/-- Literal nonzero square multipliers relating the original pair of
Kummer coordinates to one of the four actual two-torsion classes. -/
def SquarePair (A B c d : K) : Prop :=
  ∃ u v : K, u ≠ 0 ∧ v ≠ 0 ∧ A=c*u^2 ∧ B=d*v^2

def TorsionPair (n A B : K) : Prop :=
  SquarePair A B 1 1 ∨ SquarePair A B n 1 ∨
    SquarePair A B 3 (-n) ∨ SquarePair A B (3*n) (-n)

lemma actual_identity_pair (n x y r s : K) (hx : x ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hy : y ≠ 0) (hc : y^2=x*(x-n)*(x+3*n))
    (hA : r^2=(x+3*n)/x) (hB : s^2=(x-n)/x) :
    SquarePair (x+3*n) (x-n) 1 1 := by
  have hA' : x+3*n=x*r^2 := by rw [hA]; field_simp [hx] <;> ring
  have hB' : x-n=x*s^2 := by rw [hB]; field_simp [hx] <;> ring
  let w := y/(x*r*s)
  have hw0 : w ≠ 0 := div_ne_zero hy (mul_ne_zero (mul_ne_zero hx hr) hs)
  have hw : w^2=x := by
    dsimp [w]
    rw [div_pow,hc,hA',hB']
    field_simp [hx,hr,hs]
    <;> ring
  refine ⟨w*r,w*s,mul_ne_zero hw0 hr,mul_ne_zero hw0 hs,?_,?_⟩
  · rw [one_mul,mul_pow,hw]; exact hA'
  · rw [one_mul,mul_pow,hw]; exact hB'

lemma actual_first_torsion_pair (n x y r s : K) (hn : n ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (hy : y ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (hx : r^2=x/n) (hA : s^2=(x+3*n)/(4*n)) :
    SquarePair (x+3*n) (x-n) n 1 := by
  have hx' : x=n*r^2 := by rw [hx]; field_simp [hn] <;> ring
  have hA' : x+3*n=4*n*s^2 := by rw [hA]; field_simp [hn] <;> ring
  let v := y/(2*n*r*s)
  have hv0 : v ≠ 0 := div_ne_zero hy
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hr) hs)
  have hc' : y^2=(x-n)*(2*n*r*s)^2 := by
    calc
      y^2=x*(x-n)*(x+3*n) := hc
      _=(x-n)*(n*r^2)*(4*n*s^2) := by rw [hA',hx']; ring
      _=(x-n)*(2*n*r*s)^2 := by ring
  have hv : v^2=x-n := by
    dsimp [v]
    rw [div_pow,hc']
    field_simp [hn,hr,hs]
  refine ⟨2*s,v,mul_ne_zero (by norm_num) hs,hv0,?_,?_⟩
  · rw [hA']; ring
  · simpa only [one_mul] using hv.symm

lemma actual_second_torsion_pair (n x y r s : K) (hn : n ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (hy : y ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n))
    (hx : r^2=x/(-3*n)) (hB : s^2=(x-n)/(-4*n)) :
    SquarePair (x+3*n) (x-n) 3 (-n) := by
  have hx' : x=(-3*n)*r^2 := by rw [hx]; field_simp [hn] <;> ring
  have hB' : x-n=(-4*n)*s^2 := by rw [hB]; field_simp [hn] <;> ring
  let u := y/(6*n*r*s)
  have hu0 : u ≠ 0 := div_ne_zero hy
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hr) hs)
  have hc' : y^2=12*n^2*r^2*s^2*(x+3*n) := by
    calc
      y^2=x*(x-n)*(x+3*n) := hc
      _=((-3*n)*r^2)*((-4*n)*s^2)*(x+3*n) := by rw [hB',hx']
      _=12*n^2*r^2*s^2*(x+3*n) := by ring
  have hu : 3*u^2=x+3*n := by
    dsimp [u]
    rw [div_pow,hc']
    field_simp [hn,hr,hs]
    <;> ring
  refine ⟨u,2*s,hu0,mul_ne_zero (by norm_num) hs,hu.symm,?_⟩
  rw [hB']; ring

end ActualTwoDescentTorsionSquarePairs318
