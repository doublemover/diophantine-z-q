module
public import SelectedCoprimePeriodLifts318
public import MarkedPeriod318
public import PrimitiveTorsion318
public section
noncomputable section

open scoped MatrixGroups Matrix

namespace SelectedActualPrimitiveOrbit318
open PrimitiveTorsion318 MarkedPeriod318
open EllipticTorsion318 ModularTorusTransport318 ModularTorsionTransport318

/-- Every primitive label at the original (possibly composite) level
is moved to the standard 1/N mark by a genuine integral SL₂ matrix.
The matrix acts by inverse transpose, in the native (τ,1) order. -/
theorem exists_matrix (N : ℕ) [NeZero N] (x : ZMod N × ZMod N) (hx : Primitive N x) :
    ∃ g : SL(2,ℤ), residueMap g N x = standardLabel N := by
  have hprim : N.gcd (x.1.val.gcd x.2.val) = 1 := hx
  obtain ⟨a,b,ha,hb,hcop⟩ := SelectedCoprimePeriodLifts318.coprime_lifts N x.1 x.2 hprim
  let u := Nat.gcdA a b
  let v := Nat.gcdB a b
  have hbez : (a : ℤ)*u+(b : ℤ)*v = 1 := by
    have hgcd : Nat.gcd a b = 1 := hcop
    simpa only [hgcd,Int.natCast_one,u,v] using (Nat.gcd_eq_gcd_ab a b).symm
  let g : SL(2,ℤ) := ⟨!![v,-u;(a : ℤ),(b : ℤ)],by
    rw [Matrix.det_fin_two_of]
    linear_combination hbez⟩
  have hlabel : x = (((a : ℤ) : ZMod N),((b : ℤ) : ZMod N)) := by
    exact Prod.ext (by simpa only [Int.cast_natCast] using ha.symm)
      (by simpa only [Int.cast_natCast] using hb.symm)
  refine ⟨g,?_⟩
  rw [hlabel,residueMap_intCast]
  change ((((b : ℤ)*(a : ℤ)-(a : ℤ)*(b : ℤ) : ℤ) : ZMod N),
    ((v*(b : ℤ)-(-u)*(a : ℤ) : ℤ) : ZMod N)) = (0,1)
  have h₁ : (b : ℤ)*(a : ℤ)-(a : ℤ)*(b : ℤ) = 0 := by ring
  have h₂ : v*(b : ℤ)-(-u)*(a : ℤ) = 1 := by linear_combination hbez
  rw [h₁,h₂] <;> simp

/-- The literal native algebraic point transport sends every genuine
exact-order point to the standard 1/N point of the transported period. -/
theorem exists_point_transport (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (P : (ModularWeierstrass318.curve τ).toAffine.Point) (hP : addOrderOf P = N) :
    ∃ g : SL(2,ℤ), pointAddEquiv g τ P = standardPoint N (g • τ) := by
  obtain ⟨x,hx⟩ := (primitiveEquiv τ N).surjective ⟨P,hP⟩
  have he : torsionMap τ N x.val = P := congrArg Subtype.val hx
  obtain ⟨g,hg⟩ := exists_matrix N x.val x.property
  refine ⟨g,?_⟩
  rw [←he,torsion_transport,hg]
  rfl

end SelectedActualPrimitiveOrbit318

#print axioms SelectedActualPrimitiveOrbit318.exists_matrix
#print axioms SelectedActualPrimitiveOrbit318.exists_point_transport
