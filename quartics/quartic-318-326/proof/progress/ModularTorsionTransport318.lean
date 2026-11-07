module
public import ModularTorusTransport318
public import PrimitiveTorsion318
public section
noncomputable section
open scoped MatrixGroups
open PeriodEisenstein318 LatticeModelPoint318 ModularLattice318
open ModularPointTransport318 ModularTorusTransport318 EllipticTorsion318
namespace ModularTorsionTransport318
set_option maxHeartbeats 0

variable (g : SL(2,ℤ)) (N : ℕ)

/-- The literal inverse-transpose matrix action on the two period coordinates.
Vectors are columns in (tau,1) order, so the matrix is [[d,-c],[-b,a]]. -/
@[expose] def residueMap : ZMod N × ZMod N →+ ZMod N × ZMod N where
  toFun x := ((g 1 1:ZMod N)*x.1-(g 1 0:ZMod N)*x.2,
    (g 0 0:ZMod N)*x.2-(g 0 1:ZMod N)*x.1)
  map_zero' := by simp
  map_add' x y := by ext <;> simp <;> ring

lemma residueMap_intCast (m n : ℤ) :
    residueMap g N ((m:ZMod N),(n:ZMod N))=
      (((g 1 1*m-g 1 0*n:ℤ):ZMod N),((g 0 0*n-g 0 1*m:ℤ):ZMod N)) := by
  simp [residueMap]

/-- The actual elliptic transport carries literal N-torsion labels by the precise
inverse period-coordinate matrix. -/
theorem torsion_transport (tau : UpperHalfPlane) [NeZero N] (x : ZMod N × ZMod N) :
    pointAddEquiv g tau (torsionMap tau N x)=torsionMap (g•tau) N (residueMap g N x) := by
  obtain ⟨m,hm⟩ := ZMod.intCast_surjective x.1
  obtain ⟨n,hn⟩ := ZMod.intCast_surjective x.2
  have hx : x=((m:ZMod N),(n:ZMod N)) := Prod.ext hm.symm hn.symm
  rw [hx,residueMap_intCast,torsionMap_intCast,torsionMap_intCast]
  change slPointEquiv g tau (point tau (((m:ℂ)*tau+n)/(N:ℂ)))=_
  rw [point_transport]
  congr 1
  calc
    _ = (((m:ℂ)*tau+n)/d g tau)/(N:ℂ) := by ring
    _ = _ := by rw [period_inverse]

/-- The actual residue-coordinate map is injective. -/
theorem residueMap_injective (tau : UpperHalfPlane) [NeZero N] :
    Function.Injective (residueMap g N) := by
  intro x y h
  apply torsionMap_injective tau N
  apply (pointAddEquiv g tau).injective
  rw [torsion_transport,torsion_transport,h]

/-- An actual additive equivalence of the residue-label groups. -/
@[expose] def residueEquiv (tau : UpperHalfPlane) [NeZero N] :
    (ZMod N × ZMod N) ≃+ (ZMod N × ZMod N) :=
  AddEquiv.ofBijective (residueMap g N)
    ⟨residueMap_injective g N tau,Finite.surjective_of_injective (residueMap_injective g N tau)⟩

/-- Exact order is preserved by the literal residue-coordinate transformation. -/
theorem residue_order (tau : UpperHalfPlane) [NeZero N] (x : ZMod N × ZMod N) :
    addOrderOf (residueMap g N x)=addOrderOf x := by
  have hi := addOrderOf_injective (pointAddEquiv g tau).toAddMonoidHom
    (pointAddEquiv g tau).injective (torsionMap tau N x)
  change addOrderOf (pointAddEquiv g tau (torsionMap tau N x))=_ at hi
  rw [torsion_transport,addOrderOf_injective (torsionMap (g•tau) N) (torsionMap_injective (g•tau) N),
    addOrderOf_injective (torsionMap tau N) (torsionMap_injective tau N)] at hi
  exact hi

/-- Primitivity is genuinely retained, hence the point map transports exact-order-N fibers. -/
theorem primitive_iff (tau : UpperHalfPlane) [NeZero N] (x : ZMod N × ZMod N) :
    PrimitiveTorsion318.Primitive N (residueMap g N x) ↔ PrimitiveTorsion318.Primitive N x := by
  rw [← PrimitiveTorsion318.point_order_eq_iff (g•tau) N,
    ← PrimitiveTorsion318.point_order_eq_iff tau N,
    addOrderOf_injective (torsionMap (g•tau) N) (torsionMap_injective (g•tau) N),
    addOrderOf_injective (torsionMap tau N) (torsionMap_injective tau N),residue_order g N tau]

end ModularTorsionTransport318
