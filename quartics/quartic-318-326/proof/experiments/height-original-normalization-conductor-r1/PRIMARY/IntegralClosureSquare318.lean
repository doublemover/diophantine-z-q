module
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace IntegralClosureSquare318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R S R' S':Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S']
  (a:R≃+*R') (b:S≃+*S')
  (h:(algebraMap R' S').comp a.toRingHom=b.toRingHom.comp (algebraMap R S))

include a b h

lemma inverse_square : (algebraMap R S).comp a.symm.toRingHom=
    b.symm.toRingHom.comp (algebraMap R' S') := by
  ext r
  apply b.injective
  simpa using (RingHom.congr_fun h (a.symm r)).symm

/-- Actual integral closures are identified by a genuine compatible pair of
base and ambient ring isomorphisms. -/
@[expose] def closureEquiv : integralClosure R S≃+*integralClosure R' S' where
  toFun x := ⟨b x,IsIntegral.map_of_comp_eq a.toRingHom b.toRingHom h x.property⟩
  invFun x := ⟨b.symm x,IsIntegral.map_of_comp_eq a.symm.toRingHom b.symm.toRingHom
    (inverse_square a b h) x.property⟩
  left_inv x := Subtype.ext (b.left_inv x)
  right_inv x := Subtype.ext (b.right_inv x)
  map_mul' x y := Subtype.ext (b.map_mul x y)
  map_add' x y := Subtype.ext (b.map_add x y)

lemma closure_square : (algebraMap R' (integralClosure R' S')).comp a.toRingHom=
    (closureEquiv a b h).toRingHom.comp (algebraMap R (integralClosure R S)) := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact RingHom.congr_fun h r

/-- Actual module-finiteness is transported, not postulated to be invariant
under coordinate choices. -/
theorem finite [Module.Finite R (integralClosure R S)] :
    Module.Finite R' (integralClosure R' S') := by
  apply RingHom.finite_algebraMap.mp
  apply RingHom.Finite.of_comp_finite (f:=a.toRingHom)
  rw [closure_square a b h]
  exact (closureEquiv a b h).finite.comp (RingHom.finite_algebraMap.mpr inferInstance)

end IntegralClosureSquare318
