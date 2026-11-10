module
public import IntegralWholeReciprocalOverlap318
public section
noncomputable section
namespace TensorBaseEquivalence318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B S T U V : Type*}
  [CommRing A] [CommRing B] [CommRing S] [CommRing T] [CommRing U] [CommRing V]
  [Algebra A S] [Algebra A T] [Algebra B U] [Algebra B V]

/-- Heterobasic tensor equivalence with the coefficient maps recorded
explicitly. This changes the base by the given isomorphism, not by rank. -/
@[expose] def equiv (e : A ≃+* B) (f : S ≃+* U) (g : T ≃+* V)
    (hf : ∀ a,f (algebraMap A S a)=algebraMap B U (e a))
    (hg : ∀ a,g (algebraMap A T a)=algebraMap B V (e a)) :
    S ⊗[A] T ≃+* U ⊗[B] V := by
  have hfi : ∀ b,f.symm (algebraMap B U b)=algebraMap A S (e.symm b) := by
    intro b
    apply f.injective
    rw [f.apply_symm_apply,hf,e.apply_symm_apply]
  have hgi : ∀ b,g.symm (algebraMap B V b)=algebraMap A T (e.symm b) := by
    intro b
    apply g.injective
    rw [g.apply_symm_apply,hg,e.apply_symm_apply]
  let F : S ⊗[A] T →+* U ⊗[B] V :=
    Algebra.TensorProduct.mapRingHom e.toRingHom f.toRingHom g.toRingHom
      (RingHom.ext hf) (RingHom.ext hg)
  let G : U ⊗[B] V →+* S ⊗[A] T :=
    Algebra.TensorProduct.mapRingHom e.symm.toRingHom f.symm.toRingHom g.symm.toRingHom
      (RingHom.ext hfi) (RingHom.ext hgi)
  exact RingEquiv.ofRingHom F G
    (by
      ext x
      · change F (G (x ⊗ₜ[B] (1:V)))=x ⊗ₜ[B] (1:V)
        simp only [F,G,Algebra.TensorProduct.mapRingHom_tmul,map_one]
        change f (f.symm x) ⊗ₜ[B] (1:V)=x ⊗ₜ[B] (1:V)
        rw [f.apply_symm_apply]
      · change F (G ((1:U) ⊗ₜ[B] x))=(1:U) ⊗ₜ[B] x
        simp only [F,G,Algebra.TensorProduct.mapRingHom_tmul,map_one]
        change (1:U) ⊗ₜ[B] g (g.symm x)=(1:U) ⊗ₜ[B] x
        rw [g.apply_symm_apply])
    (by
      ext x
      · change G (F (x ⊗ₜ[A] (1:T)))=x ⊗ₜ[A] (1:T)
        simp only [F,G,Algebra.TensorProduct.mapRingHom_tmul,map_one]
        change f.symm (f x) ⊗ₜ[A] (1:T)=x ⊗ₜ[A] (1:T)
        rw [f.symm_apply_apply]
      · change G (F ((1:S) ⊗ₜ[A] x))=(1:S) ⊗ₜ[A] x
        simp only [F,G,Algebra.TensorProduct.mapRingHom_tmul,map_one]
        change (1:S) ⊗ₜ[A] g.symm (g x)=(1:S) ⊗ₜ[A] x
        rw [g.symm_apply_apply])

@[simp] theorem equiv_tmul (e : A ≃+* B) (f : S ≃+* U) (g : T ≃+* V) (hf hg)
    (s : S) (t : T) : equiv e f g hf hg (s ⊗ₜ[A] t)=f s ⊗ₜ[B] g t :=
  Algebra.TensorProduct.mapRingHom_tmul
    (fR:=e.toRingHom) (fS:=f.toRingHom) (fT:=g.toRingHom)
    (HS:=RingHom.ext hf) (HT:=RingHom.ext hg) s t

theorem equiv_base (e : A ≃+* B) (f : S ≃+* U) (g : T ≃+* V) (hf hg) (a : A) :
    equiv e f g hf hg (algebraMap A (S ⊗[A] T) a)=
      algebraMap B (U ⊗[B] V) (e a) := by
  change equiv e f g hf hg ((algebraMap A S a) ⊗ₜ[A] (1:T)) = _
  rw [equiv_tmul,hf,map_one]
  rfl
end TensorBaseEquivalence318
