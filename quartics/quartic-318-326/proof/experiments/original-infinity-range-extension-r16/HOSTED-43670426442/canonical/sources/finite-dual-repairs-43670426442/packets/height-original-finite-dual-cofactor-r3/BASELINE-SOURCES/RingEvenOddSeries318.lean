module
public import RingEvenFormalQuotient318
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public section
noncomputable section
namespace RingEvenOddSeries318
set_option maxHeartbeats 0
open PowerSeries
variable {k:Type*} [CommRing k]

@[expose] def evenPart (f:k⟦X⟧):k⟦X⟧ := mk (fun n=>coeff (2*n) f)
@[expose] def oddPart (f:k⟦X⟧):k⟦X⟧ := mk (fun n=>coeff (2*n+1) f)
@[expose] def expandTwo : k⟦X⟧→ₐ[k]k⟦X⟧ := expand 2 (by decide)

theorem coeff_expand_even (f:k⟦X⟧) (n:ℕ) : coeff (2*n) (expandTwo f)=coeff n f :=
  coeff_expand_mul 2 (by decide) f n

theorem coeff_expand_odd (f:k⟦X⟧) (n:ℕ) : coeff (2*n+1) (expandTwo f)=0 :=
  coeff_expand_of_not_dvd 2 (by decide) f (by omega)

theorem coeff_X_expand_even (f:k⟦X⟧) (n:ℕ) : coeff (2*n) (X*expandTwo f)=0 := by
  cases n with
  | zero => simp
  | succ n =>
    have he:2*(n+1)=(2*n+1)+1 := by omega
    rw [he,coeff_succ_X_mul]
    exact coeff_expand_odd f n

theorem coeff_X_expand_odd (f:k⟦X⟧) (n:ℕ) : coeff (2*n+1) (X*expandTwo f)=coeff n f := by
  rw [coeff_succ_X_mul,coeff_expand_even]

/-- Every actual formal series has a unique even-plus-X-times-odd expansion. -/
theorem decomposition (f:k⟦X⟧) :
    expandTwo (evenPart f)+X*expandTwo (oddPart f)=f := by
  ext n
  rcases Nat.even_or_odd n with hn|hn
  · obtain ⟨m,hm⟩:=hn
    have he:n=2*m := by omega
    rw [he,map_add,coeff_expand_even,coeff_X_expand_even,add_zero]
    simp [evenPart]
  · obtain ⟨m,hm⟩:=hn
    have he:n=2*m+1 := by omega
    rw [he,map_add,coeff_expand_odd,coeff_X_expand_odd,zero_add]
    simp [oddPart]

theorem decomposition_injective : Function.Injective
    (fun z:k⟦X⟧×k⟦X⟧=>expandTwo z.1+X*expandTwo z.2) := by
  intro z w he
  apply Prod.ext
  · ext n
    have h:=congrArg (coeff (2*n)) he
    simpa only [map_add,coeff_expand_even,coeff_X_expand_even,add_zero] using h
  · ext n
    have h:=congrArg (coeff (2*n+1)) he
    simpa only [map_add,coeff_expand_odd,coeff_X_expand_odd,zero_add] using h

/-- The actual ring map from R[omega]/(omega²-X) to k[[T]], sending
base X to T² and omega to T. -/
@[expose] def quadraticMap : QuadraticAlgebra k⟦X⟧ X 0 →+* k⟦X⟧ where
  toFun z:=expandTwo z.re+X*expandTwo z.im
  map_zero':=by simp [expandTwo]
  map_one':=by
    change expandTwo (1:k⟦X⟧)+X*expandTwo (0:k⟦X⟧)=1
    simp
  map_add' z w:=by simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,map_add];ring
  map_mul' z w:=by
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,map_add,map_mul,map_zero,zero_mul,add_zero]
    have hX:expandTwo (X:k⟦X⟧)=X^2 := by
      rw [expandTwo,expand_apply,subst_X (HasSubst.X_pow (by decide))]
    rw [hX]
    ring

/-- Concrete ring isomorphism, proved through actual coefficient splitting. -/
@[expose] def quadraticEquiv : QuadraticAlgebra k⟦X⟧ X 0 ≃+* k⟦X⟧ :=
  RingEquiv.ofBijective quadraticMap ⟨by
    intro z w he
    have h: (z.re,z.im)=(w.re,w.im):=decomposition_injective he
    exact QuadraticAlgebra.ext (congrArg Prod.fst h) (congrArg Prod.snd h),by
    intro f
    exact ⟨⟨evenPart f,oddPart f⟩,decomposition f⟩⟩

end RingEvenOddSeries318
