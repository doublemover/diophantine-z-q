module
public import ActualAlternateRatioPrecision318
public section
noncomputable section
namespace IntegralPolynomialPrecision318
open ValuativeOrbitBounds318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))

@[expose] def Approx (r : ℤ) (a b : F) : Prop :=
  Bound v 0 a ∧ Bound v 0 b ∧ Bound v r (a-b)

lemma int_bound (n : ℤ) : Bound v 0 (n:F) := by
  cases n with
  | ofNat n => exact bnat v n
  | negSucc n => simpa only [Int.cast_negSucc] using bneg v (bnat v (n+1))

lemma of_error {r : ℤ} (hr : 0≤r) {a b : F} (hb : Bound v 0 b)
    (he : Bound v r (a-b)) : Approx v r a b := by
  refine ⟨?_,hb,he⟩
  simpa only [sub_add_cancel] using badd v (weaken v he hr) hb

lemma refl_int (r : ℤ) (n : ℤ) : Approx v r (n:F) (n:F) :=
  ⟨int_bound v n,int_bound v n,by simpa only [sub_self] using bzero v r⟩

lemma add {r : ℤ} {a b c d : F} (h : Approx v r a b) (k : Approx v r c d) :
    Approx v r (a+c) (b+d) := by
  refine ⟨badd v h.1 k.1,badd v h.2.1 k.2.1,?_⟩
  convert badd v h.2.2 k.2.2 using 1 <;> ring

lemma sub {r : ℤ} {a b c d : F} (h : Approx v r a b) (k : Approx v r c d) :
    Approx v r (a-c) (b-d) := by
  refine ⟨bsub v h.1 k.1,bsub v h.2.1 k.2.1,?_⟩
  convert bsub v h.2.2 k.2.2 using 1 <;> ring

lemma mul {r : ℤ} {a b c d : F} (h : Approx v r a b) (k : Approx v r c d) :
    Approx v r (a*c) (b*d) := by
  refine ⟨bmul_unit v h.1 k.1,bmul_unit v h.2.1 k.2.1,?_⟩
  convert badd v (bmul_unit v h.2.2 k.1) (bmul_unit_left v h.2.1 k.2.2) using 1 <;> ring

lemma sq {r : ℤ} {a b : F} (h : Approx v r a b) : Approx v r (a^2) (b^2) := by
  simpa only [pow_two] using mul v h h

@[expose] def lucas (s t z : F) : F := t^2-s*(s-2)*t*z+(s-2)^2*z^2

/-- The actual source Lucas polynomial is 1-Lipschitz on integral inputs;
its integer relation therefore absorbs all primary errors without loss. -/
theorem lucas_error {r : ℤ} (hr : 0≤r) (s t z : F) (a b c : ℤ)
    (hs : Bound v r (s-(a:F))) (ht : Bound v r (t-(b:F))) (hz : Bound v r (z-(c:F)))
    (he : b^2-a*(a-2)*b*c+(a-2)^2*c^2=1) : Bound v r (lucas s t z-1) := by
  have hS := of_error v hr (int_bound v a) hs
  have hT := of_error v hr (int_bound v b) ht
  have hZ := of_error v hr (int_bound v c) hz
  have hS2 := sub v hS (refl_int v r 2)
  have hpoly := add v (sub v (sq v hT) (mul v (mul v (mul v hS hS2) hT) hZ))
    (mul v (sq v hS2) (sq v hZ))
  have heF : lucas (a:F) (b:F) (c:F)=1 := by
    unfold lucas
    exact_mod_cast he
  have hh := hpoly.2.2
  change Bound v r (lucas s t z-lucas (a:F) (b:F) (c:F)) at hh
  simpa only [heF] using hh

end IntegralPolynomialPrecision318
