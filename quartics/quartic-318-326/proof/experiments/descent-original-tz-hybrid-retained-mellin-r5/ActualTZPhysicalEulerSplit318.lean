module
public import ActualTZReferenceZetaProduct318
public import ActualTZWheelZero318
public import ActualTZLiteralAbsoluteEuler318
import all ActualTZLiteralAbsoluteEuler318
public section
noncomputable section
namespace ActualTZPhysicalEulerSplit318
open scoped BigOperators
open ActualTZReferenceZetaProduct318 ActualTZReferenceFactorNearOne318
open ActualTZWheelZero318 ActualTZRegulatedPhysicalBounds318
open ActualTZRegulatedRelative318 ActualTZRegulatedZetaAlgebra318
open ActualTZLiteralAbsoluteEuler318

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def refAtom (p : ℕ) (s t : I→ℂ) : ℂ := ∏ i : I,B p (s i) (t i)

theorem ref_is_baseline (p : ℕ) (s t : I→ℂ) :
    refAtom p s t=baseline p (regulator p s) (regulator p t) := by
  simp only [refAtom,baseline,B,regulator,one_div]

theorem ref_nonzero (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : 0<σ)
    (s t : I→ℂ) (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) :
    refAtom p s t≠0 := by
  let x := (p:ℂ)⁻¹
  have hx : ‖x‖≤1/2 := by
    dsimp only [x]
    rw [norm_inv,Complex.norm_natCast,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)
  have hr (u : I→ℂ) (hu : ∀ i,σ≤(u i).re) (i : I) : ‖regulator p u i‖≤1 := by
    rw [regulator,Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le)
      (neg_nonpos.mpr (hσ.le.trans (hu i)))
  have hnorm : (1:ℝ)/(6:ℝ)^Fintype.card I≤‖refAtom p s t‖ := by
    rw [ref_is_baseline]
    -- Reuse the exact lower bound for the same oneSite factors.
    simpa only [baseline,Finset.card_univ,one_div,inv_pow] using
      baseline_lower (Finset.univ : Finset I) x (regulator p s) (regulator p t)
        hx (hr s hs) (hr t ht)
  exact norm_pos_iff.mp ((by positivity : 0<(1:ℝ)/(6:ℝ)^Fintype.card I).trans_le hnorm)

def actualAtom (W p : ℕ) (a : I→ℤ) (b : I→ℕ) (s t : I→ℂ) : ℂ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    factor W p a b (regulator p s) (regulator p t)
  else 1

def actualPartial (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s t : I→ℂ) : ℂ :=
  ∏ p∈Nat.primesBelow P,actualAtom W p a b s t

def offWheel (W P : ℕ) : Finset ℕ :=
  (Nat.primesBelow P).filter (fun p=>W.Coprime p)

def corrected (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s t : I→ℂ) : ℂ :=
  ∏ p∈offWheel W P,actualAtom W p a b s t/refAtom p s t

theorem atom_wheel (W p : ℕ) (hp : p.Prime) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (s t : I→ℂ) (hW : ¬W.Coprime p) :
    actualAtom W p a b s t=1 := by
  rw [actualAtom,dif_pos hp]
  exact factor_wheel W p a b hU _ _ hW

theorem signed_is_actual (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s t : I→ℂ) :
    (∏ p : PrimeAt P,∑ d : Pair I,entry W P a b s t p d)=
      actualPartial W P a b s t := by
  classical
  unfold actualPartial
  rw [←Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  have hp := Nat.prime_of_mem_primesBelow p.property
  rw [actualAtom,dif_pos hp]
  rw [Fintype.sum_prod_type]
  rfl

private theorem wheel_subset_eq (W P : ℕ) (hW : 0<W) (h : W.primeFactors⊆Nat.primesBelow P) :
    ((Nat.primesBelow P).filter (fun p=>¬W.Coprime p))=W.primeFactors := by
  ext p
  rw [Finset.mem_filter]
  constructor
  · intro hp
    have hP := Nat.prime_of_mem_primesBelow hp.1
    exact Nat.mem_primeFactors.mpr ⟨hP,hP.dvd_iff_not_coprime.mpr (fun h' => hp.2 h'.symm),hW.ne'⟩
  · intro hp
    obtain ⟨hp',hdv,_⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨h hp,fun h' => (hp'.dvd_iff_not_coprime.mp hdv) h'.symm⟩

private theorem prod_ne_zero_regular (W P : ℕ) (σ : ℝ) (hσ : 0<σ)
    (s t : I→ℂ) (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) :
    (∏ p∈offWheel W P,refAtom p s t)≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact ref_nonzero p (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1) σ hσ s t hs ht

/-- The exact same signed physical Euler product: the wheel scalar
and reference ζ partial multiply the joint off-wheel correction.
No averaging, omitted-prime limit or replacement of near collisions. -/
theorem exact_split (W P : ℕ) (hW : 0<W)
    (hP : W.primeFactors⊆Nat.primesBelow P) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ) (s t : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) :
    (alpha W)^Fintype.card I*actualPartial W P a b s t =
     ((alpha W)^Fintype.card I/wheel W s t)*
      partial s t P*corrected W P a b s t := by
  classical
  have hAw : (∏ p∈(Nat.primesBelow P).filter (fun p=>¬W.Coprime p),
      actualAtom W p a b s t)=1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact atom_wheel W p (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1)
      a b hU s t (Finset.mem_filter.mp hp).2
  have hA : actualPartial W P a b s t=∏ p∈offWheel W P,actualAtom W p a b s t := by
    unfold actualPartial offWheel
    rw [←Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow P)
      (fun p=>W.Coprime p),hAw,mul_one]
  have hB : partial s t P=(∏ p∈offWheel W P,refAtom p s t)*wheel W s t := by
    change (∏ p∈Nat.primesBelow P,refAtom p s t)=_
    unfold offWheel wheel
    rw [←Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow P)
      (fun p=>W.Coprime p),wheel_subset_eq W P hW hP]
  have hWheel : wheel W s t≠0 := by
    change (∏ p∈W.primeFactors,refAtom p s t)≠0
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact ref_nonzero p (Nat.mem_primeFactors.mp hp).1 σ hσ s t hs ht
  rw [hA,hB,corrected,Finset.prod_div_distrib]
  field_simp [hWheel,prod_ne_zero_regular W P σ hσ s t hs ht] <;> ring

/-- Exact normalization of the existing signed finite main
integrand. The explicit L factors stay on the reference product;
no wheel or collision cutoff is absorbed into them. -/
theorem normalized_split (W P : ℕ) (hW : 0<W)
    (hP : W.primeFactors⊆Nat.primesBelow P) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (σ : ℝ) (hσ : 0<σ) (s t : I→ℂ)
    (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) (L : ℝ) :
    (alpha W*(L:ℂ))^Fintype.card I*actualPartial W P a b s t =
     ((alpha W)^Fintype.card I/wheel W s t)*
      ((L:ℂ)^Fintype.card I*partial s t P)*corrected W P a b s t := by
  rw [mul_pow]
  have H := congrArg (fun v : ℂ => (L:ℂ)^Fintype.card I*v)
    (exact_split W P hW hP a b hU σ hσ s t hs ht)
  calc
    _ = (L:ℂ)^Fintype.card I*((alpha W)^Fintype.card I*actualPartial W P a b s t) := by ring
    _ = _ := H.trans (by ring)

end ActualTZPhysicalEulerSplit318
