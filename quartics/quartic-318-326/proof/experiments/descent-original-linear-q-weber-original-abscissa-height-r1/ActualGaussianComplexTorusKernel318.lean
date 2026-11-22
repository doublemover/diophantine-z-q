module
public import ActualGaussianComplexTorusCore318
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public section
noncomputable section

namespace ActualGaussianComplexTorusKernel318

abbrev Ide (a : GaussianInt) := Ideal.span ({a} : Set GaussianInt)

private def rep (a : GaussianInt) (u : GaussianInt ⧸ Ide a) : GaussianInt :=
  (Ideal.Quotient.mk_surjective u).choose

private theorem rep_good (a : GaussianInt) (u : GaussianInt ⧸ Ide a) :
    Ideal.Quotient.mk (Ide a) (rep a u)=u :=
  (Ideal.Quotient.mk_surjective u).choose_spec

private theorem torus_mk_eq {x y : ℂ} : V x=V y ↔ x-y∈lattice := by
  rw [←sub_eq_zero,←map_sub]
  exact QuotientAddGroup.eq_zero_iff _

private def scaled_lift (a : GaussianInt) (ha : a ≠ 0) (z : GaussianInt) :
    {P : Torus // scalar a P=0} := by
  have hn : iota a ≠ 0 := fun h => ha (GaussianInt.toComplex_injective
    (h.trans (map_zero iota).symm))
  refine ⟨V (iota z/iota a),?_⟩
  rw [scalar_on,mul_comm,div_mul_cancel₀ _ hn]
  exact (QuotientAddGroup.eq_zero_iff (N:=lattice) _).mpr ⟨z,rfl⟩

private theorem scaled_lift_congr (a : GaussianInt) (ha : a ≠ 0) (z w : GaussianInt) :
    scaled_lift a ha z=scaled_lift a ha w ↔ z-w∈Ide a := by
  have hn : iota a ≠ 0 := fun h => ha (GaussianInt.toComplex_injective
    (h.trans (map_zero iota).symm))
  constructor
  · intro h
    have h₀ : V (iota z/iota a)=V (iota w/iota a) := congrArg Subtype.val h
    obtain ⟨b,hb⟩ := torus_mk_eq.mp h₀
    change iota b=iota z/iota a-iota w/iota a at hb
    rw [←sub_div,←map_sub] at hb
    apply Ideal.mem_span_singleton.mpr
    refine ⟨b,GaussianInt.toComplex_injective ?_⟩
    calc
      iota (z-w) = (iota (z-w)/iota a)*iota a := (div_mul_cancel₀ _ hn).symm
      _ = iota (a*b) := by rw [←hb,map_mul,mul_comm]
  · intro h
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp h
    apply Subtype.ext
    apply torus_mk_eq.mpr
    change iota z/iota a-iota w/iota a∈lattice
    refine ⟨b,?_⟩
    change iota b=iota z/iota a-iota w/iota a
    rw [←sub_div,←map_sub,hb,map_mul,mul_comm,mul_div_cancel_right₀ _ hn]

/-- Direct arithmetic equivalence from the literal principal Gaussian
ideal quotient to the kernel of multiplication in the actual square
torus. No analytic elliptic uniformization is used by this lemma. -/
def kernel_equiv (a : GaussianInt) (ha : a ≠ 0) :
    (GaussianInt ⧸ Ide a) ≃ {P : Torus // scalar a P=0} := by
  refine Equiv.ofBijective (fun u => scaled_lift a ha (rep a u)) ⟨?_,?_⟩
  · intro u v h
    have h₀ := (Ideal.Quotient.eq (I:=Ide a)).mpr ((scaled_lift_congr a ha _ _).mp h)
    simpa only [rep_good] using h₀
  · rintro ⟨P,hP⟩
    obtain ⟨x,hx⟩ := QuotientAddGroup.mk'_surjective lattice P
    have hz : V (iota a*x)=0 := by rw [←scalar_on,hx]; exact hP
    obtain ⟨g,hg⟩ := (QuotientAddGroup.eq_zero_iff (N:=lattice) _).mp hz
    let u := Ideal.Quotient.mk (Ide a) g
    refine ⟨u,?_⟩
    have hrep : scaled_lift a ha (rep a u)=scaled_lift a ha g := by
      apply (scaled_lift_congr a ha _ _).mpr
      exact (Ideal.Quotient.eq (I:=Ide a)).mp (rep_good a u)
    change scaled_lift a ha (rep a u) = ⟨P,hP⟩
    rw [hrep]
    apply Subtype.ext
    change V (iota g/iota a)=P
    change iota g=iota a*x at hg
    have hn : iota a ≠ 0 := fun h => ha (GaussianInt.toComplex_injective
      (h.trans (map_zero iota).symm))
    rw [hg,mul_comm,mul_div_cancel_right₀ _ hn,hx]

/-- Every fibre is a translate of the same kernel, provided the
scalar is nonzero. The chosen lift of a target is simply x/a. -/
def fibre_equiv (a : GaussianInt) (ha : a ≠ 0) (Q : Torus) :
    (GaussianInt ⧸ Ide a) ≃ {P : Torus // scalar a P=Q} := by
  have hn : iota a ≠ 0 := fun h => ha (GaussianInt.toComplex_injective
    (h.trans (map_zero iota).symm))
  let x := (QuotientAddGroup.mk'_surjective lattice Q).choose
  have hx : V x=Q := (QuotientAddGroup.mk'_surjective lattice Q).choose_spec
  let x₀ := V (x/iota a)
  have he : scalar a x₀=Q := by
    change scalar a (V (x/iota a))=Q
    rw [scalar_on,mul_comm,div_mul_cancel₀ _ hn,hx]
  refine (kernel_equiv a ha).trans ?_
  exact
    { toFun := fun P => ⟨P.val+x₀,by rw [map_add,P.property,he,zero_add]⟩
      invFun := fun P => ⟨P.val-x₀,by rw [map_sub,P.property,he,sub_self]⟩
      left_inv := fun P => Subtype.ext (add_sub_cancel_right P.val x₀)
      right_inv := fun P => Subtype.ext (sub_add_cancel P.val x₀) }

end ActualGaussianComplexTorusKernel318
