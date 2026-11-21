module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public section
noncomputable section

open Polynomial

namespace SelectedFullSimpleMonicFiber318

variable {A : Type*} [CommRing A]

/-- An actual inverse for p' in the original root algebra gives a
Bezout identity in the original polynomial ring. Therefore no new
separability premise is needed after specializing its coefficients. -/
theorem separable_of_quotient_derivative_unit (p : A[X])
    (h : IsUnit (AdjoinRoot.mk p p.derivative)) : p.Separable := by
  let u : (AdjoinRoot p)ˣ := h.unit
  obtain ⟨w,hw⟩ := AdjoinRoot.mk_surjective (g:=p) ((u⁻¹:(AdjoinRoot p)ˣ):AdjoinRoot p)
  have hu : (u:AdjoinRoot p)=AdjoinRoot.mk p p.derivative := h.unit_spec
  have hone : AdjoinRoot.mk p (p.derivative*w)=1 := calc
    AdjoinRoot.mk p (p.derivative*w) =
        AdjoinRoot.mk p p.derivative * ((u⁻¹:(AdjoinRoot p)ˣ):AdjoinRoot p) := by rw [map_mul,hw]
    _ = (u:AdjoinRoot p)*((u⁻¹:(AdjoinRoot p)ˣ):AdjoinRoot p) :=
      congrArg (fun b : AdjoinRoot p => b*((u⁻¹:(AdjoinRoot p)ˣ):AdjoinRoot p)) hu.symm
    _ = 1 := Units.mul_inv u
  have hd : p∣p.derivative*w-1 := (AdjoinRoot.mk_eq_zero (f:=p)).mp (by
    rw [map_sub,hone,map_one,sub_self])
  obtain ⟨z,hz⟩ := hd
  apply (Polynomial.separable_def' p).mpr
  refine ⟨-z,w,?_⟩
  calc
    (-z)*p+w*p.derivative = p.derivative*w-p*z := by ring
    _=1 := by rw [←hz] <;> ring

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]

/-- Every geometric point of the finite monogenic fiber is counted
once. The degree stays that of the original monic p even when the
literal coefficient specialization has a nontrivial kernel. -/
theorem full_fiber_card (c : A→+*Ω) (p : A[X]) (hp : p.Monic)
    (h : IsUnit (AdjoinRoot.mk p p.derivative)) :
    (p.map c).roots.toFinset.card = p.natDegree := by
  have hs : (p.map c).Separable := (separable_of_quotient_derivative_unit p h).map
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
  apply IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff c
  rw [show p.leadingCoeff=1 from hp]
  exact isUnit_one

/-- Every counted actual coordinate has exactly its own evaluation of
the same original root algebra over c; there is no lift from a
substitute polynomial or a duplicate marked root. -/
theorem root_has_unique_original_eval (c : A→+*Ω) (p : A[X])
    {x : Ω} (hx : x∈(p.map c).roots.toFinset) :
    ∃! f : AdjoinRoot p→+*Ω, f.comp (AdjoinRoot.of p)=c ∧ f (AdjoinRoot.root p)=x := by
  have hr : x∈(p.map c).roots := Multiset.mem_toFinset.mp hx
  have he : p.eval₂ c x=0 := by
    rw [←Polynomial.eval_map]
    exact (Polynomial.IsRoot.def).mp (Polynomial.isRoot_of_mem_roots hr)
  let f : AdjoinRoot p→+*Ω := AdjoinRoot.lift c x he
  have hf : f.comp (AdjoinRoot.of p)=c := AdjoinRoot.lift_comp_of he
  have hfx : f (AdjoinRoot.root p)=x := AdjoinRoot.lift_root he
  refine ⟨f,⟨hf,hfx⟩,?_⟩
  intro g hg
  exact AdjoinRoot.ringHom_ext (hg.1.trans hf.symm) (hg.2.trans hfx.symm)

end SelectedFullSimpleMonicFiber318

#print axioms SelectedFullSimpleMonicFiber318.separable_of_quotient_derivative_unit
#print axioms SelectedFullSimpleMonicFiber318.full_fiber_card
#print axioms SelectedFullSimpleMonicFiber318.root_has_unique_original_eval
