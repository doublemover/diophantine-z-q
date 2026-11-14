module
public import LocalizedPrimitiveSelectedPolynomial318
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public section
noncomputable section
namespace LocalizedSelectedComplementProduct318
open Polynomial
open AdjoinRootSpecializedPoints318
open LocalizedPrimitiveSelectedGraphs318 LocalizedPrimitiveSelectedPolynomial318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

/-- The actual product over ALL distinct independent fiber roots equals
the specialized monic polynomial. Separability supplies multiplicity one;
algebraic closure supplies the full degree, including degree zero. -/
theorem all_root_product (hm : Q.Monic) (hs : Q.Separable)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    (∏ r ∈ allRoots d Q hm v hv, (X-C r.val)) =
      Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv) := by
  classical
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  let p := Q.map V
  have hm' : p.Monic := hm.map V
  have hs' : p.Separable := hs.map
  have he : (∏ r ∈ allRoots d Q hm v hv, (X-C r.val)) =
      ∏ z ∈ p.roots.toFinset, (X-C z) := by
    apply Finset.prod_bij (fun r _ => r.val)
    · intro r hr
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hm'.ne_zero).mpr r.property)
    · intro r hr s hs hrs
      exact Subtype.ext hrs
    · intro z hz
      have hz' : p.eval z = 0 :=
        (Polynomial.mem_roots hm'.ne_zero).mp (Multiset.mem_toFinset.mp hz)
      exact ⟨⟨z,hz'⟩,mem_allRoots d Q hm v hv _,rfl⟩
    · intro r hr
      rfl
  rw [he]
  change ((p.roots.toFinset.val).map (fun z => X-C z)).prod = p
  rw [Multiset.toFinset_val,Multiset.dedup_eq_self.mpr (hs'.nodup_roots)]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm'
    Polynomial.card_roots_eq_natDegree

/-- Canonical selection and its genuine complement partition ALL roots
of the SAME candidate fiber, preserving every factor with multiplicity1.
This is an actual polynomial identity, not just equality of zero sets. -/
theorem selected_mul_complement (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    selectedPolynomial d Q hm S v * selectedPolynomial d Q hm Sᶜ v =
      Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv) := by
  classical
  rw [selectedPolynomial_on_open d Q hm S v hv,
    selectedPolynomial_on_open d Q hm Sᶜ v hv]
  unfold fiberPolynomial selectedRoots
  change (∏ r ∈ allRoots d Q hm v hv with point d Q v hv r ∈ S, (X-C r.val)) *
    (∏ r ∈ allRoots d Q hm v hv with ¬point d Q v hv r ∈ S, (X-C r.val)) = _
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact all_root_product d Q hm hs v hv

/-- If the genuine complementary factor is one at a base point, EVERY
independent root in that fiber is selected. No source surjectivity is
assumed in this implication. -/
theorem selected_of_complement_eq_one (hm : Q.Monic)
    (S : Set (OpenRoots d Q)) (q : OpenRoots d Q)
    (hcomp : selectedPolynomial d Q hm Sᶜ q.val.val.1 = 1) : q ∈ S := by
  classical
  by_contra hq
  have hz := (selected_root_iff d Q hm Sᶜ q).mpr hq
  rw [hcomp,Polynomial.eval_one] at hz
  exact one_ne_zero hz
end LocalizedSelectedComplementProduct318
