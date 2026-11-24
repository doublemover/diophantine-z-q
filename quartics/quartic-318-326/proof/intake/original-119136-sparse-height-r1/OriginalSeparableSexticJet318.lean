module
public import OriginalSexticJetMarked318

/-! Certificate intake without a physically named or numerically reconstructed
splitting field. This does not choose actual geometric branch labels: it proves
the residue arithmetic is independent of such geometric choices. -/
public section
noncomputable section

namespace OriginalSeparableSexticJet318

open Polynomial OriginalSexticJetResidues318
open scoped BigOperators

variable {E : Type*} [Field E]

structure Data (E : Type*) [Field E] where
  F : E[X]
  G : E[X]
  degree : F.natDegree = 6
  jet_degree : G.natDegree ≤ 6
  inverse : E[X]
  inverse_quotient : E[X]
  inverse_relation : inverse * F.derivative - 1 = F * inverse_quotient
  remainder : Fin 3 → E[X]
  small : ∀ i, (remainder i).natDegree ≤ 5
  relation : ∀ i : Fin 3, ∃ Q : E[X], X ^ (i : ℕ) * G - (remainder i) * F.derivative = F * Q

theorem separable (J : Data E) : J.F.Separable := by
  change IsCoprime J.F J.F.derivative
  refine ⟨-J.inverse_quotient, J.inverse, ?_⟩
  have h := sub_eq_iff_eq_add.mp J.inverse_relation
  rw [h]
  ring

@[expose] def splittingCertificate (J : Data E) :
    OriginalSexticJetMarked318.Certificate E J.F.SplittingField := by
  classical
  let K := J.F.SplittingField
  let σ : E →+* K := algebraMap E K
  let f := J.F.map σ
  have hsplit : f.Splits := Polynomial.SplittingField.splits J.F
  have hn : f.roots.Nodup := Polynomial.nodup_roots ((separable J).map)
  let s := f.roots.toFinset
  have hs : s.card = 6 := by
    rw [Multiset.toFinset_card_of_nodup hn, ← hsplit.natDegree_eq_card_roots, Polynomial.natDegree_map, J.degree]
  let e : s ≃ Fin 6 := Finset.equivFinOfCardEq hs
  let a : Fin 6 → K := fun i => (e.symm i).1
  refine ⟨J.F, J.G, J.jet_degree, J.F.leadingCoeff, leadingCoeff_ne_zero.mpr (separable J).ne_zero,
    a, (fun _ _ h => e.symm.injective (Subtype.ext h)), ?_, J.remainder, J.small, J.relation⟩
  have hprod : (f.roots.map (fun x => X - C x)).prod = ∏ i, (X - C (a i)) := by
    calc
      _ = ∏ x ∈ s, (X - C x) := by
        rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hn]
      _ = ∏ x : s, (X - C x.val) := (Finset.prod_coe_sort (s := s) (f := fun x : K => X - C x)).symm
      _ = _ := Fintype.prod_equiv e _ _ (fun x => by simp [a])
  have hl : f.leadingCoeff = σ J.F.leadingCoeff := leadingCoeff_map σ
  change f = split (σ J.F.leadingCoeff) a
  rw [split, ← hl, ← hprod]
  exact hsplit.eq_prod_roots

open OriginalSexticJetMarked318 in
theorem moment_transport (J : Data E) (i : Fin 3) :
    algebraMap E J.F.SplittingField (-2 * ((J.remainder i).coeff 5 / J.F.leadingCoeff)) =
      branchMoment (splittingCertificate J) i := by
  exact moment_eq_branch (splittingCertificate J) i

open OriginalSexticJetMarked318 in
theorem determinant_transport (J : Data E) :
    algebraMap E J.F.SplittingField (rawB (splittingCertificate J)) =
      branchMoment (splittingCertificate J) 0 * branchMoment (splittingCertificate J) 2 -
      branchMoment (splittingCertificate J) 1 ^ 2 := rawB_eq_branch _

end OriginalSeparableSexticJet318

#print axioms OriginalSeparableSexticJet318.separable
#print axioms OriginalSeparableSexticJet318.moment_transport
#print axioms OriginalSeparableSexticJet318.determinant_transport
