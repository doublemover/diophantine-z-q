module
public import ActualTwoDescentActualShaPrimaryClassification318
public import ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
public import ActualTwoDescentInfiniteRankSelmerPruefer318
public import AdditiveTorsionTransfer318
public section
noncomputable section
namespace ActualFullPrimarySelmerLowCorank318
open ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualShaPrimaryClassification318
open ActualTwoDescentFiniteRankPrimarySelmerEquivalence318
open ActualTwoDescentInfiniteRankSelmerPruefer318
open ActualTwoDescentActualShaPrimary318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

/-- An explicit low-corank model for the ACTUAL full primary Selmer group,
proved before any global-duality or pointwise-converse input. The finite
cyclic branch is retained: neither Sha finiteness nor rank one is concluded. -/
theorem actual_full_primary_classification (n : ℚ) (hn : n≠0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n)≤8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    (∃ k : ℕ, Nonempty (actualPrimarySelmer n hn ≃+ ZMod (2^k))) ∨
      Nonempty (actualPrimarySelmer n hn ≃+ Additive PrueferTwo) := by
  classical
  by_cases hp : Finite (Point n)
  · letI := hp
    rcases actual_sha_primary_classification n hn hf hb hS with ⟨k,⟨e⟩⟩ | ⟨e⟩
    · let ea : Additive (actualShaPrimary n hn) ≃+ ZMod (2^k) :=
        { toEquiv := e.toEquiv
          map_add' x y := e.map_mul x.toMul y.toMul }
      exact Or.inl ⟨k,⟨(finiteRankPrimarySelmerEquiv n hn).trans ea⟩⟩
    · let ea : Additive (actualShaPrimary n hn) ≃+ Additive PrueferTwo :=
        { toEquiv := e.toEquiv
          map_add' x y := e.map_mul x.toMul y.toMul }
      exact Or.inr ⟨(finiteRankPrimarySelmerEquiv n hn).trans ea⟩
  · letI : Infinite (Point n) := not_finite_iff_infinite.mp hp
    exact Or.inr (actual_infinite_rank_selmer_pruefer n hn hf hb hS)

/-- The same chosen model simultaneously determines every exponent-torsion
cardinality. The quantifier over exponents comes AFTER model selection. -/
theorem actual_full_primary_torsion_models (n : ℚ) (hn : n≠0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n)≤8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    (∃ k : ℕ, ∀ m : ℕ,
      Nat.card (nsmulAddMonoidHom (α:=actualPrimarySelmer n hn) m).ker =
        Nat.card (nsmulAddMonoidHom (α:=ZMod (2^k)) m).ker) ∨
    (∀ m : ℕ,
      Nat.card (nsmulAddMonoidHom (α:=actualPrimarySelmer n hn) m).ker =
        Nat.card (nsmulAddMonoidHom (α:=Additive PrueferTwo) m).ker) := by
  rcases actual_full_primary_classification n hn hf hb hS with ⟨k,⟨e⟩⟩ | ⟨e⟩
  · exact Or.inl ⟨k,fun m => AdditiveTorsionTransfer318.torsion_card_eq e m⟩
  · exact Or.inr (fun m => AdditiveTorsionTransfer318.torsion_card_eq e m)

end ActualFullPrimarySelmerLowCorank318
