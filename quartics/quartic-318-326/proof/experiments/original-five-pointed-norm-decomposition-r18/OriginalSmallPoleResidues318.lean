module
public import OriginalFinitePoleExpansion318
public import ActualSourceHOneSmallPoles318

public section
noncomputable section
namespace OriginalSmallPoleResidues318
open RootOrderMonomialBasis318 ContactInfinityRegularFractions318 OriginalOverlapResidues318
open OriginalNegativePoleUniqueness318 ActualSourceHOneSmallPoles318
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def position (s : SmallIndex) : ℕ × ThreeIndex := (s.val.2.val-1,s.val.1)

theorem position_injective : Function.Injective position := by
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Prod.snd h
  · apply Fin.ext
    have he := congrArg Prod.fst h
    have hs := s.property.1
    have ht := t.property.1
    change s.val.2.val-1 = t.val.2.val-1 at he
    omega

variable (c : Fin 4 → ℚˣ)

/-- The five actual low-pole residue coefficients, selected from the proven
unique full negative principal part of the original overlap. -/
@[expose] def lowResidues : OverlapRing c →ₗ[ℚ] (SmallIndex → ℚ) where
  toFun x s := residues c x (position s)
  map_add' x y := by funext s; simp only [map_add,Finsupp.add_apply,Pi.add_apply]
  map_smul' q x := by funext s; simp only [map_smul,Finsupp.smul_apply,Pi.smul_apply]

theorem low_infinity (b : InfinityRing c) :
    lowResidues c (InfinityOverlapLocalization318.toOpen c b) = 0 := by
  funext s
  change residues c (infinityLinear c b) (position s) = 0
  rw [residues_infinity] <;> rfl

theorem low_zero_pole (q : ℚ) (i : ThreeIndex) : lowResidues c (poleTerm c q 0 i) = 0 := by
  have h : poleTerm c q 0 i = InfinityOverlapLocalization318.toOpen c
      (algebraMap ℚ (InfinityRing c) q * ContactHOneOrderBases318.infinityBasis c i) := by
    simp only [poleTerm,pow_zero,mul_one,map_mul,RingHom.map_rat_algebraMap]
  rw [h,low_infinity]

/-- Every high finite-chart pole has zero low residues, with the zero-pole
case treated through the actual infinity ring. -/
theorem low_high_pole (q : ℚ) (k : ℕ) (i : ThreeIndex)
    (hk : ContactFinitePoleReduction318.weight i ≤ k) : lowResidues c (poleTerm c q k i) = 0 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    exact low_zero_pole c q i
  · have hkpos : 0 < k := by omega
    funext s
    change residues c (poleTerm c q k i) (position s) = 0
    rw [residues_pole c q k i hkpos]
    have hne : (k-1,i) ≠ position s := by
      intro he
      have hi := congrArg Prod.snd he
      have hp := congrArg Prod.fst he
      change i = s.val.1 at hi
      change k-1 = s.val.2.val-1 at hp
      have hspos := s.property.1
      have hslt := s.property.2
      rw [hi] at hk
      omega
    simp only [Finsupp.single_apply,hne,Ne.symm hne,ite_false]

/-- The low residue map kills the image of every element of the entire original
finite chart, using all sixteen basis coefficients and all polynomial powers. -/
theorem low_finite (a : ContactKummerOrder318.SourceOrder c) :
    lowResidues c (SourceOpenFractionField318.orderToOpen c a) = 0 := by
  rw [OriginalFinitePoleExpansion318.finite_expansion,map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro m _
  apply low_high_pole
  have h := OriginalFinitePoleExpansion318.weight_drop_le s
  omega

/-- Each small original representative has its literal Kronecker residue,
without invoking geometric genus or target-cohomology nonvanishing. -/
theorem low_small_pole (q : ℚ) (s t : SmallIndex) :
    lowResidues c (poleTerm c q s.val.2.val s.val.1) t = if s = t then q else 0 := by
  classical
  change residues c (poleTerm c q s.val.2.val s.val.1) (position t) = _
  rw [residues_pole c q _ _ s.property.1]
  change Finsupp.single (position s) q (position t) = _
  by_cases h : s = t
  · subst t
    simp
  · simp only [Finsupp.single_apply,position_injective.eq_iff,h,Ne.symm h,ite_false]

@[expose] def fiveRepresentatives : (SmallIndex → ℚ) →ₗ[ℚ] OverlapRing c where
  toFun q := ∑ s, poleTerm c (q s) s.val.2.val s.val.1
  map_add' q r := by
    simp only [poleTerm,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' q r := by
    simp only [poleTerm,Pi.smul_apply,Algebra.smul_def,map_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring

theorem low_fiveRepresentatives (q : SmallIndex → ℚ) : lowResidues c (fiveRepresentatives c q) = q := by
  classical
  funext t
  change lowResidues c (∑ s, poleTerm c (q s) s.val.2.val s.val.1) t = q t
  rw [map_sum]
  simp only [Finset.sum_apply,low_small_pole]
  simp

end OriginalSmallPoleResidues318
