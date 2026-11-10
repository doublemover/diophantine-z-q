module
public import OriginalCharacterPullbackLines318
public import FifthSignGlobal318
public import FifthCompletedProper318

public section
noncomputable section
namespace OriginalFifthPullbackLine318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open SourceHOneCharacterIndices318 ActualSourceHOneCharacterAction318
open ActualSourceHOneCharacterProjectors318 FifthCharacterShortPolynomial318
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Target := FifthCompletedGlobal318.Target
local instance targetIntegral : IsIntegral Target := FifthCompletedProper318.target_proper_integral.2
local instance finiteChartAffine : IsAffine (ShortAffineScheme318.scheme A B) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B))))
local instance infinityChartAffine : IsAffine (InfinitySmooth318.scheme A B) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (InfinityChart318.Ring A B))))
abbrev finiteOpen : Target.Opens := (WeierstrassGluing318.finiteChart A B).opensRange
abbrev infinityOpen : Target.Opens := (WeierstrassGluing318.infinityChart A B).opensRange

theorem target_cover : finiteOpen ⊔ infinityOpen = ⊤ := by
  apply top_unique
  intro x hx
  rcases WeierstrassGluing318.charts_cover A B x with ha | hb
  · exact Or.inl ha
  · exact Or.inr hb

theorem target_boundary_surjective : Function.Surjective
    (MayerVietorisSectionKernel318.sectionBoundary (StructureAdditiveSheaf318.sheaf Target)
      finiteOpen infinityOpen target_cover) :=
  AffineCoverHOnePresentation318.boundary_surjective finiteOpen infinityOpen
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B)) target_cover

/-- The full rational character matches the original field-valued character, including its normalization. -/
theorem sign_matches (b : Fin 4 → Bool) : FifthSignAffine318.sign b =
    algebraMap ℚ (RatFunc ℚ) (epsilon none b) := by
  change (∏ i : Fin 4, if b i then (-1 : RatFunc ℚ) else 1) =
    algebraMap ℚ (RatFunc ℚ) (∏ i : Fin 4, if b i then (-1 : ℚ) else 1)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp only [map_neg,map_one]

/-- Every original positive full-product sign fixes the actual fifth-H1 pullback. -/
theorem pullback_fixed (b : Fin 4 → Bool) (hb : epsilon none b = 1)
    (x : SheafCohomologyRetraction318.structureH Target 1) :
    action b (ActualSourceHOnePullbacks318.fifthPullback x) =
      ActualSourceHOnePullbacks318.fifthPullback x := by
  have hs : FifthSignAffine318.sign b = 1 := by rw [sign_matches,hb,map_one]
  rw [← ActualSourceHOneGeometricSigns318.geometric_action]
  exact TwoChartHOneFunctoriality318.deck_invariant (ContactGlobalSigns318.map units b)
    FifthCompletedGlobal318.map (FifthSignGlobal318.positive b hs)
    finiteOpen infinityOpen target_cover target_boundary_surjective x

theorem even_separates : ∀ i : Fin 4, ∃ b : Fin 4 → Bool,
    epsilon none b = 1 ∧ epsilon (some i) b = -1 := by
  intro i
  fin_cases i
  · refine ⟨![true,true,false,false],?_⟩
    norm_num [epsilon,SourceTwistArithmetic318.complement,Fin.prod_univ_succ]
  · refine ⟨![true,true,false,false],?_⟩
    norm_num [epsilon,SourceTwistArithmetic318.complement,Fin.prod_univ_succ]
  · refine ⟨![false,false,true,true],?_⟩
    norm_num [epsilon,SourceTwistArithmetic318.complement,Fin.prod_univ_succ]
  · refine ⟨![false,false,true,true],?_⟩
    norm_num [epsilon,SourceTwistArithmetic318.complement,Fin.prod_univ_succ]

/-- Among all five actual coordinates, the even-sign fixed subspace is exactly the full-root line. -/
theorem fixed_line (y : ActualSourceHOnePullbacks318.SourceHOne)
    (hy : ∀ b : Fin 4 → Bool, epsilon none b = 1 → action b y = y) :
    ∃ q : ℚ, y = q • characterClass none := by
  classical
  obtain ⟨q,hq⟩ := character_spanning y
  have hzero : ∀ i : Fin 4, q (some i) = 0 := by
    intro i
    obtain ⟨b,hb,hi⟩ := even_separates i
    have ha : action b y = ∑ k : Index, (q k * epsilon k b) • characterClass k := by
      rw [hq]
      simp only [map_sum,map_smul,action_characterClass,smul_smul]
    have hp := congrArg (projector (some i)) (hy b hb)
    rw [ha,hq,projector_sum,projector_sum,hi] at hp
    simp only [mul_neg,mul_one] at hp
    have hz : (-q (some i) - q (some i)) • characterClass (some i) = 0 := by
      rw [sub_smul,hp,sub_self]
    rcases smul_eq_zero.mp hz with he | he
    · linarith
    · exact (ActualSourceHOneResidueBasis318.character_coordinates_nonzero (some i) he).elim
  refine ⟨q none,?_⟩
  rw [hq]
  apply Finset.sum_eq_single none
  · intro j hj hjn
    cases j with
    | none => exact (hjn rfl).elim
    | some i => rw [hzero i,zero_smul]
  · intro hnone
    exact (hnone (Finset.mem_univ _)).elim

/-- The fifth original quotient pullback lands in the exact full-root character line. -/
theorem pullback_line (x : SheafCohomologyRetraction318.structureH Target 1) :
    ∃ q : ℚ, ActualSourceHOnePullbacks318.fifthPullback x = q • characterClass none :=
  fixed_line _ (fun b hb => pullback_fixed b hb x)

end OriginalFifthPullbackLine318
