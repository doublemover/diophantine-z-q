module
public import ActualSourceHOneGeometricSigns318
public import TwoChartHOneFunctoriality318
public import CharacterSignGlobal318

public section
noncomputable section
namespace OriginalCharacterPullbackLines318
open AlgebraicGeometry CategoryTheory
open SourceTwistArithmetic318 SourceHOneCharacterIndices318
open ActualSourceHOneCharacterAction318 ActualSourceHOneCharacterProjectors318
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Target := CompletedCharacterSchemeMaps318.Target
local instance targetIntegral (i : Fin 4) : IsIntegral (Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance finiteChartAffine (i : Fin 4) :
    IsAffine (ShortAffineScheme318.scheme (publishedA i) (publishedB i)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of
    (ShortAffineJacobian318.Ring (publishedA i) (publishedB i)))))
local instance infinityChartAffine (i : Fin 4) :
    IsAffine (InfinitySmooth318.scheme (publishedA i) (publishedB i)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of
    (InfinityChart318.Ring (publishedA i) (publishedB i)))))

abbrev finiteOpen (i : Fin 4) : (Target i).Opens :=
  (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).opensRange
abbrev infinityOpen (i : Fin 4) : (Target i).Opens :=
  (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)).opensRange

theorem target_cover (i : Fin 4) : finiteOpen i ⊔ infinityOpen i = ⊤ := by
  apply top_unique
  intro x hx
  rcases WeierstrassGluing318.charts_cover (publishedA i) (publishedB i) x with ha | hb
  · exact Or.inl ha
  · exact Or.inr hb

theorem target_boundary_surjective (i : Fin 4) : Function.Surjective
    (MayerVietorisSectionKernel318.sectionBoundary (StructureAdditiveSheaf318.sheaf (Target i))
      (finiteOpen i) (infinityOpen i) (target_cover i)) :=
  AffineCoverHOnePresentation318.boundary_surjective (finiteOpen i) (infinityOpen i)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)))
    (target_cover i)

/-- All five source characters are tested against this exact omitted-root flip. -/
theorem epsilon_flip (i : Fin 4) (j : Index) :
    epsilon j (SourceCharacterFields318.flip i) = if j = some i then 1 else -1 := by
  classical
  cases j with
  | none =>
    fin_cases i <;>
      norm_num [epsilon,SourceHOneCharacterIndices318.support,
        SourceCharacterFields318.flip,Fin.prod_univ_succ]
  | some j =>
    rw [epsilon,SourceHOneCharacterIndices318.support,SourceCharacterFields318.complement_eq]
    fin_cases i <;> fin_cases j <;>
      norm_num [SourceTwistArithmetic318.complement,SourceCharacterFields318.flip]

/-- The full original target H1 pulls into the actual fixed space of its original omitted-root involution. -/
theorem pullback_fixed (i : Fin 4) (x : SheafCohomologyRetraction318.structureH (Target i) 1) :
    action (SourceCharacterFields318.flip i) (ActualSourceHOnePullbacks318.characterPullback i x) =
      ActualSourceHOnePullbacks318.characterPullback i x := by
  rw [← ActualSourceHOneGeometricSigns318.geometric_action]
  exact TwoChartHOneFunctoriality318.deck_invariant
    (ContactGlobalSigns318.map units (SourceCharacterFields318.flip i))
    (CompletedCharacterGlobal318.completedMap i) (CharacterSignGlobal318.omitted i)
    (finiteOpen i) (infinityOpen i) (target_cover i) (target_boundary_surjective i) x

/-- On the exact five-coordinate basis, being fixed by the omitted flip singles out one line. -/
theorem fixed_iff_line (i : Fin 4) (y : ActualSourceHOnePullbacks318.SourceHOne) :
    action (SourceCharacterFields318.flip i) y = y ↔ ∃ q : ℚ, y = q • characterClass (some i) := by
  classical
  constructor
  · intro hy
    obtain ⟨q,hq⟩ := character_spanning y
    have hzero : ∀ j : Index, j ≠ some i → q j = 0 := by
      intro j hji
      have ha : action (SourceCharacterFields318.flip i) y =
          ∑ k : Index, (q k * epsilon k (SourceCharacterFields318.flip i)) • characterClass k := by
        rw [hq]
        simp only [map_sum,map_smul,action_characterClass,smul_smul]
      have hp := congrArg (projector j) hy
      rw [ha,hq,projector_sum,projector_sum,epsilon_flip,if_neg hji] at hp
      simp only [mul_neg,mul_one] at hp
      have hn := ActualSourceHOneResidueBasis318.character_coordinates_nonzero j
      have hz : (-q j - q j) • characterClass j = 0 := by
        rw [sub_smul,hp,sub_self]
      rcases smul_eq_zero.mp hz with he | he
      · linarith
      · exact (hn he).elim
    refine ⟨q (some i),?_⟩
    rw [hq]
    exact Finset.sum_eq_single (some i) (fun j _ hji => by rw [hzero j hji,zero_smul])
      (fun h => False.elim (h (Finset.mem_univ _)))
  · rintro ⟨q,rfl⟩
    rw [map_smul,action_characterClass,epsilon_flip]
    simp

/-- The four original quotient pullbacks now land in their exact, nonzero source character lines. -/
theorem pullback_line (i : Fin 4) (x : SheafCohomologyRetraction318.structureH (Target i) 1) :
    ∃ q : ℚ, ActualSourceHOnePullbacks318.characterPullback i x = q • characterClass (some i) :=
  (fixed_iff_line i _).mp (pullback_fixed i x)

end OriginalCharacterPullbackLines318
