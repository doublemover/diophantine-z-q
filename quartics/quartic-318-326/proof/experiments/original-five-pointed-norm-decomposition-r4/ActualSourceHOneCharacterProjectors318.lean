module
public import ActualSourceHOneCharacterAction318

public section
noncomputable section
namespace ActualSourceHOneCharacterProjectors318
open ActualSourceHOnePrincipalRepresentatives318 ActualSourceHOneSmallPoles318
open ActualSourceHOneRationalSpanning318 ActualSourceHOneCharacterAction318
open SourceHOneCharacterIndices318 SourceHOneCharacterRepresentatives318
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector"
  stream.flush

/-- Exact normalized average over every original root-sign pattern. -/
@[expose] def projector (i : Index) : HOne →ₗ[ℚ] HOne :=
  (1/16 : ℚ) • ∑ b : Fin 4 → Bool, epsilon i b • action b

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_characterClass"
  stream.flush

theorem projector_characterClass (i j : Index) :
    projector i (characterClass j) = if i = j then characterClass j else 0 := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_characterClass"
    stream.flush
  simp only [projector,LinearMap.smul_apply,LinearMap.sum_apply,action_characterClass,smul_smul]
  rw [← Finset.sum_smul,epsilon_orthogonality]
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl,smul_smul]
    norm_num
  · simp only [hij,ite_false,zero_smul,smul_zero]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before weighted_character"
  stream.flush

theorem weighted_character (i : Index) (q : ℚ) :
    poleClass q (smallIndex i).val.2.val (smallIndex i).val.1 = q • characterClass i := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof weighted_character"
    stream.flush
  let L : ℚ →ₗ[ℚ] HOne :=
    (ActualSourceHOneFiveSpanning318.poleMap (smallIndex i).val.2.val (smallIndex i).val.1).toRatLinearMap
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR weighted linear map constructed"
    stream.flush
  have h := L.map_smul q (1 : ℚ)
  have hw : poleClass q (smallIndex i).val.2.val (smallIndex i).val.1 =
      q • poleClass 1 (smallIndex i).val.2.val (smallIndex i).val.1 := by
    simpa only [smul_eq_mul,mul_one] using h
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR weighted rational scalar established"
    stream.flush
  rw [hw]
  congr 1
  unfold poleClass characterClass representative
  rw [map_one,one_mul]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before character_spanning"
  stream.flush

/-- All actual source-H1 classes are sums of the five literally identified
character coordinates, in the fixed omitted-root/full-root order. -/
theorem character_spanning (y : HOne) :
    ∃ q : Index → ℚ, y = ∑ i, q i • characterClass i := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof character_spanning"
    stream.flush
  classical
  obtain ⟨q,rfl⟩ := fiveLinear_surjective y
  refine ⟨fun i => q (smallIndex i),?_⟩
  change (∑ s : SmallIndex, poleClass (q s) s.val.2.val s.val.1) = _
  calc
    _ = ∑ i : Index, poleClass (q (smallIndex i)) (smallIndex i).val.2.val (smallIndex i).val.1 :=
      (Fintype.sum_equiv (Equiv.ofBijective smallIndex smallIndex_bijective) _ _ (fun _ => rfl)).symm
    _ = ∑ i : Index, q (smallIndex i) • characterClass i := by
      apply Finset.sum_congr rfl
      intro i _
      exact weighted_character i _

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_sum"
  stream.flush

theorem projector_sum (i : Index) (q : Index → ℚ) :
    projector i (∑ j, q j • characterClass j) = q i • characterClass i := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_sum"
    stream.flush
  classical
  simp only [map_sum,map_smul,projector_characterClass]
  simp

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before sum_projector"
  stream.flush

theorem sum_projector (y : HOne) : ∑ i : Index, projector i y = y := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof sum_projector"
    stream.flush
  obtain ⟨q,hq⟩ := character_spanning y
  rw [hq]
  simp only [projector_sum]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_orthogonal"
  stream.flush

theorem projector_orthogonal (i j : Index) (y : HOne) :
    projector i (projector j y) = if i = j then projector j y else 0 := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_orthogonal"
    stream.flush
  obtain ⟨q,hq⟩ := character_spanning y
  rw [hq,projector_sum,map_smul,projector_characterClass]
  by_cases hij : i = j <;> simp [hij]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_idempotent"
  stream.flush

theorem projector_idempotent (i : Index) (y : HOne) : projector i (projector i y) = projector i y := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_idempotent"
    stream.flush
  simpa using projector_orthogonal i i y

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_of_range"
  stream.flush

theorem projector_of_range (i : Index) (x : (projector i).range) : projector i x.val = x.val := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_of_range"
    stream.flush
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact projector_idempotent i y

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_other_range"
  stream.flush

theorem projector_other_range (i j : Index) (hij : i ≠ j) (x : (projector j).range) :
    projector i x.val = 0 := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_other_range"
    stream.flush
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  simpa only [hij,ite_false] using projector_orthogonal i j y

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before characterDecomposition"
  stream.flush

/-- Unconditional whole-H1 decomposition into the five actual character
projector images. Some images may still be zero: nonvanishing is not assumed. -/
@[expose] def characterDecomposition : HOne ≃ₗ[ℚ] ((i : Index) → (projector i).range) where
  toFun y i := ⟨projector i y,⟨y,rfl⟩⟩
  invFun x := ∑ i, (x i).val
  left_inv y := sum_projector y
  right_inv x := by
    run_tac do
      let stream ← IO.getStderr
      stream.putStrLn "H1_PROJECTOR proof characterDecomposition"
      stream.flush
    funext i
    apply Subtype.ext
    change projector i (∑ j, (x j).val) = (x i).val
    rw [map_sum,Finset.sum_eq_single i]
    · exact projector_of_range i (x i)
    · intro j _ hji
      exact projector_other_range i j (Ne.symm hji) (x j)
    · simp
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact (projector i).map_add x y
  map_smul' q y := by
    funext i
    apply Subtype.ext
    exact (projector i).map_smul q y

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before characterDecomposition_component"
  stream.flush

theorem characterDecomposition_component (y : HOne) (i : Index) :
    ((characterDecomposition y) i).val = projector i y := rfl

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before characterDecomposition_symm"
  stream.flush

theorem characterDecomposition_symm (x : (i : Index) → (projector i).range) :
    characterDecomposition.symm x = ∑ i, (x i).val := rfl

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before projector_range_one_generator"
  stream.flush

/-- Each actual projector image is generated by the corresponding concrete
coordinate, without asserting that this coordinate is nonzero. -/
theorem projector_range_one_generator (i : Index) (x : (projector i).range) :
    ∃ q : ℚ, x.val = q • characterClass i := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof projector_range_one_generator"
    stream.flush
  obtain ⟨y,hy⟩ := x.property
  obtain ⟨q,hq⟩ := character_spanning y
  refine ⟨q i,?_⟩
  rw [← hy,hq,projector_sum]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before CoordinatesNonzero"
  stream.flush

/-- The exact remaining independence obligation, separated from field-level
nonvanishing of representatives. -/
@[expose] def CoordinatesNonzero : Prop := ∀ i : Index, characterClass i ≠ 0

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before coordinateMap"
  stream.flush

@[expose] def coordinateMap : (Index → ℚ) →ₗ[ℚ] HOne where
  toFun q := ∑ i, q i • characterClass i
  map_add' q r := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' q r := by simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul,smul_smul,Finset.smul_sum]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before coordinateMap_surjective"
  stream.flush

theorem coordinateMap_surjective : Function.Surjective coordinateMap := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof coordinateMap_surjective"
    stream.flush
  intro y
  obtain ⟨q,hq⟩ := character_spanning y
  exact ⟨q,hq.symm⟩

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before coordinateMap_injective"
  stream.flush

theorem coordinateMap_injective (hne : CoordinatesNonzero) : Function.Injective coordinateMap := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "H1_PROJECTOR proof coordinateMap_injective"
    stream.flush
  intro q r h
  funext i
  have hi := congrArg (projector i) h
  change projector i (∑ j, q j • characterClass j) = projector i (∑ j, r j • characterClass j) at hi
  rw [projector_sum,projector_sum] at hi
  have hz : (q i-r i) • characterClass i = 0 := by rw [sub_smul,hi,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (hne i))

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR before coordinateEquivalence"
  stream.flush

/-- Conditional only on actual cohomology nonvanishing, not on independence:
the five original character coordinates give a rational basis equivalence. -/
@[expose] def coordinateEquivalence (hne : CoordinatesNonzero) : (Index → ℚ) ≃ₗ[ℚ] HOne :=
  LinearEquiv.ofBijective coordinateMap ⟨coordinateMap_injective hne,coordinateMap_surjective⟩

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "H1_PROJECTOR completed"
  stream.flush

end ActualSourceHOneCharacterProjectors318
