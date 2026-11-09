module
public import IntegralFinitePairGeometry318
public import LocalSectionCompatibility318
public section
noncomputable section
namespace IntegralGlobalBicanonicalPair318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open IntegralGluedModel318 IntegralGluedDifferentialFrames318 IntegralGluedChartGeometry318
open IntegralBranchCoordinates318 IntegralBranchBicanonical318
open IntrinsicTensorChartSections318 IntegralOverlapChartMaps318
open IntegralAllBranchOverlapMaps318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
abbrev tensor := IntegralGluedTensorSections318.tensor R c
@[expose] def branchCoefficient (i : Fin 4) (n : Fin 2) : B R c i :=
  (VerticalSection318.J : B R c i)^2 *
    (if n=0 then coefficient0 R c i else coefficient1 R c i)
@[expose] def branchQ (i : Fin 4) (n : Fin 2) : Γ(tensor R c,branchEmbedding R c i ''ᵁ ⊤) :=
  weightedSquare (branchEmbedding R c i) (structureMap R c) (branch_structure R c i)
    (branchCoefficient R c i n) (KaehlerDifferential.D R (B R c i) (sourceCoordinate R c i))
@[expose] def infinityCoefficient (n : Fin 2) : IntegralInfinityChart318.Order R c :=
  (VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
    (if n=0 then IntegralInfinityCoefficients318.coefficient0 R c
      else IntegralInfinityCoefficients318.coefficient1 R c)
@[expose] def infinityQ (n : Fin 2) : Γ(tensor R c,infinityChart R c ''ᵁ ⊤) :=
  weightedSquare (infinityChart R c) (structureMap R c) (infinityChart_structure R c)
    (infinityCoefficient R c n)
    (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c) (IntegralInfinityChart318.coordinate R c))

private theorem agree_of_common {X : Scheme.{u}} (M : X.Modules) (U V W : X.Opens)
    (s : Γ(M,U)) (t : Γ(M,V)) (hU : W≤U) (hV : W≤V) (hW : W=U⊓V)
    (he : M.presheaf.map (homOfLE hU).op s=M.presheaf.map (homOfLE hV).op t) :
    LocalSectionCompatibility318.Agree M U V s t := by
  subst W
  exact he

/-- Every distinct finite pair is compared on its full product localization,
with the original coefficient and differential maps, before sheaf gluing. -/
theorem finite_pair (i j : Fin 4) (hij : i≠j) (n : Fin 2) :
    LocalSectionCompatibility318.Agree (tensor R c)
      (branchEmbedding R c i ''ᵁ ⊤) (branchEmbedding R c j ''ᵁ ⊤)
      (branchQ R c i n) (branchQ R c j n) := by
  let e := IntegralFinitePairGeometry318.embedding R c i j
  let f := IntegralFinitePairGeometry318.leftMap R c i j
  let g := IntegralFinitePairGeometry318.rightMap R c i j
  have hL : e ''ᵁ ⊤ ≤ branchEmbedding R c i ''ᵁ ⊤ := by
    rw [show e=Spec.map (CommRingCat.ofHom f.toRingHom) ≫ branchEmbedding R c i from
      (IntegralFinitePairGeometry318.left_route R c i j).symm]
    exact OpenChartSections318.imageLE _ _
  have hR : e ''ᵁ ⊤ ≤ branchEmbedding R c j ''ᵁ ⊤ := by
    rw [show e=Spec.map (CommRingCat.ofHom g.toRingHom) ≫ branchEmbedding R c j from
      (IntegralFinitePairGeometry318.right_route R c i j).symm]
    exact OpenChartSections318.imageLE _ _
  apply agree_of_common (tensor R c) _ _ (e ''ᵁ ⊤) _ _ hL hR
    (IntegralFinitePairGeometry318.full_intersection R c i j)
  unfold branchQ
  rw [weightedSquare_restrict_to _ _ _ f e (IntegralFinitePairGeometry318.over_base R c i j)
      (IntegralFinitePairGeometry318.left_route R c i j) hL,
    weightedSquare_restrict_to _ _ _ g e (IntegralFinitePairGeometry318.over_base R c i j)
      (IntegralFinitePairGeometry318.right_route R c i j) hR]
  apply IntegralBranchTensorTransport318.scaled_agreement
  · exact (IntegralFinitePairGeometry318.left_polynomial R c i j _).trans
      (IntegralFinitePairGeometry318.right_polynomial R c i j _).symm
  · exact (IntegralFinitePairGeometry318.left_polynomial R c i j _).trans
      (IntegralFinitePairGeometry318.right_polynomial R c i j _).symm
  · change IsUnit (IntegralFinitePairGeometry318.leftMap R c i j
      (algebraMap R[X] (B R c i) (quartic R)))
    rw [IntegralFinitePairGeometry318.left_polynomial]
    exact IntegralFinitePairGeometry318.quartic_unit R c i j hij

/-- Every finite/infinity pair is compared on the full genuine pushout
intersection, using the already constructed branch-zero/infinity transition. -/
theorem branch_infinity (i : Fin 4) (n : Fin 2) :
    LocalSectionCompatibility318.Agree (tensor R c)
      (branchEmbedding R c i ''ᵁ ⊤) (infinityChart R c ''ᵁ ⊤)
      (branchQ R c i n) (infinityQ R c n) := by
  have hW : overlapChart R c ''ᵁ ⊤ =
      (branchEmbedding R c i ''ᵁ ⊤) ⊓ (infinityChart R c ''ᵁ ⊤) := by
    apply Opens.ext
    change Set.range (overlapChart R c) =
      Set.range (branchEmbedding R c i) ∩ Set.range (infinityChart R c)
    exact IntegralAllBranchChartGeometry318.full_infinity_intersection R c i
  apply agree_of_common (tensor R c) _ _ _ _ _
    (IntegralAllBranchChartGeometry318.branchLE R c i) (infinityLE R c) hW
  unfold branchQ infinityQ
  rw [weightedSquare_restrict_to _ _ _ (branchMap R c i) (overlapChart R c)
      (overlap_over_base R c) (IntegralAllBranchChartGeometry318.branch_route R c i)
      (IntegralAllBranchChartGeometry318.branchLE R c i),
    weightedSquare_restrict_to _ _ _ (infinityMap R c) (overlapChart R c)
      (overlap_over_base R c) (infinity_route R c) (infinityLE R c)]
  have he := IntegralAllBranchChartGeometry318.common_pair R c i 0 n
  refine he.trans ?_
  rw [branchMap_zero]
  by_cases hn : n=0
  · simp only [hn,ite_true,infinityCoefficient]
    exact IntegralOverlapSheafCompatibility318.section0_agreement R c
      (overlapChart R c) (structureMap R c) (overlap_over_base R c)
  · simp only [hn,ite_false,infinityCoefficient]
    exact IntegralOverlapSheafCompatibility318.section1_agreement R c
      (overlapChart R c) (structureMap R c) (overlap_over_base R c)

@[expose] def opens (i : Option (Fin 4)) : (scheme R c).Opens := embedding R c i ''ᵁ ⊤
@[expose] def localQ (n : Fin 2) : (i : Option (Fin 4)) → Γ(tensor R c,opens R c i)
  | some i => branchQ R c i n
  | none => infinityQ R c n

theorem cover (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    ⊤ ≤ iSup (opens R c) := by
  intro x _
  rcases frames_cover R c hN x with ⟨i,q,hq⟩|⟨q,hq⟩
  · exact Opens.mem_iSup.mpr ⟨some i,q,trivial,hq⟩
  · exact Opens.mem_iSup.mpr ⟨none,q,trivial,hq⟩

theorem compatible (n : Fin 2) :
    TopCat.Presheaf.IsCompatible (tensor R c).presheaf (opens R c) (localQ R c n) := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact LocalSectionCompatibility318.symm _ _ _ _ _ (branch_infinity R c j n)
  | some i =>
    cases j with
    | none => exact branch_infinity R c i n
    | some j =>
      by_cases hij : i=j
      · subst j; rfl
      · exact finite_pair R c i j hij n

/-- The two original J²-scaled bicanonical sections on the ACTUAL integral
whole-source/infinity model. Existence uses full pairwise intersections and
the literal separation-unit hypothesis, not properness or a generic model. -/
@[expose] def q (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (n : Fin 2) : Γ(tensor R c,⊤) :=
  ModuleGlobalSections318.gluedTop (tensor R c) (opens R c) (cover R c hN)
    (localQ R c n) (compatible R c n)

theorem q_restrict (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (n : Fin 2) (i : Option (Fin 4)) :
    (tensor R c).presheaf.map (homOfLE (show opens R c i≤⊤ from le_top)).op
      (q R c hN n)=localQ R c n i :=
  ModuleGlobalSections318.gluedTop_restrict (tensor R c) (opens R c) (cover R c hN)
    (localQ R c n) (compatible R c n) i
end IntegralGlobalBicanonicalPair318
