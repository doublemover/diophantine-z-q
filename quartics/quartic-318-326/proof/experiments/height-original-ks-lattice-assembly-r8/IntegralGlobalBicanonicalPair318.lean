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

/-- Perform restriction and transitivity with abstract affine rings first,
so the concrete integral orders are not unfolded by a dependent rewrite. -/
theorem weighted_agree_of_common {Y : Scheme.{u}}
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (k : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion k]
    (e : Spec (CommRingCat.of T) ⟶ Y) [IsOpenImmersion e]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (hj : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hk : k ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (he : e ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (f : A →ₐ[R] T) (g : B →ₐ[R] T)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom))]
    (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j=e)
    (hg : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ k=e)
    (hL : e ''ᵁ ⊤ ≤ j ''ᵁ ⊤) (hR : e ''ᵁ ⊤ ≤ k ''ᵁ ⊤)
    (hW : e ''ᵁ ⊤=(j ''ᵁ ⊤)⊓(k ''ᵁ ⊤))
    (a : A) (b : B) (ω : KaehlerDifferential R A) (η : KaehlerDifferential R B)
    (hab : weightedSquare e p he (f a) (AlgHomDifferential318.map f ω)=
      weightedSquare e p he (g b) (AlgHomDifferential318.map g η)) :
    LocalSectionCompatibility318.Agree
      (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p))
      (j ''ᵁ ⊤) (k ''ᵁ ⊤) (weightedSquare j p hj a ω) (weightedSquare k p hk b η) := by
  apply agree_of_common _ _ _ (e ''ᵁ ⊤) _ _ hL hR hW
  exact (weightedSquare_restrict_to j p hj f e he hf hL a ω).trans
    (hab.trans (weightedSquare_restrict_to k p hk g e he hg hR b η).symm)

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
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
    change Set.range e ⊆ Set.range (branchEmbedding R c i)
    rintro x ⟨z,rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom f.toRingHom) z,?_⟩
    exact congrArg (fun k => k z) (IntegralFinitePairGeometry318.left_route R c i j)
  have hR : e ''ᵁ ⊤ ≤ branchEmbedding R c j ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
    change Set.range e ⊆ Set.range (branchEmbedding R c j)
    rintro x ⟨z,rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) z,?_⟩
    exact congrArg (fun k => k z) (IntegralFinitePairGeometry318.right_route R c i j)
  apply weighted_agree_of_common R (branchEmbedding R c i) (branchEmbedding R c j)
    e (structureMap R c) (branch_structure R c i) (branch_structure R c j)
    (IntegralFinitePairGeometry318.over_base R c i j) f g
    (IntegralFinitePairGeometry318.left_route R c i j)
    (IntegralFinitePairGeometry318.right_route R c i j) hL hR
    (IntegralFinitePairGeometry318.full_intersection R c i j)
    (branchCoefficient R c i n) (branchCoefficient R c j n)
    (KaehlerDifferential.D R (B R c i) (sourceCoordinate R c i))
    (KaehlerDifferential.D R (B R c j) (sourceCoordinate R c j))
  apply IntegralBranchTensorTransport318.scaled_agreement
  · exact (IntegralFinitePairGeometry318.left_polynomial R c i j _).trans
      (IntegralFinitePairGeometry318.right_polynomial R c i j _).symm
  · exact (IntegralFinitePairGeometry318.left_polynomial R c i j _).trans
      (IntegralFinitePairGeometry318.right_polynomial R c i j _).symm
  · change IsUnit (IntegralFinitePairGeometry318.leftMap R c i j
      (algebraMap (Polynomial R) (B R c i) (quartic R)))
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
    simp only [Scheme.Hom.image_top_eq_opensRange]
    apply Opens.ext
    change Set.range (overlapChart R c) =
      Set.range (branchEmbedding R c i) ∩ Set.range (infinityChart R c)
    exact IntegralAllBranchChartGeometry318.full_infinity_intersection R c i
  apply weighted_agree_of_common R (branchEmbedding R c i) (infinityChart R c)
    (overlapChart R c) (structureMap R c) (branch_structure R c i)
    (infinityChart_structure R c) (overlap_over_base R c)
    (branchMap R c i) (infinityMap R c)
    (IntegralAllBranchChartGeometry318.branch_route R c i) (infinity_route R c)
    (IntegralAllBranchChartGeometry318.branchLE R c i) (infinityLE R c) hW
    (branchCoefficient R c i n) (infinityCoefficient R c n)
    (KaehlerDifferential.D R (B R c i) (sourceCoordinate R c i))
    (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c)
      (IntegralInfinityChart318.coordinate R c))
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

/-- Universe-lift only the finite index type required by the existing generic
module-gluing API; the actual opens and actual local sections are unchanged. -/
@[expose] abbrev liftedOpens (i : ULift.{u} (Option (Fin 4))) : (scheme R c).Opens :=
  opens R c i.down

theorem liftedCover
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    ⊤ ≤ iSup (liftedOpens R c) := by
  intro x hx
  rcases Opens.mem_iSup.mp (cover R c hN hx) with ⟨i,hi⟩
  exact Opens.mem_iSup.mpr ⟨ULift.up i,hi⟩

@[expose] abbrev liftedLocalQ (n : Fin 2) (i : ULift.{u} (Option (Fin 4))) :
    Γ(tensor R c,liftedOpens R c i) := localQ R c n i.down

theorem liftedCompatible (n : Fin 2) :
    TopCat.Presheaf.IsCompatible (tensor R c).presheaf
      (liftedOpens R c) (liftedLocalQ R c n) := by
  intro i j
  exact compatible R c n i.down j.down

/-- The two original J²-scaled bicanonical sections on the ACTUAL integral
whole-source/infinity model. Existence uses full pairwise intersections and
the literal separation-unit hypothesis, not properness or a generic model. -/
@[expose] def q (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (n : Fin 2) : Γ(tensor R c,⊤) :=
  ModuleGlobalSections318.gluedTop (tensor R c) (liftedOpens R c) (liftedCover R c hN)
    (liftedLocalQ R c n) (liftedCompatible R c n)

theorem q_restrict (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (n : Fin 2) (i : Option (Fin 4)) :
    (tensor R c).presheaf.map (homOfLE (show opens R c i≤⊤ from le_top)).op
      (q R c hN n)=localQ R c n i := by
  simpa only [q, liftedOpens, liftedLocalQ] using
    ModuleGlobalSections318.gluedTop_restrict (tensor R c) (liftedOpens R c)
    (liftedCover R c hN) (liftedLocalQ R c n) (liftedCompatible R c n) (ULift.up i)
end IntegralGlobalBicanonicalPair318
