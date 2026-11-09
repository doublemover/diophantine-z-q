module
public import IntegralAllBranchChartGeometry318
public import FinitePairOverlap318
public section
noncomputable section
namespace IntegralFinitePairGeometry318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318 IntegralBranchDenominatorCover318
open IntegralBranchCoordinates318 IntegralGluedModel318 IntegralGluedDifferentialFrames318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ) (i j : Fin 4)
abbrev Pair := Localization.Away (denominator R c i * denominator R c j)

theorem pair_units :
    IsUnit (algebraMap (SourceOrder R c) (Pair R c i j) (denominator R c i)) ∧
    IsUnit (algebraMap (SourceOrder R c) (Pair R c i j) (denominator R c j)) := by
  have h : IsUnit (algebraMap (SourceOrder R c) (Pair R c i j)
      (denominator R c i * denominator R c j)) :=
    isUnit_iff_exists_inv.mpr ⟨IsLocalization.Away.invSelf
      (denominator R c i * denominator R c j), IsLocalization.Away.mul_invSelf _⟩
  rw [map_mul] at h
  exact isUnit_mul_iff.mp h

@[expose] def leftMap : B R c i →ₐ[R] Pair R c i j where
  __ := IsLocalization.Away.lift (g := algebraMap (SourceOrder R c) (Pair R c i j))
    (denominator R c i) (pair_units R c i j).1
  commutes' r := by
    change IsLocalization.Away.lift (g := algebraMap (SourceOrder R c) (Pair R c i j))
      (denominator R c i) (pair_units R c i j).1
      (algebraMap (SourceOrder R c) (B R c i) (algebraMap R (SourceOrder R c) r)) = _
    rw [IsLocalization.Away.lift_eq,←IsScalarTower.algebraMap_apply]
@[expose] def rightMap : B R c j →ₐ[R] Pair R c i j where
  __ := IsLocalization.Away.lift (g := algebraMap (SourceOrder R c) (Pair R c i j))
    (denominator R c j) (pair_units R c i j).2
  commutes' r := by
    change IsLocalization.Away.lift (g := algebraMap (SourceOrder R c) (Pair R c i j))
      (denominator R c j) (pair_units R c i j).2
      (algebraMap (SourceOrder R c) (B R c j) (algebraMap R (SourceOrder R c) r)) = _
    rw [IsLocalization.Away.lift_eq,←IsScalarTower.algebraMap_apply]

@[simp] theorem left_source (a : SourceOrder R c) :
    leftMap R c i j (algebraMap (SourceOrder R c) (B R c i) a) =
      algebraMap (SourceOrder R c) (Pair R c i j) a := IsLocalization.Away.lift_eq _ _ _
@[simp] theorem right_source (a : SourceOrder R c) :
    rightMap R c i j (algebraMap (SourceOrder R c) (B R c j) a) =
      algebraMap (SourceOrder R c) (Pair R c i j) a := IsLocalization.Away.lift_eq _ _ _

instance left_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (leftMap R c i j).toRingHom)) := by
  letI : Algebra (B R c i) (Pair R c i j) := (leftMap R c i j).toRingHom.toAlgebra
  letI : IsScalarTower (SourceOrder R c) (B R c i) (Pair R c i j) :=
    IsScalarTower.of_algebraMap_eq (fun a => (left_source R c i j a).symm)
  letI : IsLocalization.Away (denominator R c j * denominator R c i) (Pair R c i j) := by
    simpa only [mul_comm] using
      (inferInstance : IsLocalization.Away (denominator R c i * denominator R c j) (Pair R c i j))
  letI := ReciprocalOverlapBase318.away_of_mul (A := B R c i) (B := Pair R c i j)
    (denominator R c j) (denominator R c i)
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (SourceOrder R c) (B R c i) (denominator R c j))
instance right_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (rightMap R c i j).toRingHom)) := by
  letI : Algebra (B R c j) (Pair R c i j) := (rightMap R c i j).toRingHom.toAlgebra
  letI : IsScalarTower (SourceOrder R c) (B R c j) (Pair R c i j) :=
    IsScalarTower.of_algebraMap_eq (fun a => (right_source R c i j a).symm)
  letI := ReciprocalOverlapBase318.away_of_mul (A := B R c j) (B := Pair R c i j)
    (denominator R c i) (denominator R c j)
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (SourceOrder R c) (B R c j) (denominator R c i))

@[expose] def embedding : Spec (CommRingCat.of (Pair R c i j)) ⟶ scheme R c :=
  Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder R c) (Pair R c i j))) ≫ finiteChart R c
instance embedding_open : IsOpenImmersion (embedding R c i j) :=
  @IsOpenImmersion.comp _ _ _ _ _
    (IsOpenImmersion.of_isLocalization (denominator R c i * denominator R c j))
    (finiteChart_open R c)

theorem left_route : Spec.map (CommRingCat.ofHom (leftMap R c i j).toRingHom) ≫
    branchEmbedding R c i = embedding R c i j := by
  unfold branchEmbedding embedding
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact left_source R c i j
theorem right_route : Spec.map (CommRingCat.ofHom (rightMap R c i j).toRingHom) ≫
    branchEmbedding R c j = embedding R c i j := by
  unfold branchEmbedding embedding
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact right_source R c i j

theorem over_base : embedding R c i j ≫ structureMap R c =
    Spec.map (CommRingCat.ofHom (algebraMap R (Pair R c i j))) := by
  unfold embedding
  rw [Category.assoc,finiteChart_structure,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (IsScalarTower.algebraMap_apply R (SourceOrder R c) (Pair R c i j) r).symm

/-- Exact whole prime-spectrum intersection for every pair, including equal
indices. It is obtained from the product localization, without a density step. -/
theorem full_intersection :
    embedding R c i j ''ᵁ ⊤ =
      (branchEmbedding R c i ''ᵁ ⊤) ⊓ (branchEmbedding R c j ''ᵁ ⊤) := by
  have hr (d : SourceOrder R c) :
      (Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder R c) (Localization.Away d)))).opensRange =
      PrimeSpectrum.basicOpen d := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away d) d
  simp only [Scheme.Hom.image_top_eq_opensRange,embedding,branchEmbedding,
    Scheme.Hom.opensRange_comp,hr,PrimeSpectrum.basicOpen_mul,
    FinitePairOverlap318.image_inf]

theorem left_polynomial (q : R[X]) : leftMap R c i j (algebraMap R[X] (B R c i) q) =
    algebraMap R[X] (Pair R c i j) q := by
  rw [IsScalarTower.algebraMap_apply R[X] (SourceOrder R c) (B R c i),left_source,
    ←IsScalarTower.algebraMap_apply]
theorem right_polynomial (q : R[X]) : rightMap R c i j (algebraMap R[X] (B R c j) q) =
    algebraMap R[X] (Pair R c i j) q := by
  rw [IsScalarTower.algebraMap_apply R[X] (SourceOrder R c) (B R c j),right_source,
    ←IsScalarTower.algebraMap_apply]

/-- Two distinct original contact denominators invert every original
contact factor, over an arbitrary coefficient ring. -/
theorem quartic_unit (hij : i≠j) :
    IsUnit (algebraMap R[X] (Pair R c i j) (IntegralBranchBicanonical318.quartic R)) := by
  have hu (k : Fin 4) (hk : k=i ∨ k=j) :
      IsUnit (algebraMap R[X] (Pair R c i j) (untwisted R k)) := by
    have hd : IsUnit (algebraMap (SourceOrder R c) (Pair R c i j) (denominator R c k)) := by
      rcases hk with rfl|rfl
      · exact (pair_units R c i j).1
      · exact (pair_units R c i j).2
    change IsUnit (algebraMap (SourceOrder R c) (Pair R c i j)
      (algebraMap R[X] (SourceOrder R c) (twisted R c k))) at hd
    rw [←IsScalarTower.algebraMap_apply,twisted_factor,map_mul] at hd
    exact (isUnit_mul_iff.mp hd).2
  have hi := hu i (Or.inl rfl)
  have hj := hu j (Or.inr rfl)
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    simp only [untwisted,IntegralBranchBicanonical318.quartic,FourRootPivot318.indices,
      Fin.prod_univ_succ,Fin.prod_univ_zero,map_mul,map_one,mul_one,
      isUnit_mul_iff] at hi hj ⊢
    tauto
end IntegralFinitePairGeometry318
