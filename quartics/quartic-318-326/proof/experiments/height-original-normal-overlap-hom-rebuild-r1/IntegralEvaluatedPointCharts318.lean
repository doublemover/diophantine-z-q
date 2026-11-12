module
public import IntegralValuativePointCenter318
public import IntegralOriginalChartNorms318
public section
noncomputable section
namespace IntegralEvaluatedPointCharts318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralSourceBranches318 IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def ChartRing : Option (Fin 4) → Type _
  | some i => IntegralBranchCoordinates318.B R c i
  | none => IntegralInfinityChart318.Order R c
instance chartRing_commRing (o : Option (Fin 4)) : CommRing (ChartRing R c o) := by
  cases o <;> dsimp only [ChartRing] <;> infer_instance
@[expose] def embedding (o : Option (Fin 4)) :
    Spec (CommRingCat.of (ChartRing R c o)) ⟶ IntegralGluedModel318.scheme R c :=
  match o with
  | some i => IntegralGluedDifferentialFrames318.branchEmbedding R c i
  | none => IntegralGluedModel318.infinityChart R c
@[expose] def coefficient (o : Option (Fin 4)) (n : Fin 2) : ChartRing R c o :=
  match o with
  | some i => branchCoefficient R c i n
  | none => infinityCoefficient R c n

theorem primitive (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
    (o : Option (Fin 4)) : IsUnit (coefficient R c o 0) ∨ IsUnit (coefficient R c o 1) := by
  cases o with
  | none => exact Or.inr (IntegralScaledCoefficientUnits318.infinity_one_unit R c hN)
  | some i => exact Or.inl (IntegralScaledCoefficientUnits318.branch_zero_unit R c hN i)

variable (K : Type*) [Field K] [IsDomain R] [ValuationRing R]
  [Algebra R K] [IsFractionRing R K] (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap R K (c i : R)*(t-algebraMap R K (contacts R i)))

/-- An actual full chart center carries both the original marked generic
point and the exact ratio of its original J² pair. These are proved together,
not supplied as unrelated point or ratio hypotheses. -/
theorem exists_chart (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    ∃ (o : Option (Fin 4)) (φ : ChartRing R c o →+* R),
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ embedding R c o=
          IntegralValuativeGenericPoint318.point R K c t y hy ∧
      algebraMap R K (φ (coefficient R c o 1))=
        t*algebraMap R K (φ (coefficient R c o 0)) := by
  by_cases ht : IsLocalization.IsInteger R t
  · obtain ⟨i,φ,hφ,hyφ⟩ := IntegralValuativePointCenter318.finite_branch_center R K c t y hy hN ht
    refine ⟨some i,φ,?_,?_⟩
    · change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom φ) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c i))) ≫
          IntegralGluedModel318.finiteChart R c)=_
      have he : ((algebraMap R K).comp φ).comp
          (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c i))=
            IntegralValuativeGenericPoint318.sourceMap R K c t y hy := RingHom.ext hφ
      rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
      exact congrArg (fun f : SourceOrder R c →+* K =>
        Spec.map (CommRingCat.ofHom f) ≫ IntegralGluedModel318.finiteChart R c) he
    · change algebraMap R K (φ (branchCoefficient R c i 1))=t*_
      rw [IntegralOriginalSectionRatios318.branch_coefficients,map_mul,map_mul]
      congr 1
      exact (hφ (algebraMap R[X] (SourceOrder R c) X)).trans
        ((IntegralValuativeGenericPoint318.sourceMap_polynomial R K c t y hy X).trans
          (Polynomial.aeval_X t))
  · obtain ⟨u,z,hu,hz,hun,hz2,hd⟩ :=
      IntegralValuativeRootCoordinates318.infinity_coordinates R K c t y hy ht
    let φ := IntegralValuativeChartPoints318.infinityMap R c u z hz2 hd
    refine ⟨none,φ,?_,?_⟩
    · exact IntegralValuativeInfinityExtension318.infinity_point_extension R K c t y hy ht u z hz2 hd hu hz
    · change algebraMap R K (φ (infinityCoefficient R c 1))=
        t*algebraMap R K (φ (infinityCoefficient R c 0))
      have ht0 : t≠0 := by intro h; exact ht ⟨0,by simpa only [map_zero] using h.symm⟩
      have hc0 : algebraMap R K (c 0:R)≠0 := ((c 0).isUnit.map (algebraMap R K)).ne_zero
      have h0 : (y 0)^2=algebraMap R K (c 0:R)*t := by
        simpa only [contacts,Matrix.cons_val_zero,map_zero,sub_zero] using hy 0
      have hy0 : y 0≠0 := by
        intro h
        rw [h,zero_pow (by decide : (2:ℕ)≠0)] at h0
        exact mul_ne_zero hc0 ht0 h0.symm
      have hk : φ (IntegralInfinityCoefficients318.k0 R c)=(↑(c 0)⁻¹:R) := by
        rw [IntegralInfinityCoefficients318.k0,
          IsScalarTower.algebraMap_apply R R[X] (IntegralInfinityChart318.Order R c)]
        exact (IntegralValuativeChartPoints318.infinityMap_polynomial R c u z hz2 hd
          (C (↑(c 0)⁻¹:R))).trans (Polynomial.eval_C _ _)
      have hr : t*algebraMap R K
          (φ (IntegralInfinityCoefficients318.k0 R c*IntegralInfinityChart318.coordinate R c^2))=1 := by
        rw [map_mul,map_pow,hk,IntegralValuativeChartPoints318.infinityMap_coordinate,
          map_mul,map_pow,map_units_inv,hu,div_pow,h0]
        field_simp [hc0,ht0]
        <;> ring
      rw [IntegralOriginalSectionRatios318.infinity_coefficients,map_mul,map_mul,←mul_assoc,hr,one_mul]
end IntegralEvaluatedPointCharts318
