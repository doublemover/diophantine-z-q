module

public import SelectedActualMarkedEllipticCenterCharacter318
public import SelectedActualMarkedCompactSchemeStalk318
import all SelectedActualComplexCompactOriginalDVR318

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Filter Polynomial
open scoped Polynomial Topology TensorProduct
open SelectedComplexOrdinaryBase318
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexGenericCompactNormal318
open SelectedActualComplexCompactOriginalDVR318 (chartCoefficient)
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra literalWholeTensor)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticCenterCharacter318
open SelectedActualMarkedCompactSchemeStalk318 (finiteJ_chart_germ)
open OpenJLocalComparison318 (j)

namespace SelectedActualMarkedEllipticSchemeBranch318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem specPoint_from_affine {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    (s : Spec (CommRingCat.of ℂ) ⟶ X)
    (hs : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ≤ s ⁻¹ᵁ U) :
    Spec.map (s.appLE U ⊤ hs ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫
      hU.fromSpec = s := by
  have hTop : Spec.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫
      (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec =
        𝟙 (Spec (CommRingCat.of ℂ)) := by
    rw [IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom] <;> exact Iso.hom_inv_id _
  rw [Spec.map_comp,Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec,
    ← Category.assoc,hTop,Category.id_comp]

section CoordinateBeta

variable (F : Type) [Field F] [Algebra JField F]
variable [aC : Algebra ℂ F] [tC : IsScalarTower ℂ JField F]

include aC tC in
/-- The original chart-ring comparison preserves the structural J
coefficient map, not only the underlying integral order as a ring. -/
theorem finiteJ_chart_coefficient (a : ℂ[X]) :
    (chartRingEquiv F 1) (chartCoefficient F 1 a) = algebraMap ℂ[X] (B F) a := by
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  let R := CommRingCat.of ℂ[X]
  let K₀ := CommRingCat.of F
  let φ : R ⟶ K₀ := CommRingCat.ofHom (polynomial F 1)
  let c := JLineAtlas318.chart ℂ (1 : Fin 2)
  let V := (targetCover (1 : Fin 2)).1
  let U := (sourceCover F (1 : Fin 2)).1
  let f := genericMap F
  let ν := f.toNormalization
  let q := modelMap F
  have hf : f = Spec.map φ ≫ c := rfl
  have hWhole : f ⁻¹ᵁ V = (⊤ : (Spec K₀).Opens) := NormalizationChart318.whole_preimage φ c
  have hν : (⊤ : (Spec K₀).Opens) ≤ ν ⁻¹ᵁ U := by
    change ⊤ ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V)
    rw [← Scheme.Hom.comp_preimage,Scheme.Hom.toNormalization_fromNormalization,hWhole]
  have hC : f.appLE V ⊤ hWhole.ge ≫ (Scheme.ΓSpecIso K₀).hom =
      (NormalizationChart318.targetSections c).hom ≫ φ := by
    have hS := NormalizationChart318.section_square φ c
    change f.app V ≫ (NormalizationChart318.sourceSections φ c).hom =
      (NormalizationChart318.targetSections c).hom ≫ φ at hS
    simp only [NormalizationChart318.sourceSections,Iso.trans_hom,Functor.mapIso_hom,
      ← Category.assoc] at hS
    exact hS
  have hQ : q.app V ≫ ν.appLE U ⊤ hν = f.appLE V ⊤ hWhole.ge := by
    have h := (Scheme.Hom.comp_appLE ν q V ⊤ hν).symm
    rw [show ν ≫ q = f from (genericMap F).toNormalization_fromNormalization] at h
    exact h
  have hE : CommRingCat.ofHom ((algebraMap (B F) F).comp (chartRingEquiv F 1).toRingHom) =
      ν.appLE U ⊤ hν ≫ (Scheme.ΓSpecIso K₀).hom := finiteJ_chart_germ F
  have hEq :
      (NormalizationChart318.targetSections c).inv ≫ q.app V ≫
        CommRingCat.ofHom ((algebraMap (B F) F).comp (chartRingEquiv F 1).toRingHom) = φ := by
    rw [hE,← Category.assoc (q.app V),hQ,hC]
    simp
  apply Subtype.ext
  have hValue := congrArg (fun g : R ⟶ K₀ => g a) hEq
  change (algebraMap (B F) F) ((chartRingEquiv F 1) (chartCoefficient F 1 a)) =
    (algebraMap ℂ[X] F) a
  exact hValue

end CoordinateBeta

private theorem retarget_actual_J_chart :
    let R := CommRingCat.of ℂ[X]
    let c := JLineAtlas318.chart ℂ (1 : Fin 2)
    let V := targetCover (1 : Fin 2)
    Spec.map (NormalizationChart318.targetSections c).hom ≫ V.2.fromSpec = c := by
  let R := CommRingCat.of ℂ[X]
  let c := JLineAtlas318.chart ℂ (1 : Fin 2)
  let V := targetCover (1 : Fin 2)
  have ht : (⊤ : (Spec R).Opens) ≤ c ⁻¹ᵁ V.1 := by
    change ⊤ ≤ c ⁻¹ᵁ (c ''ᵁ ⊤)
    rw [c.preimage_image_eq]
  have hΓ : (NormalizationChart318.targetSections c).hom =
      c.appLE V.1 ⊤ ht ≫ (Scheme.ΓSpecIso R).hom := by
    simp only [NormalizationChart318.targetSections,Iso.trans_hom,Scheme.Hom.appIso_hom']
  have hId : Spec.map (Scheme.ΓSpecIso R).hom ≫
      (isAffineOpen_top (Spec R)).fromSpec = 𝟙 (Spec R) := by
    rw [IsAffineOpen.fromSpec_top,← Scheme.isoSpec_Spec_hom] <;> exact Iso.hom_inv_id _
  rw [hΓ,Spec.map_comp,Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec,
    ← Category.assoc,hId,Category.id_comp]

section Point

variable (F : Type) [Field F] [Algebra JField F]
variable [aC : Algebra ℂ F] [tC : IsScalarTower ℂ JField F]

include aC tC in
/-- The center's genuine complex point of the original compact
normalization chart, obtained using its actual affine section ring. -/
def finiteJ_complex_point (χ : B F →+* ℂ) : Spec (CommRingCat.of ℂ) ⟶ model F :=
  Spec.map (CommRingCat.ofHom (χ.comp (chartRingEquiv F 1).toRingHom)) ≫
    (sourceCover F (1 : Fin 2)).2.fromSpec

include aC tC in
theorem finiteJ_complex_point_over (χ : B F →+* ℂ) (z : ℂ)
    (hχ : χ.comp (algebraMap ℂ[X] (B F)) = Polynomial.evalRingHom z) :
    finiteJ_complex_point F χ ≫ modelMap F =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom z)) ≫ JLineAtlas318.chart ℂ 1 := by
  let c := JLineAtlas318.chart ℂ (1 : Fin 2)
  let V := targetCover (1 : Fin 2)
  let U := sourceCover F (1 : Fin 2)
  let q := modelMap F
  let γ := CommRingCat.ofHom (χ.comp (chartRingEquiv F 1).toRingHom)
  let ev := CommRingCat.ofHom (Polynomial.evalRingHom z)
  have hΓ : (NormalizationChart318.targetSections c).inv ≫ q.app V.1 ≫ γ = ev := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change χ ((chartRingEquiv F 1) (chartCoefficient F 1 a)) = (Polynomial.evalRingHom z) a
    rw [finiteJ_chart_coefficient]
    exact RingHom.congr_fun hχ a
  have hA : q.app V.1 ≫ γ = (NormalizationChart318.targetSections c).hom ≫ ev := by
    rw [← cancel_epi (NormalizationChart318.targetSections c).inv,
      Iso.inv_hom_id_assoc]
    exact hΓ
  have hq : Spec.map (q.app V.1) ≫ V.2.fromSpec = U.2.fromSpec ≫ q := by
    simpa only [← Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec q V.2 U.2 (le_rfl : U.1 ≤ q ⁻¹ᵁ V.1))
  change (Spec.map γ ≫ U.2.fromSpec) ≫ q = Spec.map ev ≫ c
  rw [Category.assoc,← hq,← Spec.map_comp_assoc,hA,Spec.map_comp_assoc,
    retarget_actual_J_chart]

include aC tC in
/-- The original punctured marked values of the actual compact finite-J
sections uniquely identify the scheme point. The candidate is a genuine
morphism from Spec C to the original normalization (not a chosen
abstract root on a new affine datum). -/
theorem finiteJ_complex_point_unique_by_puncture
    (χ : B F →+* ℂ) (ψ : ℂ → B F →+* ℂ) (z : ℂ)
    (hχ : ∀ b : B F, Tendsto (fun w => ψ w b) (𝓝[≠] z) (𝓝 (χ b)))
    (s : Spec (CommRingCat.of ℂ) ⟶ model F)
    (hs : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ≤ s ⁻¹ᵁ (sourceCover F 1).1)
    (hS : ∀ a : chartRing F 1, Tendsto (fun w => ψ w ((chartRingEquiv F 1) a)) (𝓝[≠] z)
      (𝓝 ((s.appLE (sourceCover F 1).1 ⊤ hs ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) a))) :
    s = finiteJ_complex_point F χ := by
  let U := sourceCover F (1 : Fin 2)
  have hγ : (s.appLE U.1 ⊤ hs ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) =
      CommRingCat.ofHom (χ.comp (chartRingEquiv F 1).toRingHom) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact tendsto_nhds_unique (hS a) (hχ ((chartRingEquiv F 1) a))
  have h := specPoint_from_affine U.2 s hs
  rw [hγ] at h
  exact h.symm

end Point

/-- The true elliptic center evaluation gives a complex scheme point of
the original compact normalization, over the actual finite J-value. It
is the only affine complex point compatible with the original punctured
marked evaluations of all original compact sections. -/
theorem actual_marked_elliptic_scheme_branch
    (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hRoots : fullRootSet N p) (hN : 5 ≤ N) (τ : UpperHalfPlane)
    (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
    letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
    letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
    letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
      @IsScalarTower.of_algebraMap_eq' ℂ JField F
        inferInstance inferInstance inferInstance aF aJ aC (by rfl)
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    let U := (sourceCover F (1 : Fin 2)).1
    ∃ (t : Period) (α : O F →+* F)
      (e : OrdinaryRoot N p ≃ₐ[Base] O F) (χ : B F →+* ℂ),
      let ψ := puncturedChartEvaluation N p hRoots t e
      let s := finiteJ_complex_point F χ
      α.comp (algebraMap (B F) (O F)) = algebraMap (B F) F ∧
      (∀ r : OrdinaryRoot N p, α (e r) = literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic))) ∧
      Function.Surjective χ ∧
      s ≫ modelMap F = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (j (τ : ℂ)))) ≫
        JLineAtlas318.chart ℂ 1 ∧
      ∀ (s' : Spec (CommRingCat.of ℂ) ⟶ model F)
        (hs' : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ≤ s' ⁻¹ᵁ U),
        (∀ a : chartRing F 1, Tendsto (fun w => ψ w ((chartRingEquiv F 1) a))
          (𝓝[≠] (τ : ℂ))
          (𝓝 ((s'.appLE U ⊤ hs' ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) a))) → s' = s := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
  letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ JField F
      inferInstance inferInstance inferInstance aF aJ aC (by rfl)
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  obtain ⟨t,α,e,χ,hα,he,hBase,hSurj,hUnique,hμ⟩ :=
    actual_marked_finiteJ_center N p hRoots hN τ hp hd hf
  refine ⟨t,α,e,χ,hα,he,hSurj,finiteJ_complex_point_over F χ (j (τ : ℂ)) hBase,?_⟩
  intro s' hs' hS
  exact finiteJ_complex_point_unique_by_puncture F χ (puncturedChartEvaluation N p hRoots t e)
    (τ : ℂ) (fun b => (hμ b).2.1) s' hs' hS

end SelectedActualMarkedEllipticSchemeBranch318

#print axioms SelectedActualMarkedEllipticSchemeBranch318.finiteJ_complex_point_over
#print axioms SelectedActualMarkedEllipticSchemeBranch318.finiteJ_complex_point_unique_by_puncture
#print axioms SelectedActualMarkedEllipticSchemeBranch318.actual_marked_elliptic_scheme_branch
