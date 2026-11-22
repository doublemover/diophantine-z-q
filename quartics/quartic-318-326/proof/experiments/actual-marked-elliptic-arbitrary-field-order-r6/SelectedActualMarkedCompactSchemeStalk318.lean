module

public import SelectedActualMarkedCompactPrincipalBranch318
import all NormalChart318
import all SelectedActualComplexGenericCompactNormal318
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Ideal.Maps

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Polynomial
open scoped Polynomial
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexGenericCompactNormal318
open SelectedComplexOrdinaryBase318 SelectedActualComplexOrdinaryScalar318
open SelectedActualComplexWholeRootField318 (Period periodMap)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedCompactPrincipalBranch318

namespace SelectedActualMarkedCompactSchemeStalk318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem normalChart_section_value {A F : CommRingCat} {Y : Scheme}
    (φ : A ⟶ F) (c : Spec A ⟶ Y) [IsOpenImmersion c]
    [QuasiCompact (Spec.map φ ≫ c)] [QuasiSeparated (Spec.map φ ≫ c)] :
    let f := Spec.map φ ≫ c
    let U := c ''ᵁ ⊤
    let V := f.fromNormalization ⁻¹ᵁ U
    letI := φ.hom.toAlgebra
    CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
      (NormalChart318.sectionsEquiv φ c).toRingHom) =
      f.toNormalization.appLE V ⊤
        (by rw [← Scheme.Hom.comp_preimage, f.toNormalization_fromNormalization,
          NormalizationChart318.whole_preimage]) ≫ (Scheme.ΓSpecIso F).hom := by
  let f := Spec.map φ ≫ c
  let U : Y.Opens := c ''ᵁ ⊤
  let V : f.normalization.Opens := f.fromNormalization ⁻¹ᵁ U
  letI := φ.hom.toAlgebra
  letI := (f.app U).hom.toAlgebra
  have hU : IsAffineOpen U := by
    change IsAffineOpen (c ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange c
  have hF : f ⁻¹ᵁ U = (⊤ : (Spec F).Opens) :=
    NormalizationChart318.whole_preimage φ c
  have hV : f.toNormalization ⁻¹ᵁ V = (⊤ : (Spec F).Opens) := by
    change f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = ⊤
    rw [← Scheme.Hom.comp_preimage, f.toNormalization_fromNormalization, hF]
  have h₀ : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ V := by rw [hF,hV]
  have hf : (f.normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val
        (integralClosure Γ(Y,U) Γ(Spec F, f ⁻¹ᵁ U))).toRingHom =
        f.toNormalization.appLE V (f ⁻¹ᵁ U) h₀ :=
    f.normalizationObjIso_hom_val hU
  have hb : CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
      (NormalChart318.sectionsEquiv φ c).toRingHom) =
      ((f.normalizationObjIso hU).hom ≫
        CommRingCat.ofHom (Subalgebra.val
          (integralClosure Γ(Y,U) Γ(Spec F, f ⁻¹ᵁ U))).toRingHom) ≫
            (NormalizationChart318.sourceSections φ c).hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    unfold NormalChart318.sectionsEquiv
    rfl
  rw [hb,hf]
  simp only [NormalizationChart318.sourceSections,Iso.trans_hom,Functor.mapIso_hom,
    ← Category.assoc]
  rw [Scheme.Hom.appLE_map] <;> rfl

section ActualChart

variable (F : Type) [Field F] [Algebra JField F]
variable [aF : Algebra ℂ F] [τF : IsScalarTower ℂ JField F]

include aF τF in
/-- Retains the genuine generic morphism to the literal normalization.
The inclusion after the published chart-ring isomorphism is exactly
its actual restriction on the old finite-J chart. -/
theorem finiteJ_chart_germ :
    let U := (sourceCover F 1).1
    letI := (polynomial F 1).toAlgebra
    CommRingCat.ofHom ((algebraMap (B F) F).comp (chartRingEquiv F 1).toRingHom) =
      (genericMap F).toNormalization.appLE U ⊤
        (by
          change ⊤ ≤ (genericMap F).toNormalization ⁻¹ᵁ
            ((genericMap F).fromNormalization ⁻¹ᵁ (JLineAtlas318.chart ℂ (1 : Fin 2) ''ᵁ ⊤))
          rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
          exact (NormalizationChart318.whole_preimage
            (CommRingCat.ofHom (polynomial F 1)) (JLineAtlas318.chart ℂ 1)).ge) ≫
          (Scheme.ΓSpecIso (CommRingCat.of F)).hom := by
  letI := (polynomial F 1).toAlgebra
  have h := normalChart_section_value (CommRingCat.ofHom (polynomial F 1))
    (JLineAtlas318.chart ℂ 1)
  unfold chartRingEquiv
  exact h

end ActualChart

section AffineStalk

variable {F T : Type} [Field F] [CommRing T] [Algebra T F]
variable {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
variable (e : Γ(X,U) ≃+* T) (P : Ideal T) [P.IsPrime]

private abbrev chartPrime : PrimeSpectrum Γ(X,U) :=
  (⟨P, inferInstance⟩ : PrimeSpectrum T).comap e.toRingHom

private theorem point_mem : hU.fromSpec (chartPrime e P) ∈ U := by
  have hx : hU.fromSpec (chartPrime e P) ∈ Set.range hU.fromSpec :=
    Set.mem_range_self _
  rwa [hU.range_fromSpec] at hx

private theorem affine_stalk_equiv :
    ∃ l : (X.presheaf.stalk (hU.fromSpec (chartPrime e P))) ≃+* Localization.AtPrime P,
      ∀ a : Γ(X,U),
        l (X.presheaf.germ U _ (point_mem hU e P) a) =
          algebraMap T (Localization.AtPrime P) (e a) := by
  let y := chartPrime e P
  let x := hU.fromSpec y
  let hx : x ∈ U := point_mem hU e P
  let S := X.presheaf.stalk x
  letI : Algebra Γ(X,U) S := X.presheaf.algebra_section_stalk ⟨x,hx⟩
  letI : IsLocalization.AtPrime S y.asIdeal := hU.isLocalization_stalk' y hx
  have hE : y.asIdeal.primeCompl.map e.toMonoidHom = P.primeCompl :=
    RingEquiv.map_primeCompl_comap_eq e P
  let l : S ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv S (Localization.AtPrime P) e hE
  exact ⟨l, fun a => IsLocalization.ringEquivOfRingEquiv_eq hE a⟩

private theorem nongeneric_of_order_prime [IsIntegral X]
    (hDom : IsDomain Γ(X,U)) (hP : P ≠ ⊥) :
    hU.fromSpec (chartPrime e P) ≠ genericPoint X := by
  letI := hDom
  let x := hU.fromSpec (chartPrime e P)
  letI : Nonempty U := ⟨⟨x, point_mem hU e P⟩⟩
  intro h
  let hx : genericPoint X ∈ U := h ▸ point_mem hU e P
  have he : hU.fromSpec (hU.primeIdealOf ⟨genericPoint X,hx⟩) =
      hU.fromSpec (chartPrime e P) :=
    (hU.fromSpec_primeIdealOf _).trans h.symm
  have he' : chartPrime e P = hU.primeIdealOf ⟨genericPoint X,hx⟩ :=
    hU.fromSpec.isOpenEmbedding.injective he.symm
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] at he'
  apply hP
  apply le_antisymm _ bot_le
  intro b hb
  apply Ideal.mem_bot.mpr
  have hbe : e.symm b ∈ (chartPrime e P).asIdeal := by
    change e (e.symm b) ∈ P
    rw [e.apply_symm_apply]
    exact hb
  rw [he'] at hbe
  have hz : e.symm b = 0 := Ideal.mem_bot.mp hbe
  exact e.symm.injective (hz.trans (map_zero e.symm).symm)

include hU in
/-- The induced spectrum map is the given generic morphism, not merely
another field map with the same image point. -/
private theorem localized_factor_is_actual
    (ν : Spec (CommRingCat.of F) ⟶ X) (x : X) (hx : x ∈ U)
    (δ : (X.presheaf.stalk x) →+* F)
    (htop : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤ ν ⁻¹ᵁ U)
    (hChart : CommRingCat.ofHom ((algebraMap T F).comp e.toRingHom) =
      ν.appLE U ⊤ htop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom)
    (hδ : ∀ a : Γ(X,U), δ (X.presheaf.germ U x hx a) = algebraMap T F (e a)) :
    Spec.map (CommRingCat.ofHom δ) ≫ X.fromSpecStalk x = ν := by
  have hG : X.presheaf.germ U x hx ≫ CommRingCat.ofHom δ =
      CommRingCat.ofHom ((algebraMap T F).comp e.toRingHom) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact hδ a
  have h₀ : Spec.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫
      (isAffineOpen_top (Spec (CommRingCat.of F))).fromSpec =
        𝟙 (Spec (CommRingCat.of F)) := by
    rw [IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom] <;> exact Iso.hom_inv_id _
  calc
    Spec.map (CommRingCat.ofHom δ) ≫ X.fromSpecStalk x =
        Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom δ) ≫ hU.fromSpec := by
      rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk,
        ← Category.assoc, ← Spec.map_comp]
    _ = Spec.map (ν.appLE U ⊤ htop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom) ≫
        hU.fromSpec := by rw [hG,hChart]
    _ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫
        ((isAffineOpen_top (Spec (CommRingCat.of F))).fromSpec ≫ ν) := by
      rw [Spec.map_comp,Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec]
    _ = ν := by rw [← Category.assoc,h₀, Category.id_comp]

end AffineStalk

section ActualMarked

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p) (t : Period)

private theorem branch_contraction_ne_bot
    (F : Type) [Field F] [Algebra JField F]
    (e : OrdinaryRoot N p ≃ₐ[Base] O F) :
    let P₀ := (RingHom.ker ((atPeriod N p hRoots t).comp e.symm.toRingHom)).comap
      (algebraMap (B F) (O F))
    P₀ ≠ ⊥ := by
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  let χ := atPeriod N p hRoots t
  let P₀ := (RingHom.ker (χ.comp e.symm.toRingHom)).comap (algebraMap (B F) (O F))
  let a : ℂ[X] := Polynomial.X - Polynomial.C (periodMap N t).1.val
  let b : B F := algebraMap ℂ[X] (B F) a
  have hB : algebraMap (B F) (O F) b =
      algebraMap Base (O F) (algebraMap ℂ[X] Base a) := by
    exact (IsScalarTower.algebraMap_apply ℂ[X] (B F) (O F) a).symm.trans
      (IsScalarTower.algebraMap_apply ℂ[X] Base (O F) a)
  have hb : b ∈ P₀ := by
    change χ (e.symm (algebraMap (B F) (O F) b)) = 0
    rw [hB,e.symm.commutes,AdjoinRoot.algebraMap_eq]
    change atPeriod N p hRoots t
      (AdjoinRoot.of _ (algebraMap ℂ[X] Base a)) = 0
    rw [atPeriod_base,evaluation_polynomial]
    simp only [a,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self]
  have ha : a ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hf : Function.Injective (polynomial F 1) := by
    letI : Algebra ℂ[X] JField := (basePolynomial 1).toAlgebra
    letI : IsFractionRing ℂ[X] JField := base_fractionRing 1
    exact (algebraMap JField F).injective.comp (IsFractionRing.injective ℂ[X] JField)
  change P₀ ≠ ⊥
  intro hp
  have hb₀ : b ∈ (⊥ : Ideal (B F)) := by simpa only [hp] using hb
  have hzero : b = 0 := Ideal.mem_bot.mp hb₀
  apply ha
  apply hf
  have h := congrArg (algebraMap (B F) F) hzero
  change algebraMap (B F) F (algebraMap ℂ[X] (B F) a) = algebraMap (B F) F 0 at h
  rw [← IsScalarTower.algebraMap_apply ℂ[X] (B F) F, map_zero] at h
  exact h.trans (map_zero (polynomial F 1)).symm

/-- The literal marked period determines the actual point of the original
compact normalization. Its scheme stalk is the previously computed
ordinary localization, with the same map to the original whole field.
The fact that it is a DVR follows for this particular point, without
assuming a separately chosen branch or a generic field comparison. -/
theorem actual_marked_scheme_stalk
    (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p))) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    let F := K N p
    letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
    letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
    letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
    letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
      @IsScalarTower.of_algebraMap_eq' ℂ JField F
        inferInstance inferInstance inferInstance aF aJ aC (by rfl)
    let U := sourceCover F 1
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    let Q := RingHom.ker (atPeriod N p hRoots t)
    letI : Q.IsPrime := RingHom.ker_isPrime _
    ∃ e : OrdinaryRoot N p ≃ₐ[Base] O F,
      let P₀ := (RingHom.ker ((atPeriod N p hRoots t).comp e.symm.toRingHom)).comap
        (algebraMap (B F) (O F))
      ∃ (hP₀ : P₀.IsPrime),
        let L := @Localization.AtPrime (B F) _ P₀ hP₀
        ∃ (x : model F) (loc : Localization.AtPrime Q ≃+* L)
          (l : ((model F).presheaf.stalk x) ≃+* L) (β : L →+* F),
          x = U.2.fromSpec
            ((⟨P₀,hP₀⟩ : PrimeSpectrum (B F)).comap (chartRingEquiv F 1).toRingHom) ∧
          x ∈ U.1 ∧ algebraMap ℂ[X] (B F) denominator ∉ P₀ ∧
          IsDiscreteValuationRing ((model F).presheaf.stalk x) ∧
          (∀ z : OrdinaryRoot N p,
            β (loc (algebraMap (OrdinaryRoot N p) (Localization.AtPrime Q) z)) =
              intoWhole N p z) ∧
          Spec.map (CommRingCat.ofHom (β.comp l.toRingHom)) ≫ (model F).fromSpecStalk x =
            (genericMap F).toNormalization := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
  letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ JField F
      inferInstance inferInstance inferInstance aF aJ aC (by rfl)
  let U := (sourceCover F 1).1
  let hU : IsAffineOpen U := (sourceCover F 1).2
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  letI : IsIntegral (model F) := model_integral F
  let Q := RingHom.ker (atPeriod N p hRoots t)
  letI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨α,e,hα,he,hP₀,hDen,loc,β,hβT,hβC⟩ :=
    actual_marked_compact_branch N p hp hd hf hRoots t
  let P₀ := (RingHom.ker ((atPeriod N p hRoots t).comp e.symm.toRingHom)).comap
    (algebraMap (B F) (O F))
  letI : P₀.IsPrime := hP₀
  let E : Γ(model F,U) ≃+* B F := chartRingEquiv F 1
  let x := hU.fromSpec (chartPrime E P₀)
  let hx : x ∈ U := point_mem hU E P₀
  obtain ⟨l,hl⟩ := affine_stalk_equiv hU E P₀
  have hpC : (p.map (toComplex N)).Monic := hp.map (toComplex N)
  have hpG : (P N p).Monic := hpC.map (algebraMap Base Generic)
  have hpJ : (pJ N p).Monic := by
    unfold pJ
    letI : Algebra Base (RatFunc ℂ) := SelectedComplexGenericRatFunc318.ratscalar
    exact hpG.map SelectedComplexGenericRatFunc318.ratEquiv.toRingEquiv.toRingHom
  letI : FiniteDimensional JField F := hpJ.finite_adjoinRoot
  letI : Algebra.IsSeparable JField F := inferInstance
  have hxng : x ≠ genericPoint (model F) :=
    nongeneric_of_order_prime hU E P₀ (chart_domain_normal F 1).1
      (branch_contraction_ne_bot N p hRoots t F e)
  have hDVR : IsDiscreteValuationRing ((model F).presheaf.stalk x) :=
    (literal_projective_normalization N p hp hf).2 x hxng
  have hδ (a : Γ(model F,U)) :
      (β.comp l.toRingHom) ((model F).presheaf.germ U x hx a) =
        algebraMap (B F) F (E a) :=
    (congrArg β (hl a)).trans (hβT (E a))
  let ν := (genericMap F).toNormalization
  have htop : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤ ν ⁻¹ᵁ U := by
    change ⊤ ≤ (genericMap F).toNormalization ⁻¹ᵁ
      ((genericMap F).fromNormalization ⁻¹ᵁ (JLineAtlas318.chart ℂ (1 : Fin 2) ''ᵁ ⊤))
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
    exact (NormalizationChart318.whole_preimage
      (CommRingCat.ofHom (polynomial F 1)) (JLineAtlas318.chart ℂ 1)).ge
  exact ⟨e,hP₀,x,loc,l,β,rfl,hx,hDen,hDVR,hβC,
    localized_factor_is_actual hU E ν x hx (β.comp l.toRingHom) htop
      (finiteJ_chart_germ F) hδ⟩

end ActualMarked

end SelectedActualMarkedCompactSchemeStalk318

#print axioms SelectedActualMarkedCompactSchemeStalk318.finiteJ_chart_germ
#print axioms SelectedActualMarkedCompactSchemeStalk318.actual_marked_scheme_stalk
