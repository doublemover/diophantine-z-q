module
public import SelectedOriginalRationalOrdinaryPullback318
public import SelectedGenericCompactNormalization318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryIntegral318
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryGeometry318
open SelectedOriginalRationalOrdinaryPullback318
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericCompactNormal318
open SelectedOriginalGenericCompactCharts318 SelectedOriginalGenericClosureOverlap318

namespace SelectedOriginalCompactClassicalComparison318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev U := Spec (CommRingCat.of (ordinaryRoot N p))
abbrev V := Spec (CommRingCat.of Base)
abbrev JLine := ProjectiveJLine318.scheme ℚ
abbrev q : U N p ⟶ V := Spec.algebraMap Base (ordinaryRoot N p)

instance q_finite [Fact p.Monic] : IsFinite (q N p) := by
  letI : Module.Finite Base (ordinaryRoot N p) := ordinary_finite N p Fact.out
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance baseEmbedding_qc : QuasiCompact baseEmbedding := by
  letI : QuasiSeparatedSpace JLine :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveJLine318.structureMap ℚ)
  infer_instance

variable [hm : Fact p.Monic]
abbrev ordinaryNormalization := (q N p ≫ baseEmbedding).normalization

variable (hf : IsField (genericRoot N p)) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
local notation "a" => ordinaryEmbedding N p hf Fact.out hd

include hm hf hd in
theorem ordinary_integral : IsIntegral (U N p) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra (ordinaryRoot N p) (genericRoot N p) := (genericEmbedding N p).toAlgebra
  letI : IsIntegralClosure (ordinaryRoot N p) Base (genericRoot N p) :=
    actual_integralClosure N p Fact.out hd
  letI : IsDomain (ordinaryRoot N p) := Function.Injective.isDomain (genericEmbedding N p)
    (IsIntegralClosure.algebraMap_injective _ Base (genericRoot N p))
  infer_instance

include hm hd in
/-- A comparison built from the actual ordinary inclusion into the
compact K-normalization, not by replacing its underlying object. -/
def nativeDesc : ordinaryNormalization N p ⟶ compact N p hf := by
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  exact (q N p ≫ baseEmbedding).normalizationDesc a (compactJ N p hf) (ordinary_over_J N p hf Fact.out hd).symm

@[reassoc] theorem nativeDesc_open :
    (q N p ≫ baseEmbedding).toNormalization ≫ nativeDesc N p hf hd = a := by
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  exact (q N p ≫ baseEmbedding).toNormalization_normalizationDesc a (compactJ N p hf)
    (ordinary_over_J N p hf Fact.out hd).symm

@[reassoc] theorem nativeDesc_J :
    nativeDesc N p hf hd ≫ compactJ N p hf = (q N p ≫ baseEmbedding).fromNormalization := by
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  exact (q N p ≫ baseEmbedding).normalizationDesc_comp a (compactJ N p hf) (ordinary_over_J N p hf Fact.out hd).symm

/-- The cover and its affine section-ring witnesses are assembled at
the generic chart's own scalar keys, prior to specializing the source. -/
private theorem iso_to_normal_model (K : Type) [Field K] [Algebra JField K]
    [Algebra ℚ K] [IsScalarTower ℚ JField K] {T : Scheme} [IsIntegral T]
    (d : T ⟶ model K) [IsIntegralHom d] [IsDominant d]
    [IsIso (DominantFunctionField318.map d)] : IsIso d := by
  letI : IsIntegral (model K) := model_integral K
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  have hx : x ∈ (⨆ i, (sourceCover K i).1) := by
    rw [sourceCover_covers]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let W : (model K).Opens := (sourceCover K i).1
  letI : Nonempty W := ⟨⟨x,hi⟩⟩
  letI : IsIntegrallyClosed Γ(model K,W) := (chart_domain_normal K i).2
  exact ⟨W,hi,IntegralGenericIso318.restrict_isIso d W (sourceCover K i).2⟩

/-- The two constructions of the native compact are actually
isomorphic; the proof uses the common full ordinary generic field
and the two proved normal affine charts of the given K-model. -/
theorem nativeDesc_isIso : IsIso (nativeDesc N p hf hd) := by
  letI : IsIntegral (U N p) := ordinary_integral N p hf hd
  letI : IsIntegral (compact N p hf) := (compact_properties N p Fact.out hf).2.2.1
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  letI : IsIntegralHom (nativeDesc N p hf hd) := by unfold nativeDesc; infer_instance
  letI : IsOpenImmersion (q N p ≫ baseEmbedding).toNormalization := by infer_instance
  let a₀ : U N p ⟶ compact N p hf := ordinaryEmbedding N p hf Fact.out hd
  have ha : IsDominant a₀ :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace a₀ a₀.isOpenEmbedding.isOpenMap⟩
  letI : IsDominant ((q N p ≫ baseEmbedding).toNormalization ≫ nativeDesc N p hf hd) := by
    rw [nativeDesc_open]
    exact ha
  letI : IsDominant (nativeDesc N p hf hd) :=
    IsDominant.of_comp (q N p ≫ baseEmbedding).toNormalization (nativeDesc N p hf hd)
  letI : IsIso (DominantFunctionField318.map (nativeDesc N p hf hd)) :=
    CommonOpenFunctionField318.actual_generic_iso (q N p ≫ baseEmbedding).toNormalization a
      (nativeDesc N p hf hd) (nativeDesc_open N p hf hd)
  let K := genericRoot N p
  let fK : Field K := hf.toField
  let aJ : Algebra JField K := chartJAlgebra N p
  let aQ : Algebra ℚ K := rationalAlgebra N p
  let tQ : @IsScalarTower ℚ JField K (RatFunc.instAlgebraOfPolynomial ℚ ℚ).toSMul
      aJ.toSMul aQ.toSMul := chartTower N p
  let d : ordinaryNormalization N p ⟶ @model K fK aJ := nativeDesc N p hf hd
  have h : IsIso d := @iso_to_normal_model K fK aJ aQ tQ
    (ordinaryNormalization N p) inferInstance d inferInstance inferInstance inferInstance
  exact h

include hm hd in
def nativeIso : ordinaryNormalization N p ≅ compact N p hf := by
  letI : IsIso (nativeDesc N p hf hd) := nativeDesc_isIso N p hf hd
  exact asIso (nativeDesc N p hf hd)

theorem nativeIso_hom :
    (nativeIso N p hf hd).hom = nativeDesc N p hf hd := by
  unfold nativeIso
  rfl

section Classical

variable {Y C : Scheme} (b : Y ⟶ V) (i : Y ⟶ C) [IsOpenImmersion i]
  (j : C ⟶ JLine) [IsFinite j] [IsIntegral C]
  (e : U N p ≅ Y) (he : e.hom ≫ b = q N p) (hi : i ≫ j = b ≫ baseEmbedding)
  (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W))

include hm hd he hi normal in
/-- The given open comparison is only the genuine ordinary moduli map.
No preexisting compact isomorphism or comparison of abstract fields is
assumed. Both compactifications are identified by the common open field. -/
def classicalIso : compact N p hf ≅ C := by
  letI : IsIntegral (U N p) := ordinary_integral N p hf hd
  exact (nativeIso N p hf hd).symm.trans
    (SelectedGenericCompactNormalization318.rationalJ (q N p) baseEmbedding b i j e he hi normal)

@[reassoc] theorem classicalIso_J :
    (classicalIso N p hf hd b i j e he hi normal).hom ≫ j = compactJ N p hf := by
  letI : IsIntegral (U N p) := ordinary_integral N p hf hd
  let E := SelectedGenericCompactNormalization318.rationalJ (q N p) baseEmbedding b i j e he hi normal
  change ((nativeIso N p hf hd).inv ≫ E.hom) ≫ j = _
  rw [Category.assoc,SelectedGenericCompactNormalization318.rationalJ_over]
  apply (cancel_epi (nativeIso N p hf hd).hom).mp
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  exact ((congrArg (fun u => u ≫ compactJ N p hf) (nativeIso_hom N p hf hd)).trans
    (nativeDesc_J N p hf hd)).symm

@[reassoc] theorem classicalIso_open :
    a ≫ (classicalIso N p hf hd b i j e he hi normal).hom = e.hom ≫ i := by
  letI : IsIntegral (U N p) := ordinary_integral N p hf hd
  let E := SelectedGenericCompactNormalization318.rationalJ (q N p) baseEmbedding b i j e he hi normal
  change a ≫ (nativeIso N p hf hd).inv ≫ E.hom = _
  have hn : (q N p ≫ baseEmbedding).toNormalization ≫ (nativeIso N p hf hd).hom = a :=
    (congrArg (fun u => (q N p ≫ baseEmbedding).toNormalization ≫ u)
      (nativeIso_hom N p hf hd)).trans (nativeDesc_open N p hf hd)
  rw [← hn,Category.assoc,← Category.assoc (nativeIso N p hf hd).hom,
    Iso.hom_inv_id,Category.id_comp]
  exact SelectedGenericCompactNormalization318.rationalJ_open (q N p) baseEmbedding b i j e he hi normal

/-- Uniqueness on the original normal compact source. Agreement on the
ordinary immersion implies agreement at its same K-valued generic
point, so the universal property of the original normalization applies. -/
theorem classicalIso_unique (u : compact N p hf ⟶ C)
    (huJ : u ≫ j = compactJ N p hf) (huo : a ≫ u = e.hom ≫ i) :
    u = (classicalIso N p hf hd b i j e he hi normal).hom := by
  letI : Field (genericRoot N p) := hf.toField
  let F := genericMap (genericRoot N p)
  let t := (classicalIso N p hf hd b i j e he hi normal).hom
  let P : Scheme := Spec (CommRingCat.of (genericRoot N p))
  let k : P ⟶ U N p := Spec.map (CommRingCat.ofHom (genericEmbedding N p))
  have hF : k ≫ a = F.toNormalization := ordinary_original N p hf Fact.out hd
  have ht : a ≫ t = e.hom ≫ i := classicalIso_open N p hf hd b i j e he hi normal
  have hG : F.toNormalization ≫ u = F.toNormalization ≫ t := calc
    F.toNormalization ≫ u = (k ≫ a) ≫ u :=
      congrArg (fun w : P ⟶ compact N p hf => w ≫ u) hF.symm
    _ = k ≫ (a ≫ u) := Category.assoc k a u
    _ = k ≫ (a ≫ t) := congrArg (fun w : U N p ⟶ C => k ≫ w) (huo.trans ht.symm)
    _ = (k ≫ a) ≫ t := (Category.assoc k a t).symm
    _ = F.toNormalization ≫ t :=
      congrArg (fun w : P ⟶ compact N p hf => w ≫ t) hF
  exact Scheme.Hom.normalization.hom_ext F u t j hG huJ
    (classicalIso_J N p hf hd b i j e he hi normal)

end Classical
end SelectedOriginalCompactClassicalComparison318

#print axioms SelectedOriginalCompactClassicalComparison318.nativeDesc_isIso
#print axioms SelectedOriginalCompactClassicalComparison318.classicalIso_open
#print axioms SelectedOriginalCompactClassicalComparison318.classicalIso_unique
