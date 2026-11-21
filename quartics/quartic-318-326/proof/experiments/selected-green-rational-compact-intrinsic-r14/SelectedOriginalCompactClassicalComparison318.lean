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
local notation "f" => (q N p ≫ baseEmbedding)

include hm hf hd in
theorem ordinary_integral : IsIntegral (U N p) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra (ordinaryRoot N p) (genericRoot N p) := (genericEmbedding N p).toAlgebra
  letI : IsIntegralClosure (ordinaryRoot N p) Base (genericRoot N p) :=
    actual_integralClosure N p Fact.out hd
  letI : IsDomain (ordinaryRoot N p) := Function.Injective.isDomain (genericEmbedding N p)
    (IsIntegralClosure.algebraMap_injective _ Base (genericRoot N p))
  infer_instance

/-- A comparison built from the actual ordinary inclusion into the
compact K-normalization, not by replacing its underlying object. -/
def nativeDesc : ordinaryNormalization N p ⟶ compact N p hf := by
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  exact f.normalizationDesc a (compactJ N p hf) (ordinary_over_J N p hf Fact.out hd).symm

@[reassoc] theorem nativeDesc_open :
    f.toNormalization ≫ nativeDesc N p hf hd = a := by
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  exact f.toNormalization_normalizationDesc a (compactJ N p hf)
    (ordinary_over_J N p hf Fact.out hd).symm

@[reassoc] theorem nativeDesc_J :
    nativeDesc N p hf hd ≫ compactJ N p hf = f.fromNormalization := by
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  exact f.normalizationDesc_comp a (compactJ N p hf) (ordinary_over_J N p hf Fact.out hd).symm

/-- The two constructions of the native compact are actually
isomorphic; the proof uses the common full ordinary generic field
and the two proved normal affine charts of the given K-model. -/
theorem nativeDesc_isIso : IsIso (nativeDesc N p hf hd) := by
  letI : IsIntegral (U N p) := ordinary_integral N p hf hd
  letI : IsIntegral (compact N p hf) := (compact_properties N p Fact.out hf).2.2.1
  letI : IsFinite (compactJ N p hf) := (compact_properties N p Fact.out hf).1
  letI : IsIntegralHom (nativeDesc N p hf hd) := by unfold nativeDesc; infer_instance
  letI : IsOpenImmersion f.toNormalization := by infer_instance
  have ha : IsDominant a :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace a a.isOpenEmbedding.isOpenMap⟩
  letI : IsDominant (f.toNormalization ≫ nativeDesc N p hf hd) := by
    rw [nativeDesc_open]
    exact ha
  letI : IsDominant (nativeDesc N p hf hd) :=
    IsDominant.of_comp f.toNormalization (nativeDesc N p hf hd)
  letI : IsIso (DominantFunctionField318.map (nativeDesc N p hf hd)) :=
    CommonOpenFunctionField318.actual_generic_iso f.toNormalization a
      (nativeDesc N p hf hd) (nativeDesc_open N p hf hd)
  let K := genericRoot N p
  letI : Field K := hf.toField
  letI : Algebra ℚ K := rationalAlgebra N p
  letI : IsScalarTower ℚ JField K := rationalTower N p
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  have hx : x ∈ (⨆ i, (sourceCover K i).1) := by
    rw [sourceCover_covers]
    trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let k := chartEmbedding K i
  have hk : x ∈ k.opensRange := (chartEmbedding_range K i).symm ▸ hi
  letI : Nonempty k.opensRange := ⟨⟨x,hk⟩⟩
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  letI : IsIntegrallyClosed (Order K i) := closure_normal K i
  exact ⟨k.opensRange,hk,NormalAffineOpen318.restrict_isIso (nativeDesc N p hf hd)
    (CommRingCat.of (Order K i)) k⟩

def nativeIso : ordinaryNormalization N p ≅ compact N p hf := by
  letI : IsIso (nativeDesc N p hf hd) := nativeDesc_isIso N p hf hd
  exact asIso (nativeDesc N p hf hd)

section Classical

variable {Y C : Scheme} (b : Y ⟶ V) (i : Y ⟶ C) [IsOpenImmersion i]
  (j : C ⟶ JLine) [IsFinite j] [IsIntegral C]
  (e : U N p ≅ Y) (he : e.hom ≫ b = q N p) (hi : i ≫ j = b ≫ baseEmbedding)
  (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W))

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
  exact (nativeDesc_J N p hf hd).symm

@[reassoc] theorem classicalIso_open :
    a ≫ (classicalIso N p hf hd b i j e he hi normal).hom = e.hom ≫ i := by
  letI : IsIntegral (U N p) := ordinary_integral N p hf hd
  let E := SelectedGenericCompactNormalization318.rationalJ (q N p) baseEmbedding b i j e he hi normal
  change a ≫ (nativeIso N p hf hd).inv ≫ E.hom = _
  have hn : f.toNormalization ≫ (nativeIso N p hf hd).hom = a := nativeDesc_open N p hf hd
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
  have hG : F.toNormalization ≫ u = F.toNormalization ≫ t := by
    change (genericMap (genericRoot N p)).toNormalization ≫ u =
      (genericMap (genericRoot N p)).toNormalization ≫ t
    rw [← ordinary_original N p hf Fact.out hd]
    simp only [Category.assoc,huo,t,classicalIso_open]
  exact Scheme.Hom.normalization.hom_ext F u t j hG huJ
    (classicalIso_J N p hf hd b i j e he hi normal)

end Classical
end SelectedOriginalCompactClassicalComparison318

#print axioms SelectedOriginalCompactClassicalComparison318.nativeDesc_isIso
#print axioms SelectedOriginalCompactClassicalComparison318.classicalIso_open
#print axioms SelectedOriginalCompactClassicalComparison318.classicalIso_unique
