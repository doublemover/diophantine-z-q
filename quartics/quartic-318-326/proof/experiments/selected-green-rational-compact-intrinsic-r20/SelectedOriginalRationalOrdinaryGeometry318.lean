module
public import SelectedOriginalRationalOrdinaryOpening318
public import SelectedRationalRootCompactInstall318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericCompactNormal318
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryIntegral318 SelectedOriginalRationalOrdinaryOpening318
open SelectedRationalRootCompactInstall318

namespace SelectedOriginalRationalOrdinaryGeometry318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hf : IsField (genericRoot N p))

/-- Install the exact scalar keys of the generic chart construction.
The native standalone rational SMul interface is not the projected
action expected by these algebra-parametric scheme charts. -/
abbrev chartJAlgebra : Algebra JField (genericRoot N p) :=
  AdjoinRoot.instAlgebra (S := JField) (p.map (SelectedRationalGenericFromComplex318.rationalGenericMap N))

theorem chartTower : @IsScalarTower ℚ JField (genericRoot N p)
    (RatFunc.instAlgebraOfPolynomial ℚ ℚ).toSMul
    (chartJAlgebra N p).toSMul (rationalAlgebra N p).toSMul :=
  @IsScalarTower.of_algebraMap_eq' ℚ JField (genericRoot N p)
    inferInstance inferInstance inferInstance
    (RatFunc.instAlgebraOfPolynomial ℚ ℚ) (chartJAlgebra N p) (rationalAlgebra N p) (by rfl)

/-- The genuine open of the original projective base: the affine j
chart with the original elliptic values 0 and 1728 removed. -/
@[expose] def baseOrdinary : (ProjectiveJLine318.scheme ℚ).Opens :=
  JLineAtlas318.chart ℚ 1 ''ᵁ PrimeSpectrum.basicOpen denominator

abbrev actualOpen : (compact N p hf).Opens := (compactJ N p hf)⁻¹ᵁ baseOrdinary

@[expose] def chart :
    Spec (CommRingCat.of (CompactOrder N p hf)) ⟶ compact N p hf :=
  @SelectedOriginalGenericCompactCharts318.chartEmbedding (genericRoot N p)
    hf.toField (chartJAlgebra N p) (rationalAlgebra N p) (chartTower N p) 1

instance chart_open : IsOpenImmersion (chart N p hf) := by
  let K := genericRoot N p
  letI : Field K := hf.toField
  letI : Algebra JField K := chartJAlgebra N p
  let f := Spec.map (CommRingCat.ofHom
    (@SelectedOriginalGenericCompactCharts318.actualSections K hf.toField
      (chartJAlgebra N p) (rationalAlgebra N p) (chartTower N p) 1).toRingHom)
  let g := (sourceCover K 1).2.fromSpec
  letI : IsIso f := @SelectedOriginalGenericCompactCharts318.chartSpec_isIso K hf.toField
    (chartJAlgebra N p) (rationalAlgebra N p) (chartTower N p) 1
  change IsOpenImmersion (f ≫ g)
  exact @IsOpenImmersion.comp _ _ _ f g (IsOpenImmersion.of_isIso f)
    (sourceCover K 1).2.isOpenImmersion_fromSpec

theorem chart_range :
    (chart N p hf).opensRange = (compactJ N p hf)⁻¹ᵁ(targetCover 1).1 :=
  @SelectedOriginalGenericCompactCharts318.chartEmbedding_range (genericRoot N p)
    hf.toField (chartJAlgebra N p) (rationalAlgebra N p) (chartTower N p) 1

theorem chart_over_J :
    chart N p hf ≫ compactJ N p hf =
      Spec.algebraMap ℚ[X] (CompactOrder N p hf) ≫ JLineAtlas318.chart ℚ 1 :=
  @SelectedOriginalGenericCompactCharts318.chart_over_base (genericRoot N p)
    hf.toField (chartJAlgebra N p) (rationalAlgebra N p) (chartTower N p) 1

theorem chart_ordinary_preimage :
    (chart N p hf)⁻¹ᵁ(actualOpen N p hf) =
      PrimeSpectrum.basicOpen (openParameter N p hf) := by
  change (chart N p hf)⁻¹ᵁ((compactJ N p hf)⁻¹ᵁ baseOrdinary) = _
  rw [← Scheme.Hom.comp_preimage,chart_over_J,Scheme.Hom.comp_preimage]
  let j : Spec (CommRingCat.of ℚ[X]) ⟶ ProjectiveJLine318.scheme ℚ := JLineAtlas318.chart ℚ 1
  let U : (Spec (CommRingCat.of ℚ[X])).Opens := PrimeSpectrum.basicOpen denominator
  letI : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (JLineAtlas318.chart ℚ 1))
  have hp : j ⁻¹ᵁ baseOrdinary = U := Scheme.Hom.preimage_image_eq j U
  change (Spec.algebraMap ℚ[X] (CompactOrder N p hf)) ⁻¹ᵁ (j ⁻¹ᵁ baseOrdinary) = _
  rw [hp]
  exact SpecMap_preimage_basicOpen
    (CommRingCat.ofHom (algebraMap ℚ[X] (CompactOrder N p hf))) denominator

abbrev Localized := Localization.Away (openParameter N p hf)

@[expose] def localizeMap :
    Spec (CommRingCat.of (Localized N p hf)) ⟶ Spec (CommRingCat.of (CompactOrder N p hf)) :=
  Spec.algebraMap (CompactOrder N p hf) (Localized N p hf)

instance localizeMap_open : IsOpenImmersion (localizeMap N p hf) :=
  IsOpenImmersion.of_isLocalization (openParameter N p hf)

theorem localizeMap_range :
    (localizeMap N p hf).opensRange = PrimeSpectrum.basicOpen (openParameter N p hf) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range _ _

variable (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))

@[expose] def rootMap :
    Spec (CommRingCat.of (ordinaryRoot N p)) ⟶ Spec (CommRingCat.of (Localized N p hf)) :=
  Spec.map (CommRingCat.ofHom (openingIso N p hf hp hd).toRingHom)

private theorem spec_equiv_isIso {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  let E := Scheme.Spec.mapIso e.toCommRingCatIso.op
  change IsIso E.hom
  exact inferInstance

instance rootMap_isIso : IsIso (rootMap N p hf hp hd) :=
  @spec_equiv_isIso (Localized N p hf) (ordinaryRoot N p)
    inferInstance inferInstance (openingIso N p hf hp hd)

/-- Actual immersion of the whole rational ordinary root algebra into
the whole compact model, defined by the exact localization isomorphism. -/
@[expose] def ordinaryEmbedding :
    Spec (CommRingCat.of (ordinaryRoot N p)) ⟶ compact N p hf :=
  rootMap N p hf hp hd ≫ localizeMap N p hf ≫ chart N p hf

instance ordinaryEmbedding_open : IsOpenImmersion (ordinaryEmbedding N p hf hp hd) := by
  unfold ordinaryEmbedding
  infer_instance

theorem ordinaryEmbedding_range :
    (ordinaryEmbedding N p hf hp hd).opensRange = actualOpen N p hf := by
  have hle : actualOpen N p hf ≤ (compactJ N p hf)⁻¹ᵁ(targetCover 1).1 :=
    (compactJ N p hf).preimage_mono ((JLineAtlas318.chart ℚ 1).image_mono le_top)
  unfold ordinaryEmbedding
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Hom.opensRange_comp,localizeMap_range,
    ← chart_ordinary_preimage,Scheme.Hom.image_preimage_eq_opensRange_inf,
    chart_range,inf_eq_right.mpr hle]

/-- The requested genuine preimage open, not just an abstract ring of
the same degree, with unique factorization into the actual compact curve. -/
def ordinaryIso :
    Spec (CommRingCat.of (ordinaryRoot N p)) ≅ (actualOpen N p hf).toScheme :=
  IsOpenImmersion.isoOfRangeEq (ordinaryEmbedding N p hf hp hd) (actualOpen N p hf).ι
    (by rw [← Scheme.Hom.coe_opensRange,ordinaryEmbedding_range,Scheme.Opens.range_ι])

theorem ordinaryIso_fac :
    (ordinaryIso N p hf hp hd).hom ≫ (actualOpen N p hf).ι =
      ordinaryEmbedding N p hf hp hd :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem spec_three_of_value {A B C K : Type}
    [CommRing A] [CommRing B] [CommRing C] [CommRing K]
    (a : A →+* B) (b : B →+* C) (c : C →+* K) (d : A →+* K)
    (hv : ∀ x, c (b (a x)) = d x) :
    (Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom b)) ≫
      Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom d) := by
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  simpa only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply] using hv x

/-- This ordinary embedding has the very SAME generic point, not
merely a finite map of the same degree over an abstract projective line. -/
theorem ordinary_original :
    letI : Field (genericRoot N p) := hf.toField
    Spec.map (CommRingCat.ofHom (genericEmbedding N p)) ≫ ordinaryEmbedding N p hf hp hd =
      (genericMap (genericRoot N p)).toNormalization := by
  letI : Field (genericRoot N p) := hf.toField
  let A := CompactOrder N p hf
  let B := Localized N p hf
  let C := ordinaryRoot N p
  let K := genericRoot N p
  let a : A →+* B := algebraMap A B
  let b : B →+* C := (openingIso N p hf hp hd).toRingHom
  let c : C →+* K := genericEmbedding N p
  let d : A →+* K := SelectedOriginalCompactOverlapIdentity318.orderVal K 1
  have hv (x : A) : c (b (a x)) = d x := openingIso_order_value N p hf hp hd x
  have h := @spec_three_of_value A B C K
    inferInstance inferInstance inferInstance inferInstance a b c d hv
  have hg : Spec.map (CommRingCat.ofHom (genericEmbedding N p)) =
      Spec.map (CommRingCat.ofHom c) := rfl
  have hr : rootMap N p hf hp hd = Spec.map (CommRingCat.ofHom b) := rfl
  have hl : localizeMap N p hf = Spec.map (CommRingCat.ofHom a) := rfl
  have htwo := congrArg₂ (· ≫ ·) hg hr
  have hthree := congrArg₂ (· ≫ ·) htwo hl
  have hs :
      (Spec.map (CommRingCat.ofHom (genericEmbedding N p)) ≫ rootMap N p hf hp hd) ≫
        localizeMap N p hf = Spec.map (CommRingCat.ofHom d) :=
    hthree.trans h
  calc
    _ = ((Spec.map (CommRingCat.ofHom (genericEmbedding N p)) ≫ rootMap N p hf hp hd) ≫
        localizeMap N p hf) ≫ chart N p hf := by
      simp only [ordinaryEmbedding,Category.assoc]
    _ = Spec.map (CommRingCat.ofHom d) ≫ chart N p hf :=
      congrArg (fun f => f ≫ chart N p hf) hs
    _ = (genericMap K).toNormalization :=
      @SelectedOriginalCompactOverlapIdentity318.chart_original K hf.toField
        (chartJAlgebra N p) (rationalAlgebra N p) (chartTower N p) 1

end SelectedOriginalRationalOrdinaryGeometry318

#print axioms SelectedOriginalRationalOrdinaryGeometry318.ordinaryIso_fac
#print axioms SelectedOriginalRationalOrdinaryGeometry318.ordinary_original
