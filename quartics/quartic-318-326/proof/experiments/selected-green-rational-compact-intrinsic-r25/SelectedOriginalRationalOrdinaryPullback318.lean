module
public import SelectedOriginalRationalOrdinaryGeometry318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open SelectedOriginalGenericChartClosures318 SelectedRationalGenericFromComplex318
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryIntegral318 SelectedOriginalRationalOrdinaryOpening318
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryGeometry318

namespace SelectedOriginalRationalOrdinaryPullback318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hf : IsField (genericRoot N p))
variable (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))

/-- Exact agreement on all polynomial functions of the printed J,
not merely on their generic images in unrelated field copies. -/
theorem openingIso_polynomial (a : ℚ[X]) :
    openingIso N p hf hp hd
      (algebraMap (CompactOrder N p hf) (Localized N p hf)
        (algebraMap ℚ[X] (CompactOrder N p hf) a)) =
      algebraMap Base (ordinaryRoot N p) (algebraMap ℚ[X] Base a) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : IsScalarTower ℚ[X] Base QJ := rattower
  letI : Algebra (ordinaryRoot N p) (genericRoot N p) := (genericEmbedding N p).toAlgebra
  letI : IsIntegralClosure (ordinaryRoot N p) Base (genericRoot N p) :=
    actual_integralClosure N p hp hd
  have hj : Function.Injective (genericEmbedding N p) :=
    IsIntegralClosure.algebraMap_injective (ordinaryRoot N p) Base (genericRoot N p)
  apply hj
  rw [openingIso_order_value]
  change algebraMap QJ (genericRoot N p) (basePolynomial 1 a) =
    tensorComparison N p
      (algebraMap (ordinaryRoot N p) (Tensor N p)
        (algebraMap Base (ordinaryRoot N p) (algebraMap ℚ[X] Base a)))
  rw [← IsScalarTower.algebraMap_apply Base (ordinaryRoot N p) (Tensor N p),AlgEquiv.commutes]
  change algebraMap QJ (genericRoot N p) (basePolynomial 1 a) =
    algebraMap QJ (genericRoot N p) (algebraMap Base QJ (algebraMap ℚ[X] Base a))
  rw [← IsScalarTower.algebraMap_apply ℚ[X] Base QJ]
  simp [basePolynomial]

@[expose] def baseEmbedding :
    Spec (CommRingCat.of Base) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.algebraMap ℚ[X] Base ≫ JLineAtlas318.chart ℚ 1

instance baseEmbedding_open : IsOpenImmersion baseEmbedding := by
  unfold baseEmbedding
  letI : IsOpenImmersion (Spec.algebraMap ℚ[X] Base) :=
    IsOpenImmersion.of_isLocalization denominator
  infer_instance

theorem baseEmbedding_range : baseEmbedding.opensRange = baseOrdinary := by
  have hloc : (Spec.algebraMap ℚ[X] Base).opensRange = PrimeSpectrum.basicOpen denominator := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  unfold baseEmbedding
  rw [Scheme.Hom.opensRange_comp,hloc] <;> rfl

private theorem spec_projection_of_value {A B C D E : Type}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
    {Y : Scheme}
    (a : A →+* B) (b : B →+* C) (c : C →+* D) (r : A →+* E) (s : E →+* D)
    (j : Spec (CommRingCat.of A) ⟶ Y)
    (hv : ∀ x, c (b (a x)) = s (r x)) :
    Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom b) ≫
      Spec.map (CommRingCat.ofHom a) ≫ j =
    Spec.map (CommRingCat.ofHom s) ≫ Spec.map (CommRingCat.ofHom r) ≫ j := by
  let a' := CommRingCat.ofHom a
  let b' := CommRingCat.ofHom b
  let c' := CommRingCat.ofHom c
  let r' := CommRingCat.ofHom r
  let s' := CommRingCat.ofHom s
  have he : a' ≫ b' ≫ c' = r' ≫ s' := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simpa only [a',b',c',r',s',CommRingCat.hom_comp,CommRingCat.hom_ofHom,
      RingHom.comp_apply] using hv x
  have hl : (Spec.map c' ≫ Spec.map b') ≫ Spec.map a' = Spec.map (a' ≫ b' ≫ c') := by
    rw [← Spec.map_comp,← Spec.map_comp]
  have hr : Spec.map s' ≫ Spec.map r' = Spec.map (r' ≫ s') :=
    (Spec.map_comp r' s').symm
  have hm : (Spec.map c' ≫ Spec.map b') ≫ Spec.map a' = Spec.map s' ≫ Spec.map r' :=
    hl.trans ((congrArg Spec.map he).trans hr.symm)
  have hh := congrArg (fun x : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of A) => x ≫ j) hm
  simpa only [a',b',c',r',s',Category.assoc] using hh

/-- The projection of the reconstructed ordinary source is the
original J-line projection, as equality of global scheme morphisms. -/
theorem ordinary_over_J :
    ordinaryEmbedding N p hf hp hd ≫ compactJ N p hf =
      Spec.algebraMap Base (ordinaryRoot N p) ≫ baseEmbedding := by
  let A := ℚ[X]
  let B := CompactOrder N p hf
  let C := Localized N p hf
  let D := ordinaryRoot N p
  let E := Base
  let a : A →+* B := algebraMap A B
  let b : B →+* C := algebraMap B C
  let c : C →+* D := (openingIso N p hf hp hd).toRingHom
  let r : A →+* E := algebraMap A E
  let s : E →+* D := algebraMap E D
  let j : Spec (CommRingCat.of A) ⟶ ProjectiveJLine318.scheme ℚ := JLineAtlas318.chart ℚ 1
  have hv (x : A) : c (b (a x)) = s (r x) := openingIso_polynomial N p hf hp hd x
  have hmain := @spec_projection_of_value A B C D E
    inferInstance inferInstance inferInstance inferInstance inferInstance _ a b c r s j hv
  have h₀ : ordinaryEmbedding N p hf hp hd ≫ compactJ N p hf =
      rootMap N p hf hp hd ≫ localizeMap N p hf ≫ (chart N p hf ≫ compactJ N p hf) := by
    simp only [ordinaryEmbedding,Category.assoc]
  have hroot : rootMap N p hf hp hd = Spec.map (CommRingCat.ofHom c) := rfl
  have hloc : localizeMap N p hf = Spec.map (CommRingCat.ofHom b) := rfl
  have hchart : chart N p hf ≫ compactJ N p hf = Spec.map (CommRingCat.ofHom a) ≫ j :=
    chart_over_J N p hf
  have h₁ := congrArg₂ (· ≫ ·) hroot (congrArg₂ (· ≫ ·) hloc hchart)
  have hbase : baseEmbedding = Spec.map (CommRingCat.ofHom r) ≫ j := rfl
  have hs : Spec.algebraMap Base (ordinaryRoot N p) = Spec.map (CommRingCat.ofHom s) := rfl
  have h₂ := congrArg₂ (· ≫ ·) hs hbase
  exact Eq.trans h₀ (Eq.trans h₁ (Eq.trans hmain h₂.symm))

/-- Not just an isomorphic open: it is the full cartesian base change
of the normalization projection along the exact ordinary J-chart. -/
theorem ordinary_pullback :
    IsPullback (Spec.algebraMap Base (ordinaryRoot N p)) (ordinaryEmbedding N p hf hp hd)
      baseEmbedding (compactJ N p hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (ordinary_over_J N p hf hp hd) (by
    rw [baseEmbedding_range,ordinaryEmbedding_range] <;> rfl)

end SelectedOriginalRationalOrdinaryPullback318

#print axioms SelectedOriginalRationalOrdinaryPullback318.ordinary_over_J
#print axioms SelectedOriginalRationalOrdinaryPullback318.ordinary_pullback
