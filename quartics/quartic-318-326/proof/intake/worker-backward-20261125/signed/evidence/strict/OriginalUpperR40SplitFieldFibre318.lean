module
public import OriginalLiteralThickNodeReesAtlas318
public import OriginalUpperR40SplitCentralField318
public import OriginalUpperR40SplitCentralScalar318
public import OriginalUpperR40SplitOuterScalar318
public import OriginalUpperR40PullbackAffine318
public section
noncomputable section

namespace OriginalUpperR40SplitFieldFibre318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Polynomial
open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalThickCentralReesChart318 (O I x y w hw oldToNew)
open OriginalAffineReesChartLocal318 (degree_one_overlap)
open OriginalLiteralThickNodeReesAtlas318 (central outer covers central_over outer_over)
open OriginalUpperR40PullbackChart318 (lift Pj localRead)
open OriginalUpperR40PullbackAffine318 (affineIso affineIso_read)
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem range_iso_comp {A B D : Scheme} (a : A ⟶ B) (j : B ⟶ D) [IsIso a] :
    Set.range (a ≫ j) = Set.range j := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a t, (Scheme.Hom.comp_apply a j t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨v, hv⟩ := (Scheme.homeoOfIso (asIso a)).surjective t
    exact ⟨v, by rw [Scheme.Hom.comp_apply]; exact congrArg j hv⟩

variable {R : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (hq : Irreducible q) (d : ℕ)
variable {k : Type} [Field k] [Algebra R k]
variable (f : O q d →ₐ[R] k)

abbrev model := blowup (I q d)
abbrev toOld := projection (I q d)

abbrev baseRead : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (O q d)) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)
abbrev cf := central q d hq.ne_zero
abbrev ofib (b : Bool) := outer q d hq.ne_zero b

theorem central_range :
    Set.range (cf q hq d) =
      (Proj.basicOpen (grade (I q d)) (generator (I q d) (w q d) (hw q d)) : Set (model q d)) := by
  let : Algebra R (OriginalThickCentralReesChart318.B q d) :=
    (OriginalThickCentralReesChart318.coefficients q d).toAlgebra
  let E := (OriginalThickCentralReesIso318.chartIso q d hq.ne_zero).toRingEquiv.toCommRingCatIso
  let e := Scheme.Spec.mapIso E.symm.op
  let j := chartMap (I q d) (w q d) (hw q d)
  change Set.range (e.hom ≫ j) = _
  rw [range_iso_comp]
  let : IsOpenImmersion j := by
    change IsOpenImmersion (Proj.awayι (grade (I q d)) (generator (I q d) (w q d) (hw q d))
      (generator_grade (I q d) (w q d) (hw q d)) (by decide))
    infer_instance
  change (j.opensRange : Set (model q d)) = _
  change ((Proj.awayι (grade (I q d)) (generator (I q d) (w q d) (hw q d))
    (generator_grade (I q d) (w q d) (hw q d)) (by decide)).opensRange : Set (model q d)) = _
  rw [Proj.opensRange_awayι]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
private theorem degree_one_ratio (b : Bool) :
    HomogeneousLocalization.Away.isLocalizationElem
      (generator_grade (I q d) (OriginalThickOuterReesChart318.a q d b)
        (OriginalThickOuterReesChart318.a_mem q d b))
      (generator_grade (I q d) (w q d) (hw q d)) =
    OriginalThickOuterReesChart318.t q d b :=
  degree_one_overlap (I q d) (OriginalThickOuterReesChart318.a q d b)
    (OriginalThickOuterReesChart318.a_mem q d b) (w q d) (hw q d)

include hq in
/-- On the real outer scheme chart the central open is the nonzero
locus of the transported genuine ratio qT/(aT), i.e. its second axis. -/
theorem outer_preimage_central (b : Bool) :
    (ofib q hq d b) ⁻¹ᵁ
      Proj.basicOpen (grade (I q d)) (generator (I q d) (w q d) (hw q d)) =
      PrimeSpectrum.basicOpen (yAxis q) := by
  let A := OriginalThickOuterReesChart318.a q d b
  let H := OriginalThickOuterReesChart318.a_mem q d b
  let : Algebra R (OriginalThickOuterReesChart318.C q d b) :=
    (OriginalThickOuterReesChart318.coefficients q d b).toAlgebra
  let E := OriginalThickOuterReesIso318.chartIso q d b hq.ne_zero
  have htp : E.symm (OriginalThickOuterReesChart318.t q d b) = yAxis q := by
    apply E.injective
    rw [AlgEquiv.apply_symm_apply]
    change OriginalThickOuterReesChart318.t q d b =
      OriginalThickOuterReesChart318.coordinates q d b (yAxis q)
    exact (eval_y q _ _ (OriginalThickOuterReesChart318.tr q d b)).symm
  have hpre : (chartMap (I q d) A H) ⁻¹ᵁ
      Proj.basicOpen (grade (I q d)) (generator (I q d) (w q d) (hw q d)) =
      PrimeSpectrum.basicOpen (OriginalThickOuterReesChart318.t q d b) := by
    unfold chartMap
    erw [Proj.awayι_preimage_basicOpen (𝒜 := grade (I q d))
      (generator_grade (I q d) A H) (by decide : 0 < (1 : ℕ))
      (generator_grade (I q d) (w q d) (hw q d)) (by decide : 0 < (1 : ℕ))]
    rw [degree_one_ratio]
  change (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ chartMap (I q d) A H) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, hpre, SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen htp

variable (hzero : algebraMap R k q = 0)
variable (hx : f (x q d) = 0) (hy : f (y q d) = 0)

include hzero hx hy in
theorem central_connected :
    ConnectedSpace (Pj (toOld q d) (baseRead q d f) (cf q hq d)) := by
  let : Algebra (O q d) k := f.toRingHom.toAlgebra
  let : Algebra (O q d) (Node (q^d)) := (oldToNew q d).toRingHom.toAlgebra
  let e := affineIso (toOld q d) (cf q hq d) (central_over q d hq.ne_zero)
    (OriginalUpperR40SplitCentralScalar318.tensor q d f hzero hx hy)
  have hC : ConnectedSpace (Spec (CommRingCat.of (Node (OriginalUpperR40SplitCentralScalar318.cbar
      (k:=k) q d)))) := by
    have he := OriginalUpperR40SplitCentralScalar318.cbar_eq q d hzero
    by_cases hd : d = 0
    · exact (he.trans (ite_eq_left hd)).symm ▸ OriginalUpperR40SplitCentralField318.one_connected k
    · exact (he.trans (ite_eq_right hd)).symm ▸ OriginalUpperR40SplitCentralField318.zero_connected k
  let : ConnectedSpace (Spec (CommRingCat.of (Node (OriginalUpperR40SplitCentralScalar318.cbar
      (k:=k) q d)))) := hC
  exact (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous

include hzero hx hy in
theorem outer_actual_iso (b : Bool) :
    ∃ e : Spec (CommRingCat.of k[X]) ≅ Pj (toOld q d) (baseRead q d f) (ofib q hq d b),
      e.hom ≫ localRead (toOld q d) (baseRead q d f) (ofib q hq d b) =
        Spec.map (CommRingCat.ofHom (OriginalUpperR40SplitOuterScalar318.lineRead q hzero).toRingHom) := by
  let : Algebra (O q d) k := f.toRingHom.toAlgebra
  let : Algebra (O q d) (Node q) := (OriginalThickOuterReesChart318.oldToOuter q d b).toRingHom.toAlgebra
  let t := OriginalUpperR40SplitOuterScalar318.tensor q d b f hzero hx hy
  let e := affineIso (toOld q d) (ofib q hq d b) (outer_over q d hq.ne_zero b) t
  have hr := affineIso_read (toOld q d) (ofib q hq d b) (outer_over q d hq.ne_zero b) t
  have hmap : (t.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R:=O q d) (A:=k) (B:=Node q)).toRingHom) =
      (OriginalUpperR40SplitOuterScalar318.lineRead q hzero).toRingHom := by
    apply RingHom.ext
    intro z
    exact OriginalUpperR40SplitOuterScalar318.tensor_right q d b f hzero hx hy z
  refine ⟨e, ?_⟩
  exact hr.trans (congrArg (fun g : Node q →+* k[X] => Spec.map (CommRingCat.ofHom g)) hmap)

include hzero in
/-- In either actual outer pullback chart, the preimage of the true
central Proj open is literally D(X) on the coordinate affine line. -/
theorem outer_field_preimage (b : Bool)
    (e : Spec (CommRingCat.of k[X]) ≅ Pj (toOld q d) (baseRead q d f) (ofib q hq d b))
    (he : e.hom ≫ localRead (toOld q d) (baseRead q d f) (ofib q hq d b) =
      Spec.map (CommRingCat.ofHom (OriginalUpperR40SplitOuterScalar318.lineRead q hzero).toRingHom)) :
    ((e.hom ≫ lift (toOld q d) (baseRead q d f) (ofib q hq d b)) ≫
        pullback.fst (toOld q d) (baseRead q d f)) ⁻¹ᵁ
      Proj.basicOpen (grade (I q d)) (generator (I q d) (w q d) (hw q d)) =
      PrimeSpectrum.basicOpen (X : k[X]) := by
  have hh : (e.hom ≫ lift (toOld q d) (baseRead q d f) (ofib q hq d b)) ≫
      pullback.fst (toOld q d) (baseRead q d f) =
    Spec.map (CommRingCat.ofHom (OriginalUpperR40SplitOuterScalar318.lineRead q hzero).toRingHom) ≫
      ofib q hq d b := by
    rw [Category.assoc, OriginalUpperR40PullbackChart318.overChart, ← Category.assoc, he]
  rw [hh, Scheme.Hom.comp_preimage, outer_preimage_central, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (OriginalUpperR40SplitOuterScalar318.lineRead q hzero (yAxis q)) = _
  unfold OriginalUpperR40SplitOuterScalar318.lineRead
  rw [eval_y]

include hq hzero hx hy in
theorem from_algebra_map :
    ConnectedSpace (↥(pullback (C := Scheme) (toOld q d) (baseRead q d f))) := by
  let p := toOld q d
  let r := baseRead q d f
  let c := lift p r (cf q hq d)
  obtain ⟨e₁, he₁⟩ := outer_actual_iso q hq d f hzero hx hy true
  obtain ⟨e₂, he₂⟩ := outer_actual_iso q hq d f hzero hx hy false
  let a₁ := e₁.hom ≫ lift p r (ofib q hq d true)
  let a₂ := e₂.hom ≫ lift p r (ofib q hq d false)
  let η := genericPoint (Spec (CommRingCat.of k[X]))
  have hη : η = (⊥ : PrimeSpectrum k[X]) := by
    -- The closure calculation of Mathlib.AlgebraicGeometry.FunctionField,
    -- using only the already imported prime-spectrum API.
    apply (genericPoint_spec (Spec (CommRingCat.of k[X]))).eq
    rw [isGenericPoint_def]
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
    rw [← PrimeSpectrum.zeroLocus_singleton_zero]
    rfl
  let : ConnectedSpace (Pj p r (cf q hq d)) := central_connected q hq d f hzero hx hy
  have hit (b : Bool)
      (e : Spec (CommRingCat.of k[X]) ≅ Pj p r (ofib q hq d b))
      (he : e.hom ≫ localRead p r (ofib q hq d b) =
        Spec.map (CommRingCat.ofHom (OriginalUpperR40SplitOuterScalar318.lineRead q hzero).toRingHom)) :
      (e.hom ≫ lift p r (ofib q hq d b)) η ∈ Set.range c := by
    rw [show c = lift p r (cf q hq d) from rfl, OriginalUpperR40PullbackChart318.range_eq]
    change pullback.fst p r ((e.hom ≫ lift p r (ofib q hq d b)) η) ∈ Set.range (cf q hq d)
    rw [central_range]
    change η ∈ (((e.hom ≫ lift p r (ofib q hq d b)) ≫ pullback.fst p r) ⁻¹ᵁ
      Proj.basicOpen (grade (I q d)) (generator (I q d) (w q d) (hw q d)) : Set _)
    rw [outer_field_preimage q hq d f hzero b e he]
    change (X : k[X]) ∉ η.asIdeal
    rw [hη]
    exact fun h => Polynomial.X_ne_zero (Ideal.mem_bot.mp h)
  apply OriginalUpperR40PullbackChart318.connected_of_dense_arms c a₁ a₂ c.continuous
    a₁.continuous a₂.continuous ?_ η η (genericPoint_spec _) (genericPoint_spec _)
    (hit true e₁ he₁) (hit false e₂ he₂)
  intro z
  have hr y : y ∈ Set.range (cf q hq d) ∨ y ∈ Set.range (ofib q hq d true) ∨
      y ∈ Set.range (ofib q hq d false) := by
    rcases covers q d hq.ne_zero y with h | ⟨b,h⟩
    · exact Or.inl h
    · cases b
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  have h := OriginalUpperR40PullbackChart318.cover p r (cf q hq d)
    (ofib q hq d true) (ofib q hq d false) hr z
  simpa only [c, a₁, a₂, range_iso_comp] using h

include hq in
/-- The entire literal R40 point fibre over any field at the actual
marked centre. The affine ring map and all three vanishing reads are
extracted from the supplied scheme morphism, not extra hypotheses. -/
theorem split_field {K : Type} [Field K]
    (r : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (O q d)))
    (hr : ∀ v, (r v).asIdeal = I q d) :
    ConnectedSpace (↥(pullback (C := Scheme) (toOld q d) r)) := by
  obtain ⟨g, hg⟩ := Spec.map_surjective r
  let : Algebra R K := (g.hom.comp (algebraMap R (O q d))).toAlgebra
  let f : O q d →ₐ[R] K := ⟨g.hom, fun _ => rfl⟩
  have hf : baseRead q d f = r := hg
  have hker (z : O q d) (hz : z ∈ I q d) : f z = 0 := by
    have hp := hr (IsLocalRing.closedPoint K)
    rw [← hf] at hp
    have hn : z ∈ (baseRead q d f (IsLocalRing.closedPoint K)).asIdeal := by
      rw [hp]
      exact hz
    change f z ∈ IsLocalRing.maximalIdeal K at hn
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hn
  have hzero : algebraMap R K q = 0 :=
    (f.commutes q).symm.trans (hker (w q d) (hw q d))
  rw [← hf]
  exact from_algebra_map q hq d f hzero
    (hker (x q d) (Ideal.subset_span (by simp)))
    (hker (y q d) (Ideal.subset_span (by simp)))

end OriginalUpperR40SplitFieldFibre318

#print axioms OriginalUpperR40SplitFieldFibre318.outer_preimage_central
#print axioms OriginalUpperR40SplitFieldFibre318.central_connected
#print axioms OriginalUpperR40SplitFieldFibre318.outer_actual_iso
#print axioms OriginalUpperR40SplitFieldFibre318.outer_field_preimage
#print axioms OriginalUpperR40SplitFieldFibre318.from_algebra_map
#print axioms OriginalUpperR40SplitFieldFibre318.split_field
