module
public import PolynomialProjectiveChartRatios318
public import ComplexProjectiveVariableCover318
public section
noncomputable section
namespace ProjectivePreimageRegularRatios318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
open HomogeneousQuotientChart318 HomogeneousQuotientChartSupport318
variable {ι : Type*} {X : Scheme}
local instance standardGrading : GradedAlgebra (grading (ι := ι)) := MvPolynomial.gradedAlgebra
variable (f : X ⟶ Proj (grading (ι := ι)))

@[expose] def targetOpen (j : ι) : (Proj (grading (ι := ι))).Opens :=
  Proj.basicOpen grading (MvPolynomial.X j)
@[expose] def sourceOpen (j : ι) : X.Opens := f ⁻¹ᵁ targetOpen j
@[expose] def targetIso (j : ι) : (targetOpen j).toScheme ≅ Spec (CommRingCat.of (Chart j)) :=
  Proj.basicOpenIsoSpec grading (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) (by norm_num)
@[expose] def toChart (j : ι) : (sourceOpen f j).toScheme ⟶ Spec (CommRingCat.of (Chart j)) :=
  (f ∣_ targetOpen j) ≫ (targetIso j).hom

@[reassoc] theorem toChart_square (j : ι) :
    toChart f j ≫ chartMorphism j = (sourceOpen f j).ι ≫ f := by
  simp only [toChart,targetIso,chartMorphism,Proj.awayι,targetOpen,
    Category.assoc,Iso.hom_inv_id_assoc,Scheme.Hom.morphismRestrict_ι]

/-- Every standard target coordinate ratio is an ACTUAL regular global
function on its entire inverse-image open, even for a nonaffine source. -/
@[expose] def ratioSection (j i : ι) : Γ((sourceOpen f j).toScheme,⊤) :=
  (toChart f j).appTop ((Scheme.ΓSpecIso (CommRingCat.of (Chart j))).inv
    (PolynomialProjectiveChartRatios318.ratio j i))

lemma ratio_self (j : ι) : ratioSection f j j = 1 := by
  rw [ratioSection,PolynomialProjectiveChartRatios318.ratio_self,map_one,map_one]

/-- The inverse-image standard opens cover all scheme primes. -/
theorem source_cover (x : X) : ∃ j : ι, x ∈ sourceOpen f j :=
  ComplexProjectiveVariableCover318.exists_variable_nonmem (f x)

/-- Membership in the entire target standard open forces the literal
coordinate of any representing projective vector to be nonzero. -/
lemma point_coordinate_nonzero (j : ι)
    (p : Spec (CommRingCat.of ℂ) ⟶ (sourceOpen f j).toScheme)
    (v : ι → ℂ) (hv : ∃ i,v i≠0)
    (he : p ≫ (sourceOpen f j).ι ≫ f = ComplexProjectiveSchemePoint318.point v hv) :
    v j≠0 := by
  have hm : ComplexProjectiveSchemePoint318.point v hv (IsLocalRing.closedPoint ℂ) ∈
      targetOpen j := by
    rw [←he]
    exact (p (IsLocalRing.closedPoint ℂ)).property
  change MvPolynomial.X j ∉
    (ComplexProjectiveSchemePoint318.point v hv (IsLocalRing.closedPoint ℂ)).asHomogeneousIdeal at hm
  simpa only [ComplexProjectiveSchemePoint318.positive_homogeneous_mem_iff
    v hv (IsLocalRing.closedPoint ℂ) (MvPolynomial.X j) 1 (by norm_num)
      (MvPolynomial.isHomogeneous_X ℂ j),MvPolynomial.eval_X] using hm

variable (π : X ⟶ Spec (CommRingCat.of ℂ))
  (hf : f ≫ ComplexProjectiveBase318.structureMap = π)

@[reassoc] theorem chart_over_complex (j : ι) :
    toChart f j ≫ Spec.map (CommRingCat.ofHom (PolynomialProjectiveChartRatios318.scalar j)) =
      (sourceOpen f j).ι ≫ π := by
  rw [←PolynomialProjectiveChartRatios318.chart_over_complex,←Category.assoc,
    toChart_square,Category.assoc,hf]

/-- Extract the full chart ring map from a genuine complex point, with
its entire scalar square, before computing any coordinate values. -/
theorem point_chart (j : ι) (p : Spec (CommRingCat.of ℂ) ⟶ (sourceOpen f j).toScheme)
    (hp : p ≫ (sourceOpen f j).ι ≫ π = 𝟙 _) :
    ∃ φ : Chart j →+* ℂ,
      p ≫ toChart f j = Spec.map (CommRingCat.ofHom φ) ∧
      ∀ c : ℂ, φ (PolynomialProjectiveChartRatios318.scalar j c) = c := by
  obtain ⟨φ,hφ⟩ := Spec.map_surjective (p ≫ toChart f j)
  refine ⟨φ.hom,hφ.symm,?_⟩
  have hc : CommRingCat.ofHom (PolynomialProjectiveChartRatios318.scalar j) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_id,hφ,Category.assoc,chart_over_complex f π hf]
    exact hp
  intro c
  exact congrArg (fun g => g.hom c) hc

/-- Genuine evaluation of the regular ratio through p.appTop agrees
with the full actual affine chart ring map. -/
lemma point_ratio (j i : ι) (p : Spec (CommRingCat.of ℂ) ⟶ (sourceOpen f j).toScheme)
    (φ : Chart j →+* ℂ) (hφ : p ≫ toChart f j = Spec.map (CommRingCat.ofHom φ)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (ratioSection f j i)) =
      φ (PolynomialProjectiveChartRatios318.ratio j i) := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((p ≫ toChart f j).appTop ((Scheme.ΓSpecIso (CommRingCat.of (Chart j))).inv
      (PolynomialProjectiveChartRatios318.ratio j i))) = _
  rw [hφ]
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom φ)) (PolynomialProjectiveChartRatios318.ratio j i)
  rw [←he]
  exact Iso.inv_hom_id_apply _ _

/-- Literal projective-vector formula on EVERY complex point of the
whole preimage open. This is an evaluation of already-constructed
regular functions, not a definition by point values. -/
theorem evaluation (j i : ι) (p : Spec (CommRingCat.of ℂ) ⟶ (sourceOpen f j).toScheme)
    (hp : p ≫ (sourceOpen f j).ι ≫ π = 𝟙 _)
    (v : ι → ℂ) (hv : ∃ i,v i≠0) (hj : v j≠0)
    (hvpoint : p ≫ (sourceOpen f j).ι ≫ f = ComplexProjectiveSchemePoint318.point v hv) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (ratioSection f j i)) = v i/v j := by
  obtain ⟨φ,hφ,hc⟩ := point_chart f π hf j p hp
  rw [point_ratio f j i p φ hφ]
  apply PolynomialProjectiveChartRatios318.evaluation_ratio j φ hc v hv hj
  have he : Spec.map (CommRingCat.ofHom φ) ≫ chartMorphism j =
      ComplexProjectiveSchemePoint318.point v hv := by
    rw [←hφ,Category.assoc,toChart_square]
    exact hvpoint
  have hx := congrArg (fun g => g (IsLocalRing.closedPoint ℂ)) he
  simpa only [Scheme.Hom.comp_apply,ComplexProjectiveSchemePoint318.underlying_point] using hx
end ProjectivePreimageRegularRatios318
