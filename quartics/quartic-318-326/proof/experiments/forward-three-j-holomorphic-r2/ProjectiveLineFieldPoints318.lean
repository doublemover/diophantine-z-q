module
public import JLineOverlap318
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public section
noncomputable section
namespace ProjectiveLineFieldPoints318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- Actual base-preserving scheme-valued points of the original homogeneous Proj. -/
@[expose] def Points :=
  {f : Spec (CommRingCat.of K) ⟶ ProjectiveJLine318.scheme R //
    f ≫ ProjectiveJLine318.structureMap R=Spec.map (CommRingCat.ofHom (algebraMap R K))}

/-- Evaluation in an actual standard algebraic chart, not a projective tuple
standing in for a morphism of schemes. -/
@[expose] def chartPoint (j : Fin 2) (t : K) : Points (R:=R) (K:=K) :=
  ⟨Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) t).toRingHom) ≫
    JLineAtlas318.chart R j,by
    rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact (Polynomial.aeval (R:=R) t).commutes r⟩

lemma chartPoint_injective (j : Fin 2) :
    Function.Injective (chartPoint (R:=R) (K:=K) j) := by
  intro s t h
  have hh := (cancel_mono (JLineAtlas318.chart R j)).mp (congrArg Subtype.val h)
  have he := congrArg (fun f => f.hom Polynomial.X) (Spec.map_injective hh)
  simpa only [CommRingCat.hom_ofHom,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
    Polynomial.aeval_X] using he

/-- Every actual field-valued point factors through one of the two original
open charts. Coverage is on morphisms, using the singleton field spectrum. -/
lemma point_factors_chart (p : Points (R:=R) (K:=K)) :
    ∃ j : Fin 2, ∃ a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Polynomial R)),
      a ≫ JLineAtlas318.chart R j=p.val := by
  have hp : p.val default ∈ (⊤ : (ProjectiveJLine318.scheme R).Opens) := trivial
  rw [←JLineAtlas318.standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at hp
  obtain ⟨j,hj⟩ := hp
  rw [←JLineAtlas318.chart_range] at hj
  obtain ⟨x,hx⟩ := hj
  have hr : Set.range p.val ⊆ Set.range (JLineAtlas318.chart R j) := by
    rintro _ ⟨q,rfl⟩
    exact ⟨x,hx.trans (congrArg p.val (Subsingleton.elim default q))⟩
  exact ⟨j,IsOpenImmersion.lift _ p.val hr,IsOpenImmersion.lift_fac _ _ hr⟩

/-- Each factored morphism has the literal polynomial evaluation coordinate;
there is no extra unconstrained map on the coefficient field. -/
set_option maxHeartbeats 4000000 in
theorem every_point_in_chart (p : Points (R:=R) (K:=K)) :
    ∃ j : Fin 2, ∃ t : K, chartPoint (R:=R) j t=p := by
  obtain ⟨j,a,ha⟩ := point_factors_chart p
  have hb : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))=
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [←JLineAtlas318.chart_over_base R j,←Category.assoc,ha]
    exact p.property
  let φ : Polynomial R →ₐ[R] K := Spec.homEquivAlgHom ⟨a,hb⟩
  have he : Spec.map (CommRingCat.ofHom φ.toRingHom)=a :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨a,hb⟩)
  have hφ : φ=Polynomial.aeval (φ Polynomial.X) := by
    apply Polynomial.algHom_ext
    simp only [Polynomial.aeval_X]
  refine ⟨j,φ Polynomial.X,Subtype.ext ?_⟩
  change Spec.map (CommRingCat.ofHom (Polynomial.aeval (φ Polynomial.X)).toRingHom) ≫ _=_
  rw [←hφ,he,ha]

/-- The actual algebraic two-chart transition is literal reciprocal, with
both sides morphisms to the same original projective scheme. -/
theorem unit_overlap (t : Kˣ) :
    chartPoint (R:=R) 1 (t:K)=chartPoint (R:=R) 0 ((t⁻¹:Kˣ):K) :=
  Subtype.ext (JLineOverlap318.unit_chart_overlap (R:=R) t)

end ProjectiveLineFieldPoints318
