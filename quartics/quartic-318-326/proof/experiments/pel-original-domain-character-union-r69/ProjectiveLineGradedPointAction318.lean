module
public import ProjectiveSwapCharts318
public import JLineOverlap318
public section
noncomputable section
namespace ProjectiveLineGradedPointAction318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory Graded HomogeneousIdeal
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1200000
universe u
variable {R S:Type u} [CommRing R] [CommRing S]
local notation "P" => MvPolynomial (Fin 2) R
local notation "G" => ProjectiveJLine318.grading R

/-- Exact naturality of ORIGINAL homogeneous-fraction evaluations. -/
lemma evaluate_map (f:G→+*ᵍ G) (φ:P→+*S) (s:P) {d:ℕ} (hs:s∈G d)
    (hu:IsUnit (φ (f s))) :
    (JLineEvaluation318.evaluate φ (f s) hu).comp (Away.map f s)=
      JLineEvaluation318.evaluate (φ.comp f.toRingHom) s hu := by
  apply RingHom.ext
  intro a
  obtain ⟨n,p,hp,rfl⟩:=a.mk_surjective G hs
  have hv:φ (f s)*(↑hu.unit⁻¹:S)=1 := by
    rw [←hu.unit_spec]
    exact Units.mul_inv hu.unit
  simp only [RingHom.comp_apply,Away.map_mk]
  rw [JLineEvaluation318.evaluate_mk φ (f s) hu (f.map_mem hs) n (f p)
      (f.map_mem hp) (↑hu.unit⁻¹) hv,
    JLineEvaluation318.evaluate_mk (φ.comp f.toRingHom) s hu hs n p hp
      (↑hu.unit⁻¹) hv]
  rfl

@[expose] def evaluatedPoint (φ:P→+*S) (j:Fin 2) (hj:IsUnit (φ (X j))) :
    Spec (CommRingCat.of S) ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (JLineEvaluation318.evaluate φ (X j) hj)) ≫
    Proj.awayι G (X j) (isHomogeneous_X R j) (by omega)

/-- Functoriality holds on ALL genuine field/ring-valued points for which
these coordinates are units, via actual Scheme morphism equality. -/
theorem evaluatedPoint_action (f:G→+*ᵍ G) (hf:G₊≤G₊.map f)
    (φ:P→+*S) (j k:Fin 2) (hj:IsUnit (φ (X j))) (hk:IsUnit (φ (f (X k)))) :
    evaluatedPoint φ j hj ≫ Proj.map f hf =
      evaluatedPoint (φ.comp f.toRingHom) k hk := by
  have hc:=JLineEvaluation318.chart_compatibility φ (X j) (f (X k)) hj hk
    (isHomogeneous_X R j) (f.map_mem (isHomogeneous_X R k)) (by omega) (by omega)
  unfold evaluatedPoint
  rw [hc,Category.assoc,
    Proj.awayι_comp_map f hf (by omega) (X k) (isHomogeneous_X R k),
    ←Category.assoc,←Spec.map_comp]
  have he:=evaluate_map f φ (X k) (isHomogeneous_X R k) hk
  exact congrArg (fun q:Away G (X k)→+*S=>
      Spec.map (CommRingCat.ofHom q) ≫ Proj.awayι G (X k)
        (isHomogeneous_X R k) (by omega)) he

section Algebra
variable [Algebra R S]
lemma evaluatedPoint_coordinate (φ:P→ₐ[R]S) (j:Fin 2) (hj:IsUnit (φ (X j)))
    (v:S) (hv:φ (X j)*v=1) :
    evaluatedPoint φ.toRingHom j hj=
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (φ (X (j.succAbove 0))*v)).toRingHom) ≫
        JLineAtlas318.chart R j := by
  have he:=JLineOverlap318.chartEval_polynomial φ j hj v hv
  change Spec.map (CommRingCat.ofHom (JLineEvaluation318.chartEval φ j hj).toRingHom) ≫ _=_
  rw [he]
  simp only [AlgHom.comp_toRingHom,CommRingCat.ofHom_comp,Spec.map_comp,
    JLineAtlas318.chart,Category.assoc]

/-- A concrete original source coordinate and a concrete transformed target
coordinate, with no inference from an underlying topological point. -/
theorem coordinate_action (f:G→+*ᵍ G) (hf:G₊≤G₊.map f)
    (φ ψ:P→ₐ[R]S) (hψ:ψ.toRingHom=φ.toRingHom.comp f.toRingHom)
    (j k:Fin 2) (hj:IsUnit (φ (X j))) (hk:IsUnit (ψ (X k)))
    (v w:S) (hv:φ (X j)*v=1) (hw:ψ (X k)*w=1) :
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (φ (X (j.succAbove 0))*v)).toRingHom) ≫
      JLineAtlas318.chart R j) ≫ Proj.map f hf =
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (ψ (X (k.succAbove 0))*w)).toRingHom) ≫
      JLineAtlas318.chart R k := by
  rw [←evaluatedPoint_coordinate φ j hj v hv,
    ←evaluatedPoint_coordinate ψ k hk w hw]
  have hk' : IsUnit (φ (f (X k))) := by
    change IsUnit ((φ.toRingHom.comp f.toRingHom) (X k))
    rw [←hψ]
    exact hk
  simpa only [hψ] using evaluatedPoint_action f hf φ.toRingHom j k hj hk' 
end Algebra
end ProjectiveLineGradedPointAction318
