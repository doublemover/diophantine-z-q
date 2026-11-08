module
public import InfinityKernelNeighborhoodScheme318
public import InfinityBoundaryScheme318
public section
noncomputable section
namespace InfinityKernelNeighborhoodZero318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityKernelNeighborhoodAlgebra318 InfinityKernelNeighborhoodScheme318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

lemma algebra_zero {S:Type u} [CommRing S] [Algebra R S]
    (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (φ:Ring A B →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ intoCurve A B ≫ CompletedIteratedAddition318.doubling A B hD=
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ intoCurve A B ≫ GluedNegation318.negation A B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ intoCurve A B=
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  rw [doubling,negation,←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp] at h
  change Spec.map (CommRingCat.ofHom (φ.comp ((InfinityKernelNeighborhoodAlgebra318.lift A B).comp
      (BothInfinityAlgebra318.outputMap A B))).toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
    Spec.map (CommRingCat.ofHom (φ.comp ((input A B).comp (ChartNegation318.infinityNeg A B))).toRingHom) ≫
      WeierstrassGluing318.infinityChart A B at h
  have he:=ChartInputEquality318.infinity_injective A B _ _ h
  have ho:=congrArg (fun f:InfinityChart318.Ring A B →ₐ[R] S=>f (InfinityChart318.x A B)) he
  simp only [AlgHom.comp_apply,BothInfinityAlgebra318.outputMap,InfinityChart318.lift_x,
    ChartNegation318.infinityNeg_x,map_neg] at ho
  have hz:=InfinityKernelNeighborhoodAlgebra318.input_zero A B φ.toRingHom ho
  change φ (input A B (InfinityChart318.x A B))=0 ∧ φ (input A B (InfinityChart318.z A B))=0 at hz
  let f:=φ.comp (input A B)
  have hf0:f=(Algebra.ofId R S).comp (InfinityChart318.origin A B) := by
    apply InfinityChart318.hom_ext
    · simpa only [f,AlgHom.comp_apply,InfinityChart318.origin_x,map_zero] using hz.1
    · simpa only [f,AlgHom.comp_apply,InfinityChart318.origin_z,map_zero] using hz.2
  have hf:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ intoCurve A B=InfinityBoundaryScheme318.point A B f := by
    rw [intoCurve,←Category.assoc]
    change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (input A B).toRingHom)) ≫ _=_
    rw [←Spec.map_comp]
    rfl
  have hzmap:InfinityBoundaryScheme318.point A B f=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B :=
    (InfinityBoundaryScheme318.point_eq_zero_iff A B f).mpr hf0
  calc
    _=InfinityBoundaryScheme318.point A B f := hf
    _=InfinityBoundaryScheme318.point A B f ≫ WeierstrassGluing318.structureMap A B ≫
        WeierstrassGluing318.infinity A B := by
      rw [←Category.assoc,InfinityBoundaryScheme318.point_over_base]
      exact hzmap
    _=_ := by simp only [←hf,structureMap,Category.assoc]

lemma affine_zero {S:Type u} [CommRing S] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (x:Spec (CommRingCat.of S) ⟶ scheme A B)
    (h:x ≫ intoCurve A B ≫ CompletedIteratedAddition318.doubling A B hD=
      x ≫ intoCurve A B ≫ GluedNegation318.negation A B) :
    x ≫ intoCurve A B=x ≫ structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  obtain ⟨b,hb⟩:=Spec.map_surjective (x ≫ Spec.algebraMap R (Ring A B))
  letI : Algebra R S:=b.hom.toAlgebra
  have hx:x ≫ Spec.algebraMap R (Ring A B)=Spec.algebraMap R S:=hb.symm
  let φ:=AffineProductEvaluation318.toAlgHom x hx
  have hφ:Spec.map (CommRingCat.ofHom φ.toRingHom)=x:=AffineProductEvaluation318.map_toAlgHom x hx
  rw [←hφ]
  exact algebra_zero A B hD φ (by rw [hφ];exact h)

/-- Actual equality on the genuine open neighborhood, for every Scheme test.
No reducedness, affine or field restriction is placed on the test Scheme. -/
theorem scheme_zero {X:Scheme.{u}} (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (x:X ⟶ scheme A B)
    (h:x ≫ intoCurve A B ≫ CompletedIteratedAddition318.doubling A B hD=
      x ≫ intoCurve A B ≫ GluedNegation318.negation A B) :
    x ≫ intoCurve A B=x ≫ structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  apply SchemeAffineTestExt318.hom_ext
  intro S t
  simpa only [Category.assoc] using affine_zero A B hD (t ≫ x)
    (by simpa only [Category.assoc] using congrArg (fun k=>t ≫ k) h)
end InfinityKernelNeighborhoodZero318
