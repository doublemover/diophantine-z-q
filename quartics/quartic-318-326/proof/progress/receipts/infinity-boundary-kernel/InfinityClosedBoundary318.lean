module
public import InfinityBoundaryScheme318
public import AffineProductEvaluation318
public import SchemeAffineTestExt318
public section
noncomputable section
namespace InfinityClosedBoundary318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

/-- The actual possibly nonreduced closed z=0 boundary, not a reduced point. -/
abbrev Ring (A B:R) := InfinityChart318.Ring A B ⧸ Ideal.span {InfinityChart318.z A B}
@[expose] def quotient (A B:R) : InfinityChart318.Ring A B →ₐ[R] Ring A B :=
  Ideal.Quotient.mkₐ R _
lemma quotient_z (A B:R) : quotient A B (InfinityChart318.z A B)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)
@[expose] def scheme (A B:R) : Scheme := Spec (CommRingCat.of (Ring A B))
@[expose] def intoChart (A B:R) : scheme A B ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (quotient A B).toRingHom)
@[expose] def intoCurve (A B:R) : scheme A B ⟶ WeierstrassGluing318.scheme A B :=
  InfinityBoundaryScheme318.point A B (quotient A B)
@[expose] def structureMap (A B:R) : scheme A B ⟶ Spec (CommRingCat.of R) :=
  intoCurve A B ≫ WeierstrassGluing318.structureMap A B
@[reassoc] theorem intoCurve_base (A B:R) :
    intoCurve A B ≫ WeierstrassGluing318.structureMap A B=structureMap A B := rfl

lemma affine_zero {S:Type u} [CommRing S] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (h3:IsUnit (3:R))
    (x:Spec (CommRingCat.of S) ⟶ scheme A B)
    (h:x ≫ intoCurve A B ≫ CompletedIteratedAddition318.doubling A B hD=
      x ≫ intoCurve A B ≫ GluedNegation318.negation A B) :
    x ≫ intoCurve A B=x ≫ structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  obtain ⟨b,hb⟩:=Spec.map_surjective (x ≫ Spec.algebraMap R (Ring A B))
  letI : Algebra R S:=b.hom.toAlgebra
  have hx:x ≫ Spec.algebraMap R (Ring A B)=Spec.algebraMap R S:=hb.symm
  let φ:=AffineProductEvaluation318.toAlgHom x hx
  have hφ:Spec.map (CommRingCat.ofHom φ.toRingHom)=x:=AffineProductEvaluation318.map_toAlgHom x hx
  let f:=φ.comp (quotient A B)
  have hf:x ≫ intoCurve A B=InfinityBoundaryScheme318.point A B f := by
    rw [←hφ,intoCurve,InfinityBoundaryScheme318.point,←Category.assoc]
    change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (quotient A B).toRingHom)) ≫ _=_
    rw [←Spec.map_comp]
    rfl
  have hz:f (InfinityChart318.z A B)=0 := by simp only [f,AlgHom.comp_apply,quotient_z,map_zero]
  have hh:InfinityBoundaryScheme318.point A B f ≫ CompletedIteratedAddition318.doubling A B hD=
      InfinityBoundaryScheme318.point A B f ≫ GluedNegation318.negation A B := by
    simpa only [←hf,Category.assoc] using h
  have hf0: f=(Algebra.ofId R S).comp (InfinityChart318.origin A B) :=
    (InfinityBoundaryScheme318.double_neg_iff A B f hz hD
      (by simpa only [map_ofNat] using h3.map (algebraMap R S))).mp hh
  have hzmap:InfinityBoundaryScheme318.point A B f=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B :=
    (InfinityBoundaryScheme318.point_eq_zero_iff A B f).mpr hf0
  calc
    x ≫ intoCurve A B=InfinityBoundaryScheme318.point A B f := hf
    _=InfinityBoundaryScheme318.point A B f ≫ WeierstrassGluing318.structureMap A B ≫
        WeierstrassGluing318.infinity A B := by
      rw [←Category.assoc,InfinityBoundaryScheme318.point_over_base]
      exact hzmap
    _=x ≫ structureMap A B ≫ WeierstrassGluing318.infinity A B := by
      simp only [←hf,structureMap,Category.assoc]

/-- Every Scheme test, including nonaffine and nonreduced ones, sees only the
actual zero section in the doubling/negation equalizer on the closed boundary. -/
theorem scheme_zero {X:Scheme.{u}} (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (h3:IsUnit (3:R))
    (x:X ⟶ scheme A B)
    (h:x ≫ intoCurve A B ≫ CompletedIteratedAddition318.doubling A B hD=
      x ≫ intoCurve A B ≫ GluedNegation318.negation A B) :
    x ≫ intoCurve A B=x ≫ structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  apply SchemeAffineTestExt318.hom_ext
  intro S t
  simpa only [Category.assoc] using affine_zero A B hD h3 (t ≫ x)
    (by simpa only [Category.assoc] using congrArg (fun k=>t ≫ k) h)
end InfinityClosedBoundary318
