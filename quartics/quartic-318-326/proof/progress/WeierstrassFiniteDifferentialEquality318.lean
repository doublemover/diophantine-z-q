module
public import WeierstrassAffineInvariant318
public section
noncomputable section
namespace WeierstrassFiniteDifferentialEquality318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace KaehlerDifferential
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
@[expose] def chartOpen (i:ULift.{u} (Fin 2)) := InvariantChartCover318.finiteInto A B i.down ''ᵁ ⊤

theorem chart_le (i:ULift.{u} (Fin 2)) : chartOpen A B i≤WeierstrassAffineInvariant318.finiteOpen A B :=
  OpenChartSections318.imageLE _ _

include hD in
theorem cover : WeierstrassAffineInvariant318.finiteOpen A B≤ iSup (chartOpen A B) := by
  rintro _ ⟨x,_,rfl⟩
  obtain ⟨i,z,hz⟩:=InvariantChartCover318.finite_localizations_cover
    (fun i:Fin 2=>(ShortAffineJacobian318.presentation A B i).jacobian)
    (ShortAffineJacobian318.jacobian_span A B hD) x
  exact Opens.mem_iSup.mpr ⟨⟨i⟩,z,trivial,congrArg (WeierstrassGluing318.finiteChart A B) hz⟩

include hD in
/-- The two genuine Jacobian opens detect equality of differentials on the
whole finite chart, including the points where either individual denominator vanishes. -/
theorem eq_of_charts (ω η:KaehlerDifferential R (ShortAffineJacobian318.Ring A B))
    (he:∀i:Fin 2,AlgHomDifferential318.map (WeierstrassAffineInvariant318.chartMap A B i) ω=
      AlgHomDifferential318.map (WeierstrassAffineInvariant318.chartMap A B i) η) : ω=η := by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective
    (WeierstrassGluing318.finiteChart A B) (WeierstrassGluing318.structureMap A B)
      (WeierstrassAffineInvariant318.finite_structure A B)).1
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨(FamilyIntrinsicDifferentials318.familyOmega A B).presheaf,
      (FamilyIntrinsicDifferentials318.familyOmega A B).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat _)
      (chartOpen A B) (WeierstrassAffineInvariant318.finiteOpen A B)
      (fun i=>homOfLE (chart_le A B i)) (cover A B hD)
  rintro ⟨i⟩
  let a:=WeierstrassAffineInvariant318.chartMap A B i
  letI:IsOpenImmersion (Spec.map (CommRingCat.ofHom a.toRingHom)):=by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ShortAffineJacobian318.Ring A B) (WeierstrassKaehler318.AffineChart A B i))))
    exact IsOpenImmersion.of_isLocalization (ShortAffineJacobian318.presentation A B i).jacobian
  have hn (ξ:KaehlerDifferential R (ShortAffineJacobian318.Ring A B)):=
    IntrinsicChartNaturality318.section_restrict a (WeierstrassGluing318.finiteChart A B)
      (WeierstrassGluing318.structureMap A B) (WeierstrassAffineInvariant318.finite_structure A B)
      (IntrinsicFamilyFrames318.finite_structure A B i) ξ
  exact (hn ω).trans ((congrArg (IntrinsicChartSections318.sectionMap
    (InvariantChartCover318.finiteInto A B i) (WeierstrassGluing318.structureMap A B)
      (IntrinsicFamilyFrames318.finite_structure A B i)) (he i)).trans (hn η).symm)
end WeierstrassFiniteDifferentialEquality318
