module
public import ContactIntrinsicFrames318
public import ContactFrameNormalization318
public import UnitLineDifferentials318
public section
noncomputable section
namespace IntrinsicFrameDerivative318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
#check UnitLineDifferentials318.frame_inverse_one
universe u
variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e : KaehlerDifferential R S ≃ₗ[S] S)

@[expose] def chartFrame :
    (FamilyIntrinsicDifferentials318.omega p).restrict j ≅
      SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf :=
  (IntrinsicChartNormalization318.iso j p h).symm ≪≫ AffineDifferentialSheaf318.frameIso e

#check chartFrame

/-- Exact frame value on the actual ambient universal derivative of the
chart coordinate, not an independently named abstract generator. -/
theorem chartFrame_D (s : S) (hs : e (KaehlerDifferential.D R S s)=1) :
    (chartFrame j p h e).hom.app ⊤
      ((FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))) =
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  let f := IntrinsicChartNormalization318.iso j p h
  let g := AffineDifferentialSheaf318.frameIso e
  have hi := UnitLineDifferentials318.frame_inverse_one e (KaehlerDifferential.D R S s) hs
  have hd : (moduleSpecΓFunctor.map (chartFrame j p h e).inv)
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) =
      (FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) := by
    change (moduleSpecΓFunctor.map (g.inv ≫ f.hom)) _ = _
    rw [Functor.map_comp]
    exact (congrArg (moduleSpecΓFunctor.map f.hom) hi).trans
      (IntrinsicChartNormalization318.differential j p h s)
  change (moduleSpecΓFunctor.map (chartFrame j p h e).hom) _ = _
  exact (congrArg (moduleSpecΓFunctor.map (chartFrame j p h e).hom) hd).symm.trans
    (CategoryTheory.Iso.inv_hom_id_apply (moduleSpecΓFunctor.mapIso (chartFrame j p h e)) _)

/-- The same normalization, with the intrinsic derivative presented through
its checked algebraic-chart section map. -/
theorem chartFrame_section (s : S) (hs : e (KaehlerDifferential.D R S s)=1) :
    (chartFrame j p h e).hom.app ⊤
      (IntrinsicChartSections318.sectionMap j p h (KaehlerDifferential.D R S s)) =
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  let f := IntrinsicChartNormalization318.iso j p h
  let g := AffineDifferentialSheaf318.frameIso e
  have hi := UnitLineDifferentials318.frame_inverse_one e (KaehlerDifferential.D R S s) hs
  change (moduleSpecΓFunctor.map (g.hom))
    ((moduleSpecΓFunctor.map f.inv)
      ((moduleSpecΓFunctor.map f.hom)
        ((tilde.isoTop (R:=CommRingCat.of S)
          (ModuleCat.of S (KaehlerDifferential R S))).hom (KaehlerDifferential.D R S s)))) = _
  have hf := CategoryTheory.Iso.hom_inv_id_apply (moduleSpecΓFunctor.mapIso f)
    ((tilde.isoTop (R:=CommRingCat.of S)
      (ModuleCat.of S (KaehlerDifferential R S))).hom (KaehlerDifferential.D R S s))
  exact (congrArg (moduleSpecΓFunctor.map g.hom) hf).trans
    ((congrArg (moduleSpecΓFunctor.map g.hom) hi).symm.trans
      (CategoryTheory.Iso.inv_hom_id_apply (moduleSpecΓFunctor.mapIso g) _))
#check chartFrame_section

set_option maxHeartbeats 30000
variable (c : Fin 4 → ℚˣ)
@[expose] def branchDerivative (i : Fin 4) :=
  IntrinsicChartSections318.sectionMap (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
@[expose] def infinityDerivative :=
  IntrinsicChartSections318.sectionMap (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c)
    (ContactIntrinsicDifferentials318.structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
      (ContactFrameNormalization318.infinityCoordinate c))

#check branchDerivative
#check infinityDerivative

theorem branchDerivative_normalized (i : Fin 4) :
    (chartFrame (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
      (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c i)
      (ContactDifferentialFrames318.sourceLocalizationFrame c i)).hom.app ⊤
        (branchDerivative c i) =
      (show Γ(Spec (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i)),⊤) from 1) :=
  chartFrame_section (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactFrameNormalization318.sourceCoordinate c i)
    (ContactFrameNormalization318.source_coordinate_normalized c i)

#check branchDerivative_normalized

theorem infinityDerivative_normalized :
    (chartFrame (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
      (InfinityGlobalScheme318.chartEmbedding c)
      (ContactIntrinsicDifferentials318.structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
      (ContactDifferentialFrames318.infinityFrame c)).hom.app ⊤ (infinityDerivative c) =
      (show Γ(Spec (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c)),⊤) from 1) :=
  chartFrame_section (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c)
    (ContactIntrinsicDifferentials318.structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (ContactDifferentialFrames318.infinityFrame c)
    (ContactFrameNormalization318.infinityCoordinate c)
    (ContactFrameNormalization318.infinity_coordinate_normalized c)
end IntrinsicFrameDerivative318
