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

/-- Exact frame value on the actual ambient universal derivative of the
chart coordinate, not an independently named abstract generator. -/
theorem chartFrame_D (s : S) (hs : e (KaehlerDifferential.D R S s)=1) :
    (chartFrame j p h e).hom.app ⊤
      ((FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))) =
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  have hi := UnitLineDifferentials318.frame_inverse_one e (KaehlerDifferential.D R S s) hs
  have hd : (chartFrame j p h e).inv.app ⊤
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) =
      (FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) :=
    (congrArg (moduleSpecΓFunctor.map (IntrinsicChartNormalization318.iso j p h).hom) hi).trans
      (IntrinsicChartNormalization318.differential j p h s)
  have hc := congrArg (fun f => f.app ⊤
    (show Γ(Spec (CommRingCat.of S),⊤) from 1)) (chartFrame j p h e).inv_hom_id
  exact (congrArg ((chartFrame j p h e).hom.app ⊤) hd).symm.trans hc

variable (c : Fin 4 → ℚˣ)
@[expose] def branchDerivative (i : Fin 4) :=
  (ContactIntrinsicDifferentials318.derivation c).d
    (((ContactIntrinsicFrames318.branchEmbedding c i).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
        (ContactFrameNormalization318.sourceCoordinate c i)))
@[expose] def infinityDerivative :=
  (ContactIntrinsicDifferentials318.derivation c).d
    (((InfinityGlobalScheme318.chartEmbedding c).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
        (ContactFrameNormalization318.infinityCoordinate c)))

theorem branchDerivative_normalized (i : Fin 4) :
    (ContactIntrinsicFrames318.localFrame c (some i)).hom.app ⊤ (branchDerivative c i)=
      (show Γ(ContactIntrinsicFrames318.chart c (some i),⊤) from 1) :=
  chartFrame_D (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactFrameNormalization318.sourceCoordinate c i)
    (ContactFrameNormalization318.source_coordinate_normalized c i)

theorem infinityDerivative_normalized :
    (ContactIntrinsicFrames318.localFrame c none).hom.app ⊤ (infinityDerivative c)=
      (show Γ(ContactIntrinsicFrames318.chart c none,⊤) from 1) :=
  chartFrame_D (InfinityGlobalScheme318.chartEmbedding c)
    (ContactIntrinsicDifferentials318.structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (ContactDifferentialFrames318.infinityFrame c)
    (ContactFrameNormalization318.infinityCoordinate c)
    (ContactFrameNormalization318.infinity_coordinate_normalized c)
end IntrinsicFrameDerivative318
