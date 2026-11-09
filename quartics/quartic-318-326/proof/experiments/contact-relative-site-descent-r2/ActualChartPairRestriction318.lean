module
public import ActualChartPairExtension318
public section
noncomputable section
namespace ActualChartPairRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ModuleLocalGluing318
open AffineChartAmbientComparison318 AffineChartLocalPairs318
open OpenSheafRestrictionCompatibility318 ActualChartPairExtension318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f) (U V : Y.affineOpens)

lemma component_transport (Q T : Y.affineOpens)
    (hQ : Q.1 ≤ U.1) (kQ : Q.1 ≤ V.1) (hT : T.1 ≤ U.1) (kT : T.1 ≤ V.1)
    (e : Q.1 = T.1) (s : Γ(ambient f D U,T.1)) :
    res (ambient f D V) e.symm.le
        (OpenSheafTransition318.component (overPair f D U V Q hQ kQ) Q.1 le_rfl
          (res (ambient f D U) e.le s)) =
      OpenSheafTransition318.component (overPair f D U V T hT kT) T.1 le_rfl s := by
  have he : Q = T := Subtype.ext e
  subst T
  simp only [res_self]

/-- The extended whole-open pair iso is compatible with restriction to
every smaller open, affine or not. The proof compares the exact original
section maps on all affine subopens and retains the original image transports. -/
lemma pair_restrict (Z T : Y.Opens) (hU : Z ≤ U.1) (hV : Z ≤ V.1) (k : T ≤ Z) :
    schemeRestrict (ActualChartPairExtension318.pair f D U V Z hU hV) k =
      ActualChartPairExtension318.pair f D U V T (k.trans hU) (k.trans hV) := by
  apply Iso.ext
  apply AffineBasisModuleMaps318.hom_ext
  intro Q s
  rw [schemeRestrict_hom_app]
  let Q' : Z.toScheme.affineOpens :=
    ⟨(Y.homOfLE k) ''ᵁ Q.1, Q.2.image_of_isOpenImmersion (Y.homOfLE k)⟩
  let A := AffineSubopenIsoExtension318.image Z Q'
  let B := AffineSubopenIsoExtension318.image T Q
  have he : A.1 = B.1 := image_eq k Q.1
  change res (ambient f D V) he.symm.le
      ((ActualChartPairExtension318.pair f D U V Z hU hV).hom.app Q'.1
        (res (ambient f D U) he.le s)) =
    (ActualChartPairExtension318.pair f D U V T (k.trans hU) (k.trans hV)).hom.app Q.1 s
  rw [pair_affine,pair_affine]
  exact component_transport f D U V A B
    ((AffineSubopenIsoExtension318.image_le Z Q').trans hU)
    ((AffineSubopenIsoExtension318.image_le Z Q').trans hV)
    ((AffineSubopenIsoExtension318.image_le T Q).trans (k.trans hU))
    ((AffineSubopenIsoExtension318.image_le T Q).trans (k.trans hV)) he s

lemma pair_identity (Z : Y.Opens) (h : Z ≤ U.1) :
    ActualChartPairExtension318.pair f D U U Z h h = Iso.refl _ := by
  apply Iso.ext
  apply AffineBasisModuleMaps318.hom_ext
  intro T s
  rw [pair_affine]
  let Q := AffineSubopenIsoExtension318.image Z T
  let hi := (AffineSubopenIsoExtension318.image_le Z T).trans h
  have he : AffineChartLocalPairs318.pair f D U U Q hi hi = Iso.refl _ := by
    apply Iso.ext
    simp only [AffineChartLocalPairs318.pair,Iso.trans_hom,Iso.symm_hom,Iso.hom_inv_id,Iso.refl_hom]
  change OpenSheafTransition318.component
    (OpenChartModuleImages318.toOverIso Q.1 (AffineChartLocalPairs318.pair f D U U Q hi hi)) Q.1 le_rfl s = s
  rw [he]
  rw [OpenSchemeTransition318.toOver_refl]
end ActualChartPairRestriction318
