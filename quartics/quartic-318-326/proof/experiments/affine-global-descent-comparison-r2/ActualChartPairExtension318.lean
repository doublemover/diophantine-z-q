module
public import AffineSubopenIsoExtension318
public section
noncomputable section
namespace ActualChartPairExtension318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineChartAmbientComparison318 AffineChartLocalPairs318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)
  (U V : Y.affineOpens) (Z : Y.Opens) (hU : Z ≤ U.1) (hV : Z ≤ V.1)

/-- The affine component input on a possibly non-affine intersection is
constructed from the original chart reconstruction and its proved coherence. -/
@[expose] def data : AffineSubopenIsoExtension318.Data
    (A:=ambient f D U) (B:=ambient f D V) Z where
  app W hW := overPair f D U V W (hW.trans hU) (hW.trans hV)
  natural W T hW h := overPair_restrict f D U V W
    (hW.trans hU) (hW.trans hV) T h

/-- Actual whole-open comparison of the original ambient chart sheaves.
The open need not be affine, separated or quasi-compact. -/
@[expose] def pair : (ambient f D U).restrict Z.ι ≅ (ambient f D V).restrict Z.ι :=
  AffineSubopenIsoExtension318.iso Z (data f D U V Z hU hV)

lemma pair_affine (T : Z.toScheme.affineOpens) (s : Γ((ambient f D U).restrict Z.ι,T.1)) :
    (pair f D U V Z hU hV).hom.app T.1 s =
      OpenSheafTransition318.component
        (overPair f D U V (AffineSubopenIsoExtension318.image Z T)
          ((AffineSubopenIsoExtension318.image_le Z T).trans hU)
          ((AffineSubopenIsoExtension318.image_le Z T).trans hV))
        (AffineSubopenIsoExtension318.image Z T).1 le_rfl s :=
  AffineSubopenIsoExtension318.iso_affine Z (data f D U V Z hU hV) T s

/-- The full original sheaf transition on any common open satisfies the
triple cocycle, detected on every affine open of that same open subscheme. -/
lemma pair_cocycle (W : Y.affineOpens) (hW : Z ≤ W.1) :
    pair f D U V Z hU hV ≪≫ pair f D V W Z hV hW = pair f D U W Z hU hW := by
  apply Iso.ext
  apply AffineBasisModuleMaps318.hom_ext
  intro T s
  change (pair f D V W Z hV hW).hom.app T.1 ((pair f D U V Z hU hV).hom.app T.1 s) =
    (pair f D U W Z hU hW).hom.app T.1 s
  rw [pair_affine,pair_affine,pair_affine]
  let Q := AffineSubopenIsoExtension318.image Z T
  let hi := (AffineSubopenIsoExtension318.image_le Z T).trans hU
  let hj := (AffineSubopenIsoExtension318.image_le Z T).trans hV
  let hk := (AffineSubopenIsoExtension318.image_le Z T).trans hW
  have hc := AffineChartLocalPairs318.overPair_cocycle f D U V Q hi hj W hk
  exact congrArg (fun e => OpenSheafTransition318.component e Q.1 le_rfl s) hc
end ActualChartPairExtension318
