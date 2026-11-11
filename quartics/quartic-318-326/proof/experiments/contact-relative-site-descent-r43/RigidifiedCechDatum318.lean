module
public import RigidifiedCechCocycle318
public section
noncomputable section
namespace RigidifiedCechDatum318
open AlgebraicGeometry CategoryTheory ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedCechNerve318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)
  (L : RigidifiedLine e') (τ : Overlap f g e e' square L)

abbrev identityLine := RigidifiedPointedPullback318.line e' e' (𝟙 X') (𝟙 S')
  (by simp only [Category.comp_id,Category.id_comp]) L

@[expose] def diagonalIso : CompatibleIso e' (identityLine e' L) (identityLine e' L) :=
  RigidifiedPathTransport318.transport e' (doubleSection f g e e' square) e'
    (first f) (second f) (first g) (second g) (diagonal f) (diagonal g)
    (double_first f g e' e square) (double_second f g e' e square)
    (diagonal_double f g e' e square).symm (𝟙 X') (𝟙 X') (𝟙 S') (𝟙 S')
    (diagonal_first f) (diagonal_second f) (diagonal_first g) (diagonal_second g)
    (by simp only [Category.comp_id,Category.id_comp])
    (by simp only [Category.comp_id,Category.id_comp]) L τ

lemma diagonal (h : Function.Injective e'.appTop) :
    OriginalSchemeDescentData318.Diagonal f L.line τ.iso.hom := by
  have hh := compatible_unique e' h (identityLine e' L) (identityLine e' L)
    (diagonalIso f g e e' square L τ) (RigidifiedIsoCoherence318.identity e' _)
  have hmap := congrArg (fun a => a.iso.hom) hh
  change (diagonalIso f g e e' square L τ).iso.hom = 𝟙 _ at hmap
  have ht : (diagonalIso f g e e' square L τ).iso.hom =
      SheafPathTransport318.transport L.line.object (diagonal f) (first f) (second f)
        (𝟙 X') (𝟙 X') (diagonal_first f) (diagonal_second f) τ.iso.hom :=
    RigidifiedPathTransport318.transport_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ht.symm.trans hmap

/-- A compatible overlap on the actual pointed Čech double determines
original geometric descent data. Both laws are proved by rigidity on the
actual original diagonal and triple; neither is a cocycle input. -/
@[expose] def datum (hl : Function.Injective e'.appTop)
    (ht : Function.Injective (tripleSection f g e e' square).appTop) :
    OriginalSchemeDescentData318.Datum f where
  line := L.line
  overlap := τ.iso.hom
  diagonal := diagonal f g e e' square L τ hl
  triple := RigidifiedCechCocycle318.cocycle f g e e' square L τ ht
end RigidifiedCechDatum318
