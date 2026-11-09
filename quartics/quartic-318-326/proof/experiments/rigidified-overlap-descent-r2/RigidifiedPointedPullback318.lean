module
public import RigidifiedIsoCoherence318
public section
noncomputable section
namespace RigidifiedPointedPullback318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318
open RigidifiedLineIsomorphism318 RigidifiedRelativeClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S X' S' : Scheme.{u}} (e : S ⟶ X) (e' : S' ⟶ X')
  (a : X' ⟶ X) (b : S' ⟶ S) (pointed : e' ≫ a = b ≫ e)

/-- The actual composition and equality comparisons for a pointed square,
as a natural isomorphism of the original module-sheaf pullback functors. -/
@[expose] def restrictionComparison :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback e' ≅
      Scheme.Modules.pullback e ⋙ Scheme.Modules.pullback b :=
  Scheme.Modules.pullbackComp e' a ≪≫
    eqToIso (congrArg (fun f => Scheme.Modules.pullback f) pointed) ≪≫
      (Scheme.Modules.pullbackComp b e).symm

/-- Pull back the specified actual rigidification using the actual pointed
square, not a new trivialization selected from a class equality. -/
@[expose] def line (L : RigidifiedLine e) : RigidifiedLine e' where
  line := LineSheafPullback318.line a L.line
  trivialization :=
    (restrictionComparison e e' a b pointed).app L.line.object ≪≫
      (Scheme.Modules.pullback b).mapIso L.trivialization ≪≫
        IdentityCotangent318.pullbackUnitIso b

/-- The original pulled-back sheaf isomorphism itself respects the transported
rigidifications. No corrective automorphism and no global-function hypothesis
is needed for this construction. -/
@[expose] def mapIso {L M : RigidifiedLine e} (f : CompatibleIso e L M) :
    CompatibleIso e' (line e e' a b pointed L) (line e e' a b pointed M) where
  iso := (Scheme.Modules.pullback a).mapIso f.iso
  commutes := by
    change (Scheme.Modules.pullback e').map ((Scheme.Modules.pullback a).map f.iso.hom) ≫
      (restrictionComparison e e' a b pointed).hom.app M.line.object ≫
      (Scheme.Modules.pullback b).map M.trivialization.hom ≫
      (IdentityCotangent318.pullbackUnitIso b).hom =
        (restrictionComparison e e' a b pointed).hom.app L.line.object ≫
        (Scheme.Modules.pullback b).map L.trivialization.hom ≫
        (IdentityCotangent318.pullbackUnitIso b).hom
    have hn := (restrictionComparison e e' a b pointed).hom.naturality f.iso.hom
    change (Scheme.Modules.pullback e').map ((Scheme.Modules.pullback a).map f.iso.hom) ≫
      (restrictionComparison e e' a b pointed).hom.app M.line.object =
        (restrictionComparison e e' a b pointed).hom.app L.line.object ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback e).map f.iso.hom) at hn
    calc
      _ = (restrictionComparison e e' a b pointed).hom.app L.line.object ≫
          (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback e).map f.iso.hom) ≫
          (Scheme.Modules.pullback b).map M.trivialization.hom ≫
          (IdentityCotangent318.pullbackUnitIso b).hom := by
        rw [← Category.assoc, ← Category.assoc, hn]
        simp only [Category.assoc]
      _ = (restrictionComparison e e' a b pointed).hom.app L.line.object ≫
          (Scheme.Modules.pullback b).map
            (((Scheme.Modules.pullback e).mapIso f.iso).hom ≫ M.trivialization.hom) ≫
          (IdentityCotangent318.pullbackUnitIso b).hom := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
      _ = _ := by rw [f.commutes]

/-- Forgetting this transported rigidification is exactly the already defined
original relative-class pullback for the same square. -/
lemma relativeClass_line (p : X ⟶ S) (p' : X' ⟶ S')
    (square : a ≫ p = p' ≫ b) (L : RigidifiedLine e) :
    relativeClass p' e' (line e e' a b pointed L) =
      RelativeLineClassQuotient318.map p p' a b square (relativeClass p e L) := rfl

lemma mapIso_identity (L : RigidifiedLine e) :
    mapIso e e' a b pointed (RigidifiedIsoCoherence318.identity e L) =
      RigidifiedIsoCoherence318.identity e' (line e e' a b pointed L) := by
  apply CompatibleIso.ext
  apply Iso.ext
  exact (Scheme.Modules.pullback a).map_id _

lemma mapIso_compose {L M N : RigidifiedLine e}
    (f : CompatibleIso e L M) (g : CompatibleIso e M N) :
    mapIso e e' a b pointed (RigidifiedIsoCoherence318.compose e f g) =
      RigidifiedIsoCoherence318.compose e'
        (mapIso e e' a b pointed f) (mapIso e e' a b pointed g) := by
  apply CompatibleIso.ext
  apply Iso.ext
  exact (Scheme.Modules.pullback a).map_comp _ _
end RigidifiedPointedPullback318
