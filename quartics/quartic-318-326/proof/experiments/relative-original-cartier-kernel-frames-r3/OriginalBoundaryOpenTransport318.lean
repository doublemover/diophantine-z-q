module
public import NonreducedLineMayerVietoris318
public section
noncomputable section
namespace OriginalBoundaryOpenTransport318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable {X : Scheme.{0}} (L : Line X)
lemma transport (U V U' V' : X.Opens) (h : U ⊔ V = ⊤) (h' : U' ⊔ V' = ⊤)
    (hU : U = U') (hV : V = V') (s : Γ(L.object,U ⊓ V)) :
    NonreducedLineMayerVietoris318.boundary L U' V' h'
      (L.object.presheaf.map (eqToHom (congrArg₂ (· ⊓ ·) hU hV).symm).op s) =
        NonreducedLineMayerVietoris318.boundary L U V h s := by
  subst U'
  subst V'
  simp
end OriginalBoundaryOpenTransport318
