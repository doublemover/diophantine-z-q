module
public import OriginalLineEndScalars318
public import ModuleScalarComposition318
public section
noncomputable section
namespace OriginalLineAutomorphismUnits318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineEndScalars318
universe u
variable {X : Scheme.{u}} (L : Line X)

lemma scalar_id : scalar L (𝟙 L.object)=1 := by
  rw [←ModuleScalarComposition318.map_one L.object,scalar_map]
lemma scalar_comp (a b : L.object ⟶ L.object) :
    scalar L (a ≫ b)=scalar L a * scalar L b := by
  apply (equivalence L).symm.injective
  change ModuleScalar318.map L.object (scalar L (a ≫ b))=
    ModuleScalar318.map L.object (scalar L a * scalar L b)
  rw [←map_eq,ModuleScalarComposition318.map_mul,←map_eq,←map_eq]

/-- Even when the original line has no global frame, its automorphism
is multiplication by an actual unit of the WHOLE global-function ring. -/
@[expose] def value (e : L.object ≅ L.object) : Γ(X,⊤)ˣ where
  val := scalar L e.hom
  inv := scalar L e.inv
  val_inv := by rw [←scalar_comp,e.hom_inv_id,scalar_id]
  inv_val := by rw [←scalar_comp,e.inv_hom_id,scalar_id]

@[expose] def iso (u : Γ(X,⊤)ˣ) : L.object ≅ L.object :=
  ModuleScalarComposition318.unitIso L.object u
lemma iso_value (u : Γ(X,⊤)ˣ) : value L (iso L u)=u := by
  apply Units.ext
  exact scalar_map L (u:Γ(X,⊤))
lemma value_iso (e : L.object ≅ L.object) : iso L (value L e)=e := by
  apply Iso.ext
  exact (map_eq L e.hom).symm

/-- Both inverse identities for actual automorphisms of EVERY original
line on EVERY scheme, including nilpotent and nonaffine schemes. -/
@[expose] def automorphisms : (L.object ≅ L.object) ≃ Γ(X,⊤)ˣ where
  toFun := value L
  invFun := iso L
  left_inv := value_iso L
  right_inv := iso_value L

lemma value_multiplication (e d : L.object ≅ L.object) :
    value L (e ≪≫ d)=value L e * value L d := by
  apply Units.ext
  exact scalar_comp L e.hom d.hom
end OriginalLineAutomorphismUnits318
