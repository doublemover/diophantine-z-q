module
public import UniversalSheafDifferentials318
public import IdentityCotangent318
public section
noncomputable section
namespace FamilyIntrinsicDifferentials318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- The literal natural coefficient map from a ring into all regular-function
rings, obtained from its actual map into the global regular functions. -/
@[expose] def coefficientPresheaf {X : Scheme.{u}} (R : CommRingCat.{u})
    (c : R ⟶ Γ(X,⊤)) : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf where
  app U := c ≫ X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} f := by
    dsimp
    rw [Category.id_comp,Category.assoc,←Functor.map_comp]
    congr 2

/-- Coefficients are extracted from the actual structure morphism to Spec R. -/
@[expose] def coefficients {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf :=
  coefficientPresheaf R ((Scheme.ΓSpecIso R).inv ≫ f.appTop)

/-- Intrinsic sheaf of R-differentials on the actual global scheme over Spec R. -/
@[expose] def omega {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) : X.Modules :=
  UniversalSheafDifferentials318.omega (coefficients f)

@[expose] def D {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :=
  UniversalSheafDifferentials318.D (coefficients f)

variable {R : Type u} [CommRing R]

/-- The intrinsic differential sheaf of the actual globally glued Weierstrass
family. No local sheaf, rank-one frame, or universal property is assumed. -/
@[expose] def familyOmega (A B : R) : (WeierstrassGluing318.scheme A B).Modules :=
  omega (WeierstrassGluing318.structureMap A B)

/-- Its actual universal derivation, defined on every open of the actual family. -/
@[expose] def familyD (A B : R) := D (WeierstrassGluing318.structureMap A B)

/-- Every actual sheaf-valued R-derivation on the family factors uniquely. -/
theorem family_universal (A B : R) (M : (WeierstrassGluing318.scheme A B).Modules)
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (coefficients (WeierstrassGluing318.structureMap A B))) :
    ∃! f : familyOmega A B ⟶ M, (familyD A B).postcomp f.val=d :=
  UniversalSheafDifferentials318.existsUnique_desc _ d

@[expose] def literalOmega (N : ℕ) : (WeierstrassGluing318.literalScheme N).Modules :=
  familyOmega (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
@[expose] def literalD (N : ℕ) :=
  familyD (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
end FamilyIntrinsicDifferentials318
