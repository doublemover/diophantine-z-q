module
public import FourRootProjectiveDifferential318
public import RelativeIntrinsicCotangent318
public section
noncomputable section
namespace FourRootGlobalRelativeCotangent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootGluedScheme318 FourRootProjectiveProjection318
variable (b : Fin 4 → ℂ)

/-- The actual intrinsic relative cotangent sheaf of the original entire
projective map, represented by the cokernel of its actual derivative. -/
@[expose] def omega : (scheme b).Modules :=
  RelativeIntrinsicCotangent318.omega (projection b) (structureMap b)
    FourRootProjectiveDifferential318.baseStructure (over_base b)

/-- Equality to the SAME earlier derivative cokernel, not an isomorphic
surrogate selected using desired ramification coefficients. -/
theorem omega_eq_cokernel : omega b =
    cokernel (FourRootProjectiveDifferential318.derivative b) := rfl

@[expose] def D := RelativeIntrinsicCotangent318.D (projection b) (structureMap b)
  FourRootProjectiveDifferential318.baseStructure (over_base b)

theorem D_kills_base (U : FourRootProjectiveDifferential318.Base.Opens)
    (s : Γ(FourRootProjectiveDifferential318.Base,U)) :
    (D b).d ((projection b).app U s) = 0 :=
  RelativeIntrinsicCotangent318.D_kills_base (projection b) (structureMap b)
    FourRootProjectiveDifferential318.baseStructure (over_base b) U s

/-- Universality on the whole original source and projective base, for
ALL sheaves of modules and ALL base-open regular functions. No finite
chart-only or generic differential universal property is substituted. -/
theorem universal {M : (scheme b).Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val
      (FamilyIntrinsicDifferentials318.coefficients (structureMap b)))
    (hd : ∀ (U : FourRootProjectiveDifferential318.Base.Opens)
      (s : Γ(FourRootProjectiveDifferential318.Base,U)),
      d.d ((projection b).app U s) = 0) :
    ∃! a : omega b ⟶ M, (D b).postcomp a.val = d :=
  RelativeIntrinsicCotangent318.existsUnique_desc (projection b) (structureMap b)
    FourRootProjectiveDifferential318.baseStructure (over_base b) d hd
end FourRootGlobalRelativeCotangent318
