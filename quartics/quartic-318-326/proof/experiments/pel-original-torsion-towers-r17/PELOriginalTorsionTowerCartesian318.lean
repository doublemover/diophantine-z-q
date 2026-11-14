module
public import PELOriginalTorsionTowerPoints318
public section
noncomputable section
namespace PELOriginalTorsionTowerCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalTorsionKernelScheme318
open PELOriginalMultiplicationLocalDivision318
open PELOriginalTorsionTowerPoints318
variable (τ : ℂ) (hτ : 0<τ.im) (m n : ℤ)
abbrev targetPoint := (universal τ hτ n).val
abbrev Division := Cover τ hτ m (structureMap τ hτ n) (targetPoint τ hτ n)
abbrev divisionProjection : Division τ hτ m n⟶kernel τ hτ n :=
  projection τ hτ m (structureMap τ hτ n) (targetPoint τ hτ n)
abbrev divisionBase : Division τ hτ m n⟶Spec (CommRingCat.of ℂ) :=
  coverBase τ hτ m (structureMap τ hτ n) (targetPoint τ hτ n)

@[expose] def toDivision : kernel τ hτ (m*n)⟶Division τ hτ m n :=
  pullback.lift (inclusion τ hτ (m*n)) (PELOriginalTorsionTowerPoints318.map τ hτ m n)
    (map_inclusion τ hτ m n).symm
@[reassoc] lemma toDivision_first : toDivision τ hτ m n≫pullback.fst _ _=inclusion τ hτ (m*n) :=
  pullback.lift_fst _ _ _
@[reassoc] lemma toDivision_second : toDivision τ hτ m n≫divisionProjection τ hτ m n=
    PELOriginalTorsionTowerPoints318.map τ hτ m n := pullback.lift_snd _ _ _

/-- The actual division root of a universal n-torsion point is (mn)-torsion
on the WHOLE division scheme, not just its geometric points. -/
@[expose] def divisionTorsion : torsion τ hτ (m*n) (divisionBase τ hτ m n) := by
  let r := root τ hτ m (structureMap τ hτ n) (targetPoint τ hτ n)
  let F := pull τ hτ (structureMap τ hτ n) (divisionProjection τ hτ m n) rfl
  refine ⟨r,?_⟩
  calc
    (m*n) • r=n • (m • r) := by rw [mul_comm,mul_smul]
    _=n • F (targetPoint τ hτ n) :=
      congrArg (fun x => n • x) (root_equation τ hτ m (structureMap τ hτ n) (targetPoint τ hτ n))
    _=0 := by
      rw [←map_zsmul]
      exact (congrArg F (universal τ hτ n).property).trans (map_zero F)
@[expose] def fromDivision : Division τ hτ m n⟶kernel τ hτ (m*n) :=
  ((pointsEquiv τ hτ (m*n) (divisionBase τ hτ m n)).symm (divisionTorsion τ hτ m n)).val
@[reassoc] lemma fromDivision_first : fromDivision τ hτ m n≫inclusion τ hτ (m*n)=pullback.fst _ _ := by
  have h := (pointsEquiv τ hτ (m*n) (divisionBase τ hτ m n)).apply_symm_apply
    (divisionTorsion τ hτ m n)
  exact congrArg (fun x => x.val.val) h

/-- Literal Cartesian torsion tower: K_(mn) is the actual [m]-division
cover of the universal K_n point, preserving all infinitesimal structure. -/
@[expose] def iso : kernel τ hτ (m*n)≅Division τ hτ m n where
  hom := toDivision τ hτ m n
  inv := fromDivision τ hτ m n
  hom_inv_id := by
    apply (cancel_mono (inclusion τ hτ (m*n))).mp
    rw [Category.assoc,fromDivision_first,toDivision_first,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc,toDivision_first,fromDivision_first,Category.id_comp]
    · apply (cancel_mono (inclusion τ hτ n)).mp
      change ((fromDivision τ hτ m n≫toDivision τ hτ m n)≫divisionProjection τ hτ m n)≫inclusion τ hτ n=
        (𝟙 (Division τ hτ m n)≫divisionProjection τ hτ m n)≫inclusion τ hτ n
      calc
        _=fromDivision τ hτ m n≫(toDivision τ hτ m n≫divisionProjection τ hτ m n)≫inclusion τ hτ n := by
          simp only [Category.assoc]
        _=fromDivision τ hτ m n≫PELOriginalTorsionTowerPoints318.map τ hτ m n≫inclusion τ hτ n := by
          rw [toDivision_second]
        _=fromDivision τ hτ m n≫inclusion τ hτ (m*n)≫PELOriginalIntegerMultiplication318.multiplication τ hτ m := by
          rw [map_inclusion]
        _=pullback.fst _ _≫PELOriginalIntegerMultiplication318.multiplication τ hτ m := by
          rw [←Category.assoc,fromDivision_first]
        _=divisionProjection τ hτ m n≫inclusion τ hτ n := pullback.condition
        _=_ := by rw [Category.id_comp]

@[reassoc] lemma iso_projection : (iso τ hτ m n).hom≫divisionProjection τ hτ m n=
    PELOriginalTorsionTowerPoints318.map τ hτ m n := toDivision_second τ hτ m n
end PELOriginalTorsionTowerCartesian318
