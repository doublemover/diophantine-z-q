module
public import PELOriginalTorsionTowerCartesian318
public import PELOriginalMultiplicationFppfCover318
public section
noncomputable section
namespace PELOriginalTorsionTowerFiniteEtale318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalTorsionKernelScheme318
open PELOriginalTorsionTowerCartesian318
variable (τ : ℂ) (hτ : 0<τ.im) (m n : ℤ)
/-- The genuine tower transition is finite etale and surjective for
m nonzero; n is arbitrary, including zero. -/
lemma finite_etale_surjective (hm : m≠0) :
    IsFinite (PELOriginalTorsionTowerPoints318.map τ hτ m n) ∧
    Etale (PELOriginalTorsionTowerPoints318.map τ hτ m n) ∧
    Function.Surjective (PELOriginalTorsionTowerPoints318.map τ hτ m n) := by
  have h := PELOriginalDivisionTorsorIso318.finite_etale_cover τ hτ m
    (structureMap τ hτ n) (targetPoint τ hτ n) hm
  letI : IsFinite (divisionProjection τ hτ m n) := h.1
  letI : Etale (divisionProjection τ hτ m n) := h.2.1
  letI : Surjective (divisionProjection τ hτ m n) := ⟨h.2.2⟩
  rw [←iso_projection]
  exact ⟨inferInstance,inferInstance,((iso τ hτ m n).hom≫divisionProjection τ hτ m n).surjective⟩
/-- Native all-prime rank of the actual tower map, not a quotient of
geometric torsion-point counts. -/
lemma degree (hm : m≠0) (x : kernel τ hτ n) :
    (PELOriginalTorsionTowerPoints318.map τ hτ m n).finrank x=m.natAbs^4 := by
  have h := PELOriginalDivisionTorsorIso318.finite_etale_cover τ hτ m
    (structureMap τ hτ n) (targetPoint τ hτ n) hm
  letI : IsFinite (divisionProjection τ hτ m n) := h.1
  letI : Etale (divisionProjection τ hτ m n) := h.2.1
  rw [←iso_projection,Scheme.Hom.finrank_comp_left_of_isIso]
  exact PELOriginalDivisionTorsorIso318.degree τ hτ m
    (structureMap τ hτ n) (targetPoint τ hτ n) hm x

variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ)) (p : torsion τ hτ n ρ)
/-- Every actual n-torsion point has an (mn)-torsion lift under [m]
on the explicit finite etale division cover, even for nonreduced tests. -/
@[expose] def localLift : torsion τ hτ (m*n)
    (PELOriginalMultiplicationLocalDivision318.coverBase τ hτ m ρ p.val) := by
  let r := PELOriginalMultiplicationLocalDivision318.root τ hτ m ρ p.val
  let F := pull τ hτ ρ (PELOriginalMultiplicationLocalDivision318.projection τ hτ m ρ p.val) rfl
  refine ⟨r,?_⟩
  calc
    (m*n) • r=n • (m • r) := by rw [mul_comm,mul_smul]
    _=n • F p.val := congrArg (fun x => n • x)
      (PELOriginalMultiplicationLocalDivision318.root_equation τ hτ m ρ p.val)
    _=0 := by rw [←map_zsmul,p.property,map_zero]
lemma localLift_action :
    (PELOriginalTorsionTowerPoints318.down τ hτ m n _ (localLift τ hτ m n ρ p)).val=
      pull τ hτ ρ (PELOriginalMultiplicationLocalDivision318.projection τ hτ m ρ p.val) rfl p.val :=
  PELOriginalMultiplicationLocalDivision318.root_equation τ hτ m ρ p.val
/-- The precise arrow used by that lift is a covering singleton in the
native fppf topology. Combined with middle exactness, this gives honest
fppf-local exactness rather than false pointwise torsion divisibility. -/
lemma covering (hm : m≠0) :
    Sieve.ofArrows (fun _ : PUnit => Over.mk
      (PELOriginalMultiplicationLocalDivision318.coverBase τ hτ m ρ p.val))
      (fun _ => Over.homMk
        (PELOriginalMultiplicationLocalDivision318.projection τ hτ m ρ p.val) rfl) ∈
      RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)) (Over.mk ρ) :=
  PELOriginalMultiplicationFppfCover318.covering τ hτ m ρ p.val hm
end PELOriginalTorsionTowerFiniteEtale318
