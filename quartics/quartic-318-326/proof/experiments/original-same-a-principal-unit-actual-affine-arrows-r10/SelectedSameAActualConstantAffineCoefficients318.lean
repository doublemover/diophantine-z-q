module

public import SelectedSameAConstantActualReduction318
public import SelectedSameAAffineCoordinatePullback318

/-! The coefficient ring on the true constant-family chart, its literal
closed reduction and both structure maps. The reduction coefficient is
fst and the marked base epsilon is inr 1, before any choice of gauges. -/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SelectedSameAActualConstantAffineCoefficients318

open SelectedSameAConstantActualReduction318
open SelectedSameAConstantAffineCoverProduced318
open SelectedSameAConstantTargetTriangle318
open SelectedSameAConstantDualNumberBaseChange318
open SelectedSameAAffineCoordinatePullback318
open SelectedSameAActualAffineOpenCoefficientIso318 (coordinate coordinateIso coordinate_natural)

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ S k)
variable {B : Type u} [CommRing B] [Algebra k B]
variable (j : S B ⟶ A) [IsOpenImmersion j] (hj : j ≫ a = sp (algebraMap k B))

abbrev originalOpen : A.Opens := j.opensRange
abbrev constantOpen : (pullback a (base k)).Opens :=
  (pullback.fst a (base k)) ⁻¹ᵁ originalOpen j

theorem chart_open_range :
    letI := constant_chart_open a j hj
    (constantAffineMap a j hj).opensRange = constantOpen a j := by
  letI := constant_chart_open a j hj
  have hp := constantAffineMap_fst a j hj
  apply TopologicalSpace.Opens.ext
  ext z
  change z ∈ (constantAffineMap a j hj).opensRange ↔
    pullback.fst a (base k) z ∈ j.opensRange
  rw [Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · rintro ⟨y, rfl⟩
    use sp (TrivSqZeroExt.inlHom B B) y
    have hx := congrArg (fun f : S (TrivSqZeroExt B B) ⟶ A => f y) hp
    simpa only [Scheme.Hom.comp_apply] using hx.symm
  · rintro ⟨x, hx⟩
    obtain ⟨y, _, hy⟩ := Scheme.exists_preimage_of_isPullback
      (constant_chart_pullback a j hj) x z hx
    exact ⟨y, hy⟩

theorem preimage_constantOpen :
    (constantReduction a) ⁻¹ᵁ constantOpen a j = originalOpen j := by
  unfold constantOpen
  rw [← Scheme.Hom.comp_preimage, constantReduction_fst, Scheme.Hom.id_preimage]

/-- The coefficient iso on the exact target affine open, with no freely
chosen coordinate iso. -/
noncomputable def actualCoordinateIso :
    Γ(pullback a (base k),constantOpen a j) ≅ CommRingCat.of (TrivSqZeroExt B B) := by
  letI := constant_chart_open a j hj
  exact coordinateIso (constantAffineMap a j hj) (constantOpen a j) (chart_open_range a j hj)

theorem actualCoordinateIso_hom :
    letI := constant_chart_open a j hj
    (actualCoordinateIso a j hj).hom =
      coordinate (constantAffineMap a j hj) (constantOpen a j) (chart_open_range a j hj) := by
  letI := constant_chart_open a j hj
  unfold actualCoordinateIso
  exact SelectedSameAActualAffineOpenCoefficientIso318.coordinateIso_hom _ _ _

/-- Reduction on the same ambient open is literally the first
coefficient. The appLE inequality is equality of the original opens. -/
theorem closed_coefficient :
    (constantReduction a).appLE (constantOpen a j) (originalOpen j)
        (preimage_constantOpen a j).ge ≫ coordinate j (originalOpen j) rfl =
      (actualCoordinateIso a j hj).hom ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom := by
  letI := constant_chart_open a j hj
  rw [actualCoordinateIso_hom]
  exact coordinate_pullback (constantReduction a) (constantAffineMap a j hj) j
    (constantOpen a j) (originalOpen j) (chart_open_range a j hj) rfl
    (preimage_constantOpen a j).ge _ (constant_chart_on_closed_fibre a j hj)

/-- The pullback of the reduced coefficients uses the original first
projection, not a chosen local algebra section of a deformation. -/
theorem constant_coefficient :
    (pullback.fst a (base k)).app (originalOpen j) ≫ (actualCoordinateIso a j hj).hom =
      coordinate j (originalOpen j) rfl ≫ CommRingCat.ofHom (TrivSqZeroExt.inlHom B B) := by
  letI := constant_chart_open a j hj
  rw [actualCoordinateIso_hom]
  rw [Scheme.Hom.app_eq_appLE (pullback.fst a (base k))]
  exact coordinate_pullback (pullback.fst a (base k)) j (constantAffineMap a j hj)
    (originalOpen j) (constantOpen a j) rfl (chart_open_range a j hj)
    le_rfl _ (constantAffineMap_fst a j hj).symm

/-- The actual marked scalar is obtained from the second projection.
It retains the originally chosen inr 1, with no unit rescaling. -/
theorem base_coefficient :
    (pullback.snd a (base k)).appLE ⊤ (constantOpen a j) le_top ≫
      (actualCoordinateIso a j hj).hom =
      (Scheme.ΓSpecIso (CommRingCat.of (D k))).hom ≫
        CommRingCat.ofHom (coeffMap (algebraMap k B)) := by
  letI := constant_chart_open a j hj
  rw [actualCoordinateIso_hom]
  exact coordinate_pullback_global (pullback.snd a (base k)) (constantAffineMap a j hj)
    (constantOpen a j) (chart_open_range a j hj) _ (constantAffineMap_snd a j hj)

theorem marked_epsilon_coefficient :
    (actualCoordinateIso a j hj).hom
      ((pullback.snd a (base k)).appLE ⊤ (constantOpen a j) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (D k))).inv
          (TrivSqZeroExt.inr (1 : k)))) =
      (TrivSqZeroExt.inr (1 : B) : TrivSqZeroExt B B) := by
  let eps : D k := TrivSqZeroExt.inr (1 : k)
  let s := (Scheme.ΓSpecIso (CommRingCat.of (D k))).inv eps
  have h := congrArg (fun m : Γ(S (D k),⊤) ⟶
    CommRingCat.of (TrivSqZeroExt B B) => m s) (base_coefficient a j hj)
  refine h.trans ?_
  change coeffMap (algebraMap k B) ((Scheme.ΓSpecIso (CommRingCat.of (D k))).hom s) = _
  have hε : (Scheme.ΓSpecIso (CommRingCat.of (D k))).hom s = eps :=
    congrArg (fun m : CommRingCat.of (D k) ⟶ CommRingCat.of (D k) => m eps)
      (Scheme.ΓSpecIso (CommRingCat.of (D k))).inv_hom_id
  rw [hε]
  apply TrivSqZeroExt.ext
  · simp only [eps, coeffMap_fst, TrivSqZeroExt.fst_inr, map_zero]
  · simp only [eps, coeffMap_snd, TrivSqZeroExt.snd_inr, map_one]


variable {B' : Type u} [CommRing B'] [Algebra k B']
variable (j' : S B' ⟶ A) [IsOpenImmersion j'] (hj' : j' ≫ a = sp (algebraMap k B'))
variable (f : B →ₐ[k] B') (hf : sp f.toRingHom ≫ j = j')
variable (hU : originalOpen j' ≤ originalOpen j)

/-- The two true thickened coordinate rings restrict coefficientwise
under the same literal original affine restriction. -/
include hf in
theorem constant_coefficient_restriction :
    (pullback a (base k)).presheaf.map
        (homOfLE ((pullback.fst a (base k)).preimage_mono hU)).op ≫
        (actualCoordinateIso a j' hj').hom =
      (actualCoordinateIso a j hj).hom ≫ CommRingCat.ofHom (coeffMap f.toRingHom) := by
  letI := constant_chart_open a j hj
  letI := constant_chart_open a j' hj'
  rw [actualCoordinateIso_hom a j' hj', actualCoordinateIso_hom a j hj]
  exact coordinate_natural (constantAffineMap a j hj) (constantOpen a j)
    (chart_open_range a j hj) (constantAffineMap a j' hj') (constantOpen a j')
    (chart_open_range a j' hj') ((pullback.fst a (base k)).preimage_mono hU)
    (coeffMap f.toRingHom) (constantAffineMap_restriction a j j' hj hj' f hf)

end SelectedSameAActualConstantAffineCoefficients318
