module
public import OriginalAffineRankOneCommutation318
public import OriginalAffineSectionZero318
public section
noncomputable section
namespace AffineLineSectionGenerator318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (A : CommRingCat.{u}) (L : Line (Spec A))
local notation "P" => OriginalLineAffineModel318.sections A L
variable (s : P)

/-- The actual evaluation ideal is unit precisely when a genuine original
linear functional takes the section to one. No global frame is assumed. -/
lemma ideal_top_iff : OriginalAffineSectionZero318.ideal A L s=⊤ ↔
    ∃ φ : Module.Dual A P,φ s=1 := by
  constructor
  · intro h
    have hm : (1:A)∈OriginalAffineSectionZero318.ideal A L s := by rw [h]; trivial
    exact hm
  · rintro ⟨φ,hφ⟩
    exact Ideal.eq_top_iff_one.mpr ⟨φ,hφ⟩

/-- Rank-one commutation, proved on the original principal frame cover,
turns a unit evaluation into an actual inverse of scalar multiplication. -/
@[expose] def equivalence (h : OriginalAffineSectionZero318.ideal A L s=⊤) : A ≃ₗ[A] P := by
  let φ := ((ideal_top_iff A L s).mp h).choose
  have hφ : φ s=1 := ((ideal_top_iff A L s).mp h).choose_spec
  exact
    { toFun := fun a => a • s
      invFun := φ
      left_inv := by intro a; rw [map_smul,hφ,smul_eq_mul,mul_one]
      right_inv := by
        intro x
        have hc := OriginalAffineRankOneCommutation318.commutation A L φ s x
        rw [hφ,one_smul] at hc
        exact hc.symm
      map_add' := fun a b => add_smul a b s
      map_smul' := fun a b => mul_smul a b s }

lemma bijective_iff : Function.Bijective (fun a : A => a • s) ↔
    OriginalAffineSectionZero318.ideal A L s=⊤ := by
  constructor
  · intro h
    let e := LinearEquiv.ofBijective (LinearMap.toSpanSingleton A P s) h
    apply (ideal_top_iff A L s).mpr
    refine ⟨e.symm.toLinearMap,?_⟩
    have he : e 1=s := one_smul A s
    rw [←he,LinearEquiv.symm_apply_apply]
  · intro h
    exact (equivalence A L s h).bijective
end AffineLineSectionGenerator318
