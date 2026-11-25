module
public import OriginalLiteralContactQuotientPoint318
public import SourceGlobalAffine318
public import SourceTwistArithmetic318
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section
noncomputable section

namespace OriginalLiteralCoarseFibre318
open AlgebraicGeometry CategoryTheory Limits Polynomial
open scoped TensorProduct
open ContactKummerOrder318 (R SourceOrder)
open OriginalLiteralContactQuotientPoint318 (coord evalAffine affinePoint point actual_noncontact)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local notation "c" => SourceTwistArithmetic318.units
local notation "P" => ProjectiveJLine318.scheme ℚ
local notation "Y" => ContactProjectiveModel318.model c
local notation "π" => ContactProjectiveModel318.modelMap c
local notation "j" => SourceGlobalAffine318.chartEmbedding c
local notation "W" => SourceOrder c
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "g" => Spec.algebraMap R W
local notation "k" => JLineAtlas318.chart ℚ 1

variable (u v : ℤ)

abbrev coeff (i : Fin 4) : ℚ := evalAffine u v (ContactKummerOrder318.coefficient c i)

theorem coeff_exact (i : Fin 4) : coeff u v i =
    SourceTwistArithmetic318.constants i * (coord u v - LinearContactSquareclass318.contacts i) := by
  simp only [coeff,ContactKummerOrder318.coefficient,map_mul,map_sub,evalAffine,aeval_X,
    aeval_C,algebraMap_self_apply,SourceTwistArithmetic318.units_val]

/-- The whole specialization retains all four quadratic equations,
including fibres over which some of the radicals are already squares. -/
abbrev FibreRing := FourRootOrder318.Order (coeff u v)

theorem rank : Module.finrank ℚ (FibreRing u v)=16 := FourRootOrder318.rank_sixteen _
theorem finite : Module.Finite ℚ (FibreRing u v) := (FourRootOrder318.finite_free _).1

theorem etale (hne : ∀ i : Fin 5, ContactRadical318.forms u v i≠0) :
    Algebra.Etale ℚ (FibreRing u v) := by
  apply FourRootOrder318.etale
  · exact isUnit_iff_ne_zero.mpr (by norm_num)
  · intro i
    rw [coeff_exact]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (SourceTwistArithmetic318.constants_ne_zero i)
      (sub_ne_zero.mpr ((actual_noncontact u v hne).2 i)))

private def evaluatedAlgebra : Algebra R ℚ := (evalAffine u v).toRingHom.toAlgebra
local notation "F" => FibreRing u v
local notation "B" => Spec (CommRingCat.of F)
local notation "b" => Spec.algebraMap ℚ F

/-- Stock tensor base change and the old whole four-root specialization
identify the actual affine Cartesian pullback with its full coordinate ring. -/
def affineIso : pullback (affinePoint u v) g ≅ B := by
  letI := evaluatedAlgebra u v
  let e := FourRootOrder318.baseChange (ContactKummerOrder318.coefficient c) ℚ
  exact (pullbackSpecIso R ℚ W) ≪≫ Scheme.Spec.mapIso e.symm.toCommRingCatIso.op

theorem first_read :
    (affineIso u v).inv ≫ pullback.fst (affinePoint u v) g = b := by
  letI := evaluatedAlgebra u v
  let e := FourRootOrder318.baseChange (ContactKummerOrder318.coefficient c) ℚ
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
       (pullbackSpecIso R ℚ W).inv ≫ pullback.fst (affinePoint u v) g = _
  rw [pullbackSpecIso_inv_fst',←Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact e.commutes

def affineProjection : B ⟶ Spec (CommRingCat.of W) :=
  (affineIso u v).inv ≫ pullback.snd (affinePoint u v) g

theorem affine_square :
    IsPullback (affineProjection u v) b g (affinePoint u v) := by
  have w : b ≫ affinePoint u v = affineProjection u v ≫ g := by
    rw [←first_read u v,affineProjection,Category.assoc,Category.assoc,pullback.condition]
  exact (IsPullback.of_iso_pullback ⟨w⟩ (affineIso u v).symm
    (first_read u v) rfl).flip

/-- The actual stored source affine is exactly the inverse image of
the finite chart of the original normalization, not just a dense chart. -/
theorem full_chart : IsPullback j g π k := by
  refine (IsOpenImmersion.isPullback g j k π
    (SourceGlobalAffine318.chartEmbedding_over_contact_line c) ?_).flip
  rw [SourceGlobalAffine318.chartEmbedding_range]
  change π ⁻¹ᵁ k.opensRange = π ⁻¹ᵁ (k ''ᵁ ⊤)
  rw [Scheme.Hom.image_top_eq_opensRange]

def projection : B ⟶ Y := affineProjection u v ≫ j

/-- The whole rank-16 fibre is the pullback of the actual proper
Q-model along the original projective contact point q. -/
theorem actual_square : IsPullback (projection u v) b π (point u v) :=
  (affine_square u v).paste_horiz full_chart

/-- One exact number-field point on that same original coarse model.
The residue is taken once from the genuine whole fibre, not assumed
to have the full degree sixteen. -/
theorem closed_point :
    ∃ m : Ideal F, m.IsMaximal ∧
      Module.Finite ℚ (F ⧸ m) ∧
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ projection u v) ≫ π =
        Spec.algebraMap ℚ (F ⧸ m) ≫ point u v := by
  have hF : Nontrivial F :=
    Module.nontrivial_of_finrank_pos (R:=ℚ) (by rw [rank u v]; decide)
  letI := hF
  letI := finite u v
  obtain ⟨m,hm⟩ := Ideal.exists_maximal (α:=F)
  have hL : Module.Finite ℚ (F ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℚ m)
  refine ⟨m,hm,hL,?_⟩
  let pp := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))
  change (pp ≫ projection u v) ≫ π=_
  rw [Category.assoc,(actual_square u v).w,←Category.assoc]
  congr 1
  rw [←Spec.map_comp]

end OriginalLiteralCoarseFibre318

#print axioms OriginalLiteralCoarseFibre318.coeff_exact
#print axioms OriginalLiteralCoarseFibre318.etale
#print axioms OriginalLiteralCoarseFibre318.first_read
#print axioms OriginalLiteralCoarseFibre318.full_chart
#print axioms OriginalLiteralCoarseFibre318.actual_square
#print axioms OriginalLiteralCoarseFibre318.closed_point
