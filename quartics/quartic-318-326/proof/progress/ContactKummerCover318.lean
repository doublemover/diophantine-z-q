module
public import ContactKummerOrder318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace ContactKummerCover318
set_option maxHeartbeats 300000
open CategoryTheory AlgebraicGeometry ContactKummerOrder318
@[expose] def base : Scheme := Spec (CommRingCat.of OpenBase)
@[expose] def baseMap : base ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R OpenBase))

theorem base_open : IsOpenImmersion baseMap := by
  dsimp [baseMap,base,OpenBase]
  infer_instance

theorem omitted_points (q:ℚ) : Polynomial.eval q denominator≠0 ↔
    ∀i:Fin 4,q≠LinearContactSquareclass318.contacts i := by
  simp [denominator,Polynomial.eval_prod,Finset.prod_ne_zero_iff,sub_ne_zero]

@[expose] def cover (c:Fin 4→ℚˣ) : Scheme := Spec (CommRingCat.of (OpenOrder c))
@[expose] def structureMap (c:Fin 4→ℚˣ) : cover c ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap OpenBase (OpenOrder c)))

theorem finite_etale (c:Fin 4→ℚˣ) : IsFinite (structureMap c) ∧ Etale (structureMap c) := by
  constructor
  · apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr (open_finite_free_etale c).1
  · apply (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
    exact RingHom.etale_algebraMap.mpr (open_finite_free_etale c).2.2

theorem flat_surjective (c:Fin 4→ℚˣ) : Flat (structureMap c) ∧ Surjective (structureMap c) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr (open_faithfullyFlat c)

/-- The complement of exactly the four literal finite contacts is the
actual base of the constructed cover, with no geometric cover input. -/
theorem actual_cover (c:Fin 4→ℚˣ) :
    IsFinite (structureMap c) ∧ Etale (structureMap c) ∧
      Flat (structureMap c) ∧ Surjective (structureMap c) ∧
      Module.finrank OpenBase (OpenOrder c)=16 :=
  ⟨(finite_etale c).1,(finite_etale c).2,(flat_surjective c).1,
    (flat_surjective c).2,open_rank_sixteen c⟩
end ContactKummerCover318
