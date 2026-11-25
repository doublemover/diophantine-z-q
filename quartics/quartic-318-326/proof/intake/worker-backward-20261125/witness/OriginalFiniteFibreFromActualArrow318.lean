module
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public section
noncomputable section

namespace OriginalFiniteFibreFromActualArrow318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X : Scheme} (f : Z ⟶ X) [IsFinite f]
local notation "Q" => Spec (CommRingCat.of ℚ)
variable (q : Q ⟶ X)

abbrev actualFibre := pullback f q
abbrev base : actualFibre f q ⟶ Q := pullback.snd f q
abbrev B := Γ(actualFibre f q, ⊤)

/-- The source of the pulled-back actual finite map is genuinely affine. -/
theorem affine : IsAffine (actualFibre f q) :=
  isAffine_of_isAffineHom (base f q)

def iso : actualFibre f q ≅ Spec (B f q) := by
  letI := affine f q
  exact (actualFibre f q).isoSpec

def coeff : CommRingCat.of ℚ ⟶ B f q :=
  (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ (base f q).appTop

/-- The scalar algebra is determined by the structural arrow of the
actual fibre. It is not a separate input to the point construction. -/
@[instance_reducible] def scalar : Algebra ℚ (B f q) := (coeff f q).hom.toAlgebra

theorem moduleFinite :
    letI := scalar f q
    Module.Finite ℚ (B f q) := by
  let := scalar f q
  apply RingHom.finite_algebraMap.mp
  change (coeff f q).hom.Finite
  exact RingHom.Finite.comp (base f q).finite_appTop
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).2)

theorem base_read : (iso f q).inv ≫ base f q = Spec.map (coeff f q) := by
  let S := CommRingCat.of ℚ
  let r := (Scheme.ΓSpecIso S).inv
  apply (cancel_epi (iso f q).hom).mp
  calc
    _ = base f q := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = (base f q ≫ (Spec S).toSpecΓ) ≫ Spec.map r := by
      rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = _ := by
      change (base f q ≫ (Spec S).toSpecΓ) ≫ Spec.map r =
        (actualFibre f q).toSpecΓ ≫ Spec.map (coeff f q)
      rw [Scheme.toSpecΓ_naturality, Category.assoc, coeff, Spec.map_comp]

def projection : Spec (B f q) ⟶ Z :=
  (iso f q).inv ≫ pullback.fst f q

/-- R214's affine Cartier base square is constructed from the original
finite arrow; we do not assume any independently represented fibre. -/
theorem actual_square :
    letI := scalar f q
    IsPullback (projection f q) (Spec.algebraMap ℚ (B f q)) f q := by
  change IsPullback (projection f q) (Spec.map (coeff f q)) f q
  have w : projection f q ≫ f = Spec.map (coeff f q) ≫ q := by
    rw [← base_read f q]
    change ((iso f q).inv ≫ pullback.fst f q) ≫ f =
      ((iso f q).inv ≫ pullback.snd f q) ≫ q
    rw [Category.assoc, Category.assoc, pullback.condition]
  exact IsPullback.of_iso_pullback ⟨w⟩ (iso f q).symm rfl (base_read f q)

/-- Nonempty only where it is genuinely needed: one actual point above
this rational q. No full-base surjectivity or new geometric count. -/
theorem nontrivialAt (h : ∃ x : Z, f x=q (⊥ : PrimeSpectrum ℚ)) :
    Nontrivial (B f q) := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨z,_,_⟩ := Scheme.Pullback.exists_preimage_pullback (f:=f) (g:=q)
    x (⊥ : PrimeSpectrum ℚ) hx
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨(iso f q).hom z⟩

/-- A closed residue on that same fibre, not a separately mapped
number field. Its field structure is the exact maximal-ideal quotient. -/
theorem exists_closedAt (h : ∃ x : Z, f x=q (⊥ : PrimeSpectrum ℚ)) :
    letI := scalar f q
    ∃ m : Ideal (B f q), m.IsMaximal ∧ Module.Finite ℚ ((B f q) ⧸ m) := by
  let := scalar f q
  let := nontrivialAt f q h
  let := moduleFinite f q
  obtain ⟨m,hm⟩ := Ideal.exists_maximal (α:=B f q)
  exact ⟨m,hm,Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ m).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℚ m)⟩

end OriginalFiniteFibreFromActualArrow318

#print axioms OriginalFiniteFibreFromActualArrow318.moduleFinite
#print axioms OriginalFiniteFibreFromActualArrow318.base_read
#print axioms OriginalFiniteFibreFromActualArrow318.actual_square
#print axioms OriginalFiniteFibreFromActualArrow318.nontrivialAt
#print axioms OriginalFiniteFibreFromActualArrow318.exists_closedAt
