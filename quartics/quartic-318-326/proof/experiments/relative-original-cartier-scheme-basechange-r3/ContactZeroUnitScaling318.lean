module
public import OriginalCoefficientUnitIso318
public import ContactZeroLineIso318
public import ContactGlobalResidueFlat318
public section
noncomputable section
namespace ContactZeroUnitScaling318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactGlobalSectionZero318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactRelativeStructuralHOne318.projection R c
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R p L ⊤
variable (u : Rˣ) (s : Γ(L.object,⊤))
local notation "a" => OriginalCoefficientUnitIso318.iso R p L u

/-- Unit scaling preserves the literal original section-zero ideal on the
full finite chart, including nilpotents and multiplicities. -/
lemma finite_ideal : finiteIdeal R c L ((u:R) • s)=finiteIdeal R c L s := by
  rw [← OriginalCoefficientUnitIso318.hom_section R p L u s]
  exact ContactZeroLineComparison318.finite_ideal R c L L a s
lemma infinity_ideal : infinityIdeal R c L ((u:R) • s)=infinityIdeal R c L s := by
  rw [← OriginalCoefficientUnitIso318.hom_section R p L u s]
  exact ContactZeroLineComparison318.infinity_ideal R c L L a s
lemma overlap_ideal : overlapIdeal R c L ((u:R) • s)=overlapIdeal R c L s := by
  rw [← OriginalCoefficientUnitIso318.hom_section R p L u s]
  exact ContactZeroLineComparison318.overlap_ideal R c L L a s

/-- The SAME entire original glued zero scheme is unchanged by genuine
coefficient-unit scaling. This is the geometric invariance required before
quotienting nonzero section parameters, not yet such a quotient. -/
lemma scheme_eq : scheme R c L ((u:R) • s)=scheme R c L s := by
  unfold scheme toFinite toInfinity finiteZero infinityZero overlapZero
  simp only [finite_ideal,infinity_ideal,overlap_ideal]
@[expose] def iso : scheme R c L ((u:R) • s) ≅ scheme R c L s :=
  eqToIso (scheme_eq R c L u s)
@[reassoc] lemma iso_into : (iso R c L u s).hom ≫ ContactGlobalSectionZero318.into R c L s =
    ContactGlobalSectionZero318.into R c L ((u:R) • s) := by
  unfold iso ContactGlobalSectionZero318.into finiteIntoOriginal infinityIntoOriginal
  unfold scheme toFinite toInfinity finiteZero infinityZero overlapZero
  simp only [finite_ideal,infinity_ideal,overlap_ideal,eqToIso_refl,Iso.refl_hom,Category.id_comp]

/-- The comparison preserves the actual parameter projection, not only
its abstract source scheme or its set of zeros. -/
@[reassoc] lemma iso_projection : (iso R c L u s).hom ≫
    ContactGlobalResidueFlat318.projection R c L s =
    ContactGlobalResidueFlat318.projection R c L ((u:R) • s) := by
  rw [ContactGlobalResidueFlat318.projection,← Category.assoc,iso_into]
  rfl
end ContactZeroUnitScaling318
