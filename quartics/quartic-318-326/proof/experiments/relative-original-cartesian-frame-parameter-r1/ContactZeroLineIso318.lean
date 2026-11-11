module
public import ContactZeroLineComparison318
public import ContactGlobalZeroClosed318
public section
noncomputable section
namespace ContactZeroLineIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactGlobalSectionZero318 ContactZeroLineComparison318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L N : Line (curve R c)) (a : L.object ≅ N.object) (s : Γ(L.object,⊤))

/-- The explicit global gluing construction depends only on the three
literal original zero ideals. Their equality under the actual line
comparison identifies the entire scheme, not merely its underlying set. -/
lemma scheme_eq : scheme R c N (section R c L N a s) = scheme R c L s := by
  unfold scheme toFinite toInfinity finiteZero infinityZero overlapZero
  simp only [finite_ideal,infinity_ideal,overlap_ideal]

@[expose] def iso : scheme R c N (section R c L N a s) ≅ scheme R c L s :=
  eqToIso (scheme_eq R c L N a s)

/-- This specific zero-scheme comparison lies OVER THE SAME original
curve. Equality of the actual quotient gluing maps, not point bijectivity,
provides the structural compatibility. -/
@[reassoc] lemma iso_into : (iso R c L N a s).hom ≫ ContactGlobalSectionZero318.into R c L s =
    ContactGlobalSectionZero318.into R c N (section R c L N a s) := by
  unfold iso ContactGlobalSectionZero318.into finiteIntoOriginal infinityIntoOriginal
  unfold scheme toFinite toInfinity finiteZero infinityZero overlapZero
  simp only [finite_ideal,infinity_ideal,overlap_ideal,eqToIso_refl,Iso.refl_hom,Category.id_comp]
end ContactZeroLineIso318
