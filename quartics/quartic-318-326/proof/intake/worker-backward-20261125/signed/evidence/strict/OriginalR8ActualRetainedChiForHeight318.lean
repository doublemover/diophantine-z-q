module
public import OriginalR8GluedRetainedSection318
public import OriginalUpperR60AmbientChi318

@[expose] public section
noncomputable section

namespace OriginalR8ActualRetainedChiForHeight318

open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalR8ExactMarkedReciprocal318 (χ π)
open OriginalR8GluedProjectiveMap318 (projection)
open OriginalR8BinaryNormalGlue318 (glued includeChart)
open OriginalR8IntegralMarkedRead318 (CentreRead)
open OriginalR8GluedRetainedSection318 (retainedSection actual_target_coordinate)
open OriginalUpperR60RetainedChiRead318 (retained retained_ambient)
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E V : Type u} [Field E] [Field V] [Algebra E[X] V] [Algebra (𝓞 E) V]
variable (hχ : χ (E:=E) (V:=V)≠0)
abbrev source : Scheme.{u} := glued (R:=𝓞 E) (π hχ)

abbrev zeroChart (E : Type u) [Field E] :
    Spec (CommRingCat.of ((𝓞 E)[X])) ⟶ ProjectiveJLine318.scheme (𝓞 E) :=
  JLineAtlas318.chart (𝓞 E) 0

abbrev proj : source hχ ⟶ ProjectiveJLine318.scheme (𝓞 E) :=
  projection (R:=𝓞 E) (π hχ)

/-- The actual full χ-open of the existing chosen model. -/
def U : (source hχ).Opens := proj hχ ⁻¹ᵁ (zeroChart E).opensRange

theorem entire_normal_chart :
    U hχ=(includeChart (R:=𝓞 E) (π hχ) ⟨false⟩).opensRange :=
  OriginalR8GluedCartesianCharts318.full_preimage (R:=𝓞 E) (π hχ) ⟨false⟩

theorem range_of_restriction :
    Set.range ((U hχ).ι ≫ proj hχ) ⊆ Set.range (zeroChart E) := by
  rintro _ ⟨x,rfl⟩
  have hx : (U hχ).ι x∈ proj hχ ⁻¹ᵁ (zeroChart E).opensRange := x.property
  obtain ⟨y,hy⟩ := Scheme.Hom.mem_opensRange.mp ((Scheme.Hom.mem_preimage (proj hχ)).mp hx)
  exact ⟨y,hy.trans (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- The literal affine χ-coordinate map of this open. It is the lift of
the actual global projection, not a newly chosen local function. -/
def coordinate : (U hχ).toScheme ⟶ Spec (CommRingCat.of ((𝓞 E)[X])) :=
  IsOpenImmersion.lift (zeroChart E) ((U hχ).ι ≫ proj hχ) (range_of_restriction hχ)

theorem coordinate_factors :
    coordinate hχ ≫ zeroChart E = (U hχ).ι ≫ proj hχ :=
  IsOpenImmersion.lift_fac _ _ _

theorem cartesian :
    IsPullback (coordinate hχ) (U hχ).ι (zeroChart E) (proj hχ) :=
  IsOpenImmersion.isPullback _ _ _ _ (coordinate_factors hχ).symm
    (Scheme.Opens.opensRange_ι (U hχ)).symm

variable [NumberField E] [Algebra E V] [IsScalarTower (𝓞 E) E V] [IsScalarTower E E[X] V]
variable (n : 𝓞 E) (full : CentreRead (E:=E) (V:=V) n)

abbrev sameSection : Spec (CommRingCat.of (𝓞 E)) ⟶ source hχ :=
  retainedSection hχ n full

theorem lands (x : Spec (CommRingCat.of (𝓞 E))) : sameSection hχ n full x∈U hχ := by
  apply (Scheme.Hom.mem_preimage (proj hχ)).mpr
  apply Scheme.Hom.mem_opensRange.mpr
  let a := Spec.map (CommRingCat.ofHom (Polynomial.aeval n : (𝓞 E)[X]→ₐ[𝓞 E]𝓞 E).toRingHom)
  refine ⟨a x,?_⟩
  calc
    zeroChart E (a x)=(a ≫ zeroChart E) x := (Scheme.Hom.comp_apply _ _ _).symm
    _=(sameSection hχ n full ≫ proj hχ) x :=
      congrArg (fun g : Spec (CommRingCat.of (𝓞 E))⟶ProjectiveJLine318.scheme (𝓞 E) => g x)
        (actual_target_coordinate hχ n full).symm
    _=proj hχ (sameSection hχ n full x) := Scheme.Hom.comp_apply _ _ _

/-- This is the entire affine evaluation used by the native R60
recipient, on exactly the arithmetic section constructed from full. -/
theorem entire_coordinate :
    retained (sameSection hχ n full) (U hχ) (lands hχ n full) ≫ coordinate hχ =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom n)) := by
  apply (cancel_mono (zeroChart E)).mp
  rw [Category.assoc,coordinate_factors,←Category.assoc,retained_ambient]
  have he : (Polynomial.aeval n : (𝓞 E)[X]→ₐ[𝓞 E]𝓞 E).toRingHom =
      Polynomial.evalRingHom n := Polynomial.coe_aeval_eq_evalRingHom n
  rw [←he]
  exact actual_target_coordinate hχ n full

/-- Exact value of the genuine coordinate in the actual local ring at
each retained arithmetic specialization, even at places dividing n. -/
theorem stalk_coordinate (x : Spec (CommRingCat.of (𝓞 E))) :
    ((sameSection hχ n full).stalkMap x).hom
      (((source hχ).presheaf.germ (U hχ) (sameSection hχ n full x) (lands hχ n full x)).hom
        (OriginalUpperR60AmbientChi318.ambient (U hχ) (coordinate hχ))) =
      (StructureSheaf.toStalk (CommRingCat.of (𝓞 E)) x).hom n :=
  OriginalUpperR60AmbientChi318.stalk (sameSection hχ n full) (U hχ)
    (lands hχ n full) (coordinate hχ) n (entire_coordinate hχ n full) x

end OriginalR8ActualRetainedChiForHeight318

#print axioms OriginalR8ActualRetainedChiForHeight318.entire_normal_chart
#print axioms OriginalR8ActualRetainedChiForHeight318.cartesian
#print axioms OriginalR8ActualRetainedChiForHeight318.entire_coordinate
#print axioms OriginalR8ActualRetainedChiForHeight318.stalk_coordinate
