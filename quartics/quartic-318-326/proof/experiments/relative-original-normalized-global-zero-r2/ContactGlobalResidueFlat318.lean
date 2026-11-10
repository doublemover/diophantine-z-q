module
public import ContactResidueRegularFlat318
public import ContactGlobalSectionZero318
public import ContactRelativeStructuralHOne318
public section
noncomputable section
namespace ContactGlobalResidueFlat318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactGlobalSectionZero318 OriginalSectionPullbackComposition318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

@[expose] def projection : scheme R c L s ⟶ Spec R :=
  ContactGlobalSectionZero318.into R c L s ≫ ContactRelativeStructuralHOne318.projection R c

@[expose] def chart (i : Fin 2) : Scheme :=
  Fin.cases (finiteZero R c L s) (fun _ => infinityZero R c L s) i
@[expose] def chartInto (i : Fin 2) : chart R c L s i ⟶ scheme R c L s := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact finiteChart R c L s
  · exact infinityChart R c L s
instance (i : Fin 2) : IsOpenImmersion (chartInto R c L s i) := by
  fin_cases i <;> dsimp [chartInto] <;> infer_instance

/-- Actual open cover of the SAME glued global zero by its two full
original quotient charts. It remembers the nilpotent zero structure. -/
@[expose] def cover : (scheme R c L s).OpenCover where
  I₀ := Fin 2
  X := chart R c L s
  f := chartInto R c L s
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro x
    rcases charts_cover R c L s x with hf | hi
    · exact ⟨0,hf⟩
    · exact ⟨1,hi⟩

lemma finite_projection : finiteChart R c L s ≫ projection R c L s =
    OriginalAffineSectionFlat318.projection R (finiteRing c)
      (LineSheafPullback318.line (finiteInto R c) L) (pull (finiteInto R c) L.object s) := by
  rw [projection,← Category.assoc,finiteChart_into]
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s))) ≫
    finiteInto R c) ≫ ContactRelativeStructuralHOne318.projection R c = _
  rw [Category.assoc,RelativeOriginalAffineChart318.over_test]
  rfl
lemma infinity_projection : infinityChart R c L s ≫ projection R c L s =
    OriginalAffineSectionFlat318.projection R (infinityRing c)
      (LineSheafPullback318.line (infinityInto R c) L) (pull (infinityInto R c) L.object s) := by
  rw [projection,← Category.assoc,infinityChart_into]
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s))) ≫
    infinityInto R c) ≫ ContactRelativeStructuralHOne318.projection R c = _
  rw [Category.assoc,RelativeOriginalAffineChart318.over_test]
  rfl

/-- Flatness of the genuine GLOBAL zero projection from actual nonzero
geometric residue sections. The full quotient charts cover its original
glued scheme, so no replacement zero model or pointwise gluing is used. -/
theorem flat (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s) :
    Flat (projection R c L s) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Flat) (cover R c L s)
  intro i
  fin_cases i
  · change Flat (finiteChart R c L s ≫ projection R c L s)
    rw [finite_projection]
    exact ContactResidueRegularFlat318.finite_flat R c L s hs
  · change Flat (infinityChart R c L s ≫ projection R c L s)
    rw [infinity_projection]
    exact ContactResidueRegularFlat318.infinity_flat R c L s hs
end ContactGlobalResidueFlat318
