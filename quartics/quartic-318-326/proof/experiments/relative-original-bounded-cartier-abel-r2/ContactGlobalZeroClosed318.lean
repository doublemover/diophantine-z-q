module
public import ContactGlobalZeroChartSquares318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace ContactGlobalZeroClosed318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactGlobalSectionZero318 ContactGlobalZeroChartSquares318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

@[expose] def chart (i : Fin 2) : Scheme :=
  Fin.cases (Spec (CommRingCat.of (R ⊗[ℚ] finiteRing c)))
    (fun _ => Spec (CommRingCat.of (R ⊗[ℚ] infinityRing c))) i
@[expose] def chartInto (i : Fin 2) : chart R c i ⟶ curve R c := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact finiteInto R c
  · exact infinityInto R c
instance (i : Fin 2) : IsOpenImmersion (chartInto R c i) := by
  fin_cases i <;> dsimp [chartInto] <;> infer_instance

@[expose] def originalCover : (curve R c).OpenCover where
  I₀ := Fin 2
  X := chart R c
  f := chartInto R c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro x
    have hx : x ∈ (finiteInto R c).opensRange ⊔ (infinityInto R c).opensRange := by
      rw [ContactOriginalRelativePolynomialCharts318.cover]
      trivial
    rcases hx with hf | hi
    · exact ⟨0,hf⟩
    · exact ⟨1,hi⟩

variable (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- The glued original section-zero map is actually a CLOSED IMMERSION.
Its entire inverse images over BOTH original affine charts are the quotient
closed immersions, by the preceding geometric pullback squares. -/
instance closed : IsClosedImmersion (ContactGlobalSectionZero318.into R c L s) := by
  apply IsZariskiLocalAtTarget.of_openCover (originalCover R c)
  intro i
  fin_cases i
  · have h := (finite_square R c L s).flip
    haveI : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hc : IsClosedImmersion (h.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s)))) := inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
  · have h := (infinity_square R c L s).flip
    haveI : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hc : IsClosedImmersion (h.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s)))) := inferInstance
    simpa only [h.isoPullback_inv_snd] using hc

/-- Canonical ideal sheaf of the actual glued zero closed subscheme. No
radical is taken; nilpotent multiplicities of the original zeros survive. -/
@[expose] def idealSheaf : (curve R c).IdealSheafData :=
  (ContactGlobalSectionZero318.into R c L s).ker

/-- The original glued zero scheme is the subscheme of this actual ideal
sheaf, by closed immersion, not by identifying only their underlying points. -/
@[expose] def subschemeIso : scheme R c L s ≅ (idealSheaf R c L s).subscheme :=
  asIso (ContactGlobalSectionZero318.into R c L s).toImage

@[reassoc] lemma subschemeIso_into : (subschemeIso R c L s).hom ≫
    (idealSheaf R c L s).subschemeι = ContactGlobalSectionZero318.into R c L s :=
  (ContactGlobalSectionZero318.into R c L s).toImage_imageι
end ContactGlobalZeroClosed318
