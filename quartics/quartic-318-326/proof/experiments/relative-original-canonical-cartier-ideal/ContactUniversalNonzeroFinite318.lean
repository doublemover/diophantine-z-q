module
public import ContactUniversalFieldFinite318
public import ContactZeroParameterBaseChange318
public import ContactUniversalNonzeroFlat318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace ContactUniversalNonzeroFinite318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
universe u

/-- Transfer finiteness between two actual Cartesian models of the same
base change, retaining the original second projection on each model. -/
lemma finite_same_pullback {Z Z' X Y B : Scheme.{u}}
    {a : Z ⟶ X} {b : Z ⟶ Y} {a' : Z' ⟶ X} {b' : Z' ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B}
    (h : IsPullback a b f g) (h' : IsPullback a' b' f g) [IsFinite b] : IsFinite b' := by
  have hc : IsFinite (h'.isoPullback.hom ≫ h.isoPullback.inv ≫ b) := inferInstance
  simpa only [h.isoPullback_inv_snd,h'.isoPullback_hom_snd] using hc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
local notation "U" => universalLine R c L
local notation "σ" => universalSection R c L hz
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "πW" => ContactUniversalNonzeroFamily318.projection R c L hz

/-- The literal residue-field fiber of the EXISTING nonzero universal
zero projection is finite over that same residue field. Its comparison
with an actual coefficient test is Cartesian, not merely a point bijection. -/
lemma fiber_finite (y : W.toScheme) : IsFinite (πW.fiberToSpecResidueField y) := by
  let K := W.toScheme.residueField y
  let j : Spec K ⟶ W.toScheme := W.toScheme.fromSpecResidueField y
  let b : A ⟶ K := Spec.preimage (j ≫ W.ι)
  letI : Algebra ℚ K := (b.hom.comp (algebraMap ℚ A)).toAlgebra
  let g : A →ₐ[ℚ] K := ContactOriginalRelativeOverlap318.rationalMap (j ≫ W.ι)
  have hg : Spec.map (CommRingCat.ofHom g.toRingHom)=j ≫ W.ι :=
    ContactOriginalRelativeOverlap318.rationalMap_spec _
  have hmem : ∀ t : Spec K, Spec.map (CommRingCat.ofHom g.toRingHom) t∈W := by
    intro t
    rw [hg]
    exact (j t).property
  let N := ContactUniversalResidueNonzero318.line R c L K g
  let s := ContactUniversalResidueNonzero318.section R c L hz K g
  haveI : IsFinite (ContactGlobalResidueFlat318.projection K c N s) :=
    ContactUniversalFieldFinite318.finite R c L hz K g hmem
  have hS : IsPullback (ContactZeroCoefficientMap318.map A K g c U σ)
      (ContactGlobalResidueFlat318.projection K c N s) π (j ≫ W.ι) := by
    rw [← hg]
    exact ContactZeroParameterBaseChange318.square A K g c U σ
  have hT : IsPullback
      (pullback.fst πW j ≫ pullback.fst π W.ι)
      (pullback.snd πW j) π (j ≫ W.ι) :=
    (IsPullback.of_hasPullback πW j).paste_horiz (.of_hasPullback π W.ι)
  change IsFinite (pullback.snd πW j)
  exact finite_same_pullback hS hT

/-- Actual finite residue fibers give local quasi-finiteness; properness
of the SAME existing family then gives finiteness. No fiber finiteness or
zero degree is supplied as an external geometric premise. -/
theorem finite : IsFinite πW := by
  haveI : LocallyQuasiFinite πW :=
    LocallyQuasiFinite.of_fiberToSpecResidueField (f:=πW) (fun y => by
      letI := fiber_finite R c L hz y
      infer_instance)
  exact IsFinite.of_isProper_of_locallyQuasiFinite πW

/-- The existing nonzero universal section-zero family is finite, flat,
and locally finitely presented. Its degree/rank and the represented Picard
comparison are not replaced by this finite-flat conclusion. -/
theorem properties : IsFinite πW ∧ Flat πW ∧ LocallyOfFinitePresentation πW :=
  ⟨finite R c L hz,ContactUniversalNonzeroFlat318.flat R c L hz,inferInstance⟩
end ContactUniversalNonzeroFinite318
