module
public import ContactUniversalRangeFlat318
public import ContactZeroParameterBaseChange318
public import ContactUniversalNonzeroFamily318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace ContactUniversalNonzeroFlat318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
universe u

/-- Transfer flatness between two actual Cartesian models of the same
base change, retaining the original second projection on each model. -/
lemma flat_same_pullback {Z Z' X Y B : Scheme.{u}}
    {a : Z ⟶ X} {b : Z ⟶ Y} {a' : Z' ⟶ X} {b' : Z' ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B}
    (h : IsPullback a b f g) (h' : IsPullback a' b' f g) [Flat b] : Flat b' := by
  have hc : Flat (h'.isoPullback.hom ≫ h.isoPullback.inv ≫ b) := inferInstance
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

/-- The actual universal zero family restricted to the EXISTING nonzero
parameter open is flat. Actual affine opens of that base supply their own
rational coefficient rings; actual image containment supplies all residue
nonvanishing. Original zero base-change squares then identify these flat
tests with the canonical pullbacks of the SAME restricted global family. -/
theorem flat : Flat πW := by
  let C := W.toScheme.affineOpenCover
  apply IsZariskiLocalAtTarget.of_openCover (P:=@Flat) C.openCover
  intro i
  let T := C.X i
  let j : Spec T ⟶ W.toScheme := C.f i
  let b : A ⟶ T := Spec.preimage (j ≫ W.ι)
  letI : Algebra ℚ T := (b.hom.comp (algebraMap ℚ A)).toAlgebra
  let g : A →ₐ[ℚ] T := ContactOriginalRelativeOverlap318.rationalMap (j ≫ W.ι)
  have hg : Spec.map (CommRingCat.ofHom g.toRingHom)=j ≫ W.ι :=
    ContactOriginalRelativeOverlap318.rationalMap_spec _
  have hmem : ∀ t : Spec T, Spec.map (CommRingCat.ofHom g.toRingHom) t∈W := by
    intro t
    rw [hg]
    exact (j t).property
  let N := ContactUniversalResidueNonzero318.line R c L T g
  let s := ContactUniversalResidueNonzero318.section R c L hz T g
  haveI : Flat (ContactGlobalResidueFlat318.projection T c N s) :=
    ContactUniversalRangeFlat318.global_flat R c L hz T g hmem
  have hS : IsPullback (ContactZeroCoefficientMap318.map A T g c U σ)
      (ContactGlobalResidueFlat318.projection T c N s) π (j ≫ W.ι) := by
    rw [← hg]
    exact ContactZeroParameterBaseChange318.square A T g c U σ
  have hT : IsPullback
      (pullback.fst πW j ≫ pullback.fst π W.ι)
      (pullback.snd πW j) π (j ≫ W.ι) :=
    (IsPullback.of_hasPullback πW j).paste_horiz (.of_hasPullback π W.ι)
  change Flat (pullback.snd πW j)
  exact flat_same_pullback hS hT

/-- The SAME nonzero universal zero projection is now proper, flat and
locally finitely presented. Finite degree and divisor-to-Picard
representability are further steps, not bundled assumptions. -/
theorem properties : IsProper πW ∧ Flat πW ∧ LocallyOfFinitePresentation πW :=
  ⟨inferInstance,flat R c L hz,inferInstance⟩
end ContactUniversalNonzeroFlat318
