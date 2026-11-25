module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Stalk

public section
noncomputable section
namespace OriginalUpperActualFibreComponents318

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Z : Scheme.{u}} (s : X ⟶ Z) (p : Z)

/-- Exactly the same vertices as the literal reduced-fibre graph. -/
abbrev C := ↥(irreducibleComponents (s.fiber p))

def fibreSupport (E : C s p) : Closeds (s.fiber p) :=
  ⟨E, isClosed_of_mem_irreducibleComponents _ E.property⟩

def fibreIdeal (E : C s p) : (s.fiber p).IdealSheafData :=
  vanishingIdeal (fibreSupport s p E)

/-- The reduced induced scheme structure on the actual component,
not the ambient fibre or a geometrically split replacement. -/
abbrev curve (E : C s p) : Scheme := (fibreIdeal s p E).subscheme

abbrev fibreInclusion (E : C s p) : curve s p E ⟶ s.fiber p :=
  (fibreIdeal s p E).subschemeι

/-- Structure on the true residue field of the named base point. -/
abbrev overResidue (E : C s p) : curve s p E ⟶ Spec (Z.residueField p) :=
  fibreInclusion s p E ≫ s.fiberToSpecResidueField p

abbrev ι (E : C s p) : curve s p E ⟶ X :=
  fibreInclusion s p E ≫ s.fiberι p

abbrev fibreGeneric (E : C s p) : s.fiber p := (genericPoints.ofComponent E).1
abbrev ambientGeneric (E : C s p) : X := s.fiberι p (fibreGeneric s p E)

def ambientSupport (E : C s p) : Closeds X :=
  .closure {ambientGeneric s p E}

def ambientIdeal (E : C s p) : X.IdealSheafData :=
  vanishingIdeal (ambientSupport s p E)

theorem fibre_closed_embedding (closed : IsClosed ({p} : Set Z)) :
    IsClosedImmersion (s.fiberι p) :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [s.range_fiberι p]
    exact closed.preimage s.continuous)

theorem component_closed_embedding (closed : IsClosed ({p} : Set Z)) (E : C s p) :
    IsClosedImmersion (ι s p E) := by
  letI := fibre_closed_embedding s p closed
  infer_instance

theorem image_in_closure (E : C s p) :
    (s.fiberι p '' (E : Set (s.fiber p))) ⊆ (ambientSupport s p E : Set X) := by
  rintro _ ⟨x,hx,rfl⟩
  exact (((genericPoints.isGenericPoint_ofComponent E).specializes hx).map
    (s.fiberι p).continuous).mem_closure

/-- Because the fibre is an actual closed immersion, the ambient
closure of its component's generic point has exactly the points of E. -/
theorem support_image (closed : IsClosed ({p} : Set Z)) (E : C s p) :
    (ambientSupport s p E : Set X) = s.fiberι p '' (E : Set (s.fiber p)) := by
  letI := fibre_closed_embedding s p closed
  refine le_antisymm (closure_minimal ?_ ?_) (image_in_closure s p E)
  · exact Set.singleton_subset_iff.mpr ⟨fibreGeneric s p E,
      (genericPoints.isGenericPoint_ofComponent E).mem,rfl⟩
  · exact (s.fiberι p).isClosedEmbedding.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ E.property)

/-- The actual embedded reduced curve's ideal is not a different
Cartier parameter: it is literally the ambient vanishing ideal of
the true generic component. -/
theorem embedded_ker (E : C s p) : (ι s p E).ker = ambientIdeal s p E := by
  rw [Scheme.Hom.ker_comp]
  change (fibreInclusion s p E).ker.map (s.fiberι p) = _
  rw [ker_subschemeι, fibreIdeal, map_vanishingIdeal]
  congr 1
  apply SetLike.coe_injective
  apply le_antisymm
  · exact closure_minimal (image_in_closure s p E) (ambientSupport s p E).isClosed
  · exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨fibreGeneric s p E,(genericPoints.isGenericPoint_ofComponent E).mem,rfl⟩)

theorem on_affine_radical (E : C s p) (U : X.affineOpens) :
    ((ambientIdeal s p E).ideal U).IsRadical := by
  rw [ambientIdeal, vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- On any actual affine containing the component generic point, the
ideal of this embedded curve is exactly that point's prime ideal. -/
theorem on_affine (E : C s p) (U : X.affineOpens) (v : Spec Γ(X,U))
    (hv : U.2.fromSpec v = ambientGeneric s p E) :
    (ambientIdeal s p E).ideal U = v.asIdeal := by
  rw [ambientIdeal,vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (closure {ambientGeneric s p E})) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      U.2.fromSpec.continuous ({ambientGeneric s p E} : Set X),
      PrimeSpectrum.vanishingIdeal_closure]
  have H : U.2.fromSpec ⁻¹' {ambientGeneric s p E} = {v} := by
    ext t
    simp only [Set.mem_preimage,Set.mem_singleton_iff,←hv,
      U.2.fromSpec.isOpenEmbedding.injective.eq_iff]
  rw [H,PrimeSpectrum.vanishingIdeal_singleton]

/-- The genuine point of Spec O_{X,x} over the named generic point.
No arbitrary regular parameters or completed valuation enter. -/
def pointAt (E : C s p) (x : X) (hx : x ∈ ambientSupport s p E) : Spec (X.presheaf.stalk x) :=
  have H : ambientGeneric s p E ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact specializes_iff_mem_closure.mpr hx
  H.choose

theorem pointAt_reads (E : C s p) (x : X) (hx : x ∈ ambientSupport s p E) :
    X.fromSpecStalk x (pointAt s p E x hx) = ambientGeneric s p E :=
  (show ambientGeneric s p E ∈ Set.range (X.fromSpecStalk x) from by
    rw [Scheme.range_fromSpecStalk]
    exact specializes_iff_mem_closure.mpr hx).choose_spec

/-- The ordinary (uncompleted) image ideal under the actual germ.
This makes the local intersection quotient independent of the chart. -/
theorem idealAt_from_affine (E : C s p) (U : X.affineOpens) (x : X)
    (hxU : x ∈ U.1) (hxE : x ∈ ambientSupport s p E) :
    ((ambientIdeal s p E).ideal U).map (X.presheaf.germ U.1 x hxU).hom =
      (pointAt s p E x hxE).asIdeal := by
  let v := pointAt s p E x hxE
  let g := X.presheaf.germ U.1 x hxU
  let u := Spec.map g v
  have hu : U.2.fromSpec u = ambientGeneric s p E := by
    calc
      _ = U.2.fromSpecStalk hxU v := (Scheme.Hom.comp_apply _ _ _).symm
      _ = X.fromSpecStalk x v :=
        congrArg (fun f : Spec (X.presheaf.stalk x) ⟶ X => f v)
          (U.2.fromSpecStalk_eq_fromSpecStalk hxU)
      _ = _ := pointAt_reads s p E x hxE
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,hxU⟩ : U.1)
  letI := U.2.isLocalization_stalk (⟨x,hxU⟩ : U.1)
  rw [on_affine s p E U u hu]
  exact IsLocalization.map_under (U.2.primeIdealOf ⟨x,hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) v.asIdeal

end OriginalUpperActualFibreComponents318

#print axioms OriginalUpperActualFibreComponents318.support_image
#print axioms OriginalUpperActualFibreComponents318.embedded_ker
#print axioms OriginalUpperActualFibreComponents318.on_affine
#print axioms OriginalUpperActualFibreComponents318.idealAt_from_affine
