module
public import OriginalR47TraitRoundKernel318
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public section
noncomputable section

namespace OriginalR47ProperBadSupport318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318 (base)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- An actual closed subset avoiding the generic point of the fixed
Dedekind base is finite, by finite minimal primes of its nonzero
vanishing ideal. No list of bad primes is supplied. -/
theorem finite_nongeneric (D : Set (base (R:=R))) (hD : IsClosed D)
    (hη : genericPoint (base (R:=R)) ∉ D) : D.Finite := by
  obtain ⟨I,hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal D).mp hD
  have hi : I ≠ ⊥ := by
    intro he
    apply hη
    rw [hI,he]
    change (⊥ : Ideal R) ≤ (genericPoint (base (R:=R))).asIdeal
    exact bot_le
  let q : base (R:=R) → Ideal R := PrimeSpectrum.asIdeal
  have hq : Set.InjOn q (q ⁻¹' I.minimalPrimes) := by
    intro a _ b _ he
    exact PrimeSpectrum.ext he
  apply ((I.finite_minimalPrimes_of_isNoetherianRing).preimage hq).subset
  intro x hx
  have hIx : I ≤ x.asIdeal := by
    have hx' : x ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [← hI]
      exact hx
    exact hx'
  let : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨J,hJ,hJx⟩ := Ideal.exists_minimalPrimes_le hIx
  have hJn : J ≠ ⊥ := by
    intro he
    apply hi
    exact bot_unique (he ▸ hJ.1.2)
  have hm : J.IsMaximal := hJ.1.1.isMaximal hJn
  have he := hm.eq_of_le x.isPrime.ne_top hJx
  change x.asIdeal ∈ I.minimalPrimes
  rw [← he]
  exact hJ

variable {X : Scheme.{u}} (s : X ⟶ base (R:=R)) [IsProper s]
variable (D : Set X) (hD : IsClosed D)
variable (hg : ∀ x ∈ D, s x ≠ genericPoint (base (R:=R)))

include hD hg in
theorem finite_image : (s '' D).Finite :=
  finite_nongeneric (s '' D) (s.isClosedMap D hD)
    (by rintro ⟨x,hx,hx'⟩; exact hg x hx hx')

include hD hg in
/-- The canonical relative bad locus is finite once each true closed
fibre has finitely many singular points: properness provides the
finite image, and the canonical fibre morphisms hit every point.
No incidence with a separate finite set is assumed. -/
theorem finite_support
    (H : ∀ t, ((s.fiberι t) ⁻¹' D).Finite) : D.Finite := by
  apply ((finite_image s D hD hg).biUnion
    (fun t _ => (H t).image (s.fiberι t))).subset
  intro x hx
  let t := s x
  have hxt : x ∈ Set.range (s.fiberι t) := by
    rw [s.range_fiberι]
    rfl
  obtain ⟨u,hu⟩ := hxt
  have huD : u ∈ (s.fiberι t) ⁻¹' D := by
    change s.fiberι t u ∈ D
    rw [hu]
    exact hx
  exact Set.mem_iUnion₂.mpr ⟨t,⟨x,hx,rfl⟩,u,huD,hu⟩

/-- The singular locus of a finite type field fibre is itself a finite
closed subset of a Jacobson space. Its points therefore are all closed,
not just closed in some independently chosen affine chart. -/
private theorem finite_closed_points {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    {D : Set T} (hD : IsClosed D) (hf : D.Finite) (x : T) (hx : x ∈ D) :
    IsClosed ({x} : Set T) := by
  have H : closure (D ∩ closedPoints T) = D := closure_inter_closedPoints hD
  have hp : (D ∩ closedPoints T).Finite := hf.subset Set.inter_subset_left
  have hc : IsClosed (D ∩ closedPoints T) := by
    rw [← (D ∩ closedPoints T).biUnion_of_singleton]
    exact hp.isClosed_biUnion fun _ hz => hz.2
  rw [hc.closure_eq] at H
  exact ((show x ∈ D ∩ closedPoints T from H.symm ▸ hx).2)

include hD hg in
theorem closed_points
    (H : ∀ t, ((s.fiberι t) ⁻¹' D).Finite) (x : X) (hx : x ∈ D) :
    IsClosed ({x} : Set X) := by
  let t := s x
  have ht0 : t.asIdeal ≠ ⊥ := by
    intro h
    apply hg x hx
    rw [show genericPoint (base (R:=R)) = (⊥ : PrimeSpectrum R)
      from genericPoint_eq_bot_of_affine _]
    exact PrimeSpectrum.ext h
  let : t.asIdeal.IsMaximal := t.isPrime.isMaximal ht0
  have ht : IsClosed ({t} : Set (base (R:=R))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal t).mpr inferInstance
  let : IsClosedImmersion ((base (R:=R)).fromSpecResidueField t) :=
    isClosed_singleton_iff_isClosedImmersion.mp ht
  let : IsClosedImmersion (s.fiberι t) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hxt : x ∈ Set.range (s.fiberι t) := by rw [s.range_fiberι]; rfl
  obtain ⟨u,hu⟩ := hxt
  have huD : u ∈ (s.fiberι t) ⁻¹' D := by
    change s.fiberι t u ∈ D
    rw [hu]
    exact hx
  have huc : IsClosed ({u} : Set (s.fiber t)) :=
    finite_closed_points (hD.preimage (s.fiberι t).continuous) (H t) u huD
  simpa only [Set.image_singleton,hu] using (s.fiberι t).isClosedMap {u} huc

end OriginalR47ProperBadSupport318

#print axioms OriginalR47ProperBadSupport318.finite_nongeneric
#print axioms OriginalR47ProperBadSupport318.finite_support
#print axioms OriginalR47ProperBadSupport318.closed_points
