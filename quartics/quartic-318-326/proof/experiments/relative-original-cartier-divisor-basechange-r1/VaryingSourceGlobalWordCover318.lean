module
public import VaryingSourceSurjectiveCoefficient318
public import VaryingSourceLocalWordCover318
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section
namespace VaryingSourceGlobalWordCover318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open VaryingSourceSurjectiveCoefficient318 VaryingMatrixWords318
open CyclicQuotientEvaluation318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Action R A ι S)

/-- All literal source-word determinants generate the unit ideal for a
cyclic action over ANY coefficient ring. Maximal-ideal reduction is used
only to detect a proper ideal, never to replace the scheme-theoretic data. -/
lemma determinants_span_top
    (h : Function.Surjective (evaluation (linearAction R A ι S a) a.marked)) :
    Ideal.span (Set.range (determinant (point R A ι S a).val))=⊤ := by
  classical
  by_contra hn
  obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal
    (Ideal.span (Set.range (determinant (point R A ι S a).val))) hn
  letI : m.IsMaximal := hm
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let f : S →ₐ[R] S ⧸ m := Ideal.Quotient.mkₐ R m
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have ht := cyclic_of_surjective R A ι S (S ⧸ m) f a hf h
  obtain ⟨w,hw⟩ := VaryingSourceLocalWordCover318.exists_word_chart
    R A ι (S ⧸ m) (mapAction R A ι S (S ⧸ m) f a) ht
  have hz : f (determinant (point R A ι S a).val w)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_range_self w)))
  rw [VaryingSourceSurjectiveCoefficient318.determinant_map] at hz
  exact hw.ne_zero hz

/-- The principal word-determinant opens cover the whole coefficient
spectrum, retaining arbitrary nonreduced coefficient rings. This is the
framed cyclic-action cover, not a frame quotient or glued Picard scheme. -/
lemma basic_open_cover
    (h : Function.Surjective (evaluation (linearAction R A ι S a) a.marked)) :
    (⨆ w : ι → List A, PrimeSpectrum.basicOpen
      (determinant (point R A ι S a).val w))=⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (determinants_span_top R A ι S a h)
end VaryingSourceGlobalWordCover318
