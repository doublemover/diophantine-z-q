module
public import VaryingCyclicPointNaturality318
public section
noncomputable section
namespace VaryingCyclicCoefficientComposition318
open VaryingSourceFreeQuotientClassifier318 VaryingCyclicCoefficientSections318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (S : Type u) [CommRing S] [Algebra R S]
lemma cyclic_ext {a b : Cyclic R A ι S} (hm : a.data.map=b.data.map) (hv : a.data.marked=b.data.marked) : a=b := by
  cases a with | mk a ha =>
    cases b with | mk b hb =>
      cases a
      cases b
      cases hm
      cases hv
      rfl
lemma map_id (a : Cyclic R A ι S) : mapCyclic R A ι S a S (AlgHom.id R S)=a := by
  apply cyclic_ext R A ι S
  · apply AlgHom.ext
    intro x
    ext i j
    rfl
  · rfl
variable (T U : Type u) [CommRing T] [Algebra R T] [CommRing U] [Algebra R U]
lemma map_comp (a : Cyclic R A ι S) (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    mapCyclic R A ι T (mapCyclic R A ι S a T f) U g=mapCyclic R A ι S a U (g.comp f) := by
  apply cyclic_ext R A ι U
  · apply AlgHom.ext
    intro x
    ext i j
    rfl
  · rfl
end VaryingCyclicCoefficientComposition318
