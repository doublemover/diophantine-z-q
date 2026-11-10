module
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.Algebra.Module.FinitePresentation
public section
noncomputable section
namespace FaithfullyFlatFinitePresentation318
open TensorProduct
universe u v w
variable (R : Type u) (S : Type v) (M : Type w)
  [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module.FaithfullyFlat R S]
set_option maxHeartbeats 500000

/-- Finite presentation descends along the actual faithfully flat scalar
extension: a finite presentation is obtained by descending the finite
kernel of the base-changed original finite free surjection. -/
lemma descent [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  let : Module.Finite R M :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let g := AlgebraTensorModule.lTensor S S f
  have hg : Function.Surjective g := LinearMap.lTensor_surjective S hf
  let : Module.Finite S (LinearMap.ker g) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker g hg)
  let : Module.Finite S (S ⊗[R] LinearMap.ker f) :=
    Module.Finite.equiv (LinearMap.tensorKerEquiv S S f).symm
  let : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact Module.finitePresentation_of_free_of_surjective f hf
    (Module.Finite.iff_fg.mp inferInstance)
end FaithfullyFlatFinitePresentation318
