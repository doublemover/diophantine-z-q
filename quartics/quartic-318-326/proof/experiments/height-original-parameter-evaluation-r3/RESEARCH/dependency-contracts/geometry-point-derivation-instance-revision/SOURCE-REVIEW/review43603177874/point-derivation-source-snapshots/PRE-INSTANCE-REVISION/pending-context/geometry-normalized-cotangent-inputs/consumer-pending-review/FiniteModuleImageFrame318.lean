module
public import FiniteGeneratedPlaceFrame318
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace FiniteModuleImageFrame318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)
  (E : Type*) [AddCommGroup E] [Module (Integers w) E] [Module.Finite (Integers w) E]
  (ev : E →ₗ[Integers w] K)

/-- The embedded integral module is the actual evaluation image. No lattice,
rank-one frame, injectivity or image-finiteness assumption is supplied. -/
@[expose] def image : Submodule (Integers w) K := ev.range

theorem image_fg : (image w E ev).FG := Submodule.fg_range ev

theorem evaluated_mem (x : E) : ev x∈image w E ev := ⟨x,rfl⟩

/-- A single actual nonzero evaluated section rules out the zero image and
constructs its generator. Evaluation may have torsion or any other kernel. -/
@[expose] def generator (x : E) (hx : ev x≠0) : K :=
  FiniteGeneratedPlaceFrame318.generator w (image w E ev) (image_fg w E ev)
    (ev x) (evaluated_mem w E ev x) hx

theorem generator_ne (x : E) (hx : ev x≠0) : generator w E ev x hx≠0 :=
  FiniteGeneratedPlaceFrame318.generator_ne w _ _ _ _ _

theorem lattice_generator (x : E) (hx : ev x≠0) :
    lattice w (generator w E ev x hx)=image w E ev :=
  FiniteGeneratedPlaceFrame318.lattice_generator w _ _ _ _ _

@[expose] def frame (x : E) (hx : ev x≠0) : Integers w ≃ₗ[Integers w] image w E ev :=
  FiniteGeneratedPlaceFrame318.frame w (image w E ev) (image_fg w E ev)
    (ev x) (evaluated_mem w E ev x) hx
end FiniteModuleImageFrame318
