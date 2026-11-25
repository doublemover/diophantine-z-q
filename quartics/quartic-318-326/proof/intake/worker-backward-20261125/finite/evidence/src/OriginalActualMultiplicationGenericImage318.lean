module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section
noncomputable section

namespace OriginalActualMultiplicationGenericImage318

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

def stalkGeneric (x : X) : Spec (X.presheaf.stalk x) :=
  (⊥ : PrimeSpectrum (X.presheaf.stalk x))

lemma identity_stalk_generic_value (x : X) :
    X.fromSpecStalk x (stalkGeneric x)=genericPoint X := by
  have h : genericPoint X∈Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨y,hy⟩ := h
  have sp : stalkGeneric x ⤳ y :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have forward : X.fromSpecStalk x (stalkGeneric x) ⤳ genericPoint X :=
    hy ▸ sp.map (X.fromSpecStalk x).continuous
  exact (forward.antisymm (genericPoint_specializes _)).eq

variable (f : X ⟶ Y) (x : X)
variable (h : Function.Injective (f.stalkMap x).hom)

include h in
lemma actual_generic_stalk_map :
    Spec.map (f.stalkMap x) (stalkGeneric x)=stalkGeneric (f x) := by
  apply PrimeSpectrum.ext
  ext z
  change z∈Ideal.comap (f.stalkMap x).hom ⊥ ↔ z∈(⊥ : Ideal (Y.presheaf.stalk (f x)))
  rw [Ideal.mem_comap,Submodule.mem_bot,Submodule.mem_bot]
  exact ⟨fun e => h (e.trans (map_zero _).symm),fun e => e.symm ▸ map_zero _⟩

include h in
/-- Injectivity of the actual origin stalk map suffices for dominance
of the installed multiplication, with no generic smooth locus API. -/
theorem actual_dominant_from_origin_stalk : IsDominant f := by
  have e := congrArg (fun p : Spec (X.presheaf.stalk x) ⟶ Y => p (stalkGeneric x))
    (Scheme.SpecMap_stalkMap_fromSpecStalk f (x:=x))
  rw [Scheme.Hom.comp_apply,Scheme.Hom.comp_apply,actual_generic_stalk_map f x h,
    identity_stalk_generic_value,identity_stalk_generic_value] at e
  have hs : ({genericPoint Y} : Set Y) ⊆ Set.range f := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    exact ⟨genericPoint X,e.symm.trans hz.symm⟩
  have hc := closure_mono hs
  rw [genericPoint_closure] at hc
  exact ⟨fun z => hc (Set.mem_univ z)⟩

include h in
/-- Properness is relative properness on the true projective abelian
scheme. Scheme surjectivity here is separate from rational-point lifting. -/
theorem actual_scheme_surjective [IsProper f] : Surjective f := by
  letI := actual_dominant_from_origin_stalk f x h
  infer_instance

end OriginalActualMultiplicationGenericImage318
