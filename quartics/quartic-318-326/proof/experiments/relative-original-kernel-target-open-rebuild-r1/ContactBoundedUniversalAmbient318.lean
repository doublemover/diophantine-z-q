module
public import ContactBoundedHilbertParameter318
public section
noncomputable section
namespace ContactBoundedUniversalAmbient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactBoundedHilbertParameter318.structureMap c N
abbrev scheme := pullback p b
abbrev chart (d : Fin (N+1)) := ContactProjectiveUniversalAmbient318.scheme c d.val
abbrev into (d : Fin (N+1)) : chart c N d ⟶ scheme c N :=
  RelativeSchemeCoefficient318.map p b (ContactProjectiveParameterStructure318.structureMap c d.val)
    (ContactBoundedHilbertParameter318.into c N d) (ContactBoundedHilbertParameter318.into_structure c N d)
lemma cartesian (d : Fin (N+1)) : IsPullback (into c N d)
    (ContactProjectiveUniversalAmbient318.projection c d.val) (pullback.snd p b)
    (ContactBoundedHilbertParameter318.into c N d) := RelativeSchemeCoefficient318.cartesian _ _ _ _ _
instance open (d : Fin (N+1)) : IsOpenImmersion (into c N d) := inferInstance
/-- Full original ambient cover over all rank components. -/
@[expose] def cover : (scheme c N).OpenCover where
  I₀ := Fin (N+1)
  X := chart c N
  f := into c N
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun d => inferInstance⟩
    intro x
    obtain ⟨d,y,hy⟩ := ((ContactBoundedHilbertParameter318.cover c N).pullback₁ (pullback.snd p b)).exists_eq x
    let h := cartesian c N d
    refine ⟨d,h.isoPullback.inv y,?_⟩
    exact (congrArg (fun k : pullback (pullback.snd p b) (ContactBoundedHilbertParameter318.into c N d) ⟶ scheme c N => k y)
      h.isoPullback_inv_fst).trans hy
end ContactBoundedUniversalAmbient318
