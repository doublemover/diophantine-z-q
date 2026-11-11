module
public import SchemeClosedCoverGluing318
public section
noncomputable section
namespace ContactProjectiveUniversalAmbient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactProjectiveParameterStructure318.structureMap c n
local notation "u" => ContactProjectiveQuotientParameter318.into c n
abbrev scheme := pullback p b
abbrev projection : scheme c n ⟶ ContactProjectiveQuotientParameter318.scheme c n := pullback.snd p b
abbrev chart (a : Chart) := ContactQuotientUniversalOriginal318.curve c a n
abbrev into (a : Chart) : chart c n a ⟶ scheme c n :=
  RelativeSchemeCoefficient318.map p b (ContactQuotientUniversalOriginal318.structureMap c a n) (u a)
    (ContactProjectiveParameterStructure318.into_structureMap c n a)
lemma cartesian (a : Chart) : IsPullback (into c n a)
    (pullback.snd p (ContactQuotientUniversalOriginal318.structureMap c a n)) (projection c n) (u a) :=
  RelativeSchemeCoefficient318.cartesian _ _ _ _ _
instance open (a : Chart) : IsOpenImmersion (into c n a) := inferInstance
/-- The entire original source product is covered by actual parameter
chart base changes, not by selected points or affine source pieces. -/
@[expose] def cover : (scheme c n).OpenCover where
  I₀ := Chart
  X := chart c n
  f := into c n
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun a => inferInstance⟩
    intro x
    obtain ⟨a,y,hy⟩ := ((ContactProjectiveQuotientParameter318.cover c n).pullback₁ (projection c n)).exists_eq x
    let h := cartesian c n a
    refine ⟨a,h.isoPullback.inv y,?_⟩
    exact (congrArg (fun k : pullback (projection c n) (u a) ⟶ scheme c n => k y) h.isoPullback_inv_fst).trans hy
abbrev localFamily (a : Chart) := ContactQuotientUniversalOriginal318.family c a n
abbrev localInto (a : Chart) : localFamily c n a ⟶ scheme c n :=
  ContactQuotientUniversalOriginal318.into c a n ≫ into c n a
instance local_mono (a : Chart) : Mono (localInto c n a) := by unfold localInto; infer_instance
end ContactProjectiveUniversalAmbient318
