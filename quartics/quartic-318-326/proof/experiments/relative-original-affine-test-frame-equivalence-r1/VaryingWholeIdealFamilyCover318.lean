module
public import VaryingWholeIdealFamily318
public import AffineCoefficientCover318
public section
noncomputable section
namespace VaryingWholeIdealFamilyCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingWholeIdealFamily318
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
variable (I : Ideal (S ⊗[R] A)) (C : AffineCoefficientCover318.Data R S)
local notation "U" => AffineCoefficientCover318.cover R S C
abbrev chart (i : C.Index) := family R A (C.ring i) (extended R A S I (C.ring i) (C.coefficient i))
abbrev into (i : C.Index) : chart R A S I C i ⟶ family R A S I :=
  map R A S I (C.ring i) (C.coefficient i)
instance open_map (i : C.Index) : IsOpenImmersion (into R A S I C i) :=
  MorphismProperty.of_isPullback (cartesian R A S I (C.ring i) (C.coefficient i)).flip inferInstance
/-- The whole original quotient is covered by the actual extended
quotients, because the coefficient cover is complete and the squares
are genuine pullbacks. No finite or free quotient hypothesis occurs. -/
@[expose] def cover : (family R A S I).OpenCover where
  I₀ := C.Index
  X := chart R A S I C
  f := into R A S I C
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro x
    obtain ⟨i,y,hy⟩ := (U.pullback₁ (projection R A S I)).exists_eq x
    let h := cartesian R A S I (C.ring i) (C.coefficient i)
    refine ⟨i,h.isoPullback.inv y,?_⟩
    have he := congrArg (fun k : pullback (projection R A S I) (U.f i) ⟶ family R A S I => k y)
      h.isoPullback_inv_fst
    exact he.trans hy
end VaryingWholeIdealFamilyCover318
