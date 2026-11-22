module

public import SelectedSameAModuleSplitExplicit318
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! Use smoothness and the stock Jacobi–Zariski sequence on the actual old
rings. This removes a separate derivation-lifting dependency. -/

public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace SelectedSameASmoothTransitivitySplit318

universe u

variable (k T C : Type u) [CommRing k] [CommRing T] [CommRing C]
  [Algebra k T] [Algebra k C] [Algebra T C] [IsScalarTower k T C]

abbrev leftModule := C ⊗[T] KaehlerDifferential k T

abbrev jacobian := KaehlerDifferential.mapBaseChange k T C

abbrev relativeProjection := KaehlerDifferential.map k T C C

theorem jacobian_injective [Algebra.FormallySmooth T C] :
    Function.Injective (jacobian k T C) := by
  have hz (x : leftModule k T C) (h : jacobian k T C x = 0) : x = 0 := by
    obtain ⟨z, hz⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k T C x).mp h
    have he : z = 0 := Subsingleton.elim _ _
    rw [he, map_zero] at hz
    exact hz.symm
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

/-- The corrected identity on the actual middle lands in the actual left
range. Invert the actual first map on that range and obtain a retraction. -/
theorem retraction_of_formally_smooth [Algebra.FormallySmooth T C] :
    ∃ r : KaehlerDifferential k C →ₗ[C] leftModule k T C,
      Function.LeftInverse r (jacobian k T C) := by
  let f := jacobian k T C
  let g := relativeProjection k T C
  have hf : Function.Injective f := jacobian_injective k T C
  have he : Function.Exact f g := KaehlerDifferential.exact_mapBaseChange_map k T C
  have hs : Function.Surjective g := KaehlerDifferential.map_surjective k T C
  obtain ⟨s, hsg⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  have hg (x : KaehlerDifferential T C) : g (s x) = x := DFunLike.congr_fun hsg x
  let a : KaehlerDifferential k C →ₗ[C] KaehlerDifferential k C := LinearMap.id - s.comp g
  have ha (m : KaehlerDifferential k C) : a m ∈ LinearMap.range f := by
    apply LinearMap.mem_range.mpr
    apply (he (a m)).mp
    change g (m - s (g m)) = 0
    rw [map_sub, hg, sub_self]
  let r := LinearMap.codRestrictOfInjective a f hf ha
  refine ⟨r, ?_⟩
  intro x
  have hfg : g (f x) = 0 := (he (f x)).mpr ⟨x, rfl⟩
  apply hf
  have hr := LinearMap.codRestrictOfInjective_comp_apply a f hf ha (f x)
  change f (r (f x)) = a (f x) at hr
  refine hr.trans ?_
  change f x - s (g (f x)) = f x
  rw [hfg, map_zero, sub_zero]

/-- Same original arrows and proof-independent row used by the old
actual-fibre split owner. No new coordinates or body choices in the row. -/
def smoothTransitivityRow : ShortComplex (ModuleCat.{u} C) :=
  SelectedSameAModuleSplitExplicit318.row (jacobian k T C) (relativeProjection k T C)
    (KaehlerDifferential.exact_mapBaseChange_map k T C)

theorem split_before_reduction [Algebra.FormallySmooth T C] :
    Nonempty ((smoothTransitivityRow k T C).Splitting) := by
  obtain ⟨r, hr⟩ := retraction_of_formally_smooth k T C
  exact ⟨SelectedSameAModuleSplitExplicit318.splitting
    (jacobian k T C) (relativeProjection k T C)
    (KaehlerDifferential.exact_mapBaseChange_map k T C) r hr
    (KaehlerDifferential.map_surjective k T C)⟩

end SelectedSameASmoothTransitivitySplit318
