module
public import FiniteOrderConductorTraceDual318
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace FiniteFrameConductorDenominator318
open Module
variable {R F A B ι : Type*} [CommRing R] [CommRing F] [CommRing A] [CommRing B]
  [Algebra R F] [Algebra R A] [Algebra F B] [Algebra R B] [IsScalarTower R F B]
  [Fintype ι] [DecidableEq ι] (S : Submonoid R) [IsLocalization S F]
  (e : A →ₐ[R] B) (a : Basis ι R A) (b : Basis ι F B)
  (hb : ∀ i,e (a i)=b i) (N : Subalgebra R B) [Module.Finite R N]

include hb in
/-- Clear the actual coefficients of finitely many generators of the
entire normal order in the SAME marked original basis. One genuine
localization denominator therefore lies in the actual conductor. -/
theorem exists_denominator : ∃ r : S,algebraMap R B r ∈
    FiniteOrderConductorTraceDual318.conductor e N := by
  classical
  obtain ⟨s,hs⟩ := (Submodule.FG.of_finite : N.toSubmodule.FG)
  obtain ⟨r,hr⟩ := IsLocalization.exist_integer_multiples_of_finite S
    (fun ji : s × ι => b.repr ji.1.val ji.2)
  have hgen (x : s) : ∃ y : A,e y=(r:R) • x.val := by
    have hx (i : ι) : ∃ u : R,algebraMap R F u=(r:R) • b.repr x.val i := hr (x,i)
    choose u hu using hx
    refine ⟨∑ i,u i • a i,?_⟩
    rw [map_sum]
    simp only [map_smul,hb]
    calc
      ∑ i,u i • b i = ∑ i,(r:R) • (b.repr x.val i • b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [←IsScalarTower.algebraMap_smul R F B,hu]
        exact smul_assoc (r:R) (b.repr x.val i) (b i)
      _ = (r:R) • x.val := by rw [←Finset.smul_sum,b.sum_repr]
  have hn : N.toSubmodule ≤
      (FiniteOrderConductorTraceDual318.orderImage e).comap
        ((r:R) • (LinearMap.id : B →ₗ[R] B)) := by
    rw [←hs]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨y,hy⟩ := hgen ⟨x,hx⟩
    exact ⟨y,hy⟩
  refine ⟨r,?_⟩
  rw [FiniteOrderConductorTraceDual318.mem_conductor]
  intro n
  obtain ⟨y,hy⟩ := hn n.property
  refine ⟨y,?_⟩
  simpa only [LinearMap.smul_apply,LinearMap.id_apply,Algebra.smul_def] using hy
end FiniteFrameConductorDenominator318
