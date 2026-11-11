module
public import FiniteSurjectiveAlgebraicallyClosedPoints318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace FiniteComplexAlgebraPointLift318
open AlgebraicGeometry CategoryTheory
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- Every ordinary complex point lifts through an injective finite map
of WHOLE complex algebras, preserving the complete algebra evaluation.
No component, generic point, or source point is selected in advance. -/
theorem exists_lift (g : A →ₐ[ℂ] B) (hg : Function.Injective g) (hf : g.Finite)
    (e : A →ₐ[ℂ] ℂ) : ∃ f : B →ₐ[ℂ] ℂ, f.comp g = e := by
  let G := Spec.map (CommRingCat.ofHom g.toRingHom)
  letI : IsFinite G := (IsFinite.SpecMap_iff _).mpr hf
  letI : Surjective G := ⟨(RingHom.Finite.to_isIntegral hf).comap_surjective hg⟩
  obtain ⟨q,hq⟩ := FiniteSurjectiveAlgebraicallyClosedPoints318.exists_lift G
    (Spec.map (CommRingCat.ofHom e.toRingHom))
  obtain ⟨φ,rfl⟩ := Spec.map_surjective q
  have he : CommRingCat.ofHom g.toRingHom ≫ φ = CommRingCat.ofHom e.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact hq
  have hr : φ.hom.comp g.toRingHom = e.toRingHom := congrArg (fun f => f.hom) he
  let f : B →ₐ[ℂ] ℂ := { φ.hom with commutes' := by
    intro c
    have hc := congrArg (fun h : A →+* ℂ => h (algebraMap ℂ A c)) hr
    simpa only [RingHom.comp_apply,g.commutes,e.commutes] using hc }
  refine ⟨f,?_⟩
  ext a
  exact congrArg (fun h : A →+* ℂ => h a) hr
end FiniteComplexAlgebraPointLift318
