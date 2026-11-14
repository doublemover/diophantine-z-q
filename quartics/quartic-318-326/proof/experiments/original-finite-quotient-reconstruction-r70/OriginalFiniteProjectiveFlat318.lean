module
public import OriginalFiberPointReconstruction318
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace OriginalFiniteProjectiveFlat318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A dominant affine morphism from an integral scheme to the actual
polynomial affine line is flat: its original ring map is injective, hence
its original domain module is torsion-free over the polynomial PID. -/
theorem affine_flat {X : Scheme} [IsIntegral X] [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of (Polynomial ℚ))) [IsDominant f] : Flat f := by
  let φ := (Scheme.Spec.preimage (X.isoSpec.inv ≫ f)).unop
  have he : Spec.map φ = X.isoSpec.inv ≫ f := Scheme.Spec.map_preimage _
  letI : IsDominant (Spec.map φ) := by rw [he]; infer_instance
  have hi : Function.Injective φ.hom := by
    have hd : DenseRange (PrimeSpectrum.comap φ.hom) := (Spec.map φ).denseRange
    have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).mp hd
    intro a b hab
    have hm : a-b ∈ RingHom.ker φ.hom := by
      change φ.hom (a-b) = 0
      rw [map_sub, hab, sub_self]
    have hn : IsNilpotent (a-b) := hk hm
    exact sub_eq_zero.mp hn.eq_zero
  letI : Algebra (Polynomial ℚ) Γ(X,⊤) := φ.hom.toAlgebra
  letI : FaithfulSMul (Polynomial ℚ) Γ(X,⊤) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  have hf : Flat (Spec.map φ) := by
    apply Flat.SpecMap_iff.mpr
    change RingHom.Flat (algebraMap (Polynomial ℚ) Γ(X,⊤))
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  apply (MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv f).mp
  exact he ▸ hf

/-- Flatness of the SAME finite dominant quotient is proved on both
entire original polynomial projective charts. It is no longer a premise
in the geometric fiber-to-reconstruction interface. -/
theorem flat {Y : Scheme} [IsIntegral Y]
    (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite p] [IsDominant p] : Flat p := by
  letI : Surjective p :=
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  let C : (ProjectiveJLine318.scheme ℚ).OpenCover := {
    I₀ := Fin 2
    X := fun _ => Spec (CommRingCat.of (Polynomial ℚ))
    f := JLineAtlas318.chart ℚ
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, inferInstance⟩
      intro x
      have hx : x ∈ (⊤ : (ProjectiveJLine318.scheme ℚ).Opens) := trivial
      rw [← JLineAtlas318.standard_opens_cover ℚ, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨j, hj⟩ := hx
      rw [← JLineAtlas318.chart_range] at hj
      obtain ⟨q, hq⟩ := hj
      exact ⟨j, q, hq⟩ }
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) C]
  intro i
  change Flat (pullback.snd p (JLineAtlas318.chart ℚ i))
  let T := pullback p (JLineAtlas318.chart ℚ i)
  let j : T ⟶ Y := pullback.fst p (JLineAtlas318.chart ℚ i)
  let q : T ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
    pullback.snd p (JLineAtlas318.chart ℚ i)
  letI : IsAffine T := isAffine_of_isAffineHom q
  letI : Nonempty T := by
    obtain ⟨x, _⟩ := q.surjective (genericPoint (Spec (CommRingCat.of (Polynomial ℚ))))
    exact ⟨x⟩
  letI : IsIntegral T := isIntegral_of_isOpenImmersion j
  exact affine_flat q
end OriginalFiniteProjectiveFlat318
