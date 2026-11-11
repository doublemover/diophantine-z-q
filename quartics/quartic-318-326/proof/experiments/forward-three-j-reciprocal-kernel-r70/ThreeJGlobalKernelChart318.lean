module
public import ThreeJGlobalRamificationScheme318
public section
noncomputable section
namespace ThreeJGlobalKernelChart318
universe u
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJGlobalRamificationScheme318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The global closed immersion actually pulls back to its original
nonreduced finite-chart immersion. All source points lie in this chart. -/
theorem finite_pullback : IsPullback finiteInclusion (𝟙 Source)
    (JLineAtlas318.chart ℚ 1) embedding := by
  apply IsOpenImmersion.isPullback
  · simp only [Category.id_comp,embedding]
  · apply TopologicalSpace.Opens.ext
    ext x
    constructor
    · intro _
      exact ⟨x,rfl⟩
    · intro _
      exact ⟨finiteInclusion x,rfl⟩

/-- Formal restriction equality for the actual global kernel ideal sheaf,
not only equality of supports or a proposed chartwise gluing equation. -/
theorem finite_ideal_restriction :
    ideal.comap (JLineAtlas318.chart ℚ 1)=finiteInclusion.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion embedding finiteInclusion
    (𝟙 Source) (JLineAtlas318.chart ℚ 1) finite_pullback U).symm

/-- Kernel ideals in affine-scheme coordinates retain the exact original
ring homomorphism under the canonical global-section isomorphism. -/
theorem spec_kernel_coordinates {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    ((Spec.map (CommRingCat.ofHom f)).ker.ideal
      ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of A))⟩).comap
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.ker f := by
  rw [Scheme.Hom.ker_apply]
  ext a
  change (Spec.map (CommRingCat.ofHom f)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)=0 ↔ f a=0
  change (Spec.map (CommRingCat.ofHom f)).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)=0 ↔ f a=0
  have hn := congrArg (fun g : CommRingCat.of A ⟶ _ => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply] at hn
  rw [←hn]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1

/-- The global ramification kernel restricts to the full degree-six
principal ideal, including every nilpotent multiplicity at the finite cusp. -/
theorem finite_equation :
    ((ideal.comap (JLineAtlas318.chart ℚ 1)).ideal
      ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of ℚ[X]))⟩).comap
        (Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv.hom =
      Ideal.span {ThreeJRamificationIdealCharts318.finiteEquation} := by
  rw [finite_ideal_restriction]
  exact (spec_kernel_coordinates (AdjoinRoot.mk ThreeJRamificationIdealCharts318.finiteEquation)).trans
    finite_kernel
end ThreeJGlobalKernelChart318
