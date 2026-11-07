module
public import WeierstrassCoefficientMap318
public import CubicChartGeometry318
import all WeierstrassGluing318
public section
noncomputable section
namespace WeierstrassBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassCoefficientMap318
open scoped TensorProduct
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S

lemma infinity_preimage_finite {T : Type u} [CommRing T] (A B:T) :
    WeierstrassGluing318.infinityChart A B ⁻¹ᵁ (WeierstrassGluing318.finiteChart A B).opensRange=
      PrimeSpectrum.basicOpen (InfinityChart318.z A B) := by
  rw [←CubicChartGeometry318.embedding_preimage_Z,←Scheme.Hom.comp_preimage,
    CubicProjectiveMap318.infinity_embedding,
    CubicChartGeometry318.infinityMap_preimage _ _ _ (MvPolynomial.isHomogeneous_X T 2) (by omega)]
  simp [CubicChartGeometry318.infinityCoordinates]
lemma finite_preimage_infinity {T : Type u} [CommRing T] (A B:T) :
    WeierstrassGluing318.finiteChart A B ⁻¹ᵁ (WeierstrassGluing318.infinityChart A B).opensRange=
      PrimeSpectrum.basicOpen (ShortAffineJacobian318.y A B) := by
  rw [←CubicChartGeometry318.embedding_preimage_Y,←Scheme.Hom.comp_preimage,
    CubicProjectiveMap318.finite_embedding,
    CubicChartGeometry318.finiteMap_preimage _ _ _ (MvPolynomial.isHomogeneous_X T 1) (by omega)]
  simp [CubicChartGeometry318.finiteCoordinates]

lemma coefficient_preimage_finite (A B:R) : coefficientMap (S:=S) A B ⁻¹ᵁ
    (WeierstrassGluing318.finiteChart A B).opensRange=
      (WeierstrassGluing318.finiteChart (a A) (a B)).opensRange := by
  ext p
  rcases WeierstrassGluing318.charts_cover (a A) (a B) p with ⟨p,rfl⟩ | ⟨p,rfl⟩
  · constructor
    · intro _; exact ⟨p,rfl⟩
    · intro _
      refine ⟨finiteMap A B p,?_⟩
      change WeierstrassGluing318.finiteChart A B (finiteMap A B p)=
        coefficientMap A B (WeierstrassGluing318.finiteChart (a A) (a B) p)
      rw [←Scheme.Hom.comp_apply,←Scheme.Hom.comp_apply,finite_coefficientMap]
  · change p ∈ WeierstrassGluing318.infinityChart (a A) (a B) ⁻¹ᵁ
      (coefficientMap A B ⁻¹ᵁ (WeierstrassGluing318.finiteChart A B).opensRange) ↔
        p ∈ WeierstrassGluing318.infinityChart (a A) (a B) ⁻¹ᵁ
          (WeierstrassGluing318.finiteChart (a A) (a B)).opensRange
    rw [←Scheme.Hom.comp_preimage,infinity_coefficientMap,Scheme.Hom.comp_preimage,
      infinity_preimage_finite,infinity_preimage_finite]
    unfold infinityMap
    rw [SpecMap_preimage_basicOpen]
    change p ∈ PrimeSpectrum.basicOpen (InfinityBaseChange318.coefficientMap A B (InfinityChart318.z A B)) ↔ _
    rw [InfinityBaseChange318.coefficientMap_z]

lemma coefficient_preimage_infinity (A B:R) : coefficientMap (S:=S) A B ⁻¹ᵁ
    (WeierstrassGluing318.infinityChart A B).opensRange=
      (WeierstrassGluing318.infinityChart (a A) (a B)).opensRange := by
  ext p
  rcases WeierstrassGluing318.charts_cover (a A) (a B) p with ⟨p,rfl⟩ | ⟨p,rfl⟩
  · change p ∈ WeierstrassGluing318.finiteChart (a A) (a B) ⁻¹ᵁ
      (coefficientMap A B ⁻¹ᵁ (WeierstrassGluing318.infinityChart A B).opensRange) ↔
        p ∈ WeierstrassGluing318.finiteChart (a A) (a B) ⁻¹ᵁ
          (WeierstrassGluing318.infinityChart (a A) (a B)).opensRange
    rw [←Scheme.Hom.comp_preimage,finite_coefficientMap,Scheme.Hom.comp_preimage,
      finite_preimage_infinity,finite_preimage_infinity]
    unfold finiteMap
    rw [SpecMap_preimage_basicOpen]
    change p ∈ PrimeSpectrum.basicOpen (AffineBaseChange318.coefficientMap A B (ShortAffineJacobian318.y A B)) ↔ _
    rw [AffineBaseChange318.coefficientMap_y]
  · constructor
    · intro _; exact ⟨p,rfl⟩
    · intro _
      refine ⟨infinityMap A B p,?_⟩
      change WeierstrassGluing318.infinityChart A B (infinityMap A B p)=
        coefficientMap A B (WeierstrassGluing318.infinityChart (a A) (a B) p)
      rw [←Scheme.Hom.comp_apply,←Scheme.Hom.comp_apply,infinity_coefficientMap]

/-- The coefficient map has precisely the actual finite-chart base-change square. -/
theorem finite_chart_pullback (A B:R) : IsPullback (finiteMap (S:=S) A B)
    (WeierstrassGluing318.finiteChart (a A) (a B)) (WeierstrassGluing318.finiteChart A B)
      (coefficientMap A B) :=
  IsOpenImmersion.isPullback _ _ _ _ (finite_coefficientMap A B) (coefficient_preimage_finite A B)
theorem infinity_chart_pullback (A B:R) : IsPullback (infinityMap (S:=S) A B)
    (WeierstrassGluing318.infinityChart (a A) (a B)) (WeierstrassGluing318.infinityChart A B)
      (coefficientMap A B) :=
  IsOpenImmersion.isPullback _ _ _ _ (infinity_coefficientMap A B) (coefficient_preimage_infinity A B)

lemma finite_iso_inv_curve (A B:R) : (AffineSchemeBaseChange318.schemeIso (S:=S) A B).inv ≫ pullback.snd _ _=
    finiteMap (S:=S) A B := by
  have he : (AffineBaseChange318.forward (S:=S) A B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : ShortAffineJacobian318.Ring A B →ₐ[R]
        S ⊗[R] ShortAffineJacobian318.Ring A B).toRingHom=
      (AffineBaseChange318.coefficientMap (S:=S) A B).toRingHom := by
    apply RingHom.ext
    intro x
    exact AffineBaseChange318.forward_includeRight (S:=S) A B x
  change Spec.map (CommRingCat.ofHom (AffineBaseChange318.forward (S:=S) A B).toRingHom) ≫
    (pullbackSpecIso R S (ShortAffineJacobian318.Ring A B)).inv ≫ pullback.snd _ _=_
  rw [pullbackSpecIso_inv_snd R S (ShortAffineJacobian318.Ring A B),←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he

theorem finite_base_pullback (A B:R) : IsPullback (finiteMap (S:=S) A B)
    (ShortAffineScheme318.structureMap (a A) (a B)) (ShortAffineScheme318.structureMap A B)
      (Spec.map (CommRingCat.ofHom a)) := by
  apply IsPullback.flip
  exact IsPullback.of_iso_pullback ⟨(finiteMap_base A B).symm⟩
    (AffineSchemeBaseChange318.schemeIso (S:=S) A B).symm
    (AffineSchemeBaseChange318.schemeIso_inv_base A B) (finite_iso_inv_curve A B)
theorem infinity_base_pullback (A B:R) : IsPullback (infinityMap (S:=S) A B)
    (InfinitySmooth318.structureMap (a A) (a B)) (InfinitySmooth318.structureMap A B)
      (Spec.map (CommRingCat.ofHom a)) := by
  apply IsPullback.flip
  exact IsPullback.of_iso_pullback ⟨(infinityMap_base A B).symm⟩
    (InfinityBaseChange318.schemeIso (S:=S) A B).symm
    (InfinityBaseChange318.schemeIso_inv_base A B) (InfinityBaseChange318.schemeIso_inv_curve A B)

/-- The two original affine charts as an actual two-element open cover. -/
def twoChartCover {T : Type u} [CommRing T] (A B:T) : (WeierstrassGluing318.scheme A B).OpenCover where
  I₀ := Bool
  X b := if b then ShortAffineScheme318.scheme A B else InfinitySmooth318.scheme A B
  f b := by
    cases b
    · exact WeierstrassGluing318.infinityChart A B
    · exact WeierstrassGluing318.finiteChart A B
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      rcases WeierstrassGluing318.charts_cover A B p with ⟨q,hq⟩ | ⟨q,hq⟩
      · exact ⟨true,q,hq⟩
      · exact ⟨false,q,hq⟩
    · intro b
      cases b <;> infer_instance

lemma transport_chart_pullback {W X Y U V Z : Scheme} (f : X ⟶ Y) (iX : U ⟶ X) (iY : V ⟶ Y)
    (f' : U ⟶ V) (sX : X ⟶ W) (sY : Y ⟶ Z) (b : W ⟶ Z)
    (hchart : IsPullback f' iX iY f) (hbase : IsPullback f' (iX ≫ sX) (iY ≫ sY) b) :
    IsPullback (pullback.snd f iY) (pullback.fst f iY ≫ sX) (iY ≫ sY) b := by
  apply hbase.of_iso hchart.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp

/-- Actual arbitrary coefficient base change of the complete glued Weierstrass family. -/
theorem coefficient_base_pullback (A B:R) : IsPullback (coefficientMap (S:=S) A B)
    (WeierstrassGluing318.structureMap (a A) (a B)) (WeierstrassGluing318.structureMap A B)
      (Spec.map (CommRingCat.ofHom a)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (twoChartCover A B)
  intro b
  cases b
  · change IsPullback (pullback.snd (coefficientMap A B) (WeierstrassGluing318.infinityChart A B))
      (pullback.fst (coefficientMap A B) (WeierstrassGluing318.infinityChart A B) ≫
        WeierstrassGluing318.structureMap (a A) (a B))
      (WeierstrassGluing318.infinityChart A B ≫ WeierstrassGluing318.structureMap A B)
      (Spec.map (CommRingCat.ofHom a))
    apply transport_chart_pullback _ _ _ _ _ _ _ (infinity_chart_pullback A B)
    rw [WeierstrassGluing318.infinityChart_structure,WeierstrassGluing318.infinityChart_structure]
    exact infinity_base_pullback A B
  · change IsPullback (pullback.snd (coefficientMap A B) (WeierstrassGluing318.finiteChart A B))
      (pullback.fst (coefficientMap A B) (WeierstrassGluing318.finiteChart A B) ≫
        WeierstrassGluing318.structureMap (a A) (a B))
      (WeierstrassGluing318.finiteChart A B ≫ WeierstrassGluing318.structureMap A B)
      (Spec.map (CommRingCat.ofHom a))
    apply transport_chart_pullback _ _ _ _ _ _ _ (finite_chart_pullback A B)
    rw [WeierstrassGluing318.finiteChart_structure,WeierstrassGluing318.finiteChart_structure]
    exact finite_base_pullback A B

/-- The actual Scheme fiber product is the complete cubic with mapped coefficients. -/
@[expose] def schemeIso (A B:R) :
    pullback (Spec.map (CommRingCat.ofHom a)) (WeierstrassGluing318.structureMap A B) ≅
      WeierstrassGluing318.scheme (a A) (a B) :=
  (coefficient_base_pullback A B).flip.isoPullback.symm

theorem schemeIso_inv_base (A B:R) : (schemeIso (S:=S) A B).inv ≫ pullback.fst _ _=
    WeierstrassGluing318.structureMap (a A) (a B) :=
  (coefficient_base_pullback A B).flip.isoPullback_hom_fst
theorem schemeIso_inv_curve (A B:R) : (schemeIso (S:=S) A B).inv ≫ pullback.snd _ _=
    coefficientMap (S:=S) A B := (coefficient_base_pullback A B).flip.isoPullback_hom_snd

/-- The complete literal OpenJ family has its actual changed-coefficient fiber at every algebra. -/
@[expose] def literalFiberIso (N:ℕ) (T:Type) [CommRing T] [Algebra (OpenJModel318.Base N) T] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) T)))
      (WeierstrassGluing318.literalStructureMap N) ≅
      WeierstrassGluing318.scheme
        (algebraMap (OpenJModel318.Base N) T (OpenJAffineScheme318.A N))
        (algebraMap (OpenJModel318.Base N) T (OpenJAffineScheme318.B N)) :=
  schemeIso _ _

end WeierstrassBaseChange318
