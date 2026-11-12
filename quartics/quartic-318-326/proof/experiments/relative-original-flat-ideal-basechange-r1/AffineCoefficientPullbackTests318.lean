module
public import AffineCoefficientOverlapTests318
public section
noncomputable section
namespace AffineCoefficientPullbackTests318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (φ : S →ₐ[R] T) (C : AffineCoefficientCover318.Data R S)
local notation "U" => AffineCoefficientCover318.cover R S C
local notation "b" => Spec.map (CommRingCat.ofHom φ.toRingHom)
abbrev pulled := U.pullback₁ b
@[expose] def cover : (Spec (CommRingCat.of T)).AffineOpenCover := (pulled R S T φ C).affineRefinement
abbrev index := (cover R S T φ C).I₀
variable (i : index R S T φ C)
abbrev ring : CommRingCat.{u} := (cover R S T φ C).X i
abbrev toNew : Spec (ring R S T φ C i) ⟶ Spec (CommRingCat.of T) := (cover R S T φ C).f i
abbrev toOld : Spec (ring R S T φ C i) ⟶ Spec (C.ring i.1) :=
  ((pulled R S T φ C).X i.1).affineOpenCover.f i.2 ≫ pullback.snd b (U.f i.1)
lemma square : toOld R S T φ C i ≫ U.f i.1=toNew R S T φ C i ≫ b := by
  change (((pulled R S T φ C).X i.1).affineOpenCover.f i.2 ≫ pullback.snd b (U.f i.1)) ≫ U.f i.1=
    (((pulled R S T φ C).X i.1).affineOpenCover.f i.2 ≫ pullback.fst b (U.f i.1)) ≫ b
  rw [Category.assoc,Category.assoc,pullback.condition]
@[expose] instance algebra : Algebra R (ring R S T φ C i) :=
  ((Spec.preimage (toNew R S T φ C i)).hom.comp (algebraMap R T)).toAlgebra
@[expose] def coefficient : T →ₐ[R] ring R S T φ C i where
  __ := (Spec.preimage (toNew R S T φ C i)).hom
  commutes' _ := rfl
lemma coefficient_spec : Spec.map (CommRingCat.ofHom (coefficient R S T φ C i).toRingHom)=toNew R S T φ C i :=
  Spec.map_preimage _
lemma old_over : toOld R S T φ C i ≫ VaryingSourceCoefficientPullback318.base R (C.ring i.1)=
    VaryingSourceCoefficientPullback318.base R (ring R S T φ C i) := by
  rw [← AffineCoefficientCover318.over_base R S C i.1,← Category.assoc,square,Category.assoc,
    VaryingSourceCoefficientPullback318.coefficient_base,← coefficient_spec]
  exact VaryingSourceCoefficientPullback318.coefficient_base R T _ (coefficient R S T φ C i)
@[expose] def oldHom : C.ring i.1 →ₐ[R] ring R S T φ C i :=
  AffineSchemeAlgebraMap318.hom R _ _ (toOld R S T φ C i) (old_over R S T φ C i)
lemma old_spec : Spec.map (CommRingCat.ofHom (oldHom R S T φ C i).toRingHom)=toOld R S T φ C i :=
  AffineSchemeAlgebraMap318.spec_hom _ _ _ _ _
lemma hom_comp : (oldHom R S T φ C i).comp (C.coefficient i.1)=(coefficient R S T φ C i).comp φ := by
  have h : CommRingCat.ofHom ((oldHom R S T φ C i).comp (C.coefficient i.1)).toRingHom=
      CommRingCat.ofHom ((coefficient R S T φ C i).comp φ).toRingHom := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (C.coefficient i.1).toRingHom ≫ CommRingCat.ofHom (oldHom R S T φ C i).toRingHom)=
      Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom (coefficient R S T φ C i).toRingHom)
    rw [Spec.map_comp,Spec.map_comp,old_spec,coefficient_spec]
    exact square R S T φ C i
  apply AlgHom.ext
  intro s
  exact congrArg (fun f => f.hom s) h
/-- The WHOLE affine refinement of a pulled-back coefficient cover. -/
@[expose] def data : AffineCoefficientCover318.Data R T where
  Index := index R S T φ C
  ring := ring R S T φ C
  algebra := algebra R S T φ C
  coefficient := coefficient R S T φ C
  open_map i := by rw [coefficient_spec]; infer_instance
  covers x := by
    obtain ⟨i,y,hy⟩ := (cover R S T φ C).openCover.exists_eq x
    refine ⟨i,?_⟩
    rw [coefficient_spec]
    exact ⟨y,hy⟩
end AffineCoefficientPullbackTests318
