module
public import AffineCoefficientCover318
public section
noncomputable section
namespace AffineCoefficientOverlapTests318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (C : AffineCoefficientCover318.Data R S) (i j : C.Index)
local notation "U" => AffineCoefficientCover318.cover R S C
local notation "Y" => pullback (U.f i) (U.f j)
local notation "V" => Y.affineOpenCover
variable (k : V.I₀)
abbrev ring : CommRingCat.{u} := V.X k
abbrev left : Spec (ring R S C i j k) ⟶ Spec (C.ring i) := V.f k ≫ pullback.fst (U.f i) (U.f j)
abbrev right : Spec (ring R S C i j k) ⟶ Spec (C.ring j) := V.f k ≫ pullback.snd (U.f i) (U.f j)
abbrev base : Spec (ring R S C i j k) ⟶ Spec (CommRingCat.of S) := left R S C i j k ≫ U.f i
lemma same_base : right R S C i j k ≫ U.f j=base R S C i j k := by
  change (V.f k ≫ pullback.snd (U.f i) (U.f j)) ≫ U.f j=
    (V.f k ≫ pullback.fst (U.f i) (U.f j)) ≫ U.f i
  rw [Category.assoc,Category.assoc,pullback.condition]
@[expose] instance algebra : Algebra R (ring R S C i j k) :=
  (((Spec.preimage (base R S C i j k)).hom).comp (algebraMap R S)).toAlgebra
@[expose] def coefficient : S →ₐ[R] ring R S C i j k where
  __ := (Spec.preimage (base R S C i j k)).hom
  commutes' _ := rfl
lemma coefficient_spec : Spec.map (CommRingCat.ofHom (coefficient R S C i j k).toRingHom)=base R S C i j k :=
  Spec.map_preimage _
lemma left_base : left R S C i j k ≫ VaryingSourceCoefficientPullback318.base R (C.ring i)=
    VaryingSourceCoefficientPullback318.base R (ring R S C i j k) := by
  rw [← AffineCoefficientCover318.over_base R S C i,← Category.assoc]
  change base R S C i j k ≫ VaryingSourceCoefficientPullback318.base R S=_
  rw [← coefficient_spec]
  exact VaryingSourceCoefficientPullback318.coefficient_base R S _ (coefficient R S C i j k)
lemma right_base : right R S C i j k ≫ VaryingSourceCoefficientPullback318.base R (C.ring j)=
    VaryingSourceCoefficientPullback318.base R (ring R S C i j k) := by
  rw [← AffineCoefficientCover318.over_base R S C j,← Category.assoc,same_base,← coefficient_spec]
  exact VaryingSourceCoefficientPullback318.coefficient_base R S _ (coefficient R S C i j k)
@[expose] def leftHom : C.ring i →ₐ[R] ring R S C i j k :=
  AffineSchemeAlgebraMap318.hom R (C.ring i) _ (left R S C i j k) (left_base R S C i j k)
@[expose] def rightHom : C.ring j →ₐ[R] ring R S C i j k :=
  AffineSchemeAlgebraMap318.hom R (C.ring j) _ (right R S C i j k) (right_base R S C i j k)
lemma left_spec : Spec.map (CommRingCat.ofHom (leftHom R S C i j k).toRingHom)=left R S C i j k :=
  AffineSchemeAlgebraMap318.spec_hom _ _ _ _ _
lemma right_spec : Spec.map (CommRingCat.ofHom (rightHom R S C i j k).toRingHom)=right R S C i j k :=
  AffineSchemeAlgebraMap318.spec_hom _ _ _ _ _
lemma hom_comp : (leftHom R S C i j k).comp (C.coefficient i)=
    (rightHom R S C i j k).comp (C.coefficient j) := by
  have h : CommRingCat.ofHom ((leftHom R S C i j k).comp (C.coefficient i)).toRingHom=
      CommRingCat.ofHom ((rightHom R S C i j k).comp (C.coefficient j)).toRingHom := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (C.coefficient i).toRingHom ≫
      CommRingCat.ofHom (leftHom R S C i j k).toRingHom)=
      Spec.map (CommRingCat.ofHom (C.coefficient j).toRingHom ≫
      CommRingCat.ofHom (rightHom R S C i j k).toRingHom)
    rw [Spec.map_comp,Spec.map_comp,left_spec,right_spec]
    exact (same_base R S C i j k).symm
  apply AlgHom.ext
  intro s
  exact congrArg (fun a => a.hom s) h
end AffineCoefficientOverlapTests318
