module
public import VaryingNormalizedFamilyBaseChange318
public section
noncomputable section
namespace VaryingSourceCoefficientPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S]
@[expose] def projection : Spec (CommRingCat.of (S ⊗[R] A)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))
@[expose] def original : Spec (CommRingCat.of (S ⊗[R] A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom)
@[expose] def base : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))
lemma tensor_cartesian : IsPullback (projection R A S) (original R A S)
    (base R S) (base R A) := by
  apply IsPullback.of_iso_pullback (i := (pullbackSpecIso R S A).symm)
  · constructor
    change Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ≫ _=
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom) ≫ _
    rw [← pullbackSpecIso_inv_fst' R S A,← pullbackSpecIso_inv_snd R S A,
      Category.assoc,Category.assoc,pullback.condition]
  · exact pullbackSpecIso_inv_fst' R S A
  · exact pullbackSpecIso_inv_snd R S A

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
@[expose] def sourceChange : Spec (CommRingCat.of (T ⊗[R] A)) ⟶
    Spec (CommRingCat.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom)
@[expose] def coefficientChange : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)
@[reassoc] lemma source_original : sourceChange R A S T f ≫ original R A S=original R A T := by
  rw [sourceChange,original,original,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change Algebra.TensorProduct.map f (AlgHom.id R A) ((1 : S) ⊗ₜ[R] a)=(1 : T) ⊗ₜ[R] a
  simp only [Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply]
@[reassoc] lemma source_projection : sourceChange R A S T f ≫ projection R A S=
    projection R A T ≫ coefficientChange R S T f := by
  rw [sourceChange,projection,projection,coefficientChange,← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  change Algebra.TensorProduct.map f (AlgHom.id R A) (s ⊗ₜ[R] (1 : A))=f s ⊗ₜ[R] (1 : A)
  simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
@[reassoc] lemma coefficient_base : coefficientChange R S T f ≫ base R S=base R T := by
  rw [coefficientChange,base,base,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact f.commutes r

/-- The literal tensor-source coefficient map is Cartesian over the
coefficient map, not merely a morphism of ambient source schemes. -/
lemma cartesian : IsPullback (sourceChange R A S T f) (projection R A T)
    (projection R A S) (coefficientChange R S T f) := by
  apply IsPullback.of_right (h₁₂ := original R A S) (h₂₂ := base R S)
  · simpa only [source_original,coefficient_base] using (tensor_cartesian R A T).flip
  · exact source_projection R A S T f
  · exact (tensor_cartesian R A S).flip
end VaryingSourceCoefficientPullback318
