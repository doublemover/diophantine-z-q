module
public import AlgebraChartEvaluation318
public import SymmetricMixedAddition318
public section
noncomputable section
namespace AffineProductEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraChartEvaluation318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S T U:Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]
@[expose] def toAlgHom (f:Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of T))
    (h:f ≫ Spec.algebraMap R T=Spec.algebraMap R S) : T →ₐ[R] S :=
  Spec.homEquivAlgHom ⟨f,h⟩
theorem map_toAlgHom (f:Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of T))
    (h:f ≫ Spec.algebraMap R T=Spec.algebraMap R S) :
    Spec.map (CommRingCat.ofHom (toAlgHom f h).toRingHom)=f :=
  congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨f,h⟩)

/-- The actual tensor-product affine isomorphism evaluates on an arbitrary
Scheme-valued test map by the literal pair of algebra homomorphisms. -/
theorem product_iso (x:Spec (CommRingCat.of S) ⟶ pullback (Spec.algebraMap R T) (Spec.algebraMap R U))
    (f:T →ₐ[R] S) (g:U →ₐ[R] S)
    (hf:x ≫ pullback.fst _ _=Spec.map (CommRingCat.ofHom f.toRingHom))
    (hg:x ≫ pullback.snd _ _=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    x ≫ (pullbackSpecIso R T U).hom=Spec.map (CommRingCat.ofHom (pair f g).toRingHom) := by
  apply (cancel_mono (pullbackSpecIso R T U).inv).mp
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc,pullbackSpecIso_inv_fst,←Spec.map_comp,hf]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (pair_left f g r).symm
  · rw [Category.assoc,pullbackSpecIso_inv_snd,←Spec.map_comp,hg]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (pair_right f g r).symm

variable (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
theorem finite_evaluation
    (x:Spec (CommRingCat.of S) ⟶ RelativeChordScheme318.productScheme A B)
    (f g:F A B →ₐ[R] S)
    (hf:x ≫ pullback.fst _ _=Spec.map (CommRingCat.ofHom f.toRingHom))
    (hg:x ≫ pullback.snd _ _=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    x ≫ FiniteAdditionGluing318.addition A B hD=finite A B hD f g := by
  rw [FiniteAdditionGluing318.addition,←Category.assoc,product_iso x f g hf hg]
  rfl
theorem mixed_evaluation
    (x:Spec (CommRingCat.of S) ⟶ InfinityInputScheme318.productScheme A B)
    (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S)
    (hf:x ≫ pullback.fst _ _=Spec.map (CommRingCat.ofHom f.toRingHom))
    (hg:x ≫ pullback.snd _ _=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    x ≫ MixedAdditionGluing318.addition A B hD=mixed A B hD f g := by
  rw [MixedAdditionGluing318.addition,←Category.assoc,product_iso x f g hf hg]
  rfl
theorem symmetric_evaluation
    (x:Spec (CommRingCat.of S) ⟶ SymmetricMixedAddition318.productScheme A B)
    (f:F A B →ₐ[R] S) (g:I A B →ₐ[R] S)
    (hf:x ≫ pullback.fst _ _=Spec.map (CommRingCat.ofHom f.toRingHom))
    (hg:x ≫ pullback.snd _ _=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    x ≫ SymmetricMixedAddition318.addition A B hD=mixed A B hD g f := by
  rw [SymmetricMixedAddition318.addition,←Category.assoc]
  apply mixed_evaluation
  · simpa only [Category.assoc,pullbackSymmetry_hom_comp_fst] using hg
  · simpa only [Category.assoc,pullbackSymmetry_hom_comp_snd] using hf
theorem both_evaluation
    (x:Spec (CommRingCat.of S) ⟶ BothInfinityScheme318.productScheme A B)
    (f g:I A B →ₐ[R] S)
    (hf:x ≫ pullback.fst _ _=Spec.map (CommRingCat.ofHom f.toRingHom))
    (hg:x ≫ pullback.snd _ _=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    x ≫ WholeBothInfinity318.addition A B hD=both A B hD f g := by
  rw [WholeBothInfinity318.addition,←Category.assoc,product_iso x f g hf hg]
  rfl
end AffineProductEvaluation318
