module
public import VaryingNormalizedIdealBaseChange318
public section
noncomputable section
namespace VaryingSourceMapComposition318
open scoped TensorProduct
universe u
variable (R A S T U : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [CommRing U] [Algebra R U]
  (f : S →ₐ[R] T) (g : T →ₐ[R] U)
lemma composition : (VaryingNormalizedIdealBaseChange318.sourceMap R A T U g).comp
    (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f)=
    VaryingNormalizedIdealBaseChange318.sourceMap R A S U (g.comp f) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | zero => simp only [map_zero]
  | tmul s a => simp only [AlgHom.comp_apply,VaryingNormalizedIdealBaseChange318.sourceMap,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
  | add x y hx hy => simp only [map_add,hx,hy]
lemma ideal_map (I : Ideal (S ⊗[R] A)) :
    Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A T U g).toRingHom
      (Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom I)=
    Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S U (g.comp f)).toRingHom I := by
  rw [Ideal.map_map]
  exact congrArg (fun k : S ⊗[R] A →ₐ[R] U ⊗[R] A => Ideal.map k.toRingHom I)
    (composition R A S T U f g)
end VaryingSourceMapComposition318
