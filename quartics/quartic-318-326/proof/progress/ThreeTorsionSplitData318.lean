module
public import ThreeTorsionInvolution318
public import FourUnitCover318
public section
noncomputable section
namespace ThreeTorsionSplitData318
open Polynomial ThreeTorsionAlgebra318
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R] [Nontrivial R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

abbrev split := ShortThreeTorsion318.splitting A B hD
abbrev S := (split A B hD).S
@[expose] def xRoot (i:Fin 4) : S A B hD :=
  (split A B hD).roots ((finCongr (ShortThreeTorsion318.degree A B)).symm i)

lemma xRoot_relation (i:Fin 4) :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R (S A B hD)) (xRoot A B hD i)=0 := by
  have hh:=SplitPolynomialAlgebra318.root_eval _ (split A B hD).roots
    (split A B hD).factorization ((finCongr (ShortThreeTorsion318.degree A B)).symm i)
  simpa only [Polynomial.eval_map,xRoot] using hh

@[expose] def xEval (i:Fin 4) : XRing A B→ₐ[R]S A B hD :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (xRoot A B hD i) (xRoot_relation A B hD i)

@[expose] def units (i:Fin 4) : (S A B hD)ˣ :=
  Units.map (xEval A B hD i).toMonoidHom (cubicUnit A B hD)

lemma units_val (i:Fin 4) : (units A B hD i:S A B hD)=
    (xRoot A B hD i)^3+algebraMap R (S A B hD) A*xRoot A B hD i+
      algebraMap R (S A B hD) B := by
  change xEval A B hD i (cubicUnit A B hD:XRing A B)=_
  rw [cubicUnit_val]
  simp only [xEval,cubic,AdjoinRoot.liftAlgHom_mk,ShortTwoTorsion318.polynomial,
    eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  rfl

abbrev T := FourUnitCover318.Cover (units A B hD)

instance finite : Module.Finite R (T A B hD) := by
  have h2:IsUnit (2:S A B hD):=by
    simpa only [map_ofNat] using (two_unit A B hD).map (algebraMap R (S A B hD))
  letI:Module.Finite (S A B hD) (T A B hD):=(FourUnitCover318.finite_free_etale _ h2).1
  exact Module.Finite.trans (S A B hD) (T A B hD)
instance etale : Algebra.Etale R (T A B hD) := by
  have h2:IsUnit (2:S A B hD):=by
    simpa only [map_ofNat] using (two_unit A B hD).map (algebraMap R (S A B hD))
  letI:Algebra.Etale (S A B hD) (T A B hD):=(FourUnitCover318.finite_free_etale _ h2).2.2
  exact Algebra.Etale.comp R (S A B hD) (T A B hD)
instance faithfullyFlat : Module.FaithfullyFlat R (T A B hD) := by
  letI:Module.FaithfullyFlat (S A B hD) (T A B hD):=FourUnitCover318.faithfullyFlat _
  exact Module.FaithfullyFlat.trans R (S A B hD) (T A B hD)

instance nontrivial : Nontrivial (T A B hD) := by
  have h:=FourUnitCover318.rank_sixteen (units A B hD)
  by_contra hh
  haveI:Subsingleton (T A B hD):=not_nontrivial_iff_subsingleton.mp hh
  rw [Module.finrank_zero_of_subsingleton] at h
  norm_num at h

@[expose] def xs (i:Fin 4) : T A B hD := algebraMap (S A B hD) (T A B hD) (xRoot A B hD i)
@[expose] def ys (i:Fin 4) : T A B hD := FourUnitCover318.generator (units A B hD) i

lemma ys_square (i:Fin 4) : (ys A B hD i)^2=(xs A B hD i)^3+
    algebraMap R (T A B hD) A*xs A B hD i+algebraMap R (T A B hD) B := by
  rw [ys,FourUnitCover318.generator_square,units_val]
  simp only [map_add,map_pow,map_mul,xs]
  rfl

lemma ys_unit (i:Fin 4) : IsUnit (ys A B hD i) := by
  apply (isUnit_pow_iff (by decide:2≠0)).mp
  change IsUnit ((FourUnitCover318.generator (units A B hD) i)^2)
  rw [FourUnitCover318.generator_square]
  exact (units A B hD i).isUnit.map _

lemma xs_relation (i:Fin 4) :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R (T A B hD)) (xs A B hD i)=0 := by
  have hh:=congrArg (algebraMap (S A B hD) (T A B hD)) (xRoot_relation A B hD i)
  rw [Polynomial.hom_eval₂,map_zero] at hh
  exact hh

lemma factorization : (ShortThreeTorsion318.polynomial A B).map (algebraMap R (T A B hD))=
    ∏i:Fin 4,(X-C (xs A B hD i)) := by
  have hh:=congrArg (Polynomial.map (algebraMap (S A B hD) (T A B hD)))
    (split A B hD).factorization
  rw [Polynomial.map_map,Polynomial.map_prod] at hh
  rw [IsScalarTower.algebraMap_eq R (S A B hD) (T A B hD)]
  rw [hh]
  simpa only [xs,xRoot,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C] using
    ((finCongr (ShortThreeTorsion318.degree A B)).symm.prod_comp
      (fun j=>X-C (algebraMap (S A B hD) (T A B hD) ((split A B hD).roots j)))).symm

@[expose] def xSplitEquiv :
    T A B hD⊗[R]XRing A B≃ₐ[T A B hD](Fin 4→T A B hD) :=
  MonogenicSplitEquiv318.splitEquiv _ (xs A B hD) (factorization A B hD)
    (ShortThreeTorsion318.separable A B hD)

theorem xSplitEquiv_tmul (s:T A B hD) (f:R[X]) (i:Fin 4) :
    xSplitEquiv A B hD (s⊗ₜ[R]AdjoinRoot.mk (ShortThreeTorsion318.polynomial A B) f) i=
      s*f.eval₂ (algebraMap R (T A B hD)) (xs A B hD i) :=
  MonogenicSplitEquiv318.splitEquiv_tmul_mk _ _ _ _ s f i

end ThreeTorsionSplitData318
