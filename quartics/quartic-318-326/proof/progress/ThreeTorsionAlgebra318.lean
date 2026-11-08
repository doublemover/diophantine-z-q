module
public import ShortThreeTorsion318
public import EvenContactEtale318
public import Mathlib.LinearAlgebra.Dimension.Free
public section
noncomputable section
namespace ThreeTorsionAlgebra318
open Polynomial
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] (A B:R) [Invertible (3:R)]

abbrev XRing := ShortThreeTorsion318.Ring A B
@[expose] def cubic : XRing A B :=
  AdjoinRoot.mk (ShortThreeTorsion318.polynomial A B) (ShortTwoTorsion318.polynomial A B)
@[expose] def cubicUnit (hD:IsUnit (-16*(4*A^3+27*B^2))) : (XRing A B)ˣ :=
  (ShortThreeTorsion318.cubic_unit A B hD).unit
lemma cubicUnit_val (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (cubicUnit A B hD:XRing A B)=cubic A B := IsUnit.unit_spec _

abbrev Ring (hD:IsUnit (-16*(4*A^3+27*B^2))) :=
  EvenContactEtale318.RootRing (cubicUnit A B hD)

variable (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def x : Ring A B hD :=
  algebraMap (XRing A B) (Ring A B hD) (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B))
@[expose] def y : Ring A B hD := EvenContactEtale318.root (cubicUnit A B hD)

lemma equation : (y A B hD)^2=(x A B hD)^3+
    algebraMap R (Ring A B hD) A*x A B hD+algebraMap R (Ring A B hD) B := by
  rw [y,EvenContactEtale318.root_square,cubicUnit_val]
  simp only [cubic,ShortTwoTorsion318.polynomial,map_add,map_pow,map_mul,
    AdjoinRoot.mk_X,AdjoinRoot.mk_C]
  rfl

lemma y_unit : IsUnit (y A B hD) := EvenContactEtale318.root_isUnit _

include hD in
lemma two_unit : IsUnit (2:R) := by
  have h16:IsUnit (16:R):=by simpa only [neg_neg] using ((IsUnit.mul_iff.mp hD).1).neg
  apply (isUnit_pow_iff (by decide:4≠0)).mp
  convert h16 using 1 <;> norm_num

lemma finite : Module.Finite R (Ring A B hD) := by
  letI:=ShortThreeTorsion318.finite A B
  letI:=EvenContactEtale318.rootRing_finite (cubicUnit A B hD)
  exact Module.Finite.trans (XRing A B) (Ring A B hD)

lemma free : Module.Free R (Ring A B hD) := by
  letI:=ShortThreeTorsion318.free A B
  letI:=EvenContactEtale318.rootRing_free (cubicUnit A B hD)
  exact Module.Free.trans (R:=R) (S:=XRing A B) (M:=Ring A B hD)

lemma etale : Algebra.Etale R (Ring A B hD) := by
  letI:=ShortThreeTorsion318.etale A B hD
  have h2:IsUnit (2:XRing A B):=by
    simpa only [map_ofNat] using (two_unit A B hD).map (algebraMap R (XRing A B))
  letI:=EvenContactEtale318.rootRing_etale (cubicUnit A B hD) h2
  exact Algebra.Etale.comp R (XRing A B) (Ring A B hD)

lemma xRing_nontrivial [Nontrivial R] : Nontrivial (XRing A B) :=
  (AdjoinRoot.nontrivial_iff_of_monic (ShortThreeTorsion318.monic A B)).mpr
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [ShortThreeTorsion318.degree];decide))

lemma faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Ring A B hD) := by
  letI:=xRing_nontrivial A B
  letI:=ShortThreeTorsion318.faithfullyFlat A B
  letI:=EvenContactEtale318.rootRing_faithfullyFlat (cubicUnit A B hD)
  exact Module.FaithfullyFlat.trans R (XRing A B) (Ring A B hD)

lemma rank_eight [Nontrivial R] : Module.finrank R (Ring A B hD)=8 := by
  letI:=xRing_nontrivial A B
  letI:=ShortThreeTorsion318.free A B
  letI:=EvenContactEtale318.rootRing_free (cubicUnit A B hD)
  rw [←Module.finrank_mul_finrank R (XRing A B) (Ring A B hD),
    ShortThreeTorsion318.rank_four,EvenContactEtale318.rootRing_rank_two]

end ThreeTorsionAlgebra318
