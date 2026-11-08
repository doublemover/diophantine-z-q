module
public import QuadraticCoefficients318
public import ThreeTorsionDiamond318
public section
noncomputable section
namespace ThreeTorsionSignQuotient318
open Polynomial ThreeTorsionAlgebra318 InvariantBaseChange318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R] [Nontrivial R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma neg_on_xRing (a:XRing A B) :
    ThreeTorsionInvolution318.negEquiv A B hD
      (algebraMap (XRing A B) (Ring A B hD) a)=
        algebraMap (XRing A B) (Ring A B hD) a:=by
  have hh:((ThreeTorsionInvolution318.negEquiv A B hD).toAlgHom).comp
      (IsScalarTower.toAlgHom R (XRing A B) (Ring A B hD))=
        IsScalarTower.toAlgHom R (XRing A B) (Ring A B hD):=by
    apply AdjoinRoot.algHom_ext
    exact ThreeTorsionInvolution318.negEquiv_x A B hD
  exact AlgHom.congr_fun hh a

lemma fixed_iff_from_x (z:Ring A B hD) :
    ThreeTorsionInvolution318.negEquiv A B hD z=z ↔
      ∃a:XRing A B,algebraMap (XRing A B) (Ring A B hD) a=z :=by
  constructor
  · intro hz
    obtain ⟨a,b,hab⟩:=QuadraticCoefficients318.exists_coefficients (cubicUnit A B hD) z
    change z=algebraMap (XRing A B) (Ring A B hD) a+
      algebraMap (XRing A B) (Ring A B hD) b*y A B hD at hab
    have hn:=congrArg (ThreeTorsionInvolution318.negEquiv A B hD) hab
    rw [hz,map_add,map_mul,neg_on_xRing,neg_on_xRing,ThreeTorsionInvolution318.negEquiv_y] at hn
    have h2:IsUnit (2:Ring A B hD):=by
      simpa only [map_ofNat] using (two_unit A B hD).map (algebraMap R (Ring A B hD))
    have hb:algebraMap (XRing A B) (Ring A B hD) b=0:=by
      apply ((h2.mul (y_unit A B hD)).mul_right_eq_zero).mp
      linear_combination hn-hab
    refine ⟨a,?_⟩
    simpa only [hb,zero_mul,add_zero] using hab.symm
  · rintro ⟨a,rfl⟩
    exact neg_on_xRing A B hD a

abbrev Fixed := invariants (ThreeTorsionDiamond318.diamond A B hD)

@[expose] def xToFixed : XRing A B→ₐ[R]Fixed A B hD :=
  (IsScalarTower.toAlgHom R (XRing A B) (Ring A B hD)).codRestrict (Fixed A B hD) (by
    intro a g
    rcases ThreeTorsionLabels318.unit_cases g with rfl|rfl
    · simp
    · simpa only [ThreeTorsionDiamond318.diamond_neg_one,IsScalarTower.toAlgHom_apply]
        using neg_on_xRing A B hD a)

lemma xToFixed_bijective : Function.Bijective (xToFixed A B hD) :=by
  constructor
  · intro a b hh
    have h:=congrArg Subtype.val hh
    apply AdjoinRoot.of.injective_of_monic_of_degree_pos (EvenContactEtale318.monic (cubicUnit A B hD)) _ h
    letI:=xRing_nontrivial A B
    rw [←Polynomial.natDegree_pos_iff_degree_pos]
    simp [EvenContactEtale318.polynomial]
  · intro z
    have hn:=z.property (-1)
    rw [ThreeTorsionDiamond318.diamond_neg_one] at hn
    obtain ⟨a,ha⟩:=(fixed_iff_from_x A B hD z.val).mp hn
    exact ⟨a,Subtype.ext ha⟩

/-- The full sign quotient of the actual eight-point cover is exactly its
rank-four x-coordinate algebra, not another arbitrary algebra of rank four. -/
@[expose] def signQuotientEquiv : XRing A B≃ₐ[R]Fixed A B hD :=
  AlgEquiv.ofBijective (xToFixed A B hD) (xToFixed_bijective A B hD)

theorem signQuotientEquiv_val (a:XRing A B) :
    (signQuotientEquiv A B hD a:Ring A B hD)=
      algebraMap (XRing A B) (Ring A B hD) a:=rfl

theorem fixed_rank_four : Module.finrank R (Fixed A B hD)=4:=by
  rw [←(signQuotientEquiv A B hD).toLinearEquiv.finrank_eq]
  exact ShortThreeTorsion318.rank_four A B

end ThreeTorsionSignQuotient318
