module
public import OriginalRetainedProjectiveAffinePiece318
@[expose] public section
noncomputable section
namespace OriginalRetainedProjectiveRatio318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S ι : Type u} [CommRing R] [CommRing S]
local notation "P" => MvPolynomial ι R
local notation "G" => ProjectiveChart318.Grading R ι

def fullEval (φ : P →+* S) (f : P) (hf : IsUnit (φ f)) : Localization.Away f →+* S :=
  IsLocalization.Away.lift f hf

/-- Actual evaluation of homogeneous fractions at an invertible coordinate. -/
def evaluate (φ : P →+* S) (f : P) (hf : IsUnit (φ f)) : Away G f →+* S :=
  (fullEval φ f hf).comp (algebraMap (Away G f) (Localization.Away f))

lemma evaluate_zero (φ : P →+* S) (f : P) (hf : IsUnit (φ f)) (a : G 0) :
    evaluate φ f hf (fromZeroRingHom G _ a)=φ a := by
  change fullEval φ f hf (Localization.mk (a:P) 1)=_
  rw [Localization.mk_eq_mk',IsLocalization.mk'_one]
  exact IsLocalization.Away.lift_eq f hf _

/-- Evaluation commutes with the actual homogeneous localization map to a double overlap. -/
lemma evaluate_awayMap (φ : P →+* S) (f g : P) (hf : IsUnit (φ f)) (hg : IsUnit (φ g))
    {d : ℕ} (hgd : g ∈ G d) (a : Away G f) :
    evaluate φ (f*g) (by simpa using hf.mul hg) (awayMap G hgd rfl a)=evaluate φ f hf a := by
  have hu : IsUnit (algebraMap P (Localization.Away (f*g)) f) :=
    IsLocalization.Away.isUnit_of_dvd (f*g) (dvd_mul_right f g)
  have he : (fullEval φ (f*g) (by simpa using hf.mul hg)).comp
      (Localization.awayLift (algebraMap P (Localization.Away (f*g))) f hu)=fullEval φ f hf := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro p
    simp [fullEval,Localization.awayLift,IsLocalization.Away.lift_eq]
  change fullEval φ (f*g) (by simpa using hf.mul hg) (awayMap G hgd rfl a).val=fullEval φ f hf a.val
  rw [val_awayMap]
  exact RingHom.congr_fun he a.val

lemma evaluate_awayMap_eq (φ : P →+* S) (f g x : P) (hf : IsUnit (φ f)) (hg : IsUnit (φ g))
    {d : ℕ} (hgd : g ∈ G d) (hx : x=f*g) (a : Away G f) :
    evaluate φ x (by rw [hx]; simpa using hf.mul hg) (awayMap G hgd hx a)=evaluate φ f hf a := by
  subst x
  exact evaluate_awayMap φ f g hf hg hgd a

/-- The actual projective chart morphisms agree on a common invertible-coordinate overlap. -/
theorem chart_compatibility (φ : P →+* S) (f g : P) (hf : IsUnit (φ f)) (hg : IsUnit (φ g))
    {m n : ℕ} (hfd : f ∈ G m) (hgd : g ∈ G n) (hm : 0<m) (hn : 0<n) :
    Spec.map (CommRingCat.ofHom (evaluate φ f hf)) ≫ Proj.awayι G f hfd hm=
      Spec.map (CommRingCat.ofHom (evaluate φ g hg)) ≫ Proj.awayι G g hgd hn := by
  have hleft : (evaluate φ (f*g) (by simpa using hf.mul hg)).comp (awayMap G hgd rfl)=evaluate φ f hf := by
    ext a
    exact evaluate_awayMap φ f g hf hg hgd a
  have hright : (evaluate φ (f*g) (by simpa using hf.mul hg)).comp (awayMap G hfd (mul_comm f g))=evaluate φ g hg := by
    ext a
    exact evaluate_awayMap_eq φ g f (f*g) hg hf hfd (mul_comm f g) a
  rw [←hleft,←hright]
  simp only [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι,Proj.SpecMap_awayMap_awayι]
  rfl

lemma evaluate_mk (φ : P →+* S) (f : P) (hf : IsUnit (φ f)) {d : ℕ}
    (hfd : f ∈ G d) (n : ℕ) (p : P) (hp : p ∈ G (n • d)) (v : S) (hv : φ f*v=1) :
    evaluate φ f hf (Away.mk G hfd n p hp)=φ p*v^n := by
  change Localization.awayLift φ f hf (Localization.mk p ⟨f^n,⟨n,rfl⟩⟩)=_
  exact Localization.awayLift_mk φ f p v hv n

section Algebra
variable [Algebra R S]
/-- Actual chart evaluation as an R-algebra map. -/
def chartEval (φ : P →ₐ[R] S) (j : ι) (hj : IsUnit (φ (X j))) :
    Away G (X j) →ₐ[R] S where
  __ := evaluate φ.toRingHom (X j) hj
  commutes' r := by
    change evaluate φ.toRingHom (X j) hj (fromZeroRingHom G _ (ProjectiveChart318.coeffZero R ι r))=_
    rw [evaluate_zero]
    exact φ.commutes r

lemma chartEval_coordinate (φ : P →ₐ[R] S) (j : ι) (hj : IsUnit (φ (X j)))
    (i : {i : ι // i ≠ j}) (v : S) (hv : φ (X j)*v=1) :
    chartEval φ j hj (ProjectiveChart318.coordinate R ι j i)=φ (X (i:ι))*v := by
  change evaluate φ.toRingHom (X j) hj (Away.mk G (isHomogeneous_X R j) 1 (X (i:ι)) _)=_
  rw [evaluate_mk _ _ _ _ _ _ _ v hv,pow_one]
  rfl


end Algebra
section ActualPoint
open OriginalRetainedProjectiveAffinePiece318

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def ratio (v : κ→ℂ) (i : κ) (j : {j : κ // j≠i}) : ℂ := v j.val * (v i)⁻¹

variable (v : κ→ℂ) (i : κ) (hi : v i≠0)

def actualPointFromVector : T ⟶ Ambient κ :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (ratio v i)).toRingHom)≫affineArrow κ i

include hi in
theorem ratio_eval (h : IsUnit (MvPolynomial.aeval v (MvPolynomial.X i))) :
    (MvPolynomial.aeval (ratio v i)).comp (ProjectiveChart318.chartEquiv ℂ κ i).toAlgHom =
      chartEval (MvPolynomial.aeval v) i h := by
  let E := ProjectiveChart318.chartEquiv ℂ κ i
  have H : (chartEval (MvPolynomial.aeval v) i h).comp E.symm.toAlgHom =
      MvPolynomial.aeval (ratio v i) := by
    apply MvPolynomial.algHom_ext
    intro j
    have hc : E.symm (MvPolynomial.X j)=ProjectiveChart318.coordinate ℂ κ i j := by
      change ProjectiveChart318.toChart ℂ κ i (MvPolynomial.X j)=_
      rw [ProjectiveChart318.toChart,MvPolynomial.aeval_X]
    change chartEval (MvPolynomial.aeval v) i h (E.symm (MvPolynomial.X j)) = _
    rw [hc,MvPolynomial.aeval_X]
    calc
      _ = MvPolynomial.aeval v (MvPolynomial.X j.val) * (v i)⁻¹ :=
        chartEval_coordinate (MvPolynomial.aeval v) i h j (v i)⁻¹
          (by rw [MvPolynomial.aeval_X,mul_inv_cancel₀ hi])
      _ = _ := by rw [MvPolynomial.aeval_X,ratio]
  apply AlgHom.ext
  intro z
  have hz := AlgHom.congr_fun H (E z)
  simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.symm_apply_apply] using hz.symm

include hi in
/-- Its literal whole Spec(ℂ) evaluation on the same R182 standard
chart is the homogeneous localization evaluation at v. -/
theorem actualPoint_via_homogeneous :
    actualPointFromVector v i =
      Spec.map (CommRingCat.ofHom
        (evaluate (MvPolynomial.aeval v).toRingHom (MvPolynomial.X i)
          (by
            change IsUnit (MvPolynomial.aeval v (MvPolynomial.X i))
            rw [MvPolynomial.aeval_X]
            exact isUnit_iff_ne_zero.2 hi)))≫
      Proj.awayι (Grading κ) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) (by decide) := by
  unfold actualPointFromVector affineArrow
  rw [←Category.assoc,←Spec.map_comp]
  congr 1
  refine congrArg (fun g : CommRingCat.of (ProjectiveChart318.Chart ℂ κ i) ⟶ CommRingCat.of ℂ =>
    Spec.map g) ?_
  apply CommRingCat.hom_ext
  have h : IsUnit (MvPolynomial.aeval v (MvPolynomial.X i : MvPolynomial κ ℂ)) := by
    rw [MvPolynomial.aeval_X]
    exact isUnit_iff_ne_zero.2 hi
  exact congrArg AlgHom.toRingHom (ratio_eval v i hi h)

include hi in
/-- If two original projective coordinates are nonzero, their rational
dehomogenizations are one and the same actual Scheme point. -/
theorem actual_chart_ratio (j : κ) (hj : v j≠0) :
    actualPointFromVector v i=actualPointFromVector v j := by
  rw [actualPoint_via_homogeneous v i hi,actualPoint_via_homogeneous v j hj]
  exact chart_compatibility (MvPolynomial.aeval v).toRingHom
    (MvPolynomial.X i) (MvPolynomial.X j)
    (by
      change IsUnit (MvPolynomial.aeval v (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X]
      exact isUnit_iff_ne_zero.2 hi)
    (by
      change IsUnit (MvPolynomial.aeval v (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X]
      exact isUnit_iff_ne_zero.2 hj)
    (MvPolynomial.isHomogeneous_X ℂ i) (MvPolynomial.isHomogeneous_X ℂ j)
    (by decide) (by decide)

end ActualPoint

end OriginalRetainedProjectiveRatio318
