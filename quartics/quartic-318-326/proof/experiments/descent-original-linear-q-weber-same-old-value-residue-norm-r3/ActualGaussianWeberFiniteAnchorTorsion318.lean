module
public import ActualGaussianWeberStockReductionAdd318
public import ActualGaussianWeberMixedStockCoordinates318
public import ActualGaussianWeberFiniteAnchorJet318
public section
noncomputable section

namespace ActualGaussianWeberFiniteAnchorTorsion318
open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberStockReductionAdd318 ActualGaussianWeberMixedStockCoordinates318
open ActualGaussianWeberFiniteAnchorJet318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)
variable [DecidableEq (ResidueField V)]

private def ordinate : WP F → F
  | Point.zero => 0
  | Point.some _ y _ => y

private theorem pointTransport {x y x' y' : F}
    {h : (curve F).toAffine.Nonsingular x y}
    {h' : (curve F).toAffine.Nonsingular x' y'}
    (hx : x=x') (hy : y=y') : Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

/-- Prime-to-residue torsion cannot lie in the kernel of the literal
point reduction. Use the fixed finite two-torsion anchor T₀ and one
t-parameter of P, not repeated origin-origin chords. -/
theorem kernel_torsion_zero (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (P : WP F) (hP : specialize V h2 P=Point.zero) (m : ℕ)
    (hm : residue V (m:V) ≠ 0) (hmP : m • P=(0:WP F)) : P=Point.zero := by
  by_contra hNonzero
  obtain ⟨T⟩ := from_kernel V h2 P hP
  have ht : T.t≠0 := fun h => hNonzero (point_zero_of_chart_zero V h2 hP T h)
  have hE : (V.subtype (0:V))^2=(V.subtype (0:V))^3-V.subtype (0:V) := by simp
  let hn₀ := nonsing_of_equation hF hE
  let O₀ : WP F := Point.some (V.subtype (0:V)) (V.subtype (0:V)) hn₀
  have step (n : ℕ) : ∃ A d : V, residue V A=0 ∧ residue V d= -(n:ResidueField V) ∧
      ∃ hn : (curve F).toAffine.Nonsingular (V.subtype A) (V.subtype (T.t*d)),
        n • P+O₀=Point.some (V.subtype A) (V.subtype (T.t*d)) hn := by
    induction n with
    | zero =>
      have hW : V.subtype (T.t*(0:V))=V.subtype (0:V) := by rw [mul_zero]
      have hn : (curve F).toAffine.Nonsingular (V.subtype (0:V)) (V.subtype (T.t*(0:V))) := by
        rw [hW]
        exact hn₀
      refine ⟨0,0,by simp,by simp,hn,?_⟩
      rw [zero_nsmul,zero_add]
      exact pointTransport rfl hW.symm
    | succ n ih =>
      obtain ⟨A,d,hA,hd,hQ,hSum⟩ := ih
      obtain ⟨K,hXY,hAdd⟩ := mixed_stock_coordinates V h2 P A (T.t*d) hQ hP hNonzero T
      obtain ⟨e,hY,he⟩ := ordinate_coefficient V K T.smallT hA
      have hn : (curve F).toAffine.Nonsingular (V.subtype K.X) (V.subtype (T.t*e)) := by
        rw [←hY]
        exact hXY
      refine ⟨K.X,e,K.x_residue.trans hA,?_,hn,?_⟩
      · rw [he,hd,Nat.cast_succ]; ring
      · have hSteps : (Nat.succ n) • P+O₀=P+(n • P+O₀) := by
          rw [Nat.succ_eq_add_one,add_nsmul,one_nsmul]
          ac_rfl
        rw [hSteps,hSum,hAdd]
        have hy : V.subtype K.Y=V.subtype (T.t*e) := congrArg V.subtype hY
        exact pointTransport rfl hy
  obtain ⟨A,d,_,hd,hQ,hSum⟩ := step m
  rw [hmP,zero_add] at hSum
  have hy : V.subtype (0:V)=V.subtype (T.t*d) := by
    have h := congrArg ordinate hSum
    change V.subtype (0:V)=V.subtype (T.t*d) at h
    exact h
  have hh : T.t*d=0 := V.subtype_injective hy.symm
  have hd0 : d=0 := (mul_eq_zero.mp hh).resolve_left ht
  have hzero : (m:ResidueField V)=0 := neg_eq_zero.mp (by simpa only [hd0,map_zero] using hd.symm)
  exact hm ((map_natCast (residue V) m).trans hzero)

/-- Exact same actual additive reduction, injective on all torsion
whose level does not vanish in the residue field. -/
theorem specializeHom_injective_on_torsion (hF : (2:F) ≠ 0)
    (h2 : (2:ResidueField V) ≠ 0) (m : ℕ) (hm : residue V (m:V) ≠ 0) :
    Set.InjOn (specializeHom V hF h2) {P | m • P=(0:WP F)} := by
  intro P hP Q hQ hEq
  change m • P=0 at hP
  change m • Q=0 at hQ
  have hKernel := specialize_fibre_sub V hF h2 P Q hEq
  have hTorsion : m • (P-Q)=0 := by rw [nsmul_sub,hP,hQ,sub_zero]
  have hz : P-Q=0 := kernel_torsion_zero V hF h2 (P-Q) hKernel m hm hTorsion
  exact sub_eq_zero.mp hz

end ActualGaussianWeberFiniteAnchorTorsion318
