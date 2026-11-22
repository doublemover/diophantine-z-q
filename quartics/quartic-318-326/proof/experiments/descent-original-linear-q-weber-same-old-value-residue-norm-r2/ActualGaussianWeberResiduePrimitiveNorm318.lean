module
public import ActualGaussianWeberActualPointFrob318
public import ActualGaussianWeberGaussianScalarCore318
public import ActualGaussianWeberFiniteAnchorTorsion318
public import ActualGaussianWeberPrimitivePointNorm318
public import ActualGaussianWeberOldIntegralValueContraction318
public section
noncomputable section

namespace ActualGaussianWeberResiduePrimitiveNorm318

open NumberField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberActualLocalizedFrob318
open ActualGaussianWeberActualPointFrob318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberPlaceEquivariance318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberStockReductionAdd318
open ActualGaussianWeberReductionCoordinates318 ActualGaussianWeberFiniteAnchorTorsion318
open ActualGaussianWeberSameValueOrbit318 ActualGaussianWeberPrimitivePointNorm318
open ActualGaussianWeberNamedLocalInclusion318 ActualGaussianWeberOldIntegralValueContraction318

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L] [DecidableEq L]
variable (W : IntermediateField Base L) [NumberField W]
variable (v : HeightOneSpectrum (𝓞 W)) (w : HeightOneSpectrum (𝓞 L))
variable [DecidableEq (ResidueField (AtPlace L w))]
variable {p : ℕ} [Fact p.Prime]

/-- Isolated same-point norm in the literal residue field. The old
Weber value lives in the already named W and its old v-residue
field is p-fixed. No arithmetic automorphism of L or unramifiedness
assumption is used. The same-point premise is exactly the signed
primary comparison, not an orbit statement or a new lift. -/
theorem even_norm_at_same_old_residue_value
    (a b : ℤ) (hN : a^2+b^2=(p:ℤ)) (h₂ : (2:ZMod p)≠0)
    (hUnder : SignedAt L w (rootOf (p:=p) a b) (rootOf_sq (p:=p) a b hN))
    (hwv : SameContraction L W v w)
    (hSplit : ∀ r : (𝓞 W) ⧸ v.asIdeal, r^p=r)
    (M : ℕ) (hEven : Even M) (hM : ¬p∣M) (P : WP L) (hP : M • P=0)
    (hPrimitive :
      letI := integralAlgebra (algebraMap Base L)
      let V := AtPlace L w
      let i := integralOverI (L:=L) w
      let hi := integralOverI_sq (L:=L) w
      ∀ c d : ℤ, c • P+d • turn (by norm_num : (2:L)≠0) (V.subtype i)
        (chosen_square_generic V i hi) P=0 → (M:ℤ)∣c ∧ (M:ℤ)∣d)
    (z : W) (hz : squaredAbscissa P=some (algebraMap W L z))
    (hSamePointResidual :
      letI := integralAlgebra (algebraMap Base L)
      let V := AtPlace L w
      let j := rootOf (p:=p) a b
      let hj := rootOf_sq (p:=p) a b hN
      let hR := residue_two_ne (L:=L) w j hj hUnder h₂
      let i := integralOverI (L:=L) w
      let hi := integralOverI_sq (L:=L) w
      onCurvePoint (residueArithmeticFrob L w j hj hUnder) hR (specialize V hR P)=
        gaussian hR (residue V i) (chosen_square_residue V i hi) a b (specialize V hR P)) :
    2*(M:ℤ)∣(p:ℤ)-1 := by
  letI := integralAlgebra (algebraMap Base L)
  let V := AtPlace L w
  let K := ResidueField V
  let j := rootOf (p:=p) a b
  let hj := rootOf_sq (p:=p) a b hN
  let hL : (2:L)≠0 := by norm_num
  let hR : (2:K)≠0 := residue_two_ne (L:=L) w j hj hUnder h₂
  let i : V := integralOverI (L:=L) w
  let hi : i^2= -1 := integralOverI_sq (L:=L) w
  let iL := V.subtype i
  let hiL := chosen_square_generic V i hi
  let iR := residue V i
  let hiR := chosen_square_residue V i hi
  let ρ := specializeHom V hL hR
  let Q : WP K := specialize V hR P
  let σ := residueArithmeticFrob L w j hj hUnder
  have hm : residue V (M:V)≠0 := modulus_nonzero (L:=L) w j hj hUnder M hM
  have hTurn : ρ (turn hL iL hiL P)=turn hR iR hiR Q :=
    specialize_turn V hL hR i hi P
  have hPrimQ (c d : ℤ) (h : c • Q+d • turn hR iR hiR Q=0) :
      (M:ℤ)∣c ∧ (M:ℤ)∣d := by
    let G := gaussian hL iL hiL c d
    have hT : M • G P=0 := by rw [←map_nsmul,hP,map_zero]
    have hRed : specialize V hR (G P)=Point.zero := by
      change ρ (c • P+d • turn hL iL hiL P)=(0:WP K)
      rw [map_add,map_zsmul,map_zsmul,hTurn]
      exact h
    have hZero : G P=Point.zero := kernel_torsion_zero V hL hR (G P) hRed M hm hT
    exact hPrimitive c d hZero
  have hP0 : P≠(0:WP L) := by
    intro he
    have hz₀ := hz
    rw [he] at hz₀
    change (none : Option L)=some (algebraMap W L z) at hz₀
    cases hz₀
  have hQ0 : Q≠(0:WP K) := by
    intro h
    have hZero : specialize V hR P=Point.zero := h
    exact hP0 (kernel_torsion_zero V hL hR P hZero M hm hP)
  have hAffine : ∃ x y : L, ∃ hn : (curve L).toAffine.Nonsingular x y,
      P=Point.some x y hn := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y hn => exact ⟨x,y,hn,rfl⟩
  obtain ⟨x,y,hn,hShape⟩ := hAffine
  have hx : x∈V := by
    by_contra hOut
    apply hQ0
    change specialize V hR P=Point.zero
    rw [hShape]
    exact (specialize_some_eq_zero V hR hn).mpr hOut
  have hy : y∈V := integral_y V ((literal_equation x y).mp hn.1) hx
  let A : V := ⟨x,hx⟩
  let B : V := ⟨y,hy⟩
  obtain ⟨hnR,hRed⟩ := reduction_through_coordinates V hR hn A B rfl rfl
  have hQShape : Q=Point.some (residue V A) (residue V B) hnR := by
    change specialize V hR P=_
    rw [hShape]
    exact hRed
  have hxz : V.subtype (A^2)=algebraMap W L z := by
    rw [map_pow]
    change x^2=algebraMap W L z
    have h := hz
    rw [hShape] at h
    change some (x^2)=some (algebraMap W L z) at h
    exact Option.some.inj h
  have hPower : ((residue V A)^2)^p=(residue V A)^2 := by
    have h := upper_residue_pow_fixed_of_old_value L W v w hwv p hSplit z (A^2) hxz
    simpa only [map_pow] using h
  have hFix : σ ((residue V A)^2)=(residue V A)^2 := by
    change residueArithmeticFrob L w j hj hUnder ((residue V A)^2)=(residue V A)^2
    unfold residueArithmeticFrob
    exact hPower
  have hSame : onCurvePoint σ hR Q=gaussian hR iR hiR a b Q := hSamePointResidual
  have hValue : squaredAbscissa (a • Q+b • turn hR iR hiR Q)=squaredAbscissa Q := by
    change squaredAbscissa (gaussian hR iR hiR a b Q)=squaredAbscissa Q
    rw [←hSame,hQShape]
    unfold onCurvePoint
    change some ((σ (residue V A))^2)=some ((residue V A)^2)
    rw [←map_pow,hFix]
  have hEven' : Even (M:ℤ) := by
    obtain ⟨u,hu⟩ := hEven
    exact ⟨(u:ℤ),by exact_mod_cast hu⟩
  exact norm_one_of_fixed_primitive_value hR iR hiR (M:ℤ) hEven' Q hPrimQ a b (p:ℤ) hN hValue

end ActualGaussianWeberResiduePrimitiveNorm318
