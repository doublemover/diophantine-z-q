module
public import ActualGaussianWeberHenselianPointMap318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import all Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public section
noncomputable section

namespace ActualGaussianWeberOrdinarySlope318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318

variable {F : Type*} [Field F] (V : ValuationSubring F)
local notation "E" => (curve F).toAffine
local notation "E₀" => (curve (ResidueField V)).toAffine

theorem literal_negY (K : Type*) [CommRing K] (x y : K) :
    (curve K).toAffine.negY x y= -y := by simp [negY,curve,toAffine]

theorem literal_addX (K : Type*) [CommRing K] (x y s : K) :
    (curve K).toAffine.addX x y s=s^2-x-y := by simp [addX,curve,toAffine]

theorem literal_addY (K : Type*) [CommRing K] (x y v s : K) :
    (curve K).toAffine.addY x y v s=
      -(s*((curve K).toAffine.addX x y s-x)+v) := by
  rw [addY,literal_negY,negAddY]

theorem literal_tangent_slope {K : Type*} [Field K] [DecidableEq K] {a b c d : K}
    (hac : a=c) (h : b≠ -d) :
    (curve K).toAffine.slope a c b d=(3*a^2-1)/(2*b) := by
  have hn : b≠(curve K).toAffine.negY c d := by simpa only [literal_negY] using h
  rw [slope_of_Y_ne hac hn,literal_negY]
  simp only [curve,toAffine,mul_zero,zero_mul,add_zero,sub_zero]
  congr 1 <;> ring

theorem ratio_over_residue_unit (n d : V) (hd : residue V d≠0) :
    ∃ s : V, V.subtype s=V.subtype n/V.subtype d ∧
      residue V s=residue V n/residue V d := by
  obtain ⟨u,hu⟩ := (residue_ne_zero_iff_isUnit d).mp hd
  let s : V := n*(↑u⁻¹:V)
  have hE : s*d=n := by
    rw [←hu]
    change (n*(↑u⁻¹:V))*(u:V)=n
    rw [mul_assoc,u.inv_mul,mul_one]
  have hDF : V.subtype d≠0 := by
    intro H
    have e : d=0 := V.subtype_injective (H.trans (map_zero _).symm)
    exact hd (by rw [e,map_zero])
  exact ⟨s,(eq_div_iff hDF).mpr (by simpa only [map_mul] using congrArg V.subtype hE),
    (eq_div_iff hd).mpr (by simpa only [map_mul] using congrArg (residue V) hE)⟩

variable [DecidableEq F] [DecidableEq (ResidueField V)]

structure Lift (a b c d : V) where
  s : V
  generic_ne : ¬ (V.subtype a=V.subtype c ∧ V.subtype b=E.negY (V.subtype c) (V.subtype d))
  residue_ne : ¬ (residue V a=residue V c ∧ residue V b=E₀.negY (residue V c) (residue V d))
  generic : V.subtype s=E.slope (V.subtype a) (V.subtype c) (V.subtype b) (V.subtype d)
  residual : residue V s=E₀.slope (residue V a) (residue V c) (residue V b) (residue V d)

/-- On a finite pair whose reductions are not opposite, the actual
generic slope lies in the valuation ring and reduces to the actual
residue slope. Same residual x can be either a true generic secant
or a tangent, and both reduce to the same stock tangent. -/
theorem lift_of_nonopposite (a b c d : V)
    (he₁ : b^2=a^3-a) (he₂ : d^2=c^3-c)
    (hN : ¬(residue V a=residue V c ∧ residue V b= -(residue V d))) :
    Nonempty (Lift V a b c d) := by
  have hRN : ¬(residue V a=residue V c ∧ residue V b=E₀.negY (residue V c) (residue V d)) := by
    simpa only [literal_negY] using hN
  have hFN : ¬(V.subtype a=V.subtype c ∧ V.subtype b=E.negY (V.subtype c) (V.subtype d)) := by
    rintro ⟨hx,hy⟩
    rw [literal_negY] at hy
    have he : b= -d := V.subtype_injective (by simpa only [map_neg] using hy)
    exact hN ⟨congrArg (residue V) (V.subtype_injective hx),by rw [he,map_neg]⟩
  by_cases hX : residue V a=residue V c
  · have hY : residue V b=residue V d := by
      have e₁ := equation_in_residue V a b he₁
      have e₂ := equation_in_residue V c d he₂
      have ex : (residue V b-residue V d)*(residue V b+residue V d)=0 := by
        rw [hX] at e₁
        linear_combination e₁-e₂
      have hsum : residue V b+residue V d≠0 := by
        intro H
        apply hN
        exact ⟨hX,by linear_combination H⟩
      exact sub_eq_zero.mp ((mul_eq_zero.mp ex).resolve_right hsum)
    let N : V := a^2+a*c+c^2-1
    have hDs : residue V (b+d)≠0 := by
      rw [map_add]
      intro H
      apply hN
      exact ⟨hX,by linear_combination H⟩
    obtain ⟨s,hSF,hSR⟩ := ratio_over_residue_unit V N (b+d) hDs
    refine ⟨⟨s,hFN,hRN,?_,?_⟩⟩
    · have hFa : V.subtype (b+d)≠0 := by
        intro H
        apply hDs
        have h := V.subtype_injective (H.trans (map_zero _).symm)
        rw [h,map_zero]
      rw [hSF]
      by_cases ex : V.subtype a=V.subtype c
      · have ey : V.subtype b=V.subtype d := by
          have hsq : (V.subtype b)^2=(V.subtype d)^2 := by
            have e₁ := congrArg V.subtype he₁
            have e₂ := congrArg V.subtype he₂
            simp only [map_pow,map_sub] at e₁ e₂
            rw [ex] at e₁
            exact e₁.trans e₂.symm
          have h0 : (V.subtype b-V.subtype d)*(V.subtype b+V.subtype d)=0 := by
            linear_combination hsq
          have h1 : V.subtype b+V.subtype d≠0 := by simpa only [map_add] using hFa
          exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right h1)
        have hT : V.subtype b≠ -(V.subtype d) := fun H =>
          hFN ⟨ex,by rw [literal_negY]; exact H⟩
        rw [literal_tangent_slope ex hT]
        have hn : V.subtype N=3*(V.subtype a)^2-1 := by
          simp only [N,map_sub,map_add,map_pow,map_mul,map_one,←ex] <;> ring
        have hd : V.subtype (b+d)=2*V.subtype b := by
          simp only [map_add,←ey] <;> ring
        rw [hn,hd]
      · rw [slope_of_X_ne ex]
        apply (div_eq_div_iff hFa (sub_ne_zero.mpr ex)).mpr
        have hp : (b-d)*(b+d)=(a-c)*N := by
          change (b-d)*(b+d)=(a-c)*(a^2+a*c+c^2-1)
          linear_combination he₁-he₂
        have H := congrArg V.subtype hp
        simp only [map_sub,map_mul] at H ⊢
        linear_combination -H
    · rw [hSR,literal_tangent_slope hX (fun H => hN ⟨hX,H⟩)]
      have hn : residue V N=3*(residue V a)^2-1 := by
        simp only [N,map_sub,map_add,map_pow,map_mul,map_one,←hX] <;> ring
      have hd : residue V (b+d)=2*residue V b := by
        simp only [map_add,←hY] <;> ring
      rw [hn,hd]
  · have ex : V.subtype a≠V.subtype c :=
      fun H => hX (congrArg (residue V) (V.subtype_injective H))
    have hd : residue V (a-c)≠0 := by rw [map_sub]; exact sub_ne_zero.mpr hX
    obtain ⟨s,hSF,hSR⟩ := ratio_over_residue_unit V (b-d) (a-c) hd
    exact ⟨⟨s,hFN,hRN,
      by rw [slope_of_X_ne ex]; simpa only [map_sub] using hSF,
      by rw [slope_of_X_ne hX]; simpa only [map_sub] using hSR⟩⟩

end ActualGaussianWeberOrdinarySlope318
