module
public import GlobalSaturationHeight318
public import GlobalHeightPositivity318
public import GlobalSquareHalving318
public section
namespace GlobalSaturationLogic318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318
open GlobalSaturationHeight318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The exact rank-one, full-2-torsion, odd-index outcome of the global
2-isogeny descent. This is an explicit outstanding mathematical premise. -/
@[expose] def OddRankOneData : Prop :=
  ∃(G U:E.Point)(m:ℤ),U+U=0 ∧ R=m • G+U ∧ Odd m ∧
    ∀Q:E.Point,∃(n:ℤ)(V:E.Point),V+V=0 ∧ Q=n • G+V

/-- This intermediate statement will be discharged by the checked finite
certificate plus the explicit coefficient-height interface. -/
@[expose] def SmallHeightClassified : Prop :=
  ∀Q:E.Point,xHeight Q<Real.log 9 → Classified Q

theorem index_one_or_neg_one {H:E.Point→ℝ} (d:CanonicalData H)
    (coverage:SmallHeightClassified) (G U:E.Point) (m:ℤ)
    (hu:U+U=0) (hm:R=m • G+U) (hodd:Odd m) : m=1 ∨ m= -1 := by
  have hpos := GlobalHeightPositivity318.canonical_R_positive d
  by_contra hn
  have hm3 : 3≤|m| := by
    obtain ⟨k,hk⟩ := hodd
    push_neg at hn
    rcases le_total 0 m with hp|hm
    · rw [abs_of_nonneg hp]; omega
    · rw [abs_of_nonpos hm]; omega
  have hs := small_height_of_large_index d G U m hu hm hm3
  have hh : H G=0 ∨ H G=H R := classified_height d G (coverage G hs)
  have hR : H R=(m:ℝ)^2*H G := by rw [hm,d.torsion _ _ hu,d.zsmul]
  have hmreal : (3:ℝ)≤|(m:ℝ)| := by exact_mod_cast hm3
  have hsq : (9:ℝ)≤(m:ℝ)^2 := by nlinarith [sq_abs (m:ℝ)]
  rcases hh with hz|he
  · rw [hz,mul_zero] at hR; linarith
  · rw [he] at hR; nlinarith

theorem double_sub_multiple (U V:E.Point) (hu:U+U=0) (hv:V+V=0) (n:ℤ) :
    (V-n • U)+(V-n • U)=0 := by
  calc
    _ = (V+V)-n • (U+U) := by rw [zsmul_add]; abel
    _ = 0 := by rw [hu,hv]; simp only [zsmul_zero,sub_self]

/-- Saturation of the actual R, using the proved finite certificate and the
explicit remaining global descent/height interfaces. -/
theorem generated_mod_two_torsion {H:E.Point→ℝ} (d:CanonicalData H)
    (coverage:SmallHeightClassified) (rank:OddRankOneData) :
    ∀Q:E.Point,∃(n:ℤ)(U:E.Point),U+U=0 ∧ Q=n • R+U := by
  obtain ⟨G,U,m,hu,hm,hodd,hgen⟩ := rank
  have hm1 := index_one_or_neg_one d coverage G U m hu hm hodd
  intro Q
  obtain ⟨n,V,hv,hq⟩ := hgen Q
  rcases hm1 with rfl|rfl
  · simp only [one_zsmul] at hm
    refine ⟨n,V-n • U,double_sub_multiple U V hu hv n,?_⟩
    rw [hm,zsmul_add,hq]; abel
  · simp only [neg_one_zsmul] at hm
    refine ⟨-n,V-(-n) • U,double_sub_multiple U V hu hv (-n),?_⟩
    rw [hm,zsmul_add,hq]; simp only [zsmul_neg,neg_zsmul,neg_neg]; abel

/-- The displayed local generator P=2R generates all square-abscissa
points once the precise global descent/height facts have been supplied. -/
theorem square_point_generation {H:E.Point→ℝ} (d:CanonicalData H)
    (coverage:SmallHeightClassified) (rank:OddRankOneData)
    (dual:GlobalSquareHalving318.DualSquareAbscissa) : RawGroupAnchor318.SquarePointGeneration := by
  intro h j hj
  obtain ⟨Q,hq⟩ := GlobalSquareHalving318.square_halving dual h j hj
  obtain ⟨n,U,hu,he⟩ := generated_mod_two_torsion d coverage rank Q
  refine ⟨n,?_⟩
  calc
    n • P = n • R+n • R := by rw [←double_R,zsmul_add]
    _ = (n • R+U)+(n • R+U) := by
      rw [show (n • R+U)+(n • R+U)=(n • R+n • R)+(U+U) by abel,hu,add_zero]
    _ = Q+Q := by rw [←he]
    _ = _ := hq

end
end GlobalSaturationLogic318
