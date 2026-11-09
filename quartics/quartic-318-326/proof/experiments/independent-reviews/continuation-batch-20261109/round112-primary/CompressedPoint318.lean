module
public import SelectedContact318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
namespace CompressedPoint318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The compression polynomial reconstructs an honest affine ordinate. -/
theorem compression_identity {F : Type*} [Field F] (f s k m D : F)
    (hP : m^2=k^4-D)
    (hF : 1=k^2*(f+f*s^2)+2*m*(f*s)+D*(f*s)^2) :
    f*(m+k^2*s+D*f*s)^2=k^2*(1-D*f^2) := by
  linear_combination f*hP - (k^2+D*f)*hF

theorem constant_equation : m^2=k^4-D := by
  ext <;> norm_num [m,k,D,pair,pow_succ]

theorem k_ne : k≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [k,pair] at hh

theorem source_fH_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    fH w≠0 := by
  obtain ⟨ht,hg⟩ := source_products S w source
  have he := (source_relations S w source).2
  intro hf
  simp [hf,ht,hg] at he

theorem source_ordinate_identity (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) :
    fH w*(anchorA w)^2=k^2*(1-D*(fH w)^2) := by
  obtain ⟨ht,hg⟩ := source_products S w source
  have he := (source_relations S w source).2
  rw [ht,hg] at he
  have hh := compression_identity (fH w) (shift w) k m D constant_equation he
  simpa only [anchorA,ht,mul_assoc] using hh

@[expose] def xH (w : Assignment) : K := 1/fH w
@[expose] def yH (w : Assignment) : K := anchorA w/(k*fH w)
@[expose] def zH (w : Assignment) : K := -k/anchorA w
@[expose] def E : WeierstrassCurve.Affine K := ⟨0,0,0,-D,0⟩

theorem source_curve (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (yH w)^2=(xH w)^3-D*xH w := by
  have hf := source_fH_ne S w source
  have hh := source_ordinate_identity S w source
  dsimp [xH,yH]
  field_simp [hf,k_ne]
  linear_combination hh

/-- The reconstructed formal coordinate has exactly half the inverse-abscissa
valuation. The depth and its integrality follow from the source equation. -/
theorem ordinate_depth {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (f A k D : F) (hf0 : f≠0) (hk : v k=0) (hD : 0≤v D)
    (he : f*A^2=k^2*(1-D*f^2)) (hf : (8:WithTop ℤ)≤v f) :
    A≠0 ∧ ∃ r:ℤ, 4≤r ∧ v f=(2*r:ℤ) ∧ v A=(-r:ℤ) ∧
      v (-k/A)=(r:ℤ) := by
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf0)
  have ha8 : 8≤a := by rw [←ha] at hf; exact WithTop.coe_le_coe.mp hf
  have hpos : 0<v f := lt_of_lt_of_le (by norm_num) hf
  have hterm : 0<v (D*f^2) := by
    rw [v.map_mul,v.map_pow]
    have hh : 0<2 • v f := by
      rw [←ha]
      have he : 2 • (a:WithTop ℤ)=((2*a:ℤ):WithTop ℤ) := by simp only [two_nsmul]; norm_cast; ring
      rw [he]
      exact_mod_cast (show (0:ℤ)<2*a by omega)
    exact lt_of_lt_of_le hh (by simpa using add_le_add hD (le_refl (2 • v f)))
  have hunit : v (1-D*f^2)=0 := by
    rw [v.map_sub_eq_of_lt_left (by simpa using hterm),v.map_one]
  have hval := congrArg v he
  rw [v.map_mul,v.map_pow,v.map_mul,v.map_pow,hk,hunit] at hval
  simp only [nsmul_zero,zero_add] at hval
  have hA0 : A≠0 := by
    intro hz
    simp [hz,two_nsmul] at hval
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hA0)
  rw [←ha,←hb] at hval
  have hab : a+2*b=0 := by exact_mod_cast hval
  refine ⟨hA0,-b,by omega,?_,?_,?_⟩
  · rw [←ha]; congr 1; omega
  · simpa using hb.symm
  · rw [v.map_div,v.map_neg,hk,←hb]
    simp

theorem source_formal_depth (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hD : 0≤v D) (hf : (8:WithTop ℤ)≤v (fH w)) :
    anchorA w≠0 ∧ ∃ r:ℤ, 4≤r ∧ v (fH w)=(2*r:ℤ) ∧
      v (anchorA w)=(-r:ℤ) ∧ v (zH w)=(r:ℤ) ∧
      v (xH w)=(-2*r:ℤ) ∧ v (yH w)=(-3*r:ℤ) := by
  obtain ⟨hA,r,hr,hf',hA',hz⟩ := ordinate_depth v (fH w) (anchorA w) k D
    (source_fH_ne S w source) hk hD (source_ordinate_identity S w source) hf
  refine ⟨hA,r,hr,hf',hA',hz,?_,?_⟩
  · simp only [xH,v.map_div,v.map_one,hf']
    rw [←WithTop.coe_zero,←WithTop.LinearOrderedAddCommGroup.coe_sub]
    apply congrArg (fun x:ℤ => (x:WithTop ℤ))
    ring
  · simp only [yH,v.map_div,v.map_mul,hA',hk,hf',zero_add]
    rw [←WithTop.LinearOrderedAddCommGroup.coe_sub]
    apply congrArg (fun x:ℤ => (x:WithTop ℤ))
    ring

theorem source_formal_coordinate (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (hA : anchorA w≠0) :
    yH w≠0 ∧ zH w= -xH w/yH w := by
  have hf := source_fH_ne S w source
  refine ⟨div_ne_zero hA (mul_ne_zero k_ne hf),?_⟩
  dsimp [zH,xH,yH]
  field_simp [hf,k_ne,hA]

theorem source_nonsingular (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (hA : anchorA w≠0) :
    E.Nonsingular (xH w) (yH w) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simpa [E,sub_eq_add_neg] using source_curve S w source
  · right
    simpa [E] using mul_ne_zero (show (2:K)≠0 by norm_num)
      (source_formal_coordinate S w source hA).1

/-- The local source constructs an actual nonsingular Mathlib point together
with its exact formal-parameter depth. No abstract point-label interpretation
or formal-group valuation assertion is a premise. -/
theorem source_actual_point (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (v : AddValuation K (WithTop ℤ))
    (hk : v k=0) (hD : 0≤v D) (hf : (8:WithTop ℤ)≤v (fH w)) :
    ∃ (h : E.Nonsingular (xH w) (yH w)) (r:ℤ),
      (WeierstrassCurve.Affine.Point.some (xH w) (yH w) h : E.Point)≠0 ∧
      4≤r ∧ zH w= -xH w/yH w ∧ v (zH w)=(r:ℤ) ∧
      v (xH w)=(-2*r:ℤ) ∧ v (yH w)=(-3*r:ℤ) := by
  obtain ⟨hA,r,hr,hf',hA',hz,hx,hy⟩ := source_formal_depth S w source v hk hD hf
  refine ⟨source_nonsingular S w source hA,r,?_,hr,
    (source_formal_coordinate S w source hA).2,hz,hx,hy⟩
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

open ConcretePadic318 SourcePadic318 FiniteContact318
variable (p : ℕ) [Fact p.Prime]

theorem split_actual_point (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hgood : ¬p∣contactModulus) (hp41 : ¬p∣41)
    (hf : (8:WithTop ℤ)≤place p rho hr (fH w)) :
    ∃ (h : E.Nonsingular (xH w) (yH w)) (r:ℤ),
      (WeierstrassCurve.Affine.Point.some (xH w) (yH w) h : E.Point)≠0 ∧
      4≤r ∧ zH w= -xH w/yH w ∧ place p rho hr (zH w)=(r:ℤ) ∧
      place p rho hr (xH w)=(-2*r:ℤ) ∧ place p rho hr (yH w)=(-3*r:ℤ) := by
  have h2 := place_nat_unit p rho hr 2 (not_dvd_supported p hgood 2 (by norm_num [contactModulus]))
  have h3 := place_nat_unit p rho hr 3 (not_dvd_supported p hgood 3 (by norm_num [contactModulus]))
  have h7 := place_nat_unit p rho hr 7 (not_dvd_supported p hgood 7 (by norm_num [contactModulus]))
  have h41 := place_nat_unit p rho hr 41 hp41
  have hk := (good_constants (place p rho hr) h2 h41).1
  have hD : 0≤place p rho hr D := by
    have hh := (discriminant_units (place p rho hr) h2 h3 h7).2
    simpa only [D,hh] using (le_refl (0:WithTop ℤ))
  exact source_actual_point S w source _ hk hD hf

/-- Every actual contact of detector 0 constructs a finite elliptic point
at the very same selected place as all sixteen leaf bounds. -/
theorem source_contact0_point (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (RawWeights318.A0 S w)=a)
    (hf : rationalPlace p (RawWeights318.t0 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧ ∃ (sigma : ℚ_[p]) (hs : sigma^2=2)
      (h : E.Nonsingular (xH w) (yH w)) (r:ℤ),
      (sigma=rho ∨ sigma= -rho) ∧
      (WeierstrassCurve.Affine.Point.some (xH w) (yH w) h : E.Point)≠0 ∧
      4≤r ∧ zH w= -xH w/yH w ∧ place p sigma hs (zH w)=(r:ℤ) ∧
      place p sigma hs (xH w)=(-2*r:ℤ) ∧ place p sigma hs (yH w)=(-3*r:ℤ) ∧
      (∀x∈SourceContact318.inputs0 S w,(2*x.2.2:ℤ)≤place p sigma hs x.2.1) := by
  obtain ⟨hR,hb⟩ := SelectedContact318.source_contact0_selected p rho hr S w source a f j
    hgood hp17 hp41 hA hf hpos hodd
  refine ⟨hR,?_⟩
  rcases hb with ⟨hfH,ho,hb⟩|⟨hfH,ho,hb⟩
  · obtain ⟨h,r,hne,hr',hz,hzv,hx,hy⟩ := split_actual_point p rho hr S w source hgood hp41 hfH
    exact ⟨rho,hr,h,r,Or.inl rfl,hne,hr',hz,hzv,hx,hy,hb⟩
  · obtain ⟨h,r,hne,hr',hz,hzv,hx,hy⟩ := split_actual_point p (-rho) (negative_root p rho hr)
      S w source hgood hp41 hfH
    exact ⟨-rho,negative_root p rho hr,h,r,Or.inr rfl,hne,hr',hz,hzv,hx,hy,hb⟩

/-- Every actual contact of detector 1 constructs a finite elliptic point
at the very same selected place as all sixteen leaf bounds. -/
theorem source_contact1_point (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (RawWeights318.A1 S w)=a)
    (hf : rationalPlace p (RawWeights318.t1 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧ ∃ (sigma : ℚ_[p]) (hs : sigma^2=2)
      (h : E.Nonsingular (xH w) (yH w)) (r:ℤ),
      (sigma=rho ∨ sigma= -rho) ∧
      (WeierstrassCurve.Affine.Point.some (xH w) (yH w) h : E.Point)≠0 ∧
      4≤r ∧ zH w= -xH w/yH w ∧ place p sigma hs (zH w)=(r:ℤ) ∧
      place p sigma hs (xH w)=(-2*r:ℤ) ∧ place p sigma hs (yH w)=(-3*r:ℤ) ∧
      (∀x∈SourceContact318.inputs1 S w,(2*x.2.2:ℤ)≤place p sigma hs x.2.1) := by
  obtain ⟨hR,hb⟩ := SelectedContact318.source_contact1_selected p rho hr S w source a f j
    hgood hp17 hp41 hA hf hpos hodd
  refine ⟨hR,?_⟩
  rcases hb with ⟨hfH,ho,hb⟩|⟨hfH,ho,hb⟩
  · obtain ⟨h,r,hne,hr',hz,hzv,hx,hy⟩ := split_actual_point p rho hr S w source hgood hp41 hfH
    exact ⟨rho,hr,h,r,Or.inl rfl,hne,hr',hz,hzv,hx,hy,hb⟩
  · obtain ⟨h,r,hne,hr',hz,hzv,hx,hy⟩ := split_actual_point p (-rho) (negative_root p rho hr)
      S w source hgood hp41 hfH
    exact ⟨-rho,negative_root p rho hr,h,r,Or.inr rfl,hne,hr',hz,hzv,hx,hy,hb⟩

/-- Every actual contact of detector 2 constructs a finite elliptic point
at the very same selected place as all sixteen leaf bounds. -/
theorem source_contact2_point (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (RawWeights318.A2 S w)=a)
    (hf : rationalPlace p (RawWeights318.t2 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧ ∃ (sigma : ℚ_[p]) (hs : sigma^2=2)
      (h : E.Nonsingular (xH w) (yH w)) (r:ℤ),
      (sigma=rho ∨ sigma= -rho) ∧
      (WeierstrassCurve.Affine.Point.some (xH w) (yH w) h : E.Point)≠0 ∧
      4≤r ∧ zH w= -xH w/yH w ∧ place p sigma hs (zH w)=(r:ℤ) ∧
      place p sigma hs (xH w)=(-2*r:ℤ) ∧ place p sigma hs (yH w)=(-3*r:ℤ) ∧
      (∀x∈SourceContact318.inputs2 S w,(2*x.2.2:ℤ)≤place p sigma hs x.2.1) := by
  obtain ⟨hR,hb⟩ := SelectedContact318.source_contact2_selected p rho hr S w source a f j
    hgood hp17 hp41 hA hf hpos hodd
  refine ⟨hR,?_⟩
  rcases hb with ⟨hfH,ho,hb⟩|⟨hfH,ho,hb⟩
  · obtain ⟨h,r,hne,hr',hz,hzv,hx,hy⟩ := split_actual_point p rho hr S w source hgood hp41 hfH
    exact ⟨rho,hr,h,r,Or.inl rfl,hne,hr',hz,hzv,hx,hy,hb⟩
  · obtain ⟨h,r,hne,hr',hz,hzv,hx,hy⟩ := split_actual_point p (-rho) (negative_root p rho hr)
      S w source hgood hp41 hfH
    exact ⟨-rho,negative_root p rho hr,h,r,Or.inr rfl,hne,hr',hz,hzv,hx,hy,hb⟩

end
end CompressedPoint318
