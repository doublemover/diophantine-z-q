module
public import ScalarLocalValues318
public import InertHensel318
public section
namespace ScalarPlaceBridge318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open CompressedOrientation318 ScalarSource318 ScalarLocalValues318
set_option maxHeartbeats 0

/-- The two-place argument permits equal valuations: the inert case is
represented twice, giving residue degree2 without doubling normalization. -/
theorem two_place_source (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (vp:AddValuation ℚ (WithTop ℤ)) (v1 v2:AddValuation K (WithTop ℤ))
    (rat1:∀q:ℚ,v1 (pair q 0)=vp q) (rat2:∀q:ℚ,v2 (pair q 0)=vp q)
    (normLaw:∀x:K,vp (AnchorNorm318.norm x)=v1 x+v2 x)
    (hD1:v1 CompressedOrientation318.D=0) (hD2:v2 CompressedOrientation318.D=0)
    (R:ℤ) (hr:vp (r w)=R) (hRpos:0<R) (hR:Odd R)
    (hc:vp (114444:ℚ)=0) (h3:vp (3:ℚ)=0) (h17:vp (17:ℚ)=0) :
    0<v1 (fH w) ∧ 0<v2 (fH w) ∧
      ((16:WithTop ℤ)≤v1 (fR w/fH w) ∨ (16:WithTop ℤ)≤v2 (fR w/fH w)) := by
  obtain ⟨a,ha,haeven⟩ := source_fH_even S w source v1 hD1
  obtain ⟨b,hb,hbeven⟩ := source_fH_even S w source v2 hD2
  have hshift1 := shifted_value v1 (fH w) (pair (r w) 0) a R ha (by rw [rat1,hr]) haeven hR
  have hshift2 := shifted_value v2 (fH w) (pair (r w) 0) b R hb (by rw [rat2,hr]) hbeven hR
  have hN:vp (N w)=(min 0 (a-R)+min 0 (b-R):ℤ) := by
    rw [N_formula S w source,normLaw,hshift1,hshift2]
    norm_cast
  have hNbound := (ScalarPoleValuation318.source_bounds S w source vp R hr hRpos hR hc h3 h17).2.1
  rw [hN] at hNbound
  have hNi:-R<4*(min 0 (a-R)+min 0 (b-R)) := by exact_mod_cast hNbound
  obtain ⟨hapos,hbpos⟩ := split_positive a b R _ hRpos rfl hNi
  obtain ⟨c,hcval,hceven⟩ := source_fR_even S w source v1
  obtain ⟨d,hdval,hdeven⟩ := source_fR_even S w source v2
  have hratio1:v1 (fR w/fH w)=(c-a:ℤ) := by rw [v1.map_div,hcval,ha]; norm_cast
  have hratio2:v2 (fR w/fH w)=(d-b:ℤ) := by rw [v2.map_div,hdval,hb]; norm_cast
  obtain ⟨n,hn,hn15,hnorm⟩ := ScalarPoleValuation318.source_norm_ratio_bound
    S w source vp R hr hRpos hR hc h3 h17
  rw [normLaw,hratio1,hratio2] at hnorm
  have hsum:30≤(c-a)+(d-b) := by
    have hh:(c-a)+(d-b)=2*n := by exact_mod_cast hnorm
    omega
  have hor := split_ratio_rounding (c-a) (d-b) (hceven.sub haeven) (hdeven.sub hbeven) hsum
  refine ⟨?_,?_,?_⟩
  · rw [ha]; exact_mod_cast hapos
  · rw [hb]; exact_mod_cast hbpos
  · rw [hratio1,hratio2]
    exact hor.imp (fun h => WithTop.coe_le_coe.mpr h) (fun h => WithTop.coe_le_coe.mpr h)

variable (p:ℕ) [Fact p.Prime]

theorem correction_unit (hp2:¬p∣2) (hp3:¬p∣3) (hp11:¬p∣11) (hp17:¬p∣17) :
    ConcretePadic318.rationalPlace p (114444:ℚ)=0 := by
  apply ConcretePadic318.rational_nat_unit p 114444
  intro hd
  have he:(114444:ℕ)=2^2*3^2*11*17^2 := by norm_num
  rw [he] at hd
  rcases (Fact.out:p.Prime).dvd_mul.mp hd with hd|hd
  · rcases (Fact.out:p.Prime).dvd_mul.mp hd with hd|hd
    · rcases (Fact.out:p.Prime).dvd_mul.mp hd with hd|hd
      · exact hp2 ((Fact.out:p.Prime).dvd_of_dvd_pow hd)
      · exact hp3 ((Fact.out:p.Prime).dvd_of_dvd_pow hd)
    · exact hp11 hd
  · exact hp17 ((Fact.out:p.Prime).dvd_of_dvd_pow hd)

/-- Actual split valuation norm formula, extended from pairs to all elements. -/
theorem split_norm (rho:ℚ_[p]) (hr:rho^2=2) (x:K) :
    ConcretePadic318.rationalPlace p (AnchorNorm318.norm x)=
      ConcretePadic318.place p rho hr x+
      ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hr) x := by
  obtain ⟨a,b⟩ := x
  change ConcretePadic318.rationalPlace p (AnchorNorm318.norm (pair a b))=_
  rw [AnchorNorm318.norm_pair]
  exact (ConcretePadic318.norm_valuation p rho hr a b).symm

/-- The actual split-place scalar conclusion, before invoking any logarithm. -/
theorem split_source (rho:ℚ_[p]) (hrho:rho^2=2)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (R:ℤ) (hr:ConcretePadic318.rationalPlace p (r w)=R) (hRpos:0<R) (hR:Odd R)
    (hp2:¬p∣2) (hp3:¬p∣3) (hp7:¬p∣7) (hp11:¬p∣11) (hp17:¬p∣17) :
    0<ConcretePadic318.place p rho hrho (fH w) ∧
    0<ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hrho) (fH w) ∧
      ((16:WithTop ℤ)≤ConcretePadic318.place p rho hrho (fR w/fH w) ∨
      (16:WithTop ℤ)≤ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hrho) (fR w/fH w)) := by
  have hc := correction_unit p hp2 hp3 hp11 hp17
  have hD (s:ℚ_[p]) (hs:s^2=2):ConcretePadic318.place p s hs CompressedOrientation318.D=0 := by
    exact (SourcePadic318.discriminant_units _
      (SourcePadic318.place_nat_unit p s hs 2 hp2)
      (SourcePadic318.place_nat_unit p s hs 3 hp3)
      (SourcePadic318.place_nat_unit p s hs 7 hp7)).2
  exact two_place_source S w source _ _ _
    (ConcretePadic318.place_rational p rho hrho)
    (ConcretePadic318.place_rational p (-rho) (ConcretePadic318.negative_root p rho hrho))
    (split_norm p rho hrho) (hD rho hrho) (hD _ _) R hr hRpos hR hc
    (ConcretePadic318.rational_nat_unit p 3 hp3) (ConcretePadic318.rational_nat_unit p 17 hp17)

/-- Actual inert-place scalar depth, with rational normalization unchanged. -/
theorem inert_source (nonsquare:¬∃x:ZMod p,x^2=2)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (R:ℤ) (hr:ConcretePadic318.rationalPlace p (r w)=R) (hRpos:0<R) (hR:Odd R)
    (hp2:¬p∣2) (hp3:¬p∣3) (hp7:¬p∣7) (hp11:¬p∣11) (hp17:¬p∣17) :
    0<InertPlace318.place p nonsquare (fH w) ∧
      (16:WithTop ℤ)≤InertPlace318.place p nonsquare (fR w/fH w) := by
  let v:=InertPlace318.place p nonsquare
  have hD:v CompressedOrientation318.D=0 := by
    exact (SourcePadic318.discriminant_units v
      (InertPlace318.place_two p nonsquare)
      (InertSourceExclusion318.place_nat_unit p nonsquare 3 hp3)
      (InertSourceExclusion318.place_nat_unit p nonsquare 7 hp7)).2
  have hn (x:K):ConcretePadic318.rationalPlace p (AnchorNorm318.norm x)=v x+v x := by
    rw [InertPlace318.place_norm p nonsquare,two_nsmul]
  obtain ⟨hh,-,hor⟩ := two_place_source S w source _ v v
    (InertPlace318.place_rational p nonsquare) (InertPlace318.place_rational p nonsquare)
    hn hD hD R hr hRpos hR (correction_unit p hp2 hp3 hp11 hp17)
    (ConcretePadic318.rational_nat_unit p 3 hp3) (ConcretePadic318.rational_nat_unit p 17 hp17)
  exact ⟨hh,hor.elim id id⟩

/-- A scalar contact constructs an actual normalized place with positive
reciprocal abscissae for H and R and relative reciprocal depth at least16.
This is the complete valuation input to the separate order8 logarithm step. -/
theorem source_scalar_place
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (R:ℤ) (hr:ConcretePadic318.rationalPlace p (r w)=R) (hRpos:0<R) (hR:Odd R)
    (hp2:¬p∣2) (hp3:¬p∣3) (hp7:¬p∣7) (hp11:¬p∣11) (hp17:¬p∣17) :
    ∃v:AddValuation K (WithTop ℤ),
      (∀q:ℚ,v (pair q 0)=ConcretePadic318.rationalPlace p q) ∧
      0<v (fH w) ∧ 0<v (fR w) ∧ (16:WithTop ℤ)≤v (fR w/fH w) := by
  have hRpos' (v:AddValuation K (WithTop ℤ)) (hH:0<v (fH w))
      (hrel:(16:WithTop ℤ)≤v (fR w/fH w)) : 0<v (fR w) := by
    have he:(fR w/fH w)*fH w=fR w := div_mul_cancel₀ _ (CompressedPoint318.source_fH_ne S w source)
    rw [←he,v.map_mul]
    apply lt_of_lt_of_le hH
    simpa using add_le_add (le_trans (by norm_num:(0:WithTop ℤ)≤16) hrel) (le_refl (v (fH w)))
  by_cases hs:∃x:ZMod p,x^2=2
  · obtain ⟨rho,hrho⟩ := InertHensel318.square_root_lift p hp2 hs
    obtain ⟨hleft,hright,hdepth⟩ := split_source p rho hrho S w source R hr hRpos hR hp2 hp3 hp7 hp11 hp17
    rcases hdepth with hdepth|hdepth
    · exact ⟨ConcretePadic318.place p rho hrho,ConcretePadic318.place_rational p rho hrho,
        hleft,hRpos' _ hleft hdepth,hdepth⟩
    · exact ⟨ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hrho),
        ConcretePadic318.place_rational p (-rho) (ConcretePadic318.negative_root p rho hrho),
        hright,hRpos' _ hright hdepth,hdepth⟩
  · obtain ⟨hH,hdepth⟩ := inert_source p hs S w source R hr hRpos hR hp2 hp3 hp7 hp11 hp17
    exact ⟨InertPlace318.place p hs,InertPlace318.place_rational p hs,hH,hRpos' _ hH hdepth,hdepth⟩

end ScalarPlaceBridge318
#print axioms ScalarPlaceBridge318.two_place_source
#print axioms ScalarPlaceBridge318.split_source

#print axioms ScalarPlaceBridge318.inert_source
#print axioms ScalarPlaceBridge318.source_scalar_place
