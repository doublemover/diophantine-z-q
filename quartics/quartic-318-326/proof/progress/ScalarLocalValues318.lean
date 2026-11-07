module
public import ScalarPoleValuation318
public import InertPlace318
public section
namespace ScalarLocalValues318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay
open CompressedOrientation318 CompressedPoint318
set_option maxHeartbeats 0

/-- The abscissa value on the actual short Weierstrass curve is even.
The zero-ordinate case is permitted and requires no non-torsion premise. -/
theorem curve_x_even {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (x y D:F) (a:ℤ) (hx:v x=a) (hD:v D=0)
    (he:y^2=x^3-D*x) : Even a := by
  rcases Int.even_or_odd a with ha|ha
  · exact ha
  have ha0:a≠0 := by intro hz; subst a; norm_num at ha
  have hxx:v (x^2)=(2*a:ℤ) := by rw [v.map_pow,hx]; norm_cast
  have hdiff:v (x^2-D)=(min (2*a) 0:ℤ) := by
    rw [sub_eq_add_neg,v.map_add_of_distinct_val]
    · rw [v.map_neg,hxx,hD]; norm_cast
    · rw [v.map_neg,hxx,hD]; exact_mod_cast (show 2*a≠0 by omega)
  have hid:y^2=x*(x^2-D) := by linear_combination he
  have hval:v (y^2)=(a+min (2*a) 0:ℤ) := by
    rw [hid,v.map_mul,hx,hdiff]; norm_cast
  have hodd:Odd (a+min (2*a) 0) := by
    obtain ⟨j,hj⟩ := ha
    by_cases hh:0≤a
    · rw [min_eq_right (by omega)]; simpa using (show Odd a from ⟨j,hj⟩)
    · rw [min_eq_left (by omega)]; exact ⟨3*j+1,by omega⟩
  exact (SourcePole318.square_not_odd v y _ hval hodd).elim

theorem source_fH_even (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (v:AddValuation K (WithTop ℤ)) (hD:v CompressedOrientation318.D=0) :
    ∃a:ℤ,v (fH w)=a ∧ Even a := by
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp
    ((v.ne_top_iff).mpr (source_fH_ne S w source))
  have hx:v (xH w)=(-a:ℤ) := by simp only [xH,one_div,v.map_inv,←ha]; norm_cast
  have he:=curve_x_even v (xH w) (yH w) CompressedOrientation318.D (-a) hx hD
    (source_curve S w source)
  exact ⟨a,ha.symm,by simpa using he⟩

theorem source_fR_even (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (v:AddValuation K (WithTop ℤ)) :
    ∃a:ℤ,v (ScalarSource318.fR w)=a ∧ Even a := by
  have hn:= (RawAnchorNorm318.scalar_inverse_norm S w source).2.1
  have hr:RawAnchorNorm318.scalarRoot w≠0 := by
    intro hh; apply hn; simp [hh,AnchorNorm318.norm]
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr (inv_ne_zero hr))
  refine ⟨2*a,?_,⟨a,by ring⟩⟩
  rw [ScalarSource318.fR,v.map_pow,←ha]
  norm_cast

/-- An even local reciprocal value cannot equal the odd contact value. -/
theorem shifted_value {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (f r:F) (a R:ℤ) (hf:v f=a) (hr:v r=R) (ha:Even a) (hR:Odd R) :
    v (1+f/r)=(min 0 (a-R):ℤ) := by
  have hne:a-R≠0 := by obtain ⟨i,hi⟩:=ha; obtain ⟨j,hj⟩:=hR; omega
  have hdiv:v (f/r)=(a-R:ℤ) := by rw [v.map_div,hf,hr]; norm_cast
  rw [v.map_add_of_distinct_val]
  · rw [v.map_one,hdiv]; norm_cast
  · rw [v.map_one,hdiv]; exact_mod_cast Ne.symm hne

/-- The nonpositive summands of the norm force formality at both split places. -/
theorem split_positive (a b R n:ℤ)
    (hR:0<R) (hn:n=min 0 (a-R)+min 0 (b-R)) (hbound:-R<4*n) :
    0<a ∧ 0<b := by omega

/-- The single inert place has residue degree two, with unchanged normalization. -/
theorem inert_positive (a R n:ℤ)
    (_hR:0<R) (hn:n=2*min 0 (a-R)) (hbound:-R<4*n) : 0<a := by omega

/-- Evenness supplies the final rounding from average norm order15 to16. -/
theorem split_ratio_rounding (a b:ℤ) (ha:Even a) (hb:Even b) (hsum:30≤a+b) :
    16≤a ∨ 16≤b := LocalSoundness318.scalar_even_rounding a b ha hb hsum

theorem inert_ratio_rounding (a:ℤ) (ha:Even a) (hsum:30≤2*a) : 16≤a := by
  obtain ⟨j,hj⟩:=ha
  omega

end ScalarLocalValues318
#print axioms ScalarLocalValues318.curve_x_even
#print axioms ScalarLocalValues318.source_fH_even
#print axioms ScalarLocalValues318.source_fR_even
#print axioms ScalarLocalValues318.shifted_value
