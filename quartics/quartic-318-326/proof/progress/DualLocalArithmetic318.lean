module
public import FiniteScale318
public import GlobalSquareHalving318
public import ScalarLocalValues318
public section
namespace DualLocalArithmetic318
open ConcreteG8Domain LocalGenerator318
set_option maxHeartbeats 0

/-- Every nonzero dual abscissa is positive at each actual real embedding. -/
theorem dual_real_positive (X Y:K) (he:Y^2=X^3+4*D*X) (hX:X≠0)
    (s:ℝ) (hs:s^2=2) : 0<FiniteScale318.realPlace s hs X := by
  let e:=FiniteScale318.realPlace s hs
  have hd:0<e D := lt_trans (by norm_num) (FiniteScale318.D_real_gt_one s hs)
  have hx:e X≠0 := fun hh=>hX (e.injective (by simpa using hh))
  have hh:=congrArg e he
  simp only [map_pow,map_add,map_mul,map_ofNat] at hh
  have hp:0<(e X)^2+4*e D := by nlinarith [sq_nonneg (e X)]
  have hm:0≤e X*((e X)^2+4*e D) := by nlinarith [sq_nonneg (e Y)]
  exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_right hp).mp hm) (Ne.symm hx)

/-- At a place where the coefficient of X has value divisible by4, an odd
abscissa value gives an odd noncancelling minimum and is impossible. -/
theorem dual_even_of_coefficient_four {F:Type*} [Field F]
    (v:AddValuation F (WithTop ℤ)) (X Y A:F) (m k:ℤ)
    (hX:v X=m) (hA:v A=(4*k:ℤ)) (he:Y^2=X^3+A*X) : Even m := by
  rcases Int.even_or_odd m with hm|hm
  · exact hm
  have hne:3*m≠4*k+m := by obtain ⟨j,hj⟩:=hm; omega
  have hleft:v (X^3)=(3*m:ℤ) := by rw [v.map_pow,hX]; norm_cast
  have hright:v (A*X)=(4*k+m:ℤ) := by rw [v.map_mul,hA,hX]; norm_cast
  have hsum:v (Y^2)=(min (3*m) (4*k+m):ℤ) := by
    rw [he,v.map_add_of_distinct_val]
    · rw [hleft,hright]; norm_cast
    · rw [hleft,hright]; exact_mod_cast hne
  have hodd:Odd (min (3*m) (4*k+m)) := by
    obtain ⟨j,hj⟩:=hm
    by_cases hh:3*m≤4*k+m
    · rw [min_eq_left hh]; exact ⟨3*j+1,by omega⟩
    · rw [min_eq_right (by omega)]; exact ⟨2*k+j,by omega⟩
  exact (SourcePole318.square_not_odd v Y _ hsum hodd).elim

/-- All actual good finite valuations with 2,D units have even dual X-value. -/
theorem dual_good_even (v:AddValuation K (WithTop ℤ)) (X Y:K) (m:ℤ)
    (hX:v X=m) (h2:v (2:K)=0) (hD:v D=0) (he:Y^2=X^3+4*D*X) : Even m := by
  apply dual_even_of_coefficient_four v X Y (4*D) m 0 hX _ he
  have hfour:(4:K)=2^2 := by norm_num
  rw [v.map_mul,hfour,v.map_pow,h2,hD]
  norm_num

/-- The actual normalized ramified dyadic valuation has v(4D)=4. -/
theorem dual_two_even (X Y:K) (m:ℤ) (hX:RamifiedTwo318.place X=m)
    (he:Y^2=X^3+4*D*X) : Even m := by
  apply dual_even_of_coefficient_four RamifiedTwo318.place X Y (4*D) m 1 hX _ he
  have hfour:(4:K)=2^2 := by norm_num
  rw [RamifiedTwo318.place.map_mul,hfour,RamifiedTwo318.place.map_pow,
    RamifiedTwo318.place_two,RamifiedTwo318.place_D]
  norm_num [two_nsmul]

/-- At delta, all values except the exceptional odd value1 are already
forced even. The residue obstruction at value1 remains a separate step. -/
theorem dual_delta_even_unless_one {F:Type*} [Field F]
    (v:AddValuation F (WithTop ℤ)) (X Y A:F) (m:ℤ)
    (hX:v X=m) (hA:v A=2) (he:Y^2=X^3+A*X) : Even m ∨ m=1 := by
  rcases Int.even_or_odd m with hm|hm
  · exact Or.inl hm
  by_cases hm1:m=1
  · exact Or.inr hm1
  have hne:3*m≠2+m := by omega
  have hleft:v (X^3)=(3*m:ℤ) := by rw [v.map_pow,hX]; norm_cast
  have hright:v (A*X)=(2+m:ℤ) := by rw [v.map_mul,hA,hX]; norm_cast
  have hsum:v (Y^2)=(min (3*m) (2+m):ℤ) := by
    rw [he,v.map_add_of_distinct_val]
    · rw [hleft,hright]; norm_cast
    · rw [hleft,hright]; exact_mod_cast hne
  have hodd:Odd (min (3*m) (2+m)) := by
    obtain ⟨j,hj⟩:=hm
    by_cases hh:3*m≤2+m
    · rw [min_eq_left hh]; exact ⟨3*j+1,by omega⟩
    · rw [min_eq_right (by omega)]; exact ⟨j+1,by omega⟩
  exact (SourcePole318.square_not_odd v Y _ hsum hodd).elim

/-- The exceptional valuation1 is impossible as soon as the actual local
residue computation proves u²+4 a unit. -/
theorem dual_delta_exception {F:Type*} [Field F]
    (v:AddValuation F (WithTop ℤ)) (X Y delta:F)
    (hd:delta≠0) (hvd:v delta=1) (hX:v X=1)
    (hu:v ((X/delta)^2+4)=0) (he:Y^2=X^3+4*delta^2*X) : False := by
  have hid:Y^2=delta^3*(X/delta)*((X/delta)^2+4) := by
    field_simp [hd]
    linear_combination he
  have hval:v (Y^2)=(3:ℤ) := by
    rw [hid,v.map_mul,v.map_mul,v.map_pow,v.map_div,hvd,hX,hu]
    norm_num
  exact SourcePole318.square_not_odd v Y 3 hval (by decide)

/-- Away from2 and7, D is a unit without excluding the prime3. -/
theorem D_unit_away_two_seven (v:AddValuation K (WithTop ℤ))
    (h2:v (2:K)=0) (h7:v (7:K)=0) : v D=0 := by
  have hi0:i≠0 := by intro h; have hh:=congrArg QuadraticAlgebra.im h; norm_num [i,pair] at hh
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hi0)
  have hh:=congrArg v i_square
  rw [v.map_pow,←ha,h2] at hh
  have ha0:a=0 := by
    have he:2*a=0 := by exact_mod_cast hh
    omega
  have hi:v i=0 := by simpa [ha0] using ha.symm
  have h3:0≤v (3:K) := CompressedOrientation318.nat_nonnegative v 3
  have hminus:0≤v (3-i) := v.map_le_sub h3 (by rw [hi])
  have hplus:0≤v (3+i) := v.map_le_add h3 (by rw [hi])
  have hprod:(3-i)*(3+i)=(7:K) := by linear_combination -i_square
  have he:=congrArg v hprod
  rw [v.map_mul,h7] at he
  have hm:v (3-i)≤0 := by
    calc
      v (3-i)=v (3-i)+0 := by simp
      _≤v (3-i)+v (3+i) := add_le_add (le_refl _) hplus
      _=0 := he
  rw [D,v.map_pow,le_antisymm hm hminus]
  norm_num

theorem dual_away_two_seven_even (v:AddValuation K (WithTop ℤ)) (X Y:K) (m:ℤ)
    (hX:v X=m) (h2:v (2:K)=0) (h7:v (7:K)=0) (he:Y^2=X^3+4*D*X) : Even m :=
  dual_good_even v X Y m hX h2 (D_unit_away_two_seven v h2 h7) he

end DualLocalArithmetic318
#print axioms DualLocalArithmetic318.dual_real_positive
#print axioms DualLocalArithmetic318.dual_even_of_coefficient_four
#print axioms DualLocalArithmetic318.dual_good_even
#print axioms DualLocalArithmetic318.dual_two_even
#print axioms DualLocalArithmetic318.dual_delta_even_unless_one
#print axioms DualLocalArithmetic318.dual_delta_exception

#print axioms DualLocalArithmetic318.dual_away_two_seven_even
