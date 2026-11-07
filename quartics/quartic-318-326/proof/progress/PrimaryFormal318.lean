module
public import CompressedPoint318
public section
namespace PrimaryFormal318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318 RawDetector318
open CompressedPoint318 (E xH yH zH)
open scoped QuadraticAlgebra
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def u (w : Assignment) : Fin 4 → K := ![u1 w,u2 w,u3 w,u4 w]
@[expose] def y (w : Assignment) : Fin 4 → K := ![v1 w,v2 w,v3 w,v4 w]
@[expose] def ratio (w : Assignment) : Fin 4 → K := ![L1 w,L2 w,L3 w,L4 w]
@[expose] def leaf (S : ℚ) (w : Assignment) : Fin 4 → K :=
  ![leaf1 S w,leaf2 S w,leaf3 S w,leaf4 S w]
@[expose] def z (w : Assignment) (j : Fin 4) : K := -u w j/y w j

theorem source_curves (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ∀j,(y w j)^2=1-D*(u w j)^4 := by
  intro j
  fin_cases j <;> simp only [y,u,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact curve1 S w source
  · exact curve2 S w source
  · exact curve3 S w source
  · exact curve4 S w source

theorem source_ratios (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ∀j,k*y w j*ratio w j=u w j*anchorA w := by
  intro j
  fin_cases j <;> simp only [y,u,ratio,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact ratio1 S w source
  · exact ratio2 S w source
  · exact ratio3 S w source
  · exact ratio4 S w source

theorem source_leaves (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ∀j,leaf S w j=(u w j)^2 := by
  intro j
  fin_cases j <;> simp only [leaf,u,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · simpa [test1,u1] using leaf1_square S w source
  · simpa [test2,u2] using leaf2_square S w source
  · simpa [test3,u3] using leaf3_square S w source
  · simpa [test4,u4] using leaf4_square S w source

theorem square_depth (v : AddValuation K (WithTop ℤ)) (u : K)
    (hu : (2:WithTop ℤ)≤v (u^2)) : (1:WithTop ℤ)≤v u := by
  by_cases hu0 : u=0
  · simp [hu0]
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hu0)
  have he : v (u^2)=((2*a:ℤ):WithTop ℤ) := by
    rw [v.map_pow,←ha,two_nsmul]
    norm_cast
    ring
  rw [he] at hu
  have ha2 : 2≤2*a := WithTop.coe_le_coe.mp hu
  rw [←ha]
  exact_mod_cast (show (1:ℤ)≤a by omega)

theorem reciprocal_nonsingular (u y : K) (hu : u≠0) (hy : y≠0)
    (hc : y^2=1-D*u^4) : E.Nonsingular (1/u^2) (y/u^3) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [E,zero_mul,mul_zero,add_zero]
    field_simp [hu]
    linear_combination hc
  · right
    simp only [E,zero_mul,add_zero]
    exact mul_ne_zero (by norm_num) (div_ne_zero hy (pow_ne_zero 3 hu))

@[expose] def point (u y : K) (hy : y≠0) (hc : y^2=1-D*u^4) : E.Point :=
  if hu : u=0 then 0 else .some (1/u^2) (y/u^3) (reciprocal_nonsingular u y hu hy hc)

theorem point_zero_iff (u y : K) (hy : y≠0) (hc : y^2=1-D*u^4) :
    point u y hy hc=0 ↔ u=0 := by
  by_cases hu : u=0
  · simp [point,hu]
  · simp [point,hu,WeierstrassCurve.Affine.Point.some_ne_zero]

theorem finite_coordinates (u y : K) (hu : u≠0) (hy : y≠0)
    (hc : y^2=1-D*u^4) :
    point u y hy hc=WeierstrassCurve.Affine.Point.some (1/u^2) (y/u^3)
      (reciprocal_nonsingular u y hu hy hc) ∧ -u/y= -(1/u^2)/(y/u^3) := by
  refine ⟨by simp [point,hu],?_⟩
  field_simp [hu,hy]

/-- Every primary chart is interpreted, including its allowed identity branch.
The exact ratio is a formal-parameter ratio, not an assumed logarithm ratio. -/
theorem source_primary (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hk : v k=0) (hD : v D=0)
    (hf : (8:WithTop ℤ)≤v (fH w)) (j : Fin 4)
    (hleaf : (2:WithTop ℤ)≤v (leaf S w j)) :
    ∃ (hy : y w j≠0),
      (point (u w j) (y w j) hy (source_curves S w source j)=0 ↔ u w j=0) ∧
      v (y w j)=0 ∧ (1:WithTop ℤ)≤v (z w j) ∧ z w j=ratio w j*zH w ∧
      (u w j≠0 → ∃ h:E.Nonsingular (1/(u w j)^2) (y w j/(u w j)^3),
        point (u w j) (y w j) hy (source_curves S w source j)=
          WeierstrassCurve.Affine.Point.some _ _ h ∧
        z w j= -(1/(u w j)^2)/(y w j/(u w j)^3)) := by
  rw [source_leaves S w source j] at hleaf
  have hu := square_depth v (u w j) hleaf
  have hy := ValuationLucasOrientation318.ordinate_unit v D (u w j) (y w j) hD
    (lt_of_lt_of_le (by norm_num) hu) (source_curves S w source j)
  have hy0 : y w j≠0 := (v.ne_top_iff).mp (by rw [hy]; simp)
  have hA := (CompressedPoint318.source_formal_depth S w source v hk (by rw [hD]) hf).1
  refine ⟨hy0,point_zero_iff _ _ _ _,hy,?_,?_,?_⟩
  · simpa only [z,v.map_div,v.map_neg,hy,sub_zero] using hu
  · have hh := source_ratios S w source j
    dsimp [z,zH]
    field_simp [hy0,hA]
    linear_combination hh
  · intro hu0
    exact ⟨reciprocal_nonsingular _ _ hu0 hy0 (source_curves S w source j),
      finite_coordinates _ _ hu0 hy0 (source_curves S w source j)⟩

theorem inputs0_primary (v : AddValuation K (WithTop ℤ)) (S : ℚ) (w : Assignment)
    (hb : ∀x∈SourceContact318.inputs0 S w,(2*x.2.2:ℤ)≤v x.2.1) :
    ∀j,(2:WithTop ℤ)≤v (leaf S w j) := by
  intro j
  fin_cases j <;> simp only [leaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · simpa using hb (RawDetector318.q0_1 S w,leaf1 S w,1) (by simp [SourceContact318.inputs0])
  · simpa using hb (RawDetector318.q0_1 S w,leaf2 S w,1) (by simp [SourceContact318.inputs0])
  · simpa using hb (RawDetector318.q0_1 S w,leaf3 S w,1) (by simp [SourceContact318.inputs0])
  · simpa using hb (RawDetector318.q0_1 S w,leaf4 S w,1) (by simp [SourceContact318.inputs0])

theorem inputs1_primary (v : AddValuation K (WithTop ℤ)) (S : ℚ) (w : Assignment)
    (hb : ∀x∈SourceContact318.inputs1 S w,(2*x.2.2:ℤ)≤v x.2.1) :
    ∀j,(2:WithTop ℤ)≤v (leaf S w j) := by
  intro j
  fin_cases j <;> simp only [leaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · simpa using hb (RawDetector318.q1_1 S w,leaf1 S w,1) (by simp [SourceContact318.inputs1])
  · simpa using hb (RawDetector318.q1_1 S w,leaf2 S w,1) (by simp [SourceContact318.inputs1])
  · simpa using hb (RawDetector318.q1_1 S w,leaf3 S w,1) (by simp [SourceContact318.inputs1])
  · simpa using hb (RawDetector318.q1_1 S w,leaf4 S w,1) (by simp [SourceContact318.inputs1])

theorem inputs2_primary (v : AddValuation K (WithTop ℤ)) (S : ℚ) (w : Assignment)
    (hb : ∀x∈SourceContact318.inputs2 S w,(2*x.2.2:ℤ)≤v x.2.1) :
    ∀j,(2:WithTop ℤ)≤v (leaf S w j) := by
  intro j
  fin_cases j <;> simp only [leaf,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · simpa using hb (RawDetector318.q2_1 S w,leaf1 S w,1) (by simp [SourceContact318.inputs2])
  · simpa using hb (RawDetector318.q2_1 S w,leaf2 S w,1) (by simp [SourceContact318.inputs2])
  · simpa using hb (RawDetector318.q2_1 S w,leaf3 S w,1) (by simp [SourceContact318.inputs2])
  · simpa using hb (RawDetector318.q2_1 S w,leaf4 S w,1) (by simp [SourceContact318.inputs2])


end
end PrimaryFormal318
