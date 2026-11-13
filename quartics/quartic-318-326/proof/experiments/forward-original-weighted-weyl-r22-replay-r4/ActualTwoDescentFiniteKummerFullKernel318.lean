module
public import ActualTwoDescentFiniteExceptionalHalvingRoots318
public section
noncomputable section
namespace ActualTwoDescentFiniteKummerFullKernel318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteKummerHom318
open ActualTwoDescentFiniteKummerAffineCoordinates318 ActualTwoDescentFiniteExceptionalHalvingRoots318
open ActualTwoDescentFiniteIdentityClassHalving318 ActualTwoDescentFiniteHalvingCoordinates318
open ActualTwoDescentFiniteHalvingGroup318
variable [DecidableEq K]

/-- The full Kummer homomorphism has EXACT kernel twice the actual elliptic
group, with infinity and every two-torsion point included. -/
theorem actual_kummer_kernel (n : K) (hn : n ≠ 0) (P : Point n) :
    kummerClass n hn P=1 ↔ ∃ Q : Point n, Q+Q=P := by
  constructor
  · intro H
    cases P with
    | zero => exact ⟨0,zero_add _⟩
    | some x y h =>
      have hc := (curve_equation n x y).mp h.left
      by_cases he : x=0 ∨ x=n ∨ x= -3*n
      · obtain ⟨a,b,c,ha,hb,hcc,hprod⟩ := actual_exceptional_halving_roots n x y hn h H he
        refine ⟨point n (halfX x a b c) (halfY a b c) hn (half_curve n x a b c ha hb hcc),?_⟩
        exact actual_half_add_self n x y a b c hn hc ha hb hcc hprod
      · have hx : x ≠ 0 := fun hx => he (Or.inl hx)
        have hB : x-n ≠ 0 := sub_ne_zero.mpr (fun hx => he (Or.inr (Or.inl hx)))
        have hA : x+3*n ≠ 0 := by
          intro hx
          apply he
          exact Or.inr (Or.inr (by linear_combination hx))
        obtain ⟨⟨s,hs,hS⟩,⟨t,ht,hT⟩⟩ := kummer_one_roots n hn (.some x y h) H
        rw [actual_first_coordinate n x y hn h hA] at hS
        rw [actual_second_coordinate n x y hn h hB] at hT
        obtain ⟨Q,hQ,hhalf⟩ := actual_identity_class_half n x y hn hx hB hA hc
          ⟨s,t,hs,ht,by simpa only [one_mul] using hS,by simpa only [one_mul] using hT⟩
        exact ⟨Q,hhalf⟩
  · rintro ⟨Q,rfl⟩
    exact kummer_class_double n hn Q

end ActualTwoDescentFiniteKummerFullKernel318
