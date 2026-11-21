module
public import OriginalCasselsGoodCharacterCount318
public import OriginalSelectedCasselsLocalArithmetic318
public section

noncomputable section

namespace OriginalCasselsGoodNonsquareLabel318

open OriginalCasselsGoodCharacterCount318 OriginalSelectedCasselsLocalArithmetic318

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev Orig (n x : K) : K := source (2*n) (-3*n^2) x
abbrev Quot (n X : K) : K := target (2*n) (-3*n^2) X
abbrev xImage (n x : K) : K := x+2*n-3*n^2/x
abbrev yImage (n x y : K) : K := y+3*n^2*y/x^2

private theorem orig_eq (n x : K) : Orig n x=x*(x-n)*(x+3*n) := by
  change x*(x^2+(2*n)*x+(-3*n^2))=x*(x-n)*(x+3*n)
  ring

theorem quot_eq (n X : K) : Quot n X=X*(X^2-4*n*X+16*n^2) := by
  change X*((X-2*n)^2-4*(-3*n^2))=_
  ring

private theorem raw_chart (n x y : K) (hx : x≠0) (he : y^2=Orig n x) :
    (yImage n x y)^2=Quot n (xImage n x) := by
  rw [orig_eq] at he
  rw [quot_eq]
  exact affine_isogeny_chart n x y hx he

/-- Only a function of exact finite equation labels, including infinity.
It has no claimed finite-field group-homomorphism structure. -/
def rawMap (n : K) : RawPoints (Orig n) → RawPoints (Quot n)
  | none => none
  | some ⟨x,⟨y,he⟩⟩ =>
    if hx : x=0 then none else some ⟨xImage n x,⟨yImage n x y,raw_chart n x y hx he⟩⟩

private theorem raw_eq (F : K → K) {x y X Y : K} (h : y^2=F x) (H : Y^2=F X)
    (hx : x=X) (hy : y=Y) :
    (some ⟨x,⟨y,h⟩⟩:RawPoints F)=some ⟨X,⟨Y,H⟩⟩ := by
  subst X
  subst Y
  rfl

private theorem raw_lift (n : K) (hn : n≠0) (h2 : (2:K)≠0) (h3 : (3:K)≠0)
    (X Y u : K) (hX : X≠0) (hU : u^2=X) (h : Y^2=Quot n X) :
    ∃ P : RawPoints (Orig n), rawMap n P=some ⟨X,⟨Y,h⟩⟩ := by
  have hu : u≠0 := by
    intro hz
    exact hX (by simpa only [hz,zero_pow (by decide : (2:ℕ)≠0)] using hU.symm)
  let v := Y/u
  have hv : v^2=X^2-4*n*X+16*n^2 := by
    dsimp [v]
    rw [div_pow,h,quot_eq,hU]
    field_simp [hX] <;> ring
  let x := (X-2*n+v)/2
  have hlin : 2*x=X-2*n+v := by dsimp [x]; field_simp [h2] <;> ring
  have h4 : (4:K)≠0 := by convert mul_ne_zero h2 h2 using 1 <;> ring
  have hq : x^2+(2*n-X)*x-3*n^2=0 := by
    have he : (4:K)*(x^2+(2*n-X)*x-3*n^2)=0 := by
      calc
        _ = (2*x+(2*n-X))^2-(X^2-4*n*X+16*n^2) := by ring
        _ = 0 := by rw [hlin]; linear_combination hv
    exact (mul_eq_zero.mp he).resolve_left h4
  have hx : x≠0 := by
    intro hz
    rw [hz] at hq
    have hprod : -((3:K)*n^(2:ℕ))=0 := by
      simpa only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero,zero_sub] using hq
    exact (mul_ne_zero h3 (pow_ne_zero (2:ℕ) hn)) (neg_eq_zero.mp hprod)
  have he : (u*x)^2=Orig n x := by
    rw [orig_eq,mul_pow,hU]
    linear_combination -x*hq
  have hdiv : 3*n^2/x=x+2*n-X := by
    apply (div_eq_iff hx).2
    linear_combination -hq
  have hxx : xImage n x=X := by
    change x+2*n-3*n^2/x=X
    rw [hdiv]
    ring
  have hyy : yImage n x (u*x)=Y := by
    calc
      _ = u*(x+3*n^2/x) := by
        change u*x+3*n^2*(u*x)/x^2=u*(x+3*n^2/x)
        field_simp [hx] <;> ring
      _ = u*v := by rw [hdiv]; linear_combination u*hlin
      _ = Y := by dsimp [v]; field_simp [hu] <;> ring
  refine ⟨some ⟨x,⟨u*x,he⟩⟩,?_⟩
  simp only [rawMap,dif_neg hx]
  exact raw_eq (Quot n) _ _ hxx hyy

/-- There is a real nonzero nonsquare abscissa among the literal quotient
labels over the finite good residue field. Assuming otherwise makes the
literal map surjective, impossible at its two fixed preimages of O. -/
theorem exists_nonsquare_label (n : K) (hn : n≠0) (h2 : (2:K)≠0) (h3 : (3:K)≠0)
    (hF : ringChar K≠2) :
    ∃ X Y : K, X≠0 ∧ ¬IsSquare X ∧ Y^2=X*(X^2-4*n*X+16*n^2) := by
  classical
  by_contra h
  have hsq (X Y : K) (hX : X≠0) (he : Y^2=Quot n X) : IsSquare X := by
    by_contra hN
    exact h ⟨X,Y,hX,hN,by simpa only [quot_eq] using he⟩
  have surj : Function.Surjective (rawMap n) := by
    intro P
    cases P with
    | none => exact ⟨none,rfl⟩
    | some S =>
      rcases S with ⟨X,⟨Y,he⟩⟩
      by_cases hx : X=0
      · subst X
        have hy : Y=0 := by
          apply (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp
          simpa only [quot_eq,zero_mul] using he
        subst Y
        have hP : (0:K)^2=Orig n n := by simp only [orig_eq,sub_self,mul_zero,zero_mul,zero_pow (by decide : (2:ℕ)≠0)]
        refine ⟨some ⟨n,⟨0,hP⟩⟩,?_⟩
        simp only [rawMap,dif_neg hn]
        apply raw_eq (Quot n) _ _
        · change n+2*n-3*n^2/n=0
          field_simp [hn] <;> ring
        · change (0:K)+3*n^2*0/n^2=0
          simp
      · obtain ⟨u,hu⟩ := hsq X Y hx he
        exact raw_lift n hn h2 h3 X Y u hx (by simpa only [pow_two] using hu.symm) he
  have hcard : Fintype.card (RawPoints (Orig n))=Fintype.card (RawPoints (Quot n)) :=
    raw_points_same_card (2*n) (-3*n^2) (mul_ne_zero (neg_ne_zero.mpr h3) (pow_ne_zero _ hn)) h2 hF
  have inj : Function.Injective (rawMap n) :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨surj,hcard⟩ |>.1
  let T : RawPoints (Orig n) := some ⟨0,⟨0,by simp only [orig_eq,zero_mul,zero_pow (by decide : (2:ℕ)≠0)]⟩⟩
  have ht : rawMap n T=rawMap n none := by simp [T,rawMap]
  have hT : T≠none := by
    change (some _ : RawPoints (Orig n))≠none
    exact Option.some_ne_none _
  exact hT (inj ht)

end OriginalCasselsGoodNonsquareLabel318

#print axioms OriginalCasselsGoodNonsquareLabel318.exists_nonsquare_label
