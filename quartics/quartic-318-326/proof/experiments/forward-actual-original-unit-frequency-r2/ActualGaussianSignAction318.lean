module
public import ActualGaussianGrowingCutoff318
public section
noncomputable section
namespace ActualGaussianSignAction318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralSliceBoxCount318 LiteralAdjacentNormSlice318
open OriginalWeightedSelberg318 IntegerResidueBoxCount318 OriginalBadSliceLogWeight318
set_option maxHeartbeats 8000000

@[expose] def sign (s : Bool) : ℤ := if s then -1 else 1
@[expose] def flip (s : Bool) (a : ℤ) : ℤ := if s then -a else a
lemma flip_twice (s : Bool) (a : ℤ) : flip s (flip s a)=a := by cases s <;> simp [flip]
lemma flip_sq (s : Bool) (a : ℤ) : (flip s a)^2=a^2 := by cases s <;> simp [flip]
lemma flip_adjacent (s : Bool) (a : ℤ) : (flip s a+1)^2=(a+sign s)^2 := by
  cases s <;> dsimp [flip,sign] <;> ring
@[expose] def transform (s t : Bool) (v : Coordinates ℤ) : Coordinates ℤ :=
  ((flip s v.1.1,v.1.2),(flip t v.2.1.1,v.2.1.2),v.2.2)
lemma transform_twice (s t : Bool) (v : Coordinates ℤ) :
    transform s t (transform s t v)=v := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩,w⟩
  simp only [transform,flip_twice]
lemma equation_transform (κ : ℤ) (s t : Bool) (v : Coordinates ℤ) :
    equation κ (transform s t v)=equation κ v := by simp only [equation,transform,flip_sq]
lemma box_transform (B : ℕ) (s t : Bool) (v : Coordinates ℤ) :
    InBox B (transform s t v)↔InBox B v := by
  cases s <;> cases t <;> dsimp [InBox,transform,flip] <;> omega

@[expose] def quadricAction (κ : ℤ) (s t : Bool) : Quadric κ ≃ Quadric κ where
  toFun v := ⟨transform s t v.1,by rw [equation_transform];exact v.2⟩
  invFun v := ⟨transform s t v.1,by rw [equation_transform];exact v.2⟩
  left_inv v := Subtype.ext (transform_twice s t v.1)
  right_inv v := Subtype.ext (transform_twice s t v.1)
@[expose] def signedG (s : Bool) (v : Coordinates ℤ) : ℤ := (v.1.1+sign s)^2+v.1.2^2
@[expose] def signedH (t : Bool) (v : Coordinates ℤ) : ℤ := (v.2.1.1+sign t)^2+v.2.1.2^2
lemma actual_signed_norms (s t : Bool) (v : Coordinates ℤ) :
    G (transform s t v)=signedG s v ∧ H (transform s t v)=signedH t v := by
  simp only [G,H,transform,signedG,signedH,flip_adjacent,and_self]

variable {J : Type*} [Fintype J] [DecidableEq J]
lemma form_transform (κ : ℤ) (γ : J → ℤ) (j : J) (s t : Bool) (v : Quadric κ) :
    form κ γ j (quadricAction κ s t v)=form κ γ j v := by
  simp only [form,quadricAction,transform,flip_sq]
lemma weight_transform (κ : ℤ) (γ : J → ℤ) (s t : Bool) (v : Quadric κ) :
    weight κ γ (quadricAction κ s t v)=weight κ γ v := by
  apply Finset.prod_congr rfl
  intro j _
  rw [form_transform]

/-- Every actual bounded source below is finite without imposing a
coefficient-prime threshold or assuming a finite obstruction witness. -/
@[expose] def BoundedQuadric (B : ℕ) (κ : ℤ) := {v : Quadric κ // InBox B v.1}
@[expose] def boundedEncode (B : ℕ) (κ : ℤ) (v : BoundedQuadric B κ) : FiveBox B :=
  ((⟨v.1.1.1.1,Finset.mem_Icc.mpr v.2.1⟩,⟨v.1.1.1.2,Finset.mem_Icc.mpr v.2.2.1⟩),
   (⟨v.1.1.2.1.1,Finset.mem_Icc.mpr v.2.2.2.1⟩,⟨v.1.1.2.1.2,Finset.mem_Icc.mpr v.2.2.2.2.1⟩),
   ⟨v.1.1.2.2,Finset.mem_Icc.mpr v.2.2.2.2.2⟩)
lemma boundedEncode_injective (B : ℕ) (κ : ℤ) : Function.Injective (boundedEncode B κ) := by
  intro v w he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : FiveBox B => ((z.1.1.1,z.1.2.1),(z.2.1.1.1,z.2.1.2.1),z.2.2.1)) he
instance bounded_finite (B : ℕ) (κ : ℤ) : Finite (BoundedQuadric B κ) :=
  Finite.of_injective (boundedEncode B κ) (boundedEncode_injective B κ)

end ActualGaussianSignAction318
