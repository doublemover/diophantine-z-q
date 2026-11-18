module
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Tactic.Abel
public section

/-! Evaluation of the *native continuous homogeneous complex* at prefixes.
No arbitrary functions on an infinite discrete group are substituted. -/
namespace ActualCasselsTateNativeContinuousFaces318
open CategoryTheory TopRep ContRepresentation
variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G)
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

local notation "C2" => (homogeneousCochains X).X 2
local notation "C3" => (homogeneousCochains X).X 3
local notation "C4" => (homogeneousCochains X).X 4

/-- Boundary as the alternating sum of the four genuinely native faces. -/
lemma native_two_faces (z : C2) (a b c d : G) :
    (((homogeneousCochains X).d 2 3).hom z).val a b c d =
      z.val b c d - z.val a c d + z.val a b d - z.val a b c := by
  calc
    _ = ((TopRep.d X 3).hom z.val) a b c d :=
      congrArg (fun f : C(G,C(G,C(G,C(G,X)))) => f a b c d)
        (homogeneousCochains.d_apply X 2 z)
    _ = _ := by
      change z.val b c d - (z.val a c d - (z.val a b d - z.val a b c)) = _
      abel

lemma native_three_faces (z : C3) (a b c d e : G) :
    (((homogeneousCochains X).d 3 4).hom z).val a b c d e =
      z.val b c d e - z.val a c d e + z.val a b d e - z.val a b c e + z.val a b c d := by
  calc
    _ = ((TopRep.d X 4).hom z.val) a b c d e :=
      congrArg (fun f : C(G,C(G,C(G,C(G,C(G,X))))) => f a b c d e)
        (homogeneousCochains.d_apply X 3 z)
    _ = _ := by
      change z.val b c d e - (z.val a c d e - (z.val a b d e -
        (z.val a b c e - z.val a b c d))) = _
      abel

/-- Joint left translation of all vertices acts on the coefficient; it
does not fix its value pointwise. -/
lemma diagonal_two (z : C2) (s a b c : G) :
    z.val (s*a) (s*b) (s*c) = X.ρ s (z.val a b c) := by
  have h := congrArg (fun f : C(G,C(G,C(G,X))) => f (s*a) (s*b) (s*c)) (z.2 s)
  change X.ρ s (z.val (s⁻¹*(s*a)) (s⁻¹*(s*b)) (s⁻¹*(s*c))) = _ at h
  simpa only [inv_mul_cancel_left] using h.symm

lemma diagonal_three (z : C3) (s a b c d : G) :
    z.val (s*a) (s*b) (s*c) (s*d) = X.ρ s (z.val a b c d) := by
  have h := congrArg (fun f : C(G,C(G,C(G,C(G,X)))) => f (s*a) (s*b) (s*c) (s*d)) (z.2 s)
  change X.ρ s (z.val (s⁻¹*(s*a)) (s⁻¹*(s*b)) (s⁻¹*(s*c)) (s⁻¹*(s*d))) = _ at h
  simpa only [inv_mul_cancel_left] using h.symm

def evalTwo (z : C2) (g h : G) : X := z.val 1 g (g*h)
def evalThree (z : C3) (g h l : G) : X := z.val 1 g (g*h) (g*(h*l))
def evalFour (z : C4) (g h l m : G) : X := z.val 1 g (g*h) (g*(h*l)) (g*(h*(l*m)))

theorem eval_native_dTwo (z : C2) (g h l : G) :
    evalThree X (((homogeneousCochains X).d 2 3).hom z) g h l =
      X.ρ g (evalTwo X z h l) - evalTwo X z (g*h) l +
        evalTwo X z g (h*l) - evalTwo X z g h := by
  have he := diagonal_two X z g 1 h (h*l)
  simp only [mul_one] at he
  simp only [evalThree,evalTwo,native_two_faces,mul_assoc,he]

theorem eval_native_dThree (z : C3) (g h l m : G) :
    evalFour X (((homogeneousCochains X).d 3 4).hom z) g h l m =
      X.ρ g (evalThree X z h l m) - evalThree X z (g*h) l m +
        evalThree X z g (h*l) m - evalThree X z g h (l*m) + evalThree X z g h l := by
  have he := diagonal_three X z g 1 h (h*l) (h*(l*m))
  simp only [mul_one] at he
  simp only [evalFour,evalThree,native_three_faces,mul_assoc,he]

end ActualCasselsTateNativeContinuousFaces318
