module
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section

open Polynomial

namespace OriginalSameJAllOrderGraphQuotient318

variable {A : Type*} [CommRing A]

def thick (u : A) (m : ℕ) : Ideal A :=
  Ideal.span (Set.singleton (u ^ m))

def parameterPower (m : ℕ) : Ideal A[X] :=
  thick (X : A[X]) m

abbrev testRing (m : ℕ) := A[X] ⧸ parameterPower (A:=A) m

def pointEval (u : A) (m : ℕ) : A[X] →+* A ⧸ thick u m :=
  (Ideal.Quotient.mk (thick u m)).comp (Polynomial.evalRingHom u)

theorem eval_surj (u : A) : Function.Surjective (Polynomial.evalRingHom u) :=
  fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩

theorem mapped_parameter (u : A) (m : ℕ) :
    (parameterPower (A:=A) m).map (Polynomial.evalRingHom u) = thick u m := by
  unfold parameterPower thick
  rw [Ideal.map_span]
  have hx : Polynomial.evalRingHom u (X : A[X]) = u := Polynomial.eval_X
  have hm : Polynomial.evalRingHom u ((X : A[X]) ^ m) = u ^ m :=
    (map_pow (Polynomial.evalRingHom u) (X : A[X]) m).trans (congrArg (fun z : A => z ^ m) hx)
  have hi : (Polynomial.evalRingHom u : A[X] → A) '' Set.singleton ((X : A[X]) ^ m) =
      Set.singleton (Polynomial.evalRingHom u ((X : A[X]) ^ m)) :=
    Set.image_singleton
  exact congrArg (Ideal.span : Set A → Ideal A) (hi.trans (congrArg Set.singleton hm))

theorem raw_kernel (u : A) (m : ℕ) :
    RingHom.ker (pointEval u m) =
      parameterPower (A:=A) m ⊔ Ideal.span (Set.singleton (X - C u)) := by
  unfold pointEval
  rw [← RingHom.comap_ker,Ideal.mk_ker,← mapped_parameter u m,
    Ideal.comap_map_of_surjective' _ (eval_surj u),Polynomial.ker_evalRingHom]

theorem power_vanishes (u : A) (m : ℕ) :
    parameterPower (A:=A) m ≤ RingHom.ker (pointEval u m) := by
  rw [raw_kernel]
  exact le_sup_left

/-- The actual graph (t↦u) over the test A[t]/t^m. The target is the
literal u-adic infinitesimal neighbourhood, not its residue point. -/
def graph (u : A) (m : ℕ) : testRing (A:=A) m →+* A ⧸ thick u m :=
  Ideal.Quotient.lift (parameterPower m) (pointEval u m) (power_vanishes u m)

theorem graph_reads (u : A) (m : ℕ) (p : A[X]) :
    graph u m (Ideal.Quotient.mk (parameterPower m) p) =
      Ideal.Quotient.mk (thick u m) (p.eval u) := rfl

theorem graph_surj (u : A) (m : ℕ) : Function.Surjective (graph u m) := by
  intro z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨Ideal.Quotient.mk (parameterPower m) (C a), ?_⟩
  rw [graph_reads,Polynomial.eval_C]

/-- The whole nonreduced graph ideal really has equation t-u, for
every truncation order. A positive Cartier equation can be u-t. -/
theorem exact_graph (u : A) (m : ℕ) :
    RingHom.ker (graph u m) =
      Ideal.span (Set.singleton ((Ideal.Quotient.mk (parameterPower m)) (X - C u))) := by
  rw [graph,Ideal.ker_quotient_lift,raw_kernel,Ideal.map_sup,
    Ideal.map_quotient_self,bot_sup_eq,Ideal.map_span]
  have hi : (Ideal.Quotient.mk (parameterPower (A:=A) m) : A[X] → testRing (A:=A) m) ''
      Set.singleton (X - C u) =
      Set.singleton (Ideal.Quotient.mk (parameterPower (A:=A) m) (X - C u)) :=
    Set.image_singleton
  exact congrArg (Ideal.span : Set (testRing (A:=A) m) → Ideal (testRing (A:=A) m)) hi

end OriginalSameJAllOrderGraphQuotient318

#print axioms OriginalSameJAllOrderGraphQuotient318.raw_kernel
#print axioms OriginalSameJAllOrderGraphQuotient318.graph_reads
#print axioms OriginalSameJAllOrderGraphQuotient318.graph_surj
#print axioms OriginalSameJAllOrderGraphQuotient318.exact_graph
