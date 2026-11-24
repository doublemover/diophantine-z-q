module
public import OriginalUniversalSparsePolynomial318
public section
namespace OriginalSparsePolynomialReflection318
/-- Elementary dense univariate polynomials. Trailing zero coefficients are allowed. -/
structure Ops (α : Type) where
  zero : α
  const : ℤ → α
  add : α → α → α
  mul : α → α → α
  isZero : α → Bool
@[expose] def plus (o : Ops α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | a :: l, b :: m => o.add a b :: plus o l m
@[expose] def times (o : Ops α) : List α → List α → List α
  | [], _ => []
  | a::l, m => plus o (m.map (o.mul a)) (o.zero :: times o l m)
@[expose] def lift (o : Ops α) : Ops (List α) :=
  ⟨[],fun n=>[o.const n],plus o,times o,fun l=>l.all o.isZero⟩
@[expose] def ints : Ops ℤ := ⟨0,id,(·+·),(·*·),fun x=>x==0⟩
structure Realizes {α : Type} {R : Type*} [CommRing R] (o : Ops α) (f : α→R) : Prop where
  zero : f o.zero=0
  const : ∀ n, f (o.const n)=(n:R)
  add : ∀ a b, f (o.add a b)=f a+f b
  mul : ∀ a b, f (o.mul a b)=f a*f b
  vanishes : ∀ a, o.isZero a=true → f a=0
@[expose] def value {α : Type} {R : Type*} [CommRing R] (f : α→R) (x : R) :
    List α → R
  | [] => 0
  | h::l => f h+x*value f x l
theorem lift_ok {α : Type} {R : Type*} [CommRing R] (o : Ops α)
    (f : α→R) (h : Realizes o f) (x : R) : Realizes (lift o) (value f x) := by
  have ha (l m : List α) : value f x (plus o l m)=value f x l+value f x m := by
    induction l generalizing m with
    | nil => simp [plus,value]
    | cons a l ih =>
      cases m with
      | nil => simp [plus,value]
      | cons b m => simp only [plus,value,h.add,ih]; ring
  have hs (a : α) (l : List α) : value f x (l.map (o.mul a))=f a*value f x l := by
    induction l with
    | nil => simp [value]
    | cons b l ih => simp only [List.map_cons,value,h.mul,ih]; ring
  refine ⟨rfl,?_,ha,?_,?_⟩
  · intro n; simp [lift,value,h.const]
  · intro a b
    change value f x (times o a b)=_
    induction a with
    | nil => simp [times,value]
    | cons a l ih => simp only [times,ha,hs,value,h.zero,ih]; ring
  · intro a hz
    change a.all o.isZero=true at hz
    induction a with
    | nil => rfl
    | cons a l ih =>
      simp only [List.all_cons,Bool.and_eq_true] at hz
      simp [value,h.vanishes a hz.1,ih hz.2]

theorem ints_ok {R : Type*} [CommRing R] : Realizes ints (fun a : ℤ=>(a:R)) := by
  refine ⟨Int.cast_zero,fun _=>rfl,Int.cast_add,Int.cast_mul,?_⟩
  intro a ha
  change (a==0)=true at ha
  simp only [beq_iff_eq] at ha
  simp [ha]

abbrev Co := List (List ℤ)
abbrev Tri := List Co
@[expose] def coOps : Ops Co := lift (lift ints)
@[expose] def triOps : Ops Tri := lift coOps
@[expose] def sub (p q : Tri) : Tri := triOps.add p (triOps.mul (triOps.const (-1)) q)
@[expose] def diffRel (v df q f den rhs : Tri) : Tri :=
  sub (triOps.add (triOps.mul v df) (triOps.mul q f)) (triOps.mul den rhs)
@[expose] def co {R : Type*} [CommRing R] (s t : R) : Co→R := value (value (Int.castRingHom R) s) t
@[expose] def tri {R : Type*} [CommRing R] (s t u : R) : Tri→R := value (co s t) u
theorem tri_ok {R : Type*} [CommRing R] (s t u : R) : Realizes triOps (tri s t u) :=
  lift_ok _ _ (lift_ok _ _ (lift_ok _ _ ints_ok _) _) _
theorem relation {R : Type*} [CommRing R] (s t u : R) (v df q f den rhs : Tri)
    (h : triOps.isZero (diffRel v df q f den rhs)=true) :
    tri s t u v*tri s t u df+tri s t u q*tri s t u f=tri s t u den*tri s t u rhs := by
  have ho := tri_ok s t u
  have he := ho.vanishes _ h
  simp only [diffRel,sub,ho.add,ho.mul,ho.const] at he
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using he
end OriginalSparsePolynomialReflection318
#print axioms OriginalSparsePolynomialReflection318.relation
