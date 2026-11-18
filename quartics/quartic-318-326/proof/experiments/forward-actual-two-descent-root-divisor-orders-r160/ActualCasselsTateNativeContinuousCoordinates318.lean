module
public import ActualCasselsTateNativeContinuousFaces318
public import Mathlib.Topology.CompactOpen
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.FunProp
public section

/-! Fully bundled continuous coordinates in cochain degrees two and three.
Joint continuity of the actual action is required, not inferred from TopRep. -/
namespace ActualCasselsTateNativeContinuousCoordinates318
open CategoryTheory TopRep ContRepresentation ActualCasselsTateNativeContinuousFaces318
variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (X : TopRep k G)
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex
local notation "N2" => (homogeneousCochains X).X 2
local notation "N3" => (homogeneousCochains X).X 3

private lemma incr (s a b : G) : (s⁻¹*a)⁻¹*(s⁻¹*b)=a⁻¹*b := by group
private lemma translate (a b : G) (x : X) : X.ρ a (X.ρ b x) = X.ρ (a*b) x :=
  congrArg (fun f : X →L[k] X => f x) (map_mul X.ρ a b).symm
private lemma ident (x : X) : X.ρ (1:G) x = x :=
  congrArg (fun f : X →L[k] X => f x) (map_one X.ρ)

def nativeTwoMap (z : N2) : C(G × G, X) :=
  let nested : C(G,C(G,C(G,X))) := z.val
  let f : C((G × G) × G,X) := nested.uncurry.uncurry
  ⟨fun p => f ((1,p.1),p.1*p.2), f.continuous.comp (by fun_prop)⟩

def nativeThreeMap (z : N3) : C(G × G × G, X) :=
  let nested : C(G,C(G,C(G,C(G,X)))) := z.val
  let f : C(((G × G) × G) × G,X) := nested.uncurry.uncurry.uncurry
  ⟨fun p => f (((1,p.1),p.1*p.2.1),p.1*(p.2.1*p.2.2)), f.continuous.comp (by fun_prop)⟩

variable (hact : Continuous (fun p : G × X => X.ρ p.1 p.2))

/-- Currying a joint continuous vertex map produces a native invariant
nested continuous map, not just its underlying function. -/
def fromTwoMap (z : C(G × G,X)) : N2 := by
  let f : C((G × G) × G,X) := ⟨fun p =>
    X.ρ p.1.1 (z (p.1.1⁻¹*p.1.2,p.1.2⁻¹*p.2)), by
      exact hact.comp (show Continuous (fun p : (G × G) × G =>
        (p.1.1,z (p.1.1⁻¹*p.1.2,p.1.2⁻¹*p.2))) by fun_prop)⟩
  refine ⟨f.curry.curry,?_⟩
  intro s
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  change X.ρ s (X.ρ (s⁻¹*a) (z ((s⁻¹*a)⁻¹*(s⁻¹*b),(s⁻¹*b)⁻¹*(s⁻¹*c)))) = _
  change _ = X.ρ a (z (a⁻¹*b,b⁻¹*c))
  rw [incr,incr,translate,mul_inv_cancel_left]

def fromThreeMap (z : C(G × G × G,X)) : N3 := by
  let f : C(((G × G) × G) × G,X) := ⟨fun p =>
    X.ρ p.1.1.1 (z (p.1.1.1⁻¹*p.1.1.2,p.1.1.2⁻¹*p.1.2,p.1.2⁻¹*p.2)), by
      exact hact.comp (show Continuous (fun p : ((G × G) × G) × G =>
        (p.1.1.1,z (p.1.1.1⁻¹*p.1.1.2,p.1.1.2⁻¹*p.1.2,p.1.2⁻¹*p.2))) by fun_prop)⟩
  refine ⟨f.curry.curry.curry,?_⟩
  intro s
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  apply ContinuousMap.ext
  intro d
  change X.ρ s (X.ρ (s⁻¹*a) (z ((s⁻¹*a)⁻¹*(s⁻¹*b),(s⁻¹*b)⁻¹*(s⁻¹*c),
    (s⁻¹*c)⁻¹*(s⁻¹*d)))) = _
  change _ = X.ρ a (z (a⁻¹*b,b⁻¹*c,c⁻¹*d))
  rw [incr,incr,incr,translate,mul_inv_cancel_left]

/-- Both orientations are identities on the actual continuous functions. -/
theorem eval_fromTwo (z : C(G × G,X)) : nativeTwoMap X (fromTwoMap X hact z) = z := by
  apply ContinuousMap.ext
  rintro ⟨g,h⟩
  change X.ρ (1:G) (z ((1:G)⁻¹*g,g⁻¹*(g*h))) = z (g,h)
  rw [ident,inv_one,one_mul,inv_mul_cancel_left]

theorem eval_fromThree (z : C(G × G × G,X)) :
    nativeThreeMap X (fromThreeMap X hact z) = z := by
  apply ContinuousMap.ext
  rintro ⟨g,h,l⟩
  change X.ρ (1:G) (z ((1:G)⁻¹*g,g⁻¹*(g*h),(g*h)⁻¹*(g*(h*l)))) = z (g,h,l)
  have he : (g*h)⁻¹*(g*(h*l))=l := by group
  rw [ident,inv_one,one_mul,inv_mul_cancel_left,he]

theorem from_evalTwo (z : N2) : fromTwoMap X hact (nativeTwoMap X z) = z := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  change X.ρ a (z.val 1 (a⁻¹*b) ((a⁻¹*b)*(b⁻¹*c))) = z.val a b c
  have he : a*((a⁻¹*b)*(b⁻¹*c))=c := by group
  simpa only [mul_one,mul_inv_cancel_left,he] using
    (diagonal_two X z a 1 (a⁻¹*b) ((a⁻¹*b)*(b⁻¹*c))).symm

theorem from_evalThree (z : N3) : fromThreeMap X hact (nativeThreeMap X z) = z := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  apply ContinuousMap.ext
  intro d
  change X.ρ a (z.val 1 (a⁻¹*b) ((a⁻¹*b)*(b⁻¹*c))
    ((a⁻¹*b)*((b⁻¹*c)*(c⁻¹*d)))) = z.val a b c d
  have h2 : a*((a⁻¹*b)*(b⁻¹*c))=c := by group
  have h3 : a*((a⁻¹*b)*((b⁻¹*c)*(c⁻¹*d)))=d := by group
  simpa only [mul_one,mul_inv_cancel_left,h2,h3] using
    (diagonal_three X z a 1 (a⁻¹*b) ((a⁻¹*b)*(b⁻¹*c))
      ((a⁻¹*b)*((b⁻¹*c)*(c⁻¹*d)))).symm
end ActualCasselsTateNativeContinuousCoordinates318
