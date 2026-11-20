module
public import OriginalRCMilneSplitLocal318
public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Abel

public section

namespace OriginalRCMilneTwistedKummerCore318

open OriginalRCMilneSplitLocal318

structure OrderedAction (G A : Type*) [Group G] [AddCommGroup A] where
  ρ : G →* AddMonoid.End A
  flip : G → Bool
  flip_mul : ∀ g h, flip (g*h) = Bool.xor (flip g) (flip h)
  flip_one : flip 1 = false

variable {G A : Type*} [Group G] [AddCommGroup A]

@[expose] def OrderedAction.source (D : OrderedAction G A) (g : G) (P : A × A) : A × A :=
  if D.flip g then (D.ρ g P.2,D.ρ g P.1) else (D.ρ g P.1,D.ρ g P.2)

@[expose] def OrderedAction.target (D : OrderedAction G A) (g : G) (P : A × A) : A × A :=
  (D.ρ g P.1, if D.flip g then -(D.ρ g P.2) else D.ρ g P.2)

private theorem act_mul (D : OrderedAction G A) (g h : G) (P : A) :
    D.ρ (g*h) P = D.ρ g (D.ρ h P) := by
  rw [map_mul] <;> rfl

theorem source_mul (D : OrderedAction G A) (g h : G) (P : A × A) :
    D.source (g*h) P = D.source g (D.source h P) := by
  cases hg : D.flip g <;> cases hh : D.flip h <;>
    simp [OrderedAction.source,D.flip_mul,hg,hh,Bool.xor,act_mul]

theorem target_mul (D : OrderedAction G A) (g h : G) (P : A × A) :
    D.target (g*h) P = D.target g (D.target h P) := by
  cases hg : D.flip g <;> cases hh : D.flip h <;>
    simp [OrderedAction.target,D.flip_mul,hg,hh,Bool.xor,act_mul,map_neg]

theorem source_sub (D : OrderedAction G A) (g : G) (P Q : A × A) :
    D.source g (P-Q) = D.source g P - D.source g Q := by
  cases h : D.flip g <;> apply Prod.ext <;>
    simp [OrderedAction.source,h,map_sub]

theorem target_sub (D : OrderedAction G A) (g : G) (P Q : A × A) :
    D.target g (P-Q) = D.target g P - D.target g Q := by
  cases h : D.flip g <;> apply Prod.ext <;>
    simp [OrderedAction.target,h,map_sub] <;> abel

/-- Source is the ordered Weil pair; target has the literal twisted sign
on its second coordinate. The same normalized sum/difference serves as
the dual in the opposite direction. -/
theorem phi_equivariant (D : OrderedAction G A) (g : G) (P : A × A) :
    sumDifference A (D.source g P) = D.target g (sumDifference A P) := by
  cases h : D.flip g <;> apply Prod.ext <;>
    simp [OrderedAction.source,OrderedAction.target,sumDifference,h,map_add,map_sub] <;> abel

theorem psi_equivariant (D : OrderedAction G A) (g : G) (P : A × A) :
    sumDifference A (D.target g P) = D.source g (sumDifference A P) := by
  cases h : D.flip g <;> apply Prod.ext <;>
    simp [OrderedAction.source,OrderedAction.target,sumDifference,h,map_add,map_sub] <;> abel

@[expose] def phiLift (P T : A) : A × A := (T,P-T)
@[expose] def psiLift (P R : A) : A × A := (P-R,R)

theorem phi_lift (P U T : A) (h : T+T = P+U) :
    sumDifference A (phiLift P T) = (P,U) := by
  apply Prod.ext
  · change T+(P-T)=P
    abel
  · change T-(P-T)=U
    calc
      _ = (T+T)-P := by abel
      _ = _ := by rw [h]; abel

theorem psi_lift (V W R : A) (h : R+R = V-W) :
    sumDifference A (psiLift V R) = (V,W) := by
  apply Prod.ext
  · change (V-R)+R=V
    abel
  · change (V-R)-R=W
    calc
      _ = V-(R+R) := by abel
      _ = _ := by rw [h]; abel

@[expose] def phiBoundary (D : OrderedAction G A) (P T : A) (g : G) : A × A :=
  D.source g (phiLift P T) - phiLift P T

@[expose] def psiBoundary (D : OrderedAction G A) (V R : A) (g : G) : A × A :=
  D.target g (psiLift V R) - psiLift V R

@[expose] def phiScalar (D : OrderedAction G A) (P T : A) (g : G) : A :=
  if D.flip g then P-D.ρ g T-T else D.ρ g T-T

@[expose] def psiScalar (D : OrderedAction G A) (R : A) (g : G) : A :=
  if D.flip g then -(D.ρ g R)-R else D.ρ g R-R

theorem phi_first (D : OrderedAction G A) (P T : A) (g : G) (hP : D.ρ g P = P) :
    (phiBoundary D P T g).1 = phiScalar D P T g := by
  cases h : D.flip g <;>
    simp [phiBoundary,phiLift,OrderedAction.source,phiScalar,h,map_sub,hP]

theorem psi_second (D : OrderedAction G A) (V R : A) (g : G) :
    (psiBoundary D V R g).2 = psiScalar D R g := by
  cases h : D.flip g <;> simp [psiBoundary,psiLift,OrderedAction.target,psiScalar,h]

theorem kernel_diagonal (P : A × A) (h : sumDifference A P = 0) :
    P = (P.1,P.1) ∧ P.1+P.1=0 := by
  have hf : P.1+P.2=0 := congrArg Prod.fst h
  have hs : P.1-P.2=0 := congrArg Prod.snd h
  have he := sub_eq_zero.mp hs
  exact ⟨Prod.ext rfl he.symm,by simpa only [←he] using hf⟩

/-- These are actual 2-torsion values, without assumptions about odd
digits or choosing a different half. The two signed branches are
the explicit representatives of the original source action. -/
theorem phi_diagonal (D : OrderedAction G A) (P U T : A) (g : G)
    (hT : T+T=P+U) (hP : D.ρ g P=P)
    (hU : (if D.flip g then -(D.ρ g U) else D.ρ g U)=U) :
    phiBoundary D P T g = (phiScalar D P T g,phiScalar D P T g) ∧
      phiScalar D P T g+phiScalar D P T g=0 := by
  have hk : sumDifference A (phiBoundary D P T g)=0 := by
    rw [phiBoundary,map_sub,phi_equivariant,phi_lift P U T hT]
    change (D.ρ g P,(if D.flip g then -(D.ρ g U) else D.ρ g U))-(P,U)=0
    rw [hP,hU,sub_self]
  obtain ⟨he,h₂⟩ := kernel_diagonal _ hk
  rw [phi_first D P T g hP] at he h₂
  exact ⟨he,h₂⟩

theorem psi_diagonal (D : OrderedAction G A) (V W R : A) (g : G)
    (hR : R+R=V-W) (hVW : D.source g (V,W)=(V,W)) :
    psiBoundary D V R g = (psiScalar D R g,psiScalar D R g) ∧
      psiScalar D R g+psiScalar D R g=0 := by
  have hk : sumDifference A (psiBoundary D V R g)=0 := by
    rw [psiBoundary,map_sub,psi_equivariant,psi_lift V W R hR,hVW,sub_self]
  obtain ⟨he,h₂⟩ := kernel_diagonal _ hk
  have he₂ := congrArg Prod.snd he
  change (psiBoundary D V R g).2 = (psiBoundary D V R g).1 at he₂
  rw [psi_second] at he₂
  exact ⟨he.trans (congrArg (fun z : A => (z,z)) he₂.symm),\n    by simpa only [←he₂] using h₂⟩

theorem phi_cocycle (D : OrderedAction G A) (P T : A) (g h : G) :
    phiBoundary D P T (g*h) =
      phiBoundary D P T g + D.source g (phiBoundary D P T h) := by
  simp only [phiBoundary,source_mul,source_sub] <;> abel

theorem psi_cocycle (D : OrderedAction G A) (V R : A) (g h : G) :
    psiBoundary D V R (g*h) =
      psiBoundary D V R g + D.target g (psiBoundary D V R h) := by
  simp only [psiBoundary,target_mul,target_sub] <;> abel

/-- Literal positive coboundary of the difference between two choices of
a half. It is taken in the actual finite kernel because the difference
of two lifts of the same target lies in that kernel. -/
theorem phi_independent (D : OrderedAction G A) (P U T T' : A)
    (h : T+T=P+U) (h' : T'+T'=P+U) :
    ∃ E : A × A, sumDifference A E=0 ∧
      ∀ g, phiBoundary D P T' g-phiBoundary D P T g=D.source g E-E := by
  refine ⟨phiLift P T'-phiLift P T,?_,?_⟩
  · rw [map_sub,phi_lift P U T' h',phi_lift P U T h,sub_self]
  · intro g
    rw [phiBoundary,phiBoundary,source_sub]
    abel

theorem psi_independent (D : OrderedAction G A) (V W R R' : A)
    (h : R+R=V-W) (h' : R'+R'=V-W) :
    ∃ E : A × A, sumDifference A E=0 ∧
      ∀ g, psiBoundary D V R' g-psiBoundary D V R g=D.target g E-E := by
  refine ⟨psiLift V R'-psiLift V R,?_,?_⟩
  · rw [map_sub,psi_lift V W R' h',psi_lift V W R h,sub_self]
  · intro g
    rw [psiBoundary,psiBoundary,target_sub]
    abel

section Cartier

variable {M U : Type*} [AddCommGroup M] [CommGroup U]

/-- Product of the original Weil pairings on the two ordered sheets. -/
@[expose] def productPair (e : M → M → U) (P Q : M × M) : U :=
  e P.1 Q.1 * e P.2 Q.2

/-- If e is the actual Weil pairing on E[2], this is the pointed
Cartier pairing read: (X,0) is the chosen lift of the dual-kernel
point (X,X), and adding a diagonal two-torsion point does not
change the product value. This theorem proves that independence;
it does not postulate the geometric existence of e by itself. -/
theorem cartier_pair_read (e : M → M → U)
    (zero_right : ∀ T, e T 0=1) (add_right : ∀ T U V, e T (U+V)=e T U*e T V)
    (T X S : M) (hS : S+S=0) :
    productPair e (T,T) (X,0)=e T X ∧
      productPair e (T,T) ((X,0)+(S,S))=e T X := by
  constructor
  · change e T X*e T 0=e T X
    rw [zero_right,mul_one]
  · have h : e T S*e T S=1 := by rw [←add_right,hS,zero_right]
    change e T (X+S)*e T (0+S)=e T X
    rw [zero_add,add_right,mul_assoc,h,mul_one]

end Cartier

end OriginalRCMilneTwistedKummerCore318

#print axioms OriginalRCMilneTwistedKummerCore318.phi_diagonal
#print axioms OriginalRCMilneTwistedKummerCore318.psi_diagonal
#print axioms OriginalRCMilneTwistedKummerCore318.phi_independent
#print axioms OriginalRCMilneTwistedKummerCore318.psi_independent
#print axioms OriginalRCMilneTwistedKummerCore318.cartier_pair_read
