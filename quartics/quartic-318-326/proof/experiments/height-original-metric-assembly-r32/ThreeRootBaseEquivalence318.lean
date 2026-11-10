module
public import TensorBaseEquivalence318
public section
noncomputable section
namespace ThreeRootBaseEquivalence318
open Polynomial QuadraticPresentation318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type*} [CommRing A] [CommRing B]

@[expose] def root (e : A ≃+* B) (a : A) (b : B) (h : e a=b) :
    RootRing a ≃+* RootRing b :=
  AdjoinRoot.mapRingEquiv e (polynomial a) (polynomial b)
    (by rw [polynomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,
      Polynomial.map_C,h];exact Associated.refl _)

@[simp] theorem root_base (e : A ≃+* B) (a : A) (b : B) (h : e a=b) (r : A) :
    root e a b h (algebraMap A (RootRing a) r)=algebraMap B (RootRing b) (e r) := by
  exact AdjoinRoot.map_of ..

@[simp] theorem root_root (e : A ≃+* B) (a : A) (b : B) (h : e a=b) :
    root e a b h (AdjoinRoot.root (polynomial a))=AdjoinRoot.root (polynomial b) :=
  AdjoinRoot.map_root ..

@[expose] def pair (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i) :
    ThreeRootOrder318.Pair12 a ≃+* ThreeRootOrder318.Pair12 b :=
  TensorBaseEquivalence318.equiv e (root e (a 1) (b 1) (h 1))
    (root e (a 2) (b 2) (h 2)) (root_base ..) (root_base ..)

theorem pair_base (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i)
    (r : A) : pair e a b h (algebraMap A (ThreeRootOrder318.Pair12 a) r)=
      algebraMap B (ThreeRootOrder318.Pair12 b) (e r) :=
  TensorBaseEquivalence318.equiv_base ..

@[expose] def three (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i) :
    ThreeRootOrder318.Order a ≃+* ThreeRootOrder318.Order b :=
  TensorBaseEquivalence318.equiv e (root e (a 0) (b 0) (h 0)) (pair e a b h)
    (root_base ..) (pair_base ..)

theorem three_base (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i)
    (r : A) : three e a b h (algebraMap A (ThreeRootOrder318.Order a) r)=
      algebraMap B (ThreeRootOrder318.Order b) (e r) :=
  TensorBaseEquivalence318.equiv_base ..
end ThreeRootBaseEquivalence318
