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

lemma mapped_polynomial (e : A ≃+* B) (a : A) (b : B) (h : e a=b) :
    Associated ((polynomial a).map e.toRingHom) (polynomial b) := by
  simp only [polynomial,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  change Associated (X^2-C (e a)) (X^2-C b)
  rw [h]

@[expose] def root (e : A ≃+* B) (a : A) (b : B) (h : e a=b) :
    RootRing a ≃+* RootRing b :=
  AdjoinRoot.mapRingEquiv e (polynomial a) (polynomial b)
    (mapped_polynomial e a b h)

@[simp] theorem root_base (e : A ≃+* B) (a : A) (b : B) (h : e a=b) (r : A) :
    root e a b h (algebraMap A (RootRing a) r)=algebraMap B (RootRing b) (e r) := by
  change AdjoinRoot.map e.toRingHom (polynomial a) (polynomial b)
    (mapped_polynomial e a b h).symm.dvd (AdjoinRoot.of (polynomial a) r)=
      AdjoinRoot.of (polynomial b) (e r)
  exact AdjoinRoot.map_of e.toRingHom (polynomial a) (polynomial b)
    (mapped_polynomial e a b h).symm.dvd r

@[simp] theorem root_root (e : A ≃+* B) (a : A) (b : B) (h : e a=b) :
    root e a b h (AdjoinRoot.root (polynomial a))=AdjoinRoot.root (polynomial b) := by
  change AdjoinRoot.map e.toRingHom (polynomial a) (polynomial b)
    (mapped_polynomial e a b h).symm.dvd (AdjoinRoot.root (polynomial a))=_
  exact AdjoinRoot.map_root e.toRingHom (polynomial a) (polynomial b)
    (mapped_polynomial e a b h).symm.dvd

@[expose] def pair (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i) :
    ThreeRootOrder318.Pair12 a ≃+* ThreeRootOrder318.Pair12 b :=
  TensorBaseEquivalence318.equiv e (root e (a 1) (b 1) (h 1))
    (root e (a 2) (b 2) (h 2))
    (fun r=>root_base e (a 1) (b 1) (h 1) r)
    (fun r=>root_base e (a 2) (b 2) (h 2) r)

theorem pair_base (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i)
    (r : A) : pair e a b h (algebraMap A (ThreeRootOrder318.Pair12 a) r)=
      algebraMap B (ThreeRootOrder318.Pair12 b) (e r) :=
  TensorBaseEquivalence318.equiv_base ..

@[expose] def three (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i) :
    ThreeRootOrder318.Order a ≃+* ThreeRootOrder318.Order b :=
  TensorBaseEquivalence318.equiv e (root e (a 0) (b 0) (h 0)) (pair e a b h)
    (fun r=>root_base e (a 0) (b 0) (h 0) r) (fun r=>pair_base e a b h r)

theorem three_base (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B) (h : ∀ i,e (a i)=b i)
    (r : A) : three e a b h (algebraMap A (ThreeRootOrder318.Order a) r)=
      algebraMap B (ThreeRootOrder318.Order b) (e r) :=
  TensorBaseEquivalence318.equiv_base ..
end ThreeRootBaseEquivalence318
