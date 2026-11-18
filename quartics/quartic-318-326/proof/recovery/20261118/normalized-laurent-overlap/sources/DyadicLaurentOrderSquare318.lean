module
public import FourRootOrder318
public import UnitRootScaling318
public section
noncomputable section
namespace DyadicLaurentOrderSquare318
open TensorProduct QuadraticPresentation318
variable {K : Type*} [CommRing K]

@[simp] theorem scaled_root (a b : K) (u : Kˣ) (h : a=b*(u:K)^2) :
    UnitRootScaling318.equiv a b u h (AdjoinRoot.root (polynomial a)) =
      algebraMap K (RootRing b) (u:K) * AdjoinRoot.root (polynomial b) :=
  UnitRootScaling318.hom_root a b u h

theorem one_square (p q r s : K) (u v : Kˣ)
    (hpq : p=q*(u:K)^2) (hqs : q=s*(v:K)^2)
    (hpr : p=r*(v:K)^2) (hrs : r=s*(u:K)^2) :
    (UnitRootScaling318.equiv p q u hpq).trans (UnitRootScaling318.equiv q s v hqs) =
      (UnitRootScaling318.equiv p r v hpr).trans (UnitRootScaling318.equiv r s u hrs) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply AdjoinRoot.algHom_ext
  simp only [AlgEquiv.coe_toAlgHom,AlgEquiv.trans_apply,scaled_root,map_mul,AlgEquiv.commutes]
  ring

@[expose] def four (a b : Fin 4 → K) (u : Fin 4 → Kˣ)
    (h : ∀ i,a i=b i*(u i:K)^2) : FourRootOrder318.Order a ≃ₐ[K] FourRootOrder318.Order b :=
  Algebra.TensorProduct.congr
    (Algebra.TensorProduct.congr (UnitRootScaling318.equiv _ _ (u 0) (h 0))
      (UnitRootScaling318.equiv _ _ (u 1) (h 1)))
    (Algebra.TensorProduct.congr (UnitRootScaling318.equiv _ _ (u 2) (h 2))
      (UnitRootScaling318.equiv _ _ (u 3) (h 3)))

/-- Equality of both homomorphisms on the entire four-root algebra, not just
equality of their squared generator images. -/
theorem four_square (p q r s : Fin 4 → K) (u v : Fin 4 → Kˣ)
    (hpq : ∀ i,p i=q i*(u i:K)^2) (hqs : ∀ i,q i=s i*(v i:K)^2)
    (hpr : ∀ i,p i=r i*(v i:K)^2) (hrs : ∀ i,r i=s i*(u i:K)^2) :
    (four p q u hpq).trans (four q s v hqs) = (four p r v hpr).trans (four r s u hrs) := by
  have H (i : Fin 4) := one_square _ _ _ _ (u i) (v i) (hpq i) (hqs i) (hpr i) (hrs i)
  simp only [four,←Algebra.TensorProduct.congr_trans,H]

@[expose] def finiteRat (a b : Fin 4 → K) (t : Kˣ) (i : Fin 4) : K := a i*((t:K)-b i)
@[expose] def inverseRat (a b : Fin 4 → K) (t : Kˣ) (i : Fin 4) : K :=
  a i*(↑t⁻¹:K)*(1-b i*(↑t⁻¹:K))

theorem inverse_relation (a b : Fin 4 → K) (t : Kˣ) (i : Fin 4) :
    inverseRat a b t i=finiteRat a b t i*(↑t⁻¹:K)^2 := by
  unfold inverseRat finiteRat
  have h : (t:K)*(↑t⁻¹:K)=1 := t.mul_inv
  linear_combination (-a i*(↑t⁻¹:K)) * h

theorem finite_ratio (m a b : Fin 4 → K) (u : Fin 4 → Kˣ)
    (h : ∀ i,m i=a i*(u i:K)^2) (t : Kˣ) (i : Fin 4) :
    finiteRat m b t i=finiteRat a b t i*(u i:K)^2 := by
  unfold finiteRat; rw [h i]; ring

theorem inverse_ratio (m a b : Fin 4 → K) (u : Fin 4 → Kˣ)
    (h : ∀ i,m i=a i*(u i:K)^2) (t : Kˣ) (i : Fin 4) :
    inverseRat m b t i=inverseRat a b t i*(u i:K)^2 := by
  unfold inverseRat; rw [h i]; ring

/-- With z=t⁻¹ and reciprocal generator z*r_i, the two actual generic
chart identifications on G_m agree after untwisting the four coefficients.
Their equality includes all signs, not merely the Kummer classes. -/
theorem actual_laurent_square (m a b : Fin 4 → K) (u : Fin 4 → Kˣ)
    (h : ∀ i,m i=a i*(u i:K)^2) (t : Kˣ) :
    (four _ _ u (inverse_ratio m a b u h t)).trans
      (four _ _ (fun _ => t⁻¹) (inverse_relation a b t)) =
    (four _ _ (fun _ => t⁻¹) (inverse_relation m b t)).trans
      (four _ _ u (finite_ratio m a b u h t)) :=
  four_square _ _ _ _ u (fun _ => t⁻¹) _ _ _ _

end DyadicLaurentOrderSquare318
