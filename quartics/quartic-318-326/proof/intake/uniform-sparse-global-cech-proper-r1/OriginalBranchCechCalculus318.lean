module
public import OriginalMarkedScalarSeparableTrace318
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace OriginalBranchCechCalculus318
open Polynomial
/-- First-order marked lift of an affine branch equation, in ANY square-zero test
algebra, using the actual deformed defining polynomial F+εG. -/
theorem genuine_lift {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (F G : k[X]) (x y ε a b : A) (hε : ε^2=0)
    (hF : y^2=aeval x F) (ht : 2*y*b-aeval x F.derivative*a=aeval x G) :
    (y+ε*b)^2=aeval (x+ε*a) F+ε*aeval (x+ε*a) G := by
  have hh : (ε*a)^2=0 := by simp [mul_pow,hε]
  rw [aeval_add_of_sq_eq_zero _ _ _ hh,aeval_add_of_sq_eq_zero _ _ _ hh]
  linear_combination hF+ε*ht+(b^2-a*aeval x G.derivative)*hε

/-- The cotangent identity holds in the genuine Kähler differential module of the
curve, not merely for independently chosen tangent vectors. -/
theorem kahler {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (F : k[X]) (x y : A) (hF : y^2=aeval x F) :
    (2*y) • KaehlerDifferential.D k A y=aeval x F.derivative • KaehlerDifferential.D k A x := by
  have h:=congrArg (KaehlerDifferential.D k A) hF
  rw [pow_two,Derivation.leibniz,Derivation.map_aeval] at h
  simpa [two_mul,add_smul] using h

/-- The ordinary-x lift fixes x; the branch-y lift fixes y. Their difference
is a relative vector field. The first equation retains the negative orientation. -/
theorem two_splittings {A : Type*} [CommRing A] (y fp g iy ip : A)
    (hy : (2*y)*iy=1) (hp : fp*ip=1) :
    (2*y)*(iy*g)-fp*0=g ∧ (2*y)*0-fp*(-ip*g)=g ∧
    (2*y)*(-(iy*g))=fp*(-ip*g) := by
  refine ⟨?_,?_,?_⟩
  · linear_combination g*hy
  · linear_combination g*hp
  · linear_combination -g*hy+g*hp

/-- In the branch-y frame, ω_i=2x^i dp/F' with p=y. Contracting the two
differentials with the actual difference of the splittings has precisely this
regular simple-pole coefficient. Neither a square root of the branch unit nor
a choice of sign of a local parameter appears. -/
theorem simple_pole {A : Type*} [CommRing A] (x y g iy ip : A)
    (hy : (2*y)*iy=1) (i j : ℕ) :
    y*((2*x^i*ip)*(2*x^j*ip)*(-(iy*g)))= -2*x^(i+j)*g*ip^2 := by
  rw [pow_add]
  linear_combination (-2*x^i*x^j*g*ip^2)*hy

theorem branch_parameter {A : Type*} [CommRing A] (u y h : A)
    (rel : y^2=u*h) (hu : IsUnit h) :
    Ideal.span ({u,y}:Set A)=Ideal.span ({y}:Set A) := by
  have hy : y∈Ideal.span ({y}:Set A) := Ideal.subset_span (by simp)
  have hy2 : y^2∈Ideal.span ({y}:Set A) := Ideal.pow_mem_of_mem _ hy 2 (by decide)
  have hmem : u∈Ideal.span ({y}:Set A) := by
    obtain ⟨b,hb⟩:=isUnit_iff_exists_inv.mp hu
    have hx : u=b*(u*h) := by linear_combination -u*hb
    rw [hx]
    exact (Ideal.span ({y}:Set A)).mul_mem_left b (rel ▸ hy2)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz; rcases hz with h | h
    · exact h ▸ hmem
    · exact (Set.mem_singleton_iff.mp h) ▸ hy
  · exact Ideal.span_mono (by intro a ha; simp_all)

/-- Literal regular coefficient specializes to the simple-pole residue; only the
inverse of F' had to be adjoined, and F' is already a unit at a simple branch. -/
theorem read_residue {k A L : Type*} [CommRing k] [CommRing A] [Field L]
    [Algebra k A] [Algebra k L] (φ : A→ₐ[k]L) (x ip : A) (F G : k[X]) (k₀ : ℕ)
    (hp : aeval x F.derivative*ip=1) :
    φ (-2*x^k₀*aeval x G*ip^2)= -2*(φ x)^k₀*aeval (φ x) G / (aeval (φ x) F.derivative)^2 := by
  have him := congrArg φ hp
  simp only [map_mul,map_one,← aeval_algHom_apply] at him
  have hi : φ ip=(aeval (φ x) F.derivative)⁻¹ := by
    calc
      φ ip = (aeval (φ x) F.derivative)⁻¹*(aeval (φ x) F.derivative*φ ip) := by
        rw [←mul_assoc,inv_mul_cancel₀ (left_ne_zero_of_mul_eq_one him),one_mul]
      _ = _ := by rw [him,mul_one]
  simp [map_pow,map_mul,map_ofNat,← aeval_algHom_apply,hi,div_eq_mul_inv]
end OriginalBranchCechCalculus318
#print axioms OriginalBranchCechCalculus318.genuine_lift
#print axioms OriginalBranchCechCalculus318.kahler
#print axioms OriginalBranchCechCalculus318.read_residue
