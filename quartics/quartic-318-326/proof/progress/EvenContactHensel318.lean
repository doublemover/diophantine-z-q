module
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace EvenContactHensel318
open Polynomial IsLocalRing
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] [HenselianLocalRing R]

/-- A unit with a residue square root has an actual square root in the
Henselian local ring. Both the residue lift and the derivative unit are derived. -/
theorem unit_square_root_of_residue (u:Rˣ) (h2:(2:ResidueField R)≠0)
    (hres:∃b:ResidueField R,b^2=residue R (u:R)) :
    ∃a:R,a^2=(u:R) ∧ IsUnit a := by
  obtain ⟨b,hb⟩:=hres
  obtain ⟨a₀,ha₀⟩:=residue_surjective (R:=R) b
  have hb0:b≠0 := by
    intro hz
    have hu:=((u.isUnit).map (residue R)).ne_zero
    apply hu
    rw [←hb,hz,zero_pow (by decide)]
  let f:R[X]:=X^2-C (u:R)
  have hmon:f.Monic := by exact monic_X_pow_sub_C (u:R) (by decide)
  have heval:f.eval a₀∈maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp only [f,eval_sub,eval_pow,eval_X,eval_C,map_sub,map_pow,ha₀,hb,sub_self]
  have htwo:IsUnit (2:R):=(residue_ne_zero_iff_isUnit _).mp (by simpa only [map_ofNat] using h2)
  have hau:IsUnit a₀:=(residue_ne_zero_iff_isUnit _).mp (by rw [ha₀]; exact hb0)
  have hder:IsUnit (f.derivative.eval a₀) := by
    simpa [f,derivative_pow] using htwo.mul hau
  obtain ⟨a,ha,-⟩:=HenselianLocalRing.is_henselian f hmon a₀ heval hder
  have hs:a^2=(u:R) := by simpa [f,Polynomial.IsRoot.def,sub_eq_zero] using ha
  refine ⟨a,hs,?_⟩
  have hu:IsUnit (a^2):=hs.symm ▸ u.isUnit
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hu

/-- In a strict Henselian local ring with residue characteristic different from2,
every unit is a square; the separably closed field supplies the residue root. -/
theorem unit_square_root [IsSepClosed (ResidueField R)]
    (u:Rˣ) (h2:(2:ResidueField R)≠0) :
    ∃a:R,a^2=(u:R) ∧ IsUnit a := by
  let:NeZero (2:ResidueField R):=⟨h2⟩
  exact unit_square_root_of_residue u h2 (IsSepClosed.exists_pow_nat_eq _ 2)

/-- An actual even-contact expression has a root before adjoining any ramified
quadratic extension. This includes contact exponent zero and the zero parameter. -/
theorem even_contact_root [IsSepClosed (ResidueField R)]
    (u:Rˣ) (h2:(2:ResidueField R)≠0) (pi:R) (k:ℕ) :
    ∃z:R,z^2=(u:R)*pi^(2*k) := by
  obtain ⟨a,ha,-⟩:=unit_square_root u h2
  refine ⟨a*pi^k,?_⟩
  rw [mul_pow,ha,←pow_mul]
  congr 2
  omega

/-- A finite even value of the actual canonical DVR additive valuation gives
an actual root in the ring. The unit/uniformizer decomposition is derived. -/
theorem square_root_of_even_valuation [IsDomain R] [IsDiscreteValuationRing R]
    [IsSepClosed (ResidueField R)] (h2:(2:ResidueField R)≠0)
    (x:R) (k:ℕ) (hv:IsDiscreteValuationRing.addVal R x=((2*k:ℕ):ℕ∞)) :
    ∃z:R,z^2=x := by
  have hx:x≠0 := by
    intro hz
    rw [hz,IsDiscreteValuationRing.addVal_zero] at hv
    exact ENat.top_ne_natCast (2*k) hv
  obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n,u,hu⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hpi
  have hn:n=2*k:=by
    have hh:=IsDiscreteValuationRing.addVal_def x u hpi n hu
    rw [hh] at hv
    exact_mod_cast hv
  subst n
  rw [hu]
  exact even_contact_root u h2 pi k

/-- Exact square criterion, including zero, in a strict Henselian DVR away
from residue characteristic two. Odd positive contact orders cannot be squares. -/
theorem square_iff_even_valuation [IsDomain R] [IsDiscreteValuationRing R]
    [IsSepClosed (ResidueField R)] (h2:(2:ResidueField R)≠0) (x:R) :
    (∃z:R,z^2=x) ↔ x=0 ∨ ∃k:ℕ,IsDiscreteValuationRing.addVal R x=((2*k:ℕ):ℕ∞) := by
  constructor
  · rintro ⟨z,rfl⟩
    by_cases hz:z=0
    · exact Or.inl (by rw [hz]; simp)
    · right
      obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
      obtain ⟨k,u,hu⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hpi
      refine ⟨k,?_⟩
      rw [IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_def z u hpi k hu]
      simp [nsmul_eq_mul]
  · rintro (rfl|⟨k,hk⟩)
    · exact ⟨0,by simp⟩
    · exact square_root_of_even_valuation h2 x k hk

/-- The normalized unit equation has a simple actual root in the ring. -/
theorem unit_square_root_simple [IsSepClosed (ResidueField R)]
    (u:Rˣ) (h2:(2:ResidueField R)≠0) :
    ∃a:R,a^2=(u:R) ∧ IsUnit (2*a) := by
  obtain ⟨a,ha,hau⟩:=unit_square_root u h2
  have ht:IsUnit (2:R):=(residue_ne_zero_iff_isUnit _).mp
    (by simpa only [map_ofNat] using h2)
  exact ⟨a,ha,ht.mul hau⟩

/-- Every root in every field receiving the ring is one of the two ring roots.
This is the all-fiber-points step in the even-contact argument, not only a
choice of one square root. Actual strict-henselization/model realization is separate. -/
theorem every_root_of_even_contact [IsDomain R] [IsDiscreteValuationRing R]
    [IsSepClosed (ResidueField R)] (h2:(2:ResidueField R)≠0)
    (x:R) (k:ℕ) (hv:IsDiscreteValuationRing.addVal R x=((2*k:ℕ):ℕ∞))
    (L:Type*) [Field L] (f:R→+*L) :
    ∃z:R,z^2=x ∧ ∀y:L,y^2=f x→y=f z ∨ y= -(f z) := by
  obtain ⟨z,hz⟩:=square_root_of_even_valuation h2 x k hv
  refine ⟨z,hz,?_⟩
  intro y hy
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [←map_pow,hz]
  exact hy

end EvenContactHensel318
