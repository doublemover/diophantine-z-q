module
public import ActualCCLRetainedH22Boundary318
public import ActualGlobalTraceTorsionSupported318

public section

namespace ActualCCLRelativePrimitive318
open ActualCCLRetainedH22Boundary318 ActualGlobalTraceTorsionSupported318
open ActualOldPlaceDivisionNorm318

variable {G Γ B M I W : Type*} [Group G] [Group Γ]
variable [AddCommGroup B] [AddCommGroup M] [Fintype I]
variable {U0 U1 V0 V1 : W → Type*}
variable [∀ w, AddCommGroup (U0 w)] [∀ w, AddCommGroup (U1 w)]
variable [∀ w, AddCommGroup (V0 w)] [∀ w, AddCommGroup (V1 w)]

/-- The exact CCL split norm feeds the same original H21 cochain and
every retained H22 correction. This theorem does not produce hNorm
from a class field or prove the arithmetic hCCL point identity.
The original H21 weighted degree-zero primitive is retained literally
after multiplying by the single annihilator m of the same trace S. -/
theorem from_original_split_pointNorm
    (π : G →* Γ) (onto : Function.Surjective π)
    (ρ : G →* AddMonoid.End B) (ρS : Γ →* AddMonoid.End M)
    (iT : M →+ B) (inj : Function.Injective iT)
    (compat : ∀ g x, ρ g (iT x) = iT (ρS (π g) x))
    (precision L m : ℕ) (a_r : ℤ)
    (killM : ∀ x : M, (2^precision : ℕ) • x = 0)
    (tor : ∀ x : B, (2^precision : ℕ) • x = 0 → ∃ y : M, iT y = x)
    (H : Subgroup G) (r : I → G) (e : G → Equiv.Perm I) (h : G → I → H)
    (tile : ∀ g i, r (e g i) * (h g i : G) = g * r i)
    (Pplus S Q : B) (hQ : (2^precision : ℕ) • Q = Pplus)
    (hNorm : pointNorm ρ r Pplus = (a_r - 2) • S)
    (hmS : m • S = 0)
    (cPlus ν : M) (b : H → B) (p : Γ → M)
    (hb : ∀ x : H, b x = L • delta ρ (x:G) Q + delta ρ (x:G) (iT cPlus))
    (hp : ∀ g, iT (p (π g)) = transferAt ρ H r (e g) (h g) b + delta ρ g (iT ν))
    (A : LocalData (U0:=U0) (U1:=U1) (V0:=V0) (V1:=V1) ρS)
    (u : (w : W) → U1 w) (q : (w : W) → V0 w)
    (hH22 : ∀ w, A.dV w (q w) = A.loc1 w p - A.i1 w (u w)) :
    ∃ (v : M) (w0 : (w : W) → U0 w),
      iT v = m • (L • pointNorm ρ r Q + pointNorm ρ r (iT cPlus) + iT ν) ∧
      relativeBoundary ρS A (v,w0) = m • ((p,u,q) : Degree1 Γ M U1 V0) := by
  obtain ⟨v,hv,hδ⟩ := supported_mul_trace_torsion π onto ρ ρS iT inj compat
    (2^precision) L m (a_r-2) killM tor H r e h tile Pplus S Q hQ hNorm hmS cPlus ν b p hb hp
  obtain ⟨w0, hw0⟩ := retain_all_H22 ρS A m v p u q hδ hH22
  exact ⟨v,w0,hv,hw0⟩

end ActualCCLRelativePrimitive318

#print axioms ActualCCLRelativePrimitive318.from_original_split_pointNorm
