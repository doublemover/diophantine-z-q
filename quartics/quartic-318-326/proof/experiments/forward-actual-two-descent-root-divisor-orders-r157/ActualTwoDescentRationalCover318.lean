module
public import ActualTwoDescentKummerPointData318
public section
noncomputable section
namespace ActualTwoDescentRationalCover318
open ActualTwoDescentPointExtraction318

/-- A rational, not merely local, point on the retained beta-cover.
All three nonvanishing conditions are explicit. -/
structure Cover (β n : ℚ) where
  u : ℚ
  v : ℚ
  r : ℚ
  u_ne : u≠0
  v_ne : v≠0
  r_ne : r≠0
  first : β*u^2-v^2=4*n
  second : r^2-β*v^2=β*n

/-- The quadratic-cover equations recover the ORIGINAL Kummer convention
(x+3n,x-n)=(beta*u^2,v^2), without a rank or local-global hypothesis. -/
@[expose] def Cover.toKummer {β n : ℚ} (P : Cover β n) : KummerPoint β n := by
  have hx : β*(n+P.v^2)=P.r^2 := by nlinarith [P.second]
  have hx0 : n+P.v^2≠0 := by
    intro h
    rw [h,mul_zero] at hx
    exact (pow_ne_zero 2 P.r_ne) hx.symm
  have hfirst : (n+P.v^2)+3*n=β*P.u^2 := by nlinarith [P.first]
  refine ⟨n+P.v^2,P.u*P.v*P.r,P.u,P.v,hx0,P.u_ne,P.v_ne,?_,hfirst,?_⟩
  · rw [show (n+P.v^2)-n=P.v^2 by ring,hfirst]
    calc
      (P.u*P.v*P.r)^2=P.u^2*P.v^2*P.r^2 := by ring
      _=P.u^2*P.v^2*(β*(n+P.v^2)) := by rw [hx]
      _=(n+P.v^2)*P.v^2*(β*P.u^2) := by ring
  · ring

/-- Conversely, division uses the two actual nonzero Kummer coordinates,
not a presumed nonzero ordinate. The latter is deduced from the curve. -/
def ofKummer {β n : ℚ} (hβ : β≠0) (P : KummerPoint β n) : Cover β n := by
  have hr : (P.y/(P.u*P.v))^2=β*P.x := by
    rw [div_pow,P.curve,P.first,P.second]
    field_simp [P.u_ne,P.v_ne] <;> ring
  have hr0 : P.y/(P.u*P.v)≠0 := by
    intro h
    rw [h,zero_pow (by omega : (2:ℕ)≠0)] at hr
    exact (mul_ne_zero hβ P.x_ne) hr.symm
  refine ⟨P.u,P.v,P.y/(P.u*P.v),P.u_ne,P.v_ne,hr0,?_,?_⟩
  · nlinarith [P.first,P.second]
  · rw [hr]
    calc
      β*P.x-β*P.v^2=β*(P.x-P.v^2) := by ring
      _=β*n := by congr 1; nlinarith [P.second]

/-- Exact rational existence equivalence, with all nondegeneracy retained. -/
theorem cover_iff_kummer (β n : ℚ) (hβ : β≠0) :
    Nonempty (Cover β n) ↔ Nonempty (KummerPoint β n) :=
  ⟨fun ⟨P⟩ => ⟨P.toKummer⟩,fun ⟨P⟩ => ⟨ofKummer hβ P⟩⟩

@[simp] theorem toKummer_x {β n : ℚ} (P : Cover β n) :
    P.toKummer.x=n+P.v^2 := rfl

@[simp] theorem toKummer_y {β n : ℚ} (P : Cover β n) :
    P.toKummer.y=P.u*P.v*P.r := rfl

end ActualTwoDescentRationalCover318
