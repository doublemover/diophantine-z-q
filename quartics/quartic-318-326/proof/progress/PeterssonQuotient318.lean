module
public import QuadraticFiber318
public section
noncomputable section
open DerivativeCocycle318 QuadraticFiber318
namespace PeterssonQuotient318
set_option maxHeartbeats 0

abbrev Base (H:Subgroup G) := MulAction.orbitRel.Quotient H UpperHalfPlane
abbrev Total (H:Subgroup G) := MulAction.orbitRel.Quotient H Fiber

/-- The genuine orbit quotient norm, obtained from the proved action invariance. -/
@[expose] def norm (H:Subgroup G) : Total H→ℝ := Quotient.lift fiberNorm (by
  intro a b hab
  obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp hab
  change (g:G) • b=a at hg
  rw [←hg]
  exact fiberNorm_transport g b)

theorem norm_mk (H:Subgroup G) (v:Fiber) : norm H ⟦v⟧=fiberNorm v := rfl

theorem norm_nonnegative (H:Subgroup G) (v:Total H) : 0≤norm H v := by
  induction v using Quotient.inductionOn with
  | h v => exact fiberNorm_nonnegative v

/-- Actual projection of quotient differential fibers onto the orbit base. -/
@[expose] def projection (H:Subgroup G) : Total H→Base H := Quotient.lift (fun v=>⟦v.point⟧) (by
  intro a b hab
  obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp hab
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  refine ⟨g,?_⟩
  change (g:G) • b=a at hg
  exact congrArg Fiber.point hg)

@[expose] def zeroFiber (z:UpperHalfPlane) : Fiber := ⟨z,0⟩

theorem zeroFiber_transport (g:G) (z:UpperHalfPlane) : g • zeroFiber z=zeroFiber (g • z) := by
  apply Fiber.ext
  · rfl
  · simp only [smul_value,zeroFiber,zero_div]

@[expose] def zeroSection (H:Subgroup G) : Base H→Total H := Quotient.lift (fun z=>⟦zeroFiber z⟧) (by
  intro a b hab
  obtain ⟨g,hg⟩:=MulAction.orbitRel_apply.mp hab
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  refine ⟨g,?_⟩
  change (g:G) • b=a at hg
  change (g:G) • zeroFiber b=zeroFiber a
  rw [zeroFiber_transport,hg])

theorem projection_zeroSection (H:Subgroup G) (v:Base H) :
    projection H (zeroSection H v)=v := by
  induction v using Quotient.inductionOn with
  | h v => rfl

theorem norm_zeroSection (H:Subgroup G) (v:Base H) : norm H (zeroSection H v)=0 := by
  induction v using Quotient.inductionOn with
  | h v => exact (fiberNorm_eq_zero (zeroFiber v)).mpr rfl

/-- The descended norm vanishes exactly on the actual zero section, even when
the chosen subgroup has stabilizers. No freeness or compactness is assumed. -/
theorem norm_eq_zero_iff (H:Subgroup G) (v:Total H) :
    norm H v=0 ↔ v=zeroSection H (projection H v) := by
  constructor
  · induction v using Quotient.inductionOn with
    | h v =>
      intro hv
      have hz:v.value=0:=(fiberNorm_eq_zero v).mp hv
      have he:v=zeroFiber v.point:=by apply Fiber.ext <;> simp [zeroFiber,hz]
      exact congrArg (Quotient.mk (MulAction.orbitRel H Fiber)) he
  · intro hv
    rw [hv,norm_zeroSection]

end PeterssonQuotient318
#print axioms PeterssonQuotient318.norm
#print axioms PeterssonQuotient318.norm_eq_zero_iff
