module
public import LocallyUniqueMonicRootSimple318
public import ClosedFiberLocalInjectivity318
public section
noncomputable section
namespace LocallyInjectiveRootProjectionSimple318
open Set Polynomial MonicRootProjectionOpen318
variable {E : Type*} [TopologicalSpace E]

/-- Local injectivity of the projection on the WHOLE monic root model,
not merely on a selected branch, rules out a multiple center root when
simple fibers are dense. All neighborhoods use the ambient topology. -/
theorem derivative_ne_zero (p : E → Polynomial ℂ) (N : ℕ)
    (hm : ∀ y, (p y).Monic) (hd : ∀ y, (p y).natDegree = N)
    (hp : ∀ k, Continuous (fun y => (p y).coeff k))
    (b : E → ℂ) (hb : Continuous b) (hroot : ∀ y, (p y).IsRoot (b y))
    (hs : Dense {y : E | (p y).Separable}) (x : E)
    (V : Set (Roots p)) (hV : IsOpen V) (hx : (⟨(x,b x),hroot x⟩ : Roots p) ∈ V)
    (hinj : Set.InjOn (fun q : Roots p => q.val.1) V) :
    (p x).derivative.eval (b x) ≠ 0 := by
  obtain ⟨O,hO,rfl⟩ := isOpen_induced_iff.mp hV
  have hxO : (x,b x) ∈ O := hx
  let S : Set E := (fun y => (y,b y)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_id.prodMk hb)
  let U : Set (E × ℂ) := O ∩ Prod.fst ⁻¹' S
  have hU : IsOpen U := hO.inter (hS.preimage continuous_fst)
  apply LocallyUniqueMonicRootSimple318.derivative_ne_zero p N hm hd hp b hb hroot hs x U hU
    ⟨hxO,hxO⟩
  intro y z hyz hz
  have hzV : (⟨(y,z),hz⟩ : Roots p) ∈ Subtype.val ⁻¹' O := hyz.1
  have hbV : (⟨(y,b y),hroot y⟩ : Roots p) ∈ Subtype.val ⁻¹' O := hyz.2
  have he := hinj hzV hbV rfl
  exact congrArg (fun q : Roots p => q.val.2) he
end LocallyInjectiveRootProjectionSimple318
