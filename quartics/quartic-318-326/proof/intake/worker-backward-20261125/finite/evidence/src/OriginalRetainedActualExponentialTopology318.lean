module

public import OriginalRetainedF33ExponentialQuotient318
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section
noncomputable section

namespace OriginalRetainedActualExponentialTopology318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedF33ExponentialQuotient318
open scoped CategoryTheory.Obj CategoryTheory.MonObj Topology

variable {A₃₃ Y₃₃ : Scheme} (a₃₃ : A₃₃⟶Y₃₃) [GrpObj (Over.mk a₃₃)]
variable {E : Type} [Field E] (σ : E→+*ℂ) (P : Spec (CommRingCat.of E)⟶Y₃₃)
local notation "G" => Additive (Points a₃₃ σ P)

variable [TopologicalSpace G] [SeparatelyContinuousAdd G]
variable (exp : Tangent→+G)
variable (U : Set G) (Uopen : IsOpen U)
variable {t : ℝ} (tpos : 0<t)
local notation "B" => {w : Tangent // ‖w‖<t}

variable (actualLocal : B ≃ₜ U)
variable (same : ∀ w : B, (actualLocal w).val=exp w.val)

include same tpos in
/-- The one original exp is continuous globally. Its only topological
input is the actual marked local homeomorphism plus the true fixed
translations, rather than a supplied analytic group isomorphism. -/
theorem exp_continuous : Continuous exp := by
  have hLoc : ContinuousOn exp {x | ‖x‖<t} := by
    apply continuousOn_iff_continuous_domRestrict.2
    have eq : (fun w : B => exp w.val) = Subtype.val ∘ actualLocal :=
      funext (fun w => (same w).symm)
    change Continuous (fun w : B => exp w.val)
    rw [eq]
    exact continuous_subtype_val.comp actualLocal.continuous_toFun
  have smallOpen : IsOpen ({x : Tangent | ‖x‖<t} : Set Tangent) :=
    isOpen_lt continuous_norm continuous_const
  have atZero : ContinuousAt exp 0 :=
    hLoc.continuousAt (smallOpen.mem_nhds (by simpa only [Set.mem_setOf_eq,norm_zero] using tpos))
  apply continuous_iff_continuousAt.2
  intro x
  have shift : ContinuousAt (fun y : Tangent => y-x) x :=
    (continuous_id.sub continuous_const).continuousAt
  have q0 : ContinuousAt exp ((fun y : Tangent => y-x) x) := by
    rw [sub_self]
    exact atZero
  have trans : ContinuousAt (fun y : Tangent => exp (y-x)+exp x) x :=
    (continuous_add_const (exp x)).continuousAt.comp (q0.comp shift)
  have eq : (fun y : Tangent => exp (y-x)+exp x) = exp := by
    funext y
    rw [map_sub,sub_add_cancel]
  rwa [eq] at trans

include same tpos Uopen in
/-- Each actual small open neighborhood in the one exp moves by an
installed translation. The full quotient projection is therefore
open without presuming any quotient topology on the arithmetic group. -/
theorem exp_open : IsOpenMap exp := by
  intro S hS
  apply isOpen_iff_mem_nhds.2
  rintro _ ⟨x,hx,rfl⟩
  let V : Set B := {w | w.val+x∈S}
  have Vopen : IsOpen V :=
    ((continuous_add_const x).comp continuous_subtype_val).isOpen_preimage _ hS
  let W : Set G := Subtype.val '' (actualLocal '' V)
  have Wopen : IsOpen W :=
    Uopen.isOpenMap_subtype_val _ (actualLocal.isOpenMap _ Vopen)
  let shift : G→G := fun y=>y+exp x
  have sOpen : IsOpen (shift '' W) := isOpenMap_add_right (exp x) _ Wopen
  have zeroV : (⟨0,by simpa only [norm_zero] using tpos⟩ : B)∈V := by
    change (0:Tangent)+x∈S
    rwa [zero_add]
  have zeroW : (0:G)∈W := by
    let z : B := ⟨0,by simpa only [norm_zero] using tpos⟩
    exact ⟨actualLocal z,⟨z,zeroV,rfl⟩,(same z).trans (map_zero exp)⟩
  have here : exp x∈shift '' W := ⟨0,zeroW,zero_add _⟩
  refine Filter.mem_of_superset (sOpen.mem_nhds here) ?_
  rintro _ ⟨y,⟨u,⟨z,hz,rfl⟩,rfl⟩,rfl⟩
  refine ⟨z.val+x,hz,?_⟩
  rw [map_add,same z]
  rfl

include same in
/-- Actual isolation on a fixed origin ball, independent from any
choice of a basis for the actual periods. -/
theorem ker_origin_isolated (z : exp.ker) (small : ‖z.val‖<t)
    (tpos : 0<t) : z.val=0 := by
  let x : B := ⟨z.val,small⟩
  let e : B := ⟨0,by simpa only [norm_zero] using tpos⟩
  have h : (actualLocal x).val=(actualLocal e).val :=
    (same x).trans ((show exp z.val=0 from z.property).trans
      ((map_zero exp).symm.trans (same e).symm))
  exact congrArg Subtype.val (actualLocal.injective (Subtype.ext h))

end OriginalRetainedActualExponentialTopology318
