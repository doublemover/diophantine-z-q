module
public import EligibleGaussianEulerModel318
public section
noncomputable section
namespace TernaryQuadraticLineCover318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F]

@[expose] def Vector (F : Type*) := F×F×F
@[expose] def equation (κ : F) (v : Vector F) : Prop := 2*v.1*v.2.1=κ*v.2.2^2

/-- The q finite slopes and the actual infinity line of the original
ternary form κ*w²−2*x*z. -/
@[expose] def lineVector (κ : F) (t : Option F) (a : F) : Vector F :=
  match t with
  | none => (0,a,0)
  | some t => (a,κ*t^2*a/2,t*a)

@[expose] def lineCode (κ : F) (t : Option F) : Vector F →+ (F×F) := by
  cases t with
  | none => exact {
      toFun := fun v => (v.1,v.2.2)
      map_zero' := rfl
      map_add' := by intro v w; rfl }
  | some t => exact {
      toFun := fun v => (v.2.1-κ*t^2*v.1/2,v.2.2-t*v.1)
      map_zero' := by simp
      map_add' := by
        intro v w
        apply Prod.ext <;> dsimp <;> ring }

@[expose] def sectionVector (t : Option F) (y : F×F) : Vector F :=
  match t with
  | none => (y.1,0,y.2)
  | some _ => (0,y.1,y.2)

lemma code_section (κ : F) (t : Option F) (y : F×F) :
    lineCode κ t (sectionVector t y)=y := by
  cases t <;> simp only [lineCode,sectionVector,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    mul_zero,zero_div,sub_zero,Prod.eta]

lemma code_surjective (κ : F) (t : Option F) : Function.Surjective (lineCode κ t) :=
  fun y => ⟨sectionVector t y,code_section κ t y⟩

lemma code_zero_iff (κ : F) (t : Option F) (v : Vector F) :
    lineCode κ t v=0 ↔ ∃ a, v=lineVector κ t a := by
  rcases v with ⟨x,z,w⟩
  cases t with
  | none =>
    change (x,w)=(0,0) ↔ ∃ a, (x,z,w)=(0,a,0)
    constructor
    · intro h
      have hx := congrArg Prod.fst h
      have hw := congrArg Prod.snd h
      exact ⟨z,by simp only [hx,hw]⟩
    · rintro ⟨a,h⟩
      have hx := congrArg Prod.fst h
      have hw := congrArg (fun v : Vector F => v.2.2) h
      exact Prod.ext hx hw
  | some t =>
    change (z-κ*t^2*x/2,w-t*x)=(0,0) ↔ ∃ a, (x,z,w)=(a,κ*t^2*a/2,t*a)
    constructor
    · intro h
      have hz := sub_eq_zero.mp (congrArg Prod.fst h)
      have hw := sub_eq_zero.mp (congrArg Prod.snd h)
      exact ⟨x,by rw [hz,hw]⟩
    · rintro ⟨a,h⟩
      have hx := congrArg Prod.fst h
      have hz := congrArg (fun v : Vector F => v.2.1) h
      have hw := congrArg (fun v : Vector F => v.2.2) h
      simp only [hx,hz,hw,sub_self]

lemma line_equation (κ : F) (h2 : (2:F)≠0) (t : Option F) (a : F) :
    equation κ (lineVector κ t a) := by
  cases t <;> dsimp [equation,lineVector]
  · ring
  · field_simp [h2]
    <;> ring

/-- Every actual residue vector is covered, including the zero vector.
No isotropic direction or field-square-root oracle is supplied. -/
theorem exists_line (κ : F) (hκ : κ≠0) (h2 : (2:F)≠0) (v : Vector F)
    (hv : equation κ v) : ∃ t : Option F, ∃ a : F, v=lineVector κ t a := by
  rcases v with ⟨x,z,w⟩
  change 2*x*z=κ*w^2 at hv
  by_cases hx : x=0
  · subst x
    have hw2 : w^2=0 := (mul_eq_zero.mp (by simpa only [mul_zero,zero_mul] using hv.symm)).resolve_left hκ
    have hw : w=0 := sq_eq_zero_iff.mp hw2
    exact ⟨none,z,by simp only [lineVector,hw]⟩
  · have hz : κ*(w/x)^2*x/2=z := by
      field_simp [hx,h2]
      linear_combination -x*hv
    refine ⟨some (w/x),x,?_⟩
    simp only [lineVector,hz,div_mul_cancel₀ _ hx]

/-- The actual quadratic congruence is precisely the union of q+1 kernels. -/
theorem equation_iff_code (κ : F) (hκ : κ≠0) (h2 : (2:F)≠0) (v : Vector F) :
    equation κ v ↔ ∃ t : Option F, lineCode κ t v=0 := by
  constructor
  · intro hv
    obtain ⟨t,a,he⟩ := exists_line κ hκ h2 v hv
    exact ⟨t,(code_zero_iff κ t v).mpr ⟨a,he⟩⟩
  · rintro ⟨t,ht⟩
    obtain ⟨a,rfl⟩ := (code_zero_iff κ t v).mp ht
    exact line_equation κ h2 t a

end TernaryQuadraticLineCover318
