module
public import ActualTwoDescentOriginalPerfectPairing318
public section
noncomputable section
namespace ActualCasselsTateTwoWeilUniqueness318
open ActualTwoDescentBinarySymplectic318 ActualTwoDescentOriginalTorsionPairing318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentSquareOneBinary318
private abbrev V := BinaryPlane
private abbrev k := ZMod 2
private def e : V := (1,0)
private def f : V := (0,1)

private lemma coords (B : V →+ k) (x : V) : B x = x.1*B e+x.2*B f := by
  rcases x with ⟨a,b⟩
  fin_cases a <;> fin_cases b
  · simpa [e,f] using B.map_zero
  · simp [e,f]
  · simp [e,f]
  · have h : ((1,1) : V) = e+f := by decide
    change B (1,1) = 1*B e+1*B f
    rw [h,map_add,one_mul,one_mul]

private def atRight (B : V →+ (V →+ k)) (y : V) : V →+ k where
  toFun x := B x y
  map_zero' := congrArg (fun u : V →+ k => u y) B.map_zero
  map_add' x z := congrArg (fun u : V →+ k => u y) (B.map_add x z)

/-- Characteristic two in dimension two is essential: there is just one
nondegenerate alternating bilinear form, not a family up to a unit. -/
theorem binary_unique (B : V →+ (V →+ k)) (ha : ∀ x, B x x=0)
    (hn : ∀ x, (∀ y, B x y=0) → x=0) (x y : V) : B x y = binaryPairing x y := by
  have hef0 : B e f ≠ 0 := by
    intro h
    have he := hn e (fun z => by rw [coords (B e) z,ha e,h]; simp)
    exact (by decide : e ≠ 0) he
  have hef : B e f = 1 := by
    generalize hh : B e f = u at hef0 ⊢
    fin_cases u <;> simp_all
  have hfe : B f e = 1 := by
    have h := ha (e+f)
    rw [map_add,AddMonoidHom.add_apply,map_add,map_add,ha e,ha f,hef] at h
    generalize hh : B f e = u at h ⊢
    fin_cases u <;> simp_all
  have hx := coords (atRight B y) x
  change B x y = x.1*(B e y)+x.2*(B f y) at hx
  rw [hx,coords (B e) y,coords (B f) y,ha e,ha f,hef,hfe]
  simp only [mul_one,mul_zero,add_zero,zero_add,binaryPairing,sub_eq_add_neg,actual_binary_neg] <;> ring

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
/-- Input B is an actual perfect alternating form on the original geometric
torsion, written in additive sign coordinates only in the codomain. -/
theorem original_unique (n : F) (hn : n ≠ 0)
    (B : closedTwoTorsion n →+ (closedTwoTorsion n →+ k))
    (ha : ∀ x, B x x=0) (hnd : ∀ x, (∀ y, B x y=0) → x=0)
    (x y : closedTwoTorsion n) : B x y = originalTorsionPairing n hn x y := by
  let t := torsionBinaryEquiv n hn
  let b : V →+ (V →+ k) := {
    toFun := fun u => (B (t.symm u)).comp t.symm.toAddMonoidHom
    map_zero' := by ext v; simp
    map_add' := by intro u v; ext w; simp }
  have ba (u : V) : b u u=0 := ha _
  have bn (u : V) (hu : ∀ v, b u v=0) : u=0 := by
    have h : t.symm u=0 := hnd _ (fun y => by simpa [b] using hu (t y))
    apply t.symm.injective
    simpa using h
  simpa [b,t,originalTorsionPairing] using binary_unique b ba bn (t x) (t y)
end ActualCasselsTateTwoWeilUniqueness318
