module
public import OriginalCyclicDivisorCartierAffineFrames318
public import OriginalCyclicDivisorIntrinsicKernelSheaf318

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorCartierAllOpenFrames318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X : Scheme.{u}} {p : Z ⟶ X}

/-- One real Cartier chart, including its actual scheme-theoretic restricted
closed map. In particular the chart contains no separately posited ideal. -/
structure Chart (p : Z ⟶ X) where
  A : CommRingCat.{u}
  j : Spec A ⟶ X
  open_j : IsOpenImmersion j
  c : A
  z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z
  square : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p
  regular : ∀ a : A, a*c=0 → a=0

attribute [instance] Chart.open_j

abbrev Chart.V (Q : Chart p) : X.affineOpens :=
  OriginalCyclicDivisorCartierAffineFrames318.chartOpen Q.A Q.j

abbrev ρ {U V : X.Opens} (h : U ≤ V) : Γ(X,V) →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem ρ_comp {U V W : X.Opens} (e : U ≤ V) (f : V ≤ W) (a : Γ(X,W)) :
    ρ e (ρ f a) = ρ (e.trans f) a := by
  let i : V ⟶ W := homOfLE f
  let j : U ⟶ V := homOfLE e
  let k : U ⟶ W := homOfLE (e.trans f)
  have hk : i.op ≫ j.op = k.op := Subsingleton.elim _ _
  have eq : X.presheaf.map k.op =
      X.presheaf.map i.op ≫ X.presheaf.map j.op :=
    (congrArg X.presheaf.map hk.symm).trans (X.presheaf.map_comp i.op j.op)
  exact congrArg (fun g : Γ(X,W) ⟶ Γ(X,U) => g a) eq.symm

abbrev Ref (W : X.Opens) := {V : X.affineOpens // V.1 ≤ W}
abbrev patch {W : X.Opens} (i : Ref W) : X.Opens := i.1.1

/-- The original structure sheaf is separated on its actual full
affine basis. Empty opens are included. -/
theorem ref_cover (W : X.Opens) : W ≤ ⨆ i : Ref W,patch i := by
  intro x hx
  obtain ⟨V,hV,hit,le⟩ := exists_isAffineOpen_mem_and_subset hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨V,hV⟩,le⟩,hit⟩

theorem ref_ext (W : X.Opens) (a b : Γ(X,W))
    (h : ∀ i : Ref W,ρ i.2 a = ρ i.2 b) : a=b :=
  X.sheaf.eq_of_locally_eq' (fun i : Ref W=>patch i) W
    (fun i=>homOfLE i.2) (ref_cover W) a b h

variable (Q : Chart p)

def coeff {W : X.Opens} (h : W ≤ Q.V.1) : Γ(X,W) :=
  ρ h ((OriginalCyclicDivisorCartierAffineFrames318.coordinateIso Q.A Q.j).hom Q.c)

theorem coeff_restrict {U W : X.Opens} (h : W ≤ Q.V.1) (l : U ≤ W) :
    ρ l (coeff Q h) = coeff Q (l.trans h) := ρ_comp l h _

theorem coeff_on_affine (V : X.affineOpens) (h : V ≤ Q.V) :
    coeff Q h =
      OriginalCyclicDivisorCartierAffineFrames318.equation Q.A Q.j Q.c V h := rfl

variable [IsClosedImmersion p]

omit [IsClosedImmersion p] in
/-- An actual Cartier equation stays regular on EVERY subopen, by
separatedness and flat restriction on the full affine basis. -/
theorem coeff_regular {W : X.Opens} (h : W ≤ Q.V.1) (a : Γ(X,W))
    (ha : a*coeff Q h=0) : a=0 := by
  apply ref_ext W
  intro i
  have e : ρ i.2 a * coeff Q (i.2.trans h) = 0 := by
    calc
      _ = ρ i.2 (a*coeff Q h) := by rw [map_mul,coeff_restrict]
      _ = ρ i.2 0 := congrArg (ρ i.2) ha
      _ = 0 := map_zero _
  have haff : ρ i.2 a = 0 :=
    OriginalCyclicDivisorCartierAffineFrames318.equation_regular
      Q.A Q.j Q.c Q.regular i.1 (i.2.trans h) (ρ i.2 a) e
  exact haff.trans (map_zero (ρ i.2)).symm

omit [IsClosedImmersion p] in
theorem cancel_coeff {W : X.Opens} (h : W ≤ Q.V.1) {a b : Γ(X,W)}
    (e : a*coeff Q h=b*coeff Q h) : a=b :=
  sub_eq_zero.mp (coeff_regular Q h (a-b) (by rw [sub_mul,e,sub_self]))

abbrev I (W : X.Opens) := OriginalCyclicDivisorIntrinsicKernelSheaf318.sections p W
abbrev ires {U V : X.Opens} (h : U ≤ V) :=
  OriginalCyclicDivisorIntrinsicKernelSheaf318.restrict p h

/-- Glue vanishing in the ORIGINAL structure map, not a membership test
on reduced points. -/
theorem coeff_mem {W : X.Opens} (h : W ≤ Q.V.1) :
    coeff Q h ∈ I (p:=p) W := by
  apply (OriginalCyclicDivisorIntrinsicKernelSheaf318.mem_sections p _).mpr
  let V (i : Ref W) := p ⁻¹ᵁ patch i
  have cover : p ⁻¹ᵁ W ≤ ⨆ i,V i := by
    intro z hz
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (ref_cover W hz)
    exact Opens.mem_iSup.mpr ⟨i,hi⟩
  apply Z.sheaf.eq_of_locally_eq' V (p ⁻¹ᵁ W)
    (fun i=>homOfLE (p.preimage_mono i.2)) cover
  intro i
  let j : patch i ⟶ W := homOfLE i.2
  let k : (p ⁻¹ᵁ patch i) ⟶ (p ⁻¹ᵁ W) := homOfLE (p.preimage_mono j.le)
  change Z.presheaf.map k.op (p.app W (coeff Q h)) =
    Z.presheaf.map k.op (0 : Γ(Z,p ⁻¹ᵁ W))
  have hmem : coeff Q (i.2.trans h) ∈ I (p:=p) (patch i) := by
    change coeff Q (i.2.trans h) ∈ OriginalCyclicDivisorIntrinsicKernelSheaf318.sections p i.1.1
    rw [OriginalCyclicDivisorIntrinsicKernelSheaf318.affine_read p i.1,
      coeff_on_affine Q i.1 (i.2.trans h),
      OriginalCyclicDivisorCartierAffineFrames318.ideal_eq p Q.A Q.j Q.c Q.z Q.square i.1
        (i.2.trans h)]
    exact Ideal.subset_span (Set.mem_singleton _)
  calc
    _ = p.app (patch i) (ρ i.2 (coeff Q h)) :=
      OriginalCyclicDivisorIntrinsicKernelSheaf318.push_restrict p j (coeff Q h)
    _ = p.app (patch i) (coeff Q (i.2.trans h)) :=
      congrArg (fun a : Γ(X,patch i) => p.app (patch i) a) (coeff_restrict Q h i.2)
    _ = 0 := (OriginalCyclicDivisorIntrinsicKernelSheaf318.mem_sections p _).mp hmem
    _ = _ := (map_zero (Z.presheaf.map k.op).hom).symm

variable {W : X.Opens} (h : W ≤ Q.V.1)

def mulFrame : Γ(X,W) →ₗ[Γ(X,W)] I (p:=p) W where
  toFun a := ⟨a*coeff Q h,(I (p:=p) W).mul_mem_left a (coeff_mem Q h)⟩
  map_add' a b := Subtype.ext (add_mul a b _)
  map_smul' a b := Subtype.ext (mul_assoc a b _)

theorem mulFrame_injective : Function.Injective (mulFrame Q h) :=
  fun _ _ e=>cancel_coeff Q h (congrArg Subtype.val e)

/-- Actual restriction of an old kernel section, now viewed in the
identical full affine ideal. -/
def restrictedIdeal (i : Ref W) (a : I (p:=p) W) : p.ker.ideal i.1 :=
  ⟨ρ i.2 a.val,by
    rw [← OriginalCyclicDivisorIntrinsicKernelSheaf318.affine_read p i.1]
    exact (ires (p:=p) i.2 a).property⟩

abbrev affineFrame (i : Ref W) :=
  OriginalCyclicDivisorCartierAffineFrames318.frame p Q.A Q.j Q.c Q.z Q.square Q.regular i.1 (i.2.trans h)

def divideAt (a : I (p:=p) W) (i : Ref W) : Γ(X,patch i) :=
  (affineFrame Q h i).symm (restrictedIdeal i a)

theorem divideAt_mul (a : I (p:=p) W) (i : Ref W) :
    divideAt Q h a i * coeff Q (i.2.trans h) = ρ i.2 a.val := by
  have e := congrArg (fun b : p.ker.ideal i.1 => b.val)
    ((affineFrame Q h i).apply_symm_apply (restrictedIdeal i a))
  exact e

/-- The actual affine divisions agree even on non-affine overlaps:
apply the already proved all-open regularity on that overlap. -/
theorem divisions_agree (a : I (p:=p) W) :
    TopCat.Presheaf.IsCompatible X.presheaf (fun i : Ref W=>patch i) (divideAt Q h a) := by
  intro i j
  let l : patch i ⊓ patch j ≤ patch i := inf_le_left
  let r : patch i ⊓ patch j ≤ patch j := inf_le_right
  change ρ l (divideAt Q h a i) = ρ r (divideAt Q h a j)
  apply cancel_coeff Q (l.trans (i.2.trans h))
  calc
    _ = ρ l (divideAt Q h a i * coeff Q (i.2.trans h)) := by
      rw [map_mul,coeff_restrict]
    _ = ρ (l.trans i.2) a.val := by rw [divideAt_mul,ρ_comp]
    _ = ρ r (divideAt Q h a j * coeff Q (j.2.trans h)) := by
      rw [divideAt_mul,ρ_comp]
    _ = _ := by rw [map_mul,coeff_restrict]

theorem mulFrame_surjective : Function.Surjective (mulFrame Q h) := by
  intro a
  obtain ⟨b,hb,_⟩ := X.sheaf.existsUnique_gluing' (fun i : Ref W=>patch i) W
    (fun i=>homOfLE i.2) (ref_cover W) (divideAt Q h a) (divisions_agree Q h a)
  let b' : Γ(X,W) := b
  refine ⟨b',Subtype.ext ?_⟩
  change b'*coeff Q h=a.val
  apply ref_ext W
  intro i
  rw [map_mul,coeff_restrict]
  have e : ρ i.2 b' = divideAt Q h a i := hb i
  rw [e,divideAt_mul]

/-- Fully computed local free frame of the original sheaf of ideals:
on every subopen of a true Cartier chart, including non-affines. -/
def frame : Γ(X,W) ≃ₗ[Γ(X,W)] I (p:=p) W :=
  LinearEquiv.ofBijective (mulFrame Q h) ⟨mulFrame_injective Q h,mulFrame_surjective Q h⟩

theorem frame_value (a : Γ(X,W)) : (frame Q h a).val=a*coeff Q h := rfl

theorem frame_restrict {U : X.Opens} (l : U ≤ W) (a : Γ(X,W)) :
    ires (p:=p) l (frame Q h a) = frame Q (l.trans h) (ρ l a) := by
  apply Subtype.ext
  change ρ l (a*coeff Q h)=ρ l a*coeff Q (l.trans h)
  rw [map_mul,coeff_restrict]

theorem coord_restrict {U : X.Opens} (l : U ≤ W) (a : I (p:=p) W) :
    ρ l ((frame Q h).symm a) = (frame Q (l.trans h)).symm (ires (p:=p) l a) := by
  apply (frame Q (l.trans h)).injective
  rw [LinearEquiv.apply_symm_apply,←frame_restrict Q h l,LinearEquiv.apply_symm_apply]

end OriginalCyclicDivisorCartierAllOpenFrames318

#print axioms OriginalCyclicDivisorCartierAllOpenFrames318.frame
#print axioms OriginalCyclicDivisorCartierAllOpenFrames318.coord_restrict
