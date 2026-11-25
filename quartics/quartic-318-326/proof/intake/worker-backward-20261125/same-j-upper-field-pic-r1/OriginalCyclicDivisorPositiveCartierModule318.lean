module
public import OriginalCyclicDivisorCartierDualSheaf318

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorPositiveCartierModule318

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open OriginalCyclicDivisorCartierAllOpenFrames318
open OriginalCyclicDivisorCartierDualPairing318
  (Dual canonical coordinate read generator generator_restrict ρ_self canonical_ideal)
open OriginalCyclicDivisorCartierDualSheaf318 (glue glue_read glue_unique)
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X : Scheme.{u}} (p : Z ⟶ X)

abbrev Subopen (W : X.Opens) := {V : X.Opens // V≤W}
abbrev Slot {W : X.Opens} (i : Subopen W) :=
  I (p:=p) i.1 →ₗ[Γ(X,i.1)] Γ(X,i.1)

local instance eachModule {W : X.Opens} (i : Subopen W) :
    Module Γ(X,W) (Slot p i) :=
  Module.compHom _ (ρ i.2)

/-- Positive dual coefficients are actual linear natural functionals on the
old ideal. The scalar action is literal restriction in O_X. -/
def functions (W : X.Opens) :
    Submodule Γ(X,W) (∀ i : Subopen W,Slot p i) where
  carrier := {f | ∀ (i j : Subopen W) (l : i.1≤j.1) (a : I (p:=p) j.1),
    ρ l (f j a)=f i (ires (p:=p) l a)}
  zero_mem' := by
    intro i j l a
    change ρ l (0 : Γ(X,j.1))=0
    exact map_zero _
  add_mem' := by
    intro f g hf hg i j l a
    change ρ l (f j a + g j a)=f i (ires (p:=p) l a)+g i (ires (p:=p) l a)
    rw [map_add,hf i j l a,hg i j l a]
  smul_mem' := by
    intro b f hf i j l a
    change ρ l (ρ j.2 b * f j a)=ρ i.2 b * f i (ires (p:=p) l a)
    rw [map_mul,ρ_comp,hf i j l a]

abbrev Sec (W : X.Opens) := functions p W

variable {p} {W : X.Opens}

def ofDual (b : Dual p W) : Sec p W :=
  ⟨fun i=> b.app i.1 i.2,fun _i j l a=>b.natural j.2 l a⟩

def toDual (b : Sec p W) : Dual p W where
  app V h := b.val ⟨V,h⟩
  natural h l a := b.property ⟨_,l.trans h⟩ ⟨_,h⟩ l a

def dualEquiv : Sec p W ≃ Dual p W where
  toFun := toDual
  invFun := ofDual
  left_inv b := by cases b; rfl
  right_inv b := by cases b; rfl

def restriction {V : X.Opens} (l : V≤W) : Sec p W →+ Sec p V where
  toFun b := ⟨fun i=>b.val ⟨i.1,i.2.trans l⟩,
    fun i j h a=>b.property ⟨i.1,i.2.trans l⟩ ⟨j.1,j.2.trans l⟩ h a⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem restriction_smul {V : X.Opens} (l : V≤W) (b : Γ(X,W)) (a : Sec p W) :
    restriction l (b • a)=ρ l b • restriction l a := by
  apply Subtype.ext
  funext i
  apply LinearMap.ext
  intro c
  change ρ (i.2.trans l) b * a.val ⟨i.1,i.2.trans l⟩ c =
    ρ i.2 (ρ l b)*a.val ⟨i.1,i.2.trans l⟩ c
  rw [ρ_comp]

theorem toDual_restriction {V : X.Opens} (l : V≤W) (a : Sec p W) :
    toDual (restriction l a)=OriginalCyclicDivisorCartierDualPairing318.restrict l (toDual a) := rfl

def presheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X,V.unop) (Sec p V.unop)
  map {V U} i := by
    let M := ModuleCat.of Γ(X,V.unop) (Sec p V.unop)
    let N := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of Γ(X,U.unop) (Sec p U.unop))
    exact ConcreteCategory.ofHom (C:=ModuleCat Γ(X,V.unop)) (X:=M) (Y:=N)
      { toFun := restriction (leOfHom i.unop)
        map_add' := (restriction (p:=p) _).map_add
        map_smul' := restriction_smul _ }
  map_id _ := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl
  map_comp _ _ := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl

/-- The additive sheaf condition is provided by the already constructed
actual sheaf-Hom gluing, with the identical linear operations. -/
theorem sheaf : TopCat.Presheaf.IsSheaf (presheaf (p:=p)).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U s hs
  let a (i : ι) : Dual p (U i) := toDual (s i : Sec p (U i))
  have compatible (i j:ι) :
      OriginalCyclicDivisorCartierDualPairing318.restrict
        (inf_le_left : U i⊓U j≤U i) (a i) =
      OriginalCyclicDivisorCartierDualPairing318.restrict
        (inf_le_right : U i⊓U j≤U j) (a j) :=
    congrArg (toDual (p:=p) (W:=U i⊓U j)) (hs i j)
  let out := glue U le_rfl a compatible
  have reads (i:ι) := glue_read U (le_iSup U) le_rfl a compatible i
  refine ⟨ofDual out,?_,?_⟩
  · intro i
    exact congrArg (ofDual (p:=p) (W:=U i)) (reads i)
  · intro b hb
    have b_roots (i:ι) :
        OriginalCyclicDivisorCartierDualPairing318.restrict
          (le_iSup U i) (toDual (b : Sec p (⨆ i,U i))) = a i :=
      congrArg (toDual (p:=p) (W:=U i)) (hb i)
    exact congrArg (ofDual (p:=p)) (glue_unique U (le_iSup U) le_rfl a compatible _ b_roots)

/-- Actual positive line sheaf (the dual of I), with its O_X-linearity
built and checked on genuine opens; no old auxiliary line chosen. -/
def positive : SheafOfModules X.ringCatSheaf := ⟨presheaf (p:=p),sheaf⟩

def canon (W : X.Opens) : Sec p W :=
  ofDual (canonical (p:=p) W)

theorem canon_restrict {V : X.Opens} (l : V≤W) :
    restriction l (canon (p:=p) W)=canon (p:=p) V := rfl

/-- Pointwise evaluation is the literal pairing of the dual with the
original ideal, not a quotient by local units. -/
def evaluation : Sec p W →ₗ[Γ(X,W)] (I (p:=p) W →ₗ[Γ(X,W)] Γ(X,W)) where
  toFun a := (toDual a).app W le_rfl
  map_add' _ _ := rfl
  map_smul' b a := by
    apply LinearMap.ext
    intro c
    change ρ (le_rfl : W≤W) b * (toDual a).app W le_rfl c =
      b*(toDual a).app W le_rfl c
    rw [ρ_self]

theorem canon_inclusion (a : I (p:=p) W) :
    evaluation (canon (p:=p) W) a=a.val := rfl

theorem evaluation_restrict {V : X.Opens} (l : V≤W) (a : Sec p W) (b : I (p:=p) W) :
    ρ l (evaluation a b)=evaluation (restriction l a) (ires (p:=p) l b) :=
  (toDual a).natural le_rfl l b

variable [IsClosedImmersion p] (Q : Chart p) (h : W≤Q.V.1)

def coordinateRead : Sec p W →ₗ[Γ(X,W)] Γ(X,W) where
  toFun a := evaluation a (generator Q h)
  map_add' a b := DFunLike.congr_fun (evaluation.map_add a b) (generator Q h)
  map_smul' a b := DFunLike.congr_fun (evaluation.map_smul a b) (generator Q h)

/-- Local freeness of rank one with its exact inverse pairing, on every
subopen of the genuine original Cartier chart. -/
def frame : Sec p W ≃ₗ[Γ(X,W)] Γ(X,W) :=
  LinearEquiv.ofBijective (coordinateRead Q h)
    ((dualEquiv (p:=p) (W:=W)).trans (coordinate Q h)).bijective

/-- The positive coordinate is compatible with every genuine open
restriction, not only affine overlaps. -/
theorem frame_restrict {V : X.Opens} (l : V≤W) (a : Sec p W) :
    ρ l (frame Q h a)=frame Q (l.trans h) (restriction l a) := by
  change ρ l (evaluation a (generator Q h)) =
    evaluation (restriction l a) (generator Q (l.trans h))
  exact (evaluation_restrict l a (generator Q h)).trans
    (congrArg (evaluation (restriction l a)) (generator_restrict Q h l))

/-- The two bases of the actual kernel and its actual dual pair to
multiplication in the original structure ring. -/
theorem evaluation_in_frames (a : Sec p W) (r : Γ(X,W)) :
    evaluation a (OriginalCyclicDivisorCartierAllOpenFrames318.frame Q h r)=
      r * frame Q h a := by
  have hg : OriginalCyclicDivisorCartierAllOpenFrames318.frame Q h r=r • generator Q h :=
    Subtype.ext (OriginalCyclicDivisorCartierAllOpenFrames318.frame_value Q h r)
  exact (congrArg (evaluation a) hg).trans ((evaluation a).map_smul r _)

theorem canonical_regular (r : Γ(X,W)) (hr : r * frame Q h (canon (p:=p) W)=0) : r=0 :=
  coeff_regular Q h r hr

theorem canonical_affine (V : X.affineOpens) (hV : V≤Q.V) :
    Ideal.span {frame Q hV (canon (p:=p) V.1)}=p.ker.ideal V :=
  canonical_ideal Q V hV

end OriginalCyclicDivisorPositiveCartierModule318

#print axioms OriginalCyclicDivisorPositiveCartierModule318.positive
#print axioms OriginalCyclicDivisorPositiveCartierModule318.canonical_affine
#print axioms OriginalCyclicDivisorPositiveCartierModule318.evaluation_in_frames
#print axioms OriginalCyclicDivisorPositiveCartierModule318.frame_restrict
