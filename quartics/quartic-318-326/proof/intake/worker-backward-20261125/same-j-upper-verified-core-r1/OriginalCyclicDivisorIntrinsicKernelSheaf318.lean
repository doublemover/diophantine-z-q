module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorIntrinsicKernelSheaf318

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B]

abbrev kernelOf (f : A →+* B) : Ideal A := RingHom.ker f

end Algebra

variable {Z X : Scheme.{u}} (p : Z ⟶ X)

/-- The ideal on EVERY open is the kernel of the literal structure-sheaf
map, not a radical or a reconstructed ideal from its support. -/
def sections (U : X.Opens) : Ideal Γ(X,U) :=
  kernelOf (A:=Γ(X,U)) (B:=Γ(Z,p ⁻¹ᵁ U)) (p.app U).hom

theorem mem_sections {U : X.Opens} (a : Γ(X,U)) :
    a ∈ sections p U ↔ p.app U a=0 := Iff.rfl

theorem push_restrict {U V : X.Opens} (i : U ⟶ V) (a : Γ(X,V)) :
    Z.presheaf.map (homOfLE (p.preimage_mono i.le)).op (p.app V a) =
      p.app U (X.presheaf.map i.op a) :=
  ConcreteCategory.congr_hom (p.naturality i.op).symm a

/-- The module restriction is the original ring restriction. -/
def restrict {U V : X.Opens} (h : U ≤ V) : sections p V →+ sections p U where
  toFun a := ⟨X.presheaf.map (homOfLE h).op a.val,by
    apply (mem_sections p _).mpr
    rw [←push_restrict p (homOfLE h), (mem_sections p _).mp a.property,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem restrict_smul {U V : X.Opens} (h : U ≤ V) (a : Γ(X,V)) (b : sections p V) :
    restrict p h (a • b) = X.presheaf.map (homOfLE h).op a • restrict p h b :=
  Subtype.ext (map_mul _ _ _)

/-- Actual structure-ring modules assembled without the heavyweight
Scheme.Modules/line-class closure. -/
def presheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj U := ModuleCat.of Γ(X,U.unop) (sections p U.unop)
  map {U V} i := by
    let A := ModuleCat.of Γ(X,U.unop) (sections p U.unop)
    let B := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of Γ(X,V.unop) (sections p V.unop))
    exact ConcreteCategory.ofHom (C:=ModuleCat Γ(X,U.unop)) (X:=A) (Y:=B)
      { toFun := restrict p (leOfHom i.unop)
        map_add' := (restrict p _).map_add
        map_smul' := restrict_smul p _ }
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change X.presheaf.map (homOfLE (leOfHom (𝟙 i).unop)).op a.val = a.val
    rw [show (homOfLE (leOfHom (𝟙 i).unop)).op = 𝟙 i from Subsingleton.elim _ _]
    have hi : X.presheaf.map (𝟙 i) = 𝟙 (X.presheaf.obj i) := X.presheaf.map_id i
    exact congrArg (fun f : Γ(X,i.unop) ⟶ Γ(X,i.unop) => f a.val) hi
  map_comp {U V W} i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change X.presheaf.map (homOfLE (leOfHom (i≫j).unop)).op a.val =
      X.presheaf.map (homOfLE (leOfHom j.unop)).op
        (X.presheaf.map (homOfLE (leOfHom i.unop)).op a.val)
    rw [show (homOfLE (leOfHom (i≫j).unop)).op = i≫j from Subsingleton.elim _ _,
      show (homOfLE (leOfHom i.unop)).op = i from Subsingleton.elim _ _,
      show (homOfLE (leOfHom j.unop)).op = j from Subsingleton.elim _ _]
    have hc : X.presheaf.map (i≫j) = X.presheaf.map i ≫ X.presheaf.map j :=
      X.presheaf.map_comp i j
    exact congrArg (fun f : Γ(X,U.unop) ⟶ Γ(X,W.unop) => f a.val) hc

/-- Glue original functions in O_X; their push is zero because its
restrictions are zero on the full inverse-image cover in Z. -/
theorem is_sheaf : TopCat.Presheaf.IsSheaf (presheaf p).presheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U s hs
  let J : X.Opens := ⨆ i,U i
  let a (i:ι) : Γ(X,U i) := (s i : sections p (U i)).val
  have compat : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro i j
    exact congrArg (fun x : sections p (U i ⊓ U j) => x.val) (hs i j)
  obtain ⟨v,hv,uniq⟩ :=
    X.sheaf.existsUnique_gluing' U J (fun i => homOfLE (le_iSup U i)) le_rfl a compat
  have zero : p.app J v=0 := by
    let V (i:ι) := p ⁻¹ᵁ U i
    have cov : p ⁻¹ᵁ J ≤ ⨆ i,V i := by
      intro y hy
      obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (show p y ∈ J from hy)
      exact Opens.mem_iSup.mpr ⟨i,hi⟩
    apply Z.sheaf.eq_of_locally_eq' V (p ⁻¹ᵁ J)
      (fun i => homOfLE (p.preimage_mono (le_iSup U i))) cov
    intro i
    let j : U i ⟶ J := homOfLE (le_iSup U i)
    let k : (p ⁻¹ᵁ U i) ⟶ (p ⁻¹ᵁ J) := homOfLE (p.preimage_mono j.le)
    change Z.presheaf.map k.op (p.app J v) =
      Z.presheaf.map k.op (0 : Γ(Z,p ⁻¹ᵁ J))
    have hv' : X.presheaf.map j.op v = a i := hv i
    have pushed : p.app (U i) (a i) = 0 :=
      (mem_sections p _).mp (s i : sections p (U i)).property
    calc
      _ = p.app (U i) (X.presheaf.map j.op v) := push_restrict p j v
      _ = p.app (U i) (a i) := congrArg (fun x : Γ(X,U i) => p.app (U i) x) hv'
      _ = 0 := pushed
      _ = _ := (map_zero (Z.presheaf.map k.op).hom).symm
  let w : sections p J := ⟨v,(mem_sections p _).mpr zero⟩
  refine ⟨w,?_,?_⟩
  · intro i
    exact Subtype.ext (hv i)
  · intro b hb
    apply Subtype.ext
    exact uniq _ (fun i => congrArg (fun x : sections p (U i) => x.val) (hb i))

/-- Actual sheaf of modules on the underlying scheme. No abstract
separatedness or module-sheaf gluing has been supplied as a premise. -/
def idealSheaf : SheafOfModules X.ringCatSheaf := ⟨presheaf p,is_sheaf p⟩

/-- Exact equality with the old ideal-sheaf data on every genuine
affine scheme open. Quasi-compactness is used by the stock API. -/
theorem affine_read [QuasiCompact p] (U : X.affineOpens) :
    sections p U.1 = p.ker.ideal U :=
  (p.ker_apply U).symm

end OriginalCyclicDivisorIntrinsicKernelSheaf318

#print axioms OriginalCyclicDivisorIntrinsicKernelSheaf318.idealSheaf
#print axioms OriginalCyclicDivisorIntrinsicKernelSheaf318.affine_read
