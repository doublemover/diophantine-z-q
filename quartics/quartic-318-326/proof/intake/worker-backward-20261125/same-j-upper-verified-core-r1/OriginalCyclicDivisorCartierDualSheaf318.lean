module
public import OriginalCyclicDivisorCartierDualPairing318

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorCartierDualSheaf318

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open OriginalCyclicDivisorCartierAllOpenFrames318
open OriginalCyclicDivisorCartierDualPairing318 (Dual dual_ext restrict canonical)
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X : Scheme.{u}} {p : Z ⟶ X}

theorem ires_comp {R U V : X.Opens} (l : R≤U) (h : U≤V) (a : I (p:=p) V) :
    ires (p:=p) l (ires (p:=p) h a)=ires (p:=p) (l.trans h) a :=
  Subtype.ext (ρ_comp l h a.val)

theorem ires_self {V : X.Opens} (a : I (p:=p) V) :
    ires (p:=p) (le_rfl : V≤V) a=a :=
  Subtype.ext (OriginalCyclicDivisorCartierDualPairing318.ρ_self a.val)

variable {ι : Type u} (U : ι → X.Opens) {W : X.Opens}
variable (inc : ∀ i,U i≤W) (covered : W≤⨆ i,U i)
variable (s : ∀ i,Dual p (U i))
variable (agree : ∀ i j, restrict (inf_le_left : U i⊓U j≤U i) (s i) =
  restrict (inf_le_right : U i⊓U j≤U j) (s j))

abbrev cut (V : X.Opens) (i : ι) := V⊓U i

include covered in
theorem cut_cover {V : X.Opens} (h : V≤W) :
    V≤⨆ i,cut U V i := by
  intro x hx
  have hxW : x∈W := h hx
  have hxU : x∈⨆ i,U i := covered hxW
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxU
  exact Opens.mem_iSup.mpr ⟨i,hx,hi⟩

include covered in
theorem cut_ext {V : X.Opens} (h : V≤W) (a b : Γ(X,V))
    (e : ∀ i,ρ (inf_le_left : cut U V i≤V) a =
      ρ (inf_le_left : cut U V i≤V) b) : a=b :=
  X.sheaf.eq_of_locally_eq' (cut U V) V (fun _=>homOfLE inf_le_left)
    (cut_cover U covered (V:=V) h) a b e

/-- Evaluate one of the original linear maps after restricting its original
kernel argument to the same open. -/
def piece {V : X.Opens} (a : I (p:=p) V) (i : ι) : Γ(X,cut U V i) :=
  (s i).app (cut U V i) inf_le_right (ires (p:=p) inf_le_left a)

theorem piece_sub {V R : X.Opens} (a : I (p:=p) V) (i : ι) (d : R≤cut U V i) :
    ρ d (piece U s a i) =
      (s i).app R (d.trans inf_le_right) (ires (p:=p) (d.trans inf_le_left) a) := by
  unfold piece
  rw [(s i).natural inf_le_right d,ires_comp]

include agree in
theorem pieces_compatible {V : X.Opens} (a : I (p:=p) V) :
    TopCat.Presheaf.IsCompatible X.presheaf (cut U V) (piece U s a) := by
  intro i j
  let R := cut U V i ⊓ cut U V j
  let d : R≤cut U V i := inf_le_left
  let e : R≤cut U V j := inf_le_right
  let h : R≤U i⊓U j := le_inf (d.trans inf_le_right) (e.trans inf_le_right)
  have hr := congrArg (fun b : Dual p (U i⊓U j) =>
    b.app R h (ires (p:=p) (d.trans inf_le_left) a)) (agree i j)
  change ρ d (piece U s a i)=ρ e (piece U s a j)
  rw [piece_sub U s a i d,piece_sub U s a j e]
  exact hr

include covered agree in
theorem data {V : X.Opens} (h : V≤W) (a : I (p:=p) V) :
    ∃! v : Γ(X,V), ∀ i, ρ (inf_le_left : cut U V i≤V) v = piece U s a i :=
  X.sheaf.existsUnique_gluing' (cut U V) V (fun _=>homOfLE inf_le_left)
    (cut_cover U covered (V:=V) h) (piece U s a) (pieces_compatible U s agree a)

def value {V : X.Opens} (h : V≤W) (a : I (p:=p) V) : Γ(X,V) :=
  (data U covered s agree h a).choose

theorem value_on_cut {V : X.Opens} (h : V≤W) (a : I (p:=p) V) (i : ι) :
    ρ (inf_le_left : cut U V i≤V) (value U covered s agree h a)=piece U s a i :=
  (data U covered s agree h a).choose_spec.1 i

theorem value_add {V : X.Opens} (h : V≤W) (a b : I (p:=p) V) :
    value U covered s agree h (a+b)=value U covered s agree h a+value U covered s agree h b := by
  apply cut_ext U covered h
  intro i
  rw [map_add,value_on_cut,value_on_cut,value_on_cut]
  unfold piece
  rw [map_add,map_add]

theorem value_smul {V : X.Opens} (h : V≤W) (a : Γ(X,V)) (b : I (p:=p) V) :
    value U covered s agree h (a • b)=a*value U covered s agree h b := by
  apply cut_ext U covered h
  intro i
  rw [map_mul,value_on_cut,value_on_cut]
  unfold piece
  simp only [OriginalCyclicDivisorIntrinsicKernelSheaf318.restrict_smul,map_smul,smul_eq_mul]

theorem value_restrict {V R : X.Opens} (h : V≤W) (l : R≤V) (a : I (p:=p) V) :
    ρ l (value U covered s agree h a)=
      value U covered s agree (l.trans h) (ires (p:=p) l a) := by
  apply cut_ext U covered (l.trans h)
  intro i
  let d : cut U R i≤cut U V i := inf_le_inf_right (U i) l
  let r : cut U R i≤R := inf_le_left
  let v : cut U V i≤V := inf_le_left
  change ρ r (ρ l (value U covered s agree h a))=
    ρ r (value U covered s agree (l.trans h) (ires (p:=p) l a))
  calc
    _ = ρ d (ρ v (value U covered s agree h a)) := by rw [ρ_comp,ρ_comp]
    _ = ρ d (piece U s a i) :=
      congrArg (ρ d) (value_on_cut U covered s agree h a i)
    _ = piece U s (ires (p:=p) l a) i := by
      unfold piece
      rw [(s i).natural inf_le_right d,ires_comp,ires_comp]
    _ = _ := (value_on_cut U covered s agree (l.trans h) (ires (p:=p) l a) i).symm

/-- Actual sheaf-Hom gluing; linearity and naturality are checked on
the ordinary structure-sheaf cover, not requested as extra inputs. -/
def glue : Dual p W where
  app _ h :=
    { toFun := value U covered s agree h
      map_add' := value_add U covered s agree h
      map_smul' := value_smul U covered s agree h }
  natural h l a := value_restrict U covered s agree h l a

theorem glue_read (i : ι) : restrict (inc i) (glue U covered s agree)=s i := by
  apply dual_ext
  intro V h a
  let r : cut U V i≤V := inf_le_left
  let d : V≤cut U V i := le_inf le_rfl h
  change value U covered s agree (h.trans (inc i)) a=(s i).app V h a
  calc
    _ = ρ d (ρ r (value U covered s agree (h.trans (inc i)) a)) := by
      rw [ρ_comp,OriginalCyclicDivisorCartierDualPairing318.ρ_self]
    _ = ρ d (piece U s a i) :=
      congrArg (ρ d) (value_on_cut U covered s agree (h.trans (inc i)) a i)
    _ = _ := by rw [piece_sub,ires_self]

theorem glue_unique (b : Dual p W) (hb : ∀ i,restrict (inc i) b=s i) :
    b=glue U covered s agree := by
  apply dual_ext
  intro V h a
  apply cut_ext U covered h
  intro i
  let r : cut U V i≤V := inf_le_left
  have rs := congrArg (fun c : Dual p (U i) =>
    c.app (cut U V i) inf_le_right (ires (p:=p) r a)) (hb i)
  calc
    _ = b.app (cut U V i) (r.trans h) (ires (p:=p) r a) := b.natural h r a
    _ = piece U s a i := rs
    _ = _ := (value_on_cut U covered s agree h a i).symm

/-- The dual's underlying sheaf uses the actual natural functionals. -/
def presheaf : TopCat.Presheaf (Type u) X where
  obj V := Dual p V.unop
  map {_ _} i := ↾fun b=>restrict (leOfHom i.unop) b
  map_id _ := by ext b; rfl
  map_comp _ _ := by ext b; rfl

theorem is_sheaf : TopCat.Presheaf.IsSheaf (presheaf (p:=p)) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro κ V b hb
  let W : X.Opens := ⨆ i,V i
  let a (i : κ) : Dual p (V i) := b i
  have ha (i j : κ) :
      restrict (inf_le_left : V i⊓V j≤V i) (a i) =
        restrict (inf_le_right : V i⊓V j≤V j) (a j) := hb i j
  have cov : W ≤ ⨆ i,V i := le_rfl
  refine ⟨glue V cov a ha,?_,?_⟩
  · intro i
    change restrict (le_iSup V i) (glue V cov a ha)=a i
    exact glue_read V (le_iSup V) cov a ha i
  · intro c hc
    have hc' (i : κ) : restrict (le_iSup V i) c=a i := hc i
    exact glue_unique V (le_iSup V) cov a ha c hc'

def positiveSheaf : TopCat.Sheaf (Type u) X := ⟨presheaf (p:=p),is_sheaf⟩

end OriginalCyclicDivisorCartierDualSheaf318

#print axioms OriginalCyclicDivisorCartierDualSheaf318.glue_read
#print axioms OriginalCyclicDivisorCartierDualSheaf318.positiveSheaf
