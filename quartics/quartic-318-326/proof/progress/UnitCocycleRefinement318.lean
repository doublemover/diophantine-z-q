module
public import UnitCocycleSubopens318
public section
noncomputable section
namespace UnitCocycleRefinement318
open CategoryTheory Opposite TopologicalSpace UnitTransitionCocycle318
open UnitCocycleSubopens318
universe u v w
variable {X:TopCat.{u}} {F G:X.Presheaf CommGrpCat.{u}}
variable {ι:Type v} {κ:Type w} {U:ι→Opens X}
set_option maxHeartbeats 400000
/-- Restrict the original cocycle through the actual refinement inclusions. -/
@[expose] def refine (c:Cocycle F U) (W:κ→Opens X) (r:κ→ι)
    (h:∀k,W k≤U (r k)):Cocycle F W where
  transition i j:=restrict F (inf_le_inf (h i) (h j)) (c.transition (r i) (r j))
  diagonal i:=by rw [c.diagonal,map_one]
  triple i j k:=by
    simp only [restrict_restrict]
    exact transition_mul c (r i) (r j) (r k)
      (inf_le_left.trans (inf_le_left.trans (h i)))
      (inf_le_left.trans (inf_le_right.trans (h j))) (inf_le_right.trans (h k))
lemma map_refine (a:F⟶G) (c:Cocycle F U) (W:κ→Opens X) (r:κ→ι)
    (h:∀k,W k≤U (r k)):
    map a (refine c W r h)=refine (map a c) W r h:=by
  apply Cocycle.ext
  intro i j
  exact (restrict_map a _ _).symm
lemma refine_gauge {c d:Cocycle F U} (hd:GaugeEquivalent c d)
    (W:κ→Opens X) (r:κ→ι) (h:∀k,W k≤U (r k)):
    GaugeEquivalent (refine c W r h) (refine d W r h):=by
  obtain ⟨a,ha⟩:=hd
  refine ⟨fun k=>restrict F (h k) (a (r k)),?_⟩
  intro i j
  change restrict F _ (d.transition (r i) (r j))=_
  rw [ha]
  simp only [map_mul,map_inv,coboundary,restrict_restrict]
  rfl
/-- The common cover is the genuine intersection of the two original opens. -/
@[expose] def common (U:ι→Opens X) (V:κ→Opens X) (p:ι×κ):Opens X:=U p.1⊓V p.2
lemma common_cover (U:ι→Opens X) (V:κ→Opens X)
    (hU:(⊤:Opens X)≤⨆i,U i) (hV:(⊤:Opens X)≤⨆j,V j):
    (⊤:Opens X)≤⨆p,common U V p:=by
  intro x hx
  obtain ⟨i,hi⟩:=Opens.mem_iSup.mp (hU hx)
  obtain ⟨j,hj⟩:=Opens.mem_iSup.mp (hV hx)
  exact Opens.mem_iSup.mpr ⟨(i,j),hi,hj⟩
end UnitCocycleRefinement318
