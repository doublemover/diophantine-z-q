module
public import GammaHAction318
public import FiniteCuspEnds318
public section
noncomputable section
open Function Filter Topology TopologicalSpace UpperHalfPlane
open GammaHGroup318 GammaHDiamond318 GammaHAction318
open FiniteCuspEnds318 RotatedProjection318 FiniteCuspCoverage318
open scoped MatrixGroups
namespace GammaHCuspEnds318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Every integral rotation defines an end in the actual finite end type,
not merely those matrices selected by the finite-coset choice. -/
theorem rotation_is_end (N:ℕ) (r:SL(2,ℤ)) : neighborhood N r∈endRegions N := by
  obtain ⟨s,hs,gamma,hr⟩:=rotations_cover N r
  refine ⟨s,hs,?_⟩
  have he : rotatedMap N r=rotatedMap N s := by
    funext tau
    change GammaOneAtlas318.quotientMap N (r•tau)=GammaOneAtlas318.quotientMap N (s•tau)
    rw [hr,mul_smul,quotient_smul]
  exact congrArg (fun f:UpperHalfPlane→Fine N=>f '' WidthQParameter318.high 2) he.symm

theorem matrixAct_neighborhood (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) (r:SL(2,ℤ)) :
    matrixAct N H g '' neighborhood N r=neighborhood N (g.val*r) := by
  rw [neighborhood,Set.image_image,neighborhood]
  congr 1
  funext tau
  change GammaOneAtlas318.quotientMap N (g.val•(r•tau))=
    GammaOneAtlas318.quotientMap N ((g.val*r)•tau)
  rw [mul_smul]

/-- The actual action on distinct cusp ends, as actual high-neighborhood sets. -/
@[expose] def matrixEnd (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) (c:End N) : End N :=
  ⟨neighborhood N (g.val*representative N c),rotation_is_end N _⟩

theorem matrixEnd_val (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) (c:End N) :
    (matrixEnd N H g c).val=matrixAct N H g '' c.val := by
  rw [←representative_region N c,matrixAct_neighborhood]
  rfl

@[expose,instance_reducible] def endMatrixAction (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    MulAction (gammaH N H) (End N) where
  smul:=matrixEnd N H
  one_smul c:=by
    apply Subtype.ext
    change (matrixEnd N H 1 c).val=c.val
    rw [matrixEnd_val]
    letI:=matrixAction N H
    change (fun q:Fine N=>(1:gammaH N H)•q) '' c.val=c.val
    simp only [one_smul,Set.image_id']
  mul_smul g h c:=by
    apply Subtype.ext
    change (matrixEnd N H (g*h) c).val=(matrixEnd N H g (matrixEnd N H h c)).val
    rw [matrixEnd_val,matrixEnd_val,matrixEnd_val,Set.image_image]
    letI:=matrixAction N H
    congr 1
    funext q
    change (g*h)•q=g•(h•q)
    exact mul_smul g h q

theorem matrixEnd_eq_of_diamond_eq (N:ℕ) (H:Subgroup (ZMod N)ˣ)
    (g h:gammaH N H) (he:diamond N H g=diamond N H h) (c:End N) :
    matrixEnd N H g c=matrixEnd N H h c := by
  apply Subtype.ext
  rw [matrixEnd_val,matrixEnd_val]
  have hh:matrixAct N H g=matrixAct N H h:=funext (matrixAct_eq_of_diamond_eq N H g h he)
  rw [hh]

/-- The same actual finite diamond group acts on the actual distinct cusp type.
This supplies the end permutation for extending the action across the filling. -/
@[expose,instance_reducible] def endDiamondAction (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    MulAction H (End N) := by
  letI:=endMatrixAction N H
  letI:SMul H (End N):=⟨fun u=>matrixEnd N H (lift N H u)⟩
  apply (diamond_surjective N H).mulActionLeft (diamond N H)
  intro g c
  exact matrixEnd_eq_of_diamond_eq N H _ g (lift_spec N H (diamond N H g)) c

theorem diamondEnd_val (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) (u:H) (c:End N) :
    letI:=diamondAction N H
    letI:=endDiamondAction N H
    (u•c).val=(fun q:Fine N=>u•q) '' c.val := by
  exact matrixEnd_val N H (lift N H u) c

/-- The future cusp quotient is the orbit quotient of the actual finite end
permutation, not a new arbitrary finite indexing set. -/
abbrev OrbitEnds (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :=
  letI:=endDiamondAction N H
  MulAction.orbitRel.Quotient H (End N)

instance orbitEnds_finite (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) : Finite (OrbitEnds N H) := by
  letI:=endDiamondAction N H
  infer_instance

end GammaHCuspEnds318
