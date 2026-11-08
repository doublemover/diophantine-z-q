module
public import F3BasisFrameChange318
public import LiteralIndependentSectionAction318
public import LiteralIndependentGeometricBases318
public section
noncomputable section
namespace LiteralGeometricFrameTransitivity318
open AlgebraicGeometry CategoryTheory
open F3FrameChange318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (F:Type) [Field F] [IsAlgClosed F]
  [Algebra (OpenJModel318.Base N) F] [NeZero N]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) F))
local notation "V" => LiteralKernelSchemePoints318.Points N b
local notation "Sections" => LiteralIndependentGeometricBases318.Sections N F
local notation "act" => LiteralIndependentSectionAction318.action N b
lemma basis_frame (s:Sections) : (LiteralIndependentGeometricBases318.basisEquiv N F s : Fin 2→V)=
    LiteralIndependentSectionAction318.frame N b s:=by
  funext i
  apply Subtype.ext
  fin_cases i
  · exact (LiteralIndependentGeometricBases318.first_value N F s).trans (LiteralIndependentSectionAction318.first_value N b s).symm
  · exact (LiteralIndependentGeometricBases318.second_value N F s).trans (LiteralIndependentSectionAction318.second_value N b s).symm
/-- The already constructed basis equivalence respects the actual Scheme
action and the two original vectors. -/
theorem equivariant (g:F3FrameChange318.Group) (s:Sections) :
    (LiteralIndependentGeometricBases318.basisEquiv N F (act g s) : Fin 2→V)=
    change g (LiteralIndependentGeometricBases318.basisEquiv N F s):=by
  rw [basis_frame,LiteralIndependentSectionAction318.frame_action,basis_frame]
/-- Every two actual geometric sections differ by a unique genuine GL2
change. This is geometric simple transitivity, not yet a Scheme torsor
comparison isomorphism. -/
theorem exists_unique (s t:Sections) : ∃!g:F3FrameChange318.Group,act g s=t:=by
  let g:=F3BasisFrameChange318.between (LiteralIndependentGeometricBases318.basisEquiv N F s)
    (LiteralIndependentGeometricBases318.basisEquiv N F t)
  have hg:act g s=t:=by
    apply (LiteralIndependentGeometricBases318.basisEquiv N F).injective
    apply DFunLike.coe_injective
    rw [equivariant]
    exact F3BasisFrameChange318.change_between _ _
  refine ⟨g,hg,?_⟩
  intro h hh
  apply F3BasisFrameChange318.unique
  rw [←equivariant,hh]
end LiteralGeometricFrameTransitivity318
