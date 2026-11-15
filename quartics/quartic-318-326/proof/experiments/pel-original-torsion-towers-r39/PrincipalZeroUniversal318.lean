module
public import PrincipalIdealOpenRestriction318
public import ModuleLocalGluing318
public section
noncomputable section
namespace PrincipalZeroUniversal318
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X T : Scheme.{u}} (r : Γ(X,⊤))
open PrincipalIdealOpenRestriction318

/-- Vanishing of the genuine pulled-back equation implies inclusion of
its FULL quasi-coherent ideal in the morphism kernel, with no reducedness
or finite-type condition on the test scheme. -/
lemma principal_le_ker (f : T ⟶ X) (h : f.appTop r=0) : principal r≤f.ker := by
  apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
  intro U
  rw [principal,Scheme.IdealSheafData.ofIdealTop_ideal,Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro a ha
  rcases Set.mem_singleton_iff.mp ha with rfl
  change f.app U.1 (X.presheaf.map (homOfLE le_top).op r)=0
  rw [OpenScalarSheafNaturality318.global_app,h,map_zero]

/-- The actual principal equation vanishes in the WHOLE zero-scheme
structure sheaf, retaining nilpotents rather than using point support. -/
lemma inclusion_equation : (inclusion r).appTop r=0 := by
  let f := inclusion r
  let U : X.affineOpens → (zeroScheme r).Opens := fun V => f ⁻¹ᵁ V.1
  have hc : (⊤ : (zeroScheme r).Opens)≤⨆ V,U V := by
    intro x hx
    have hm : f x∈⨆ V : X.affineOpens,V.1 := by rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨V,hV⟩ := Opens.mem_iSup.mp hm
    exact Opens.mem_iSup.mpr ⟨V,hV⟩
  apply ModuleLocalGluing318.ext_value (N := SheafOfModules.unit (zeroScheme r).ringCatSheaf) (U := U) hc ⊤
  intro V
  change (zeroScheme r).presheaf.map (homOfLE inf_le_left).op (f.appTop r)=
    (zeroScheme r).presheaf.map (homOfLE inf_le_left).op 0
  have hr : X.presheaf.map (homOfLE (show V.1≤⊤ from le_top)).op r∈(principal r).ideal V := by
    rw [principal,Scheme.IdealSheafData.ofIdealTop_ideal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton r))
  have hk : X.presheaf.map (homOfLE (show V.1≤⊤ from le_top)).op r∈f.ker.ideal V := by
    simpa only [f,inclusion,Scheme.IdealSheafData.ker_subschemeι] using hr
  have he := RingHom.mem_ker.mp (f.ideal_ker_le V hk)
  rw [OpenScalarSheafNaturality318.global_app] at he
  simpa only [U,top_inf_eq,map_zero] using he

@[expose] def lift (f : T ⟶ X) (h : f.appTop r=0) : T ⟶ zeroScheme r :=
  IsClosedImmersion.lift (inclusion r) f (by
    simpa only [inclusion,Scheme.IdealSheafData.ker_subschemeι] using principal_le_ker r f h)
@[reassoc] lemma lift_inclusion (f : T ⟶ X) (h : f.appTop r=0) : lift r f h≫inclusion r=f :=
  IsClosedImmersion.lift_fac _ _ _

/-- Arbitrary scheme tests, including nonreduced ones: factorization is
EXACTLY equation vanishing, and is unique as a scheme morphism. -/
theorem existsUnique_lift_iff (f : T ⟶ X) :
    (∃! g : T ⟶ zeroScheme r,g≫inclusion r=f) ↔ f.appTop r=0 := by
  constructor
  · rintro ⟨g,hg,_⟩
    rw [←hg]
    change g.appTop ((inclusion r).appTop r)=0
    rw [inclusion_equation,map_zero]
  · intro h
    refine ⟨lift r f h,lift_inclusion r f h,?_⟩
    intro g hg
    apply (cancel_mono (inclusion r)).1
    rw [lift_inclusion,hg]
end PrincipalZeroUniversal318
