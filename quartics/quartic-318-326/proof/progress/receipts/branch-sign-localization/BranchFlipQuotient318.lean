module
public import BranchSignScheme318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace BranchFlipQuotient318
open ContactKummerOrder318 BranchSignLocalization318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
lemma source_flip_killed {T:Type*} [CommRing T] [Algebra R T]
    (i:Fin 4) (f:SourceOrder c→ₐ[R]T) (hz:f (ContactRootReciprocals318.root c i)=0):
    f.comp (SourceSignFieldComparison318.sourceEquiv c (SourceCharacterFields318.flip i)).toAlgHom=f:=by
  apply FourRootSignBaseChange318.hom_ext (coefficient c)
  intro k
  change f (FourRootOrderSigns318.signEquiv (coefficient c) (SourceCharacterFields318.flip i)
    (FourRootOrderSigns318.generator (coefficient c) k))=f (FourRootOrderSigns318.generator (coefficient c) k)
  rw [FourRootOrderSigns318.signEquiv_generator]
  by_cases hk:k=i
  · subst k
    change f (if SourceCharacterFields318.flip i i then -ContactRootReciprocals318.root c i
      else ContactRootReciprocals318.root c i)=f (ContactRootReciprocals318.root c i)
    simp only [SourceCharacterFields318.flip,decide_true,ite_true,map_neg,hz,neg_zero]
  · simp only [SourceCharacterFields318.flip,hk,decide_false,Bool.false_eq_true,ite_false]
@[expose] def ideal (i:Fin 4):Ideal (B c i):=
  Ideal.span {ContactFrameNormalization318.sourceCoordinate c i}
abbrev Quotient (i:Fin 4):=B c i⧸ideal c i
/-- Every element of the entire quotient by the original branch coordinate
is fixed. This is stronger than a chosen prime/residue-field identity. -/
theorem quotient_fixed (i:Fin 4) (x:B c i):
    Ideal.Quotient.mk (ideal c i) (flip c i x)=Ideal.Quotient.mk (ideal c i) x:=by
  let q:=Ideal.Quotient.mkₐ R (ideal c i)
  let f:SourceOrder c→ₐ[R]Quotient c i:=q.comp (IsScalarTower.toAlgHom R (SourceOrder c) (B c i))
  have hz:f (ContactRootReciprocals318.root c i)=0:=by
    change Ideal.Quotient.mk (ideal c i) (algebraMap (SourceOrder c) (B c i) (ContactRootReciprocals318.root c i))=0
    rw [←BranchOriginalCoordinate318.coordinate_eq_root]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hs:=source_flip_killed c i f hz
  have h:(Ideal.Quotient.mk (ideal c i)).comp (flip c i).toRingHom=
      Ideal.Quotient.mk (ideal c i):=by
    apply IsLocalization.ringHom_ext (Submonoid.powers (SourceDenominatorCover318.denominator c i))
    apply RingHom.ext
    intro z
    change Ideal.Quotient.mk (ideal c i) (flip c i (algebraMap (SourceOrder c) (B c i) z))=_
    rw [BranchSignLocalization318.flip,on_source]
    exact congrArg (fun g:SourceOrder c→ₐ[R]Quotient c i=>g z) hs
  exact RingHom.congr_fun h x
/-- Anti-invariant regular coefficients are divisible by the literal
branch coordinate. The proof uses the unit2, never quotient reducedness. -/
theorem divisible (i:Fin 4) (x:B c i) (hx:flip c i x= -x):
    ContactFrameNormalization318.sourceCoordinate c i∣x:=by
  have h:=quotient_fixed c i x
  rw [hx,map_neg] at h
  have htwo:(2:Quotient c i)*Ideal.Quotient.mk (ideal c i) x=0:=by
    linear_combination -h
  have hu:IsUnit (2:Quotient c i):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℚ) (by norm_num)).map (algebraMap ℚ (Quotient c i))
  have hz:Ideal.Quotient.mk (ideal c i) x=0:=hu.mul_right_eq_zero.mp htwo
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
end BranchFlipQuotient318
