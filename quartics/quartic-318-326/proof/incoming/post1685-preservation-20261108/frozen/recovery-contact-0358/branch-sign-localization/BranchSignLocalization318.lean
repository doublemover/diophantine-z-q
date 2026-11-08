module
public import SourceSignChart318
public import BranchOriginalCoordinate318
public import Mathlib.RingTheory.Localization.Basic
public section
noncomputable section
namespace BranchSignLocalization318
open ContactKummerOrder318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev B (i:Fin 4):=ContactIntrinsicFrames318.BranchRing c i
lemma denominator_fixed (i:Fin 4) (b:Fin 4→Bool):
    SourceSignFieldComparison318.sourceEquiv c b (SourceDenominatorCover318.denominator c i)=
      SourceDenominatorCover318.denominator c i:=
  (SourceSignFieldComparison318.sourceEquiv c b).commutes _
lemma powers_fixed (i:Fin 4) (b:Fin 4→Bool):
    (Submonoid.powers (SourceDenominatorCover318.denominator c i)).map
      (SourceSignFieldComparison318.sourceEquiv c b).toMonoidHom=
    Submonoid.powers (SourceDenominatorCover318.denominator c i):=by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (denominator_fixed c i b)
/-- The literal original sign extends to the entire branch localization,
with its original Q[t]-structure retained. -/
@[expose] def signR (i:Fin 4) (b:Fin 4→Bool):B c i≃ₐ[R]B c i:=
  IsLocalization.algEquivOfAlgEquiv (B c i) (B c i)
    (SourceSignFieldComparison318.sourceEquiv c b) (powers_fixed c i b)
@[expose] def sign (i:Fin 4) (b:Fin 4→Bool):B c i≃ₐ[ℚ]B c i:=
  (signR c i b).restrictScalars ℚ
lemma on_source (i:Fin 4) (b:Fin 4→Bool) (x:SourceOrder c):
    sign c i b (algebraMap (SourceOrder c) (B c i) x)=
      algebraMap (SourceOrder c) (B c i) (SourceSignFieldComparison318.sourceEquiv c b x):=
  IsLocalization.algEquivOfAlgEquiv_eq (powers_fixed c i b) x
lemma on_polynomial (i:Fin 4) (b:Fin 4→Bool) (p:R):
    sign c i b (algebraMap R (B c i) p)=algebraMap R (B c i) p:=
  (signR c i b).commutes p
@[expose] def root (i k:Fin 4):B c i:=
  algebraMap (SourceOrder c) (B c i) (ContactRootReciprocals318.root c k)
lemma on_root (i:Fin 4) (b:Fin 4→Bool) (k:Fin 4):
    sign c i b (root c i k)=if b k then -root c i k else root c i k:=by
  rw [root,on_source]
  change algebraMap (SourceOrder c) (B c i)
    (FourRootOrderSigns318.signEquiv (coefficient c) b
      (FourRootOrderSigns318.generator (coefficient c) k))=_
  rw [FourRootOrderSigns318.signEquiv_generator]
  split_ifs
  · exact map_neg (algebraMap (SourceOrder c) (B c i)) _
  · rfl
lemma on_coordinate (i:Fin 4) (b:Fin 4→Bool):
    sign c i b (ContactFrameNormalization318.sourceCoordinate c i)=
      if b i then -ContactFrameNormalization318.sourceCoordinate c i
      else ContactFrameNormalization318.sourceCoordinate c i:=by
  rw [BranchOriginalCoordinate318.coordinate_eq_root]
  exact on_root c i b i
/-- The actual single original-root flip on its entire ramified branch chart. -/
@[expose] def flip (i:Fin 4):B c i≃ₐ[ℚ]B c i:=sign c i (SourceCharacterFields318.flip i)
lemma flip_coordinate (i:Fin 4):
    flip c i (ContactFrameNormalization318.sourceCoordinate c i)=
      -ContactFrameNormalization318.sourceCoordinate c i:=by
  rw [flip,on_coordinate]
  simp [SourceCharacterFields318.flip]
lemma flip_other_root (i k:Fin 4) (hk:k≠i):flip c i (root c i k)=root c i k:=by
  rw [flip,on_root]
  simp [SourceCharacterFields318.flip,hk]
end BranchSignLocalization318
