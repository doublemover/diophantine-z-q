module
public import FourRootSignBaseChange318
public import ContactGlobalSigns318
public import SourceOpenFractionField318
public import FourRootAutomorphisms318
public section
noncomputable section
namespace SourceSignFieldComparison318
open ContactKummerOrder318
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ) (b:Fin 4→Bool)
abbrev L:=SourceFractionField318.L c
@[expose] def sourceEquiv:SourceOrder c≃ₐ[R]SourceOrder c:=
  FourRootOrderSigns318.signEquiv (coefficient c) b
lemma order_to_open (x:SourceOrder c):
    SourceOpenFractionField318.orderToOpen c (sourceEquiv c b x)=
      ContactGlobalSigns318.openEquiv c b (SourceOpenFractionField318.orderToOpen c x):=by
  exact congrArg (fun f:SourceOrder c→ₐ[R]OpenOrder c=>f x)
    (FourRootSignBaseChange318.sign_coefficientMap (coefficient c) OpenBase b)
lemma source_embedding (x:SourceOrder c):
    embedding c (sourceEquiv c b x)=
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b (embedding c x):=by
  exact congrArg (fun f:SourceOrder c→ₐ[R]L c=>f x)
    (FourRootSignBaseChange318.sign_coefficientMap (coefficient c) K b)

local instance openAlgebra:Algebra (SourceOrder c) (OpenOrder c):=
  (SourceOpenFractionField318.orderToOpen c).toAlgebra
local instance openLocalization:IsLocalization.Away (SourceOpenFractionField318.d c) (OpenOrder c):=
  SourceOpenFractionField318.open_isLocalization c
/-- The literal open-order sign action is the same original-field root-sign
automorphism, under the already specified actual embedding. -/
theorem open_embedding (x:OpenOrder c):
    SourceOpenFractionField318.openEmbedding c (ContactGlobalSigns318.openEquiv c b x)=
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b
        (SourceOpenFractionField318.openEmbedding c x):=by
  have h:(SourceOpenFractionField318.openEmbedding c).comp (ContactGlobalSigns318.openEquiv c b).toRingHom=
      (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).toRingHom.comp
        (SourceOpenFractionField318.openEmbedding c):=by
    apply IsLocalization.ringHom_ext (Submonoid.powers (SourceOpenFractionField318.d c))
    apply RingHom.ext
    intro y
    change SourceOpenFractionField318.openEmbedding c
      (ContactGlobalSigns318.openEquiv c b (SourceOpenFractionField318.orderToOpen c y))=
        FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b
          (SourceOpenFractionField318.openEmbedding c (SourceOpenFractionField318.orderToOpen c y))
    rw [←order_to_open,SourceOpenFractionField318.openEmbedding_on_order,
      SourceOpenFractionField318.openEmbedding_on_order,source_embedding]
  exact RingHom.congr_fun h x
end SourceSignFieldComparison318
