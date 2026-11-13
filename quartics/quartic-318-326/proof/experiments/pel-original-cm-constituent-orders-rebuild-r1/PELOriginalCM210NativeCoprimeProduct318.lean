module
public import PELOriginalCM210CoprimeKernelProduct318
public import PELOriginalCM210PrimeIdealTransport318
public section
noncomputable section
namespace PELOriginalCM210NativeCoprimeProduct318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210NativePrimeResidue318
open PELOriginalCM210PrimeIdealTransport318 PELOriginalCM210CoprimeKernelProduct318
lemma native_product (m n:ℕ) (hm:(m:ℤ)∣210) (hn:(n:ℤ)∣210)
    (hmn:((m*n:ℕ):ℤ)∣210) (a c:ℤ) (h:a*(m:ℤ)+c*(n:ℤ)=1) :
    nativeIdeal m hm*nativeIdeal n hn=nativeIdeal (m*n) hmn := by
  have he := congrArg (Ideal.map integerEquiv.toRingHom) (product_eq m n hm hn hmn a c h)
  simpa only [Ideal.map_mul,map_kernel] using he
end PELOriginalCM210NativeCoprimeProduct318
