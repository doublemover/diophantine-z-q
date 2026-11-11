module
public import VaryingNormalizedFrameEquiv318
public section
noncomputable section
namespace VaryingWordIdealChartClassifier318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The explicit normalized affine chart has, on EVERY coefficient
ring, exactly the original full source ideals whose selected literal
word tensors are a basis of the whole quotient. This is the fixed-word
chart classifier; overlap gluing and family base-change remain separate. -/
@[expose] def classifier :
    (VaryingNormalizedWordParameter318.ring R A ι w →ₐ[R] S) ≃
      CyclicNormalizedIdealClassifier318.WordIdeal S (S ⊗[R] A) ι
        (fun j => (1 : S) ⊗ₜ[R] (w j).prod) :=
  (VaryingNormalizedWordParameter318.points R A ι w S).trans
    ((VaryingNormalizedFrameEquiv318.frames R A ι w S).trans
      (CyclicNormalizedIdealClassifier318.classifier S (S ⊗[R] A) ι
        (fun j => (1 : S) ⊗ₜ[R] (w j).prod)))
end VaryingWordIdealChartClassifier318
