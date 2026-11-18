# Terminal comparison for all sixteen remaining PARITY24 close pairs

Fix the sixteen PARITY24 representatives with j=0,k=1 or 2, odd A₀=(ad−f₀)/2, including either contact tuple and unramified scalar variations. Their third genuine origin blowup was already evaluated at the sole residual point w=S=B=0,E=1. We give the exact chart isomorphism (after genuine étale comparisons on both sides) showing that the terminal norm calculations for EVENCLOSE and EVENUNSPLIT apply, though the original radical at m has **even**, not odd, valuation.

Use the displayed coefficients H₀=d(e₀−e_k)/32, M₀=a(e₀−e_m)/32, f=f₀+a₃d w⁶S², w²=2f, u=w³S, h=w³ E, b=w³B with b=((1+u)y_m−uw)/2. Thus E²+SE=H₀/f³. Directly from the half product
    V=y_m/w⁴=(wB/f+S)/(1+u) .
This V lies in the actual local algebra. Squaring y_m²=2a(d u²+e₀−e_m) and using w²=2f gives
    f V²=ad S²+4M₀/f³ .
Conversely this squared equation is equivalent, inside the function field, to the known B monic under the displayed substitution; the later variable z below recovers B with unit slope rather than treating V as a generator with invertible B coefficient.

Put K=M₀/(ad H₀)=(e₀−e_m)/(e₀−e_k), which is 2401, 1/2401, 35/3 or 3/35; Λ=2K−1. Writing X=V/E and Y=S/E+2K gives the exact norm
    Y²−(f/(ad)) X²=4K(K−1).
Indeed after division by ad·E² the previous equation reads (f/(ad))X²=(S/E)²+4K(1+S/E). E is a unit here. The oddness of A₀ says f₀/(ad)≡3 mod4; hence one may realize δ²=−f₀/(ad) by an étale quadratic using (1+δ)/2. In particular δ−1 is divisible by 2 in this ring, not just zero in the residue field. Independently adjoin ρ=1+2h' with ρ²=f/f₀, using h'²+h'=(f/f₀−1)/4 with integral RHS and unit derivative at 2. Put π=w/ρ, E'=ρ³E, S*=ρ³S. Then π²=2f₀ and
    S*=(H₀/f₀³−E'²)/E',    Y=Λ+H₀/(f₀³ E'²).
The comparison is étale in either direction: from O=D'[π]/(π²−2f₀) (D' the unramified coefficient localization containing δ), the regular E'-line acquires h' by h'²+h'=a₃d π⁶ S*²/(4f₀), since w⁶S²=π⁶S*², and the displayed substitutions invert. This is the source of the ramified coefficient DVR, embedded on the common parameter-étale chart, not an appeal to descent after a purely ramified extension.

Write X'=δρX; the norm is now X'²+Y²=4K(K−1). Crucially the coordinate z=(X'−Y)/π is a genuine integral affine replacement for B with **unit slope**:
    z=[δρ²/(f E(1+u))]B+
         [(δρ−1−u)/(π E(1+u))] S−2K/π .
Here δρ−1 is a multiple of 2, u=w³S, 2/π=π/f₀, all denominators displayed without π are units. Thus B is recovered integrally from z without inverting w or π; expanding the exact norm and canceling π² gives
    f₀ z²+πY z+Y²=2K(K−1).
This is equality of the actual chart algebras: use the reversible unit-slope substitution, the two monic quadratics of degree two over the same base, and generic equality from V or the norm. Both quadratic charts are free over the localized base and embed in their generic fibres, so the comparison has no new scale torsion or hidden component. The residual values are π=0,E'=1,z=0: B=S=0 and 2/π vanishes there. The explicit inverses for the other coordinates also identify the underlying common étale base.

This is *exactly* the O-chart in RAMIFIED-DYADIC-EVENCLOSE, with its required fields and constant units, so we may apply its two audited terminal chart calculations (and RAMIFIED-DYADIC-EVENUNSPLIT). More precisely shift b'=z−Y, define Γ=−H₀/(Λ f₀³), L=1+π, J=(1+f₀+π)/π, D₀=2K(K−1)/π¹². Then f₀ b'²+π L Y b'+π J Y²=D₀π¹², Y=Λ(1−Γ/E'²), v₂(K−1)=5. Both source proofs require only these exact data, the residue-one units, and Γ≡1 or 3 modulo 4. The split branch factors Y=unit·p(p+2γ) after an unramified γ²=Γ and uses two normalized main blowups followed by the ordinary conic stages. The unsplit branch does not adjoin such γ: the proven cancellation N∈(t,q²) and the three early plus four cusp stages use only Γ≡3, f₀,H₀ and the above constants. These complements exhaust all odd Γ; over the working sign representatives they occur eight each as checked directly. No count of chart-etale labels is being added to the number of downstairs centers.

The whole singular union and finite normalizations in that analysis commute with the identified étale charts and unramified scalars. Since every point off the third-stage origin was already resolved or regular, these terminal charts and the unchanged odd-prime construction give a proper flat regular model of each of the sixteen original X_q over Z. Together with the eight PARITY24 pair-12s, all 24 of that genuinely mixed-valuation-parity subfamily are now explicitly treated. The condition A₀ even and other parity/sign arrangements are not covered by this transfer.
