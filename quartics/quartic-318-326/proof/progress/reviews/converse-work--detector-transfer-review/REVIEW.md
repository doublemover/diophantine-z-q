# Independent shifted-detector transfer review

Accepted at the exact current arithmetic.md “Shifted square-root product height scales” scope (lines 1125–1167), not the older V10 C0-squared/(1+C1-squared)-squared list.

The reviewed input is x=Kprod=u+v sqrt(2), n=x.norm, B=x.re+n. The literal denominator product clears [1,−2B+2n,n]; each integer coefficient is bounded by 4 H(B) H(n). Primitive gcd division cannot increase that budget. Mathlib Landau supplies sqrt(3), and the actual primitive quadratic Mahler identity supplies the exact degree-two normalization. The rational branch is separately valid because n=u². Squaring x multiplies actual absolute height by two, so the output is h(C)=h(Kprod²), not the height of a norm.

The essential lambda≠0 hypothesis is explicit. B,n need not be nonzero for this height inequality alone. The upstream contact estimates, their nonzero multiplier and the circuit reconstruction still have to be supplied by their actual source lanes. The constant-seven absorption is valid for H≥1 and W≥1; the generic exponent theorem proves W≥1 from N≠0 and e≥0. The newly added adopted wrapper uses e=49/(8k); the historical19/k wrapper remains separately labeled. Both are valid specializations of the same W argument. This review accepts the conditional exponent wrappers, not an upstream proof of their detector hypotheses. The source uses k>0 even though the formal arithmetic theorem safely includes the totalized k=0 convention.

I copied the completed module into this isolated review directory and rebuilt it with debug.skipKernelTC=false. All printed theorem dependencies are only propext, Classical.choice and Quot.sound. No normalization or source-scope mismatch was found. Original worker files were not edited.
