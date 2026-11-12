# Complete bin packing and original weighted consumer

## Constructed centering and all-pairs injection
centeredValue(x)=x-floor(x+1/2), with absolute value at most1/2 including ties. For q>0, floor(2q*centeredValue(c*t)) lies in the literal integer interval[-q,q]. The inherited rational short-block theorem is applied to EVERY distinct c,d in[lo,hi], with the integer translate equal to the difference of their actual centering integers. Thus their centered values differ by at least1/(2q).

The pinned floor theorem says equal floors imply scaled distance strictly less than1. Scaling by positive2q contradicts the produced separation. The resulting injection retains all indices including an exact resonance, rather than discarding multiples of q. No residue-injection hypothesis is substituted.

## Reciprocal cost, signs and exceptional bins
reciprocalCap(N,x) is N if x=0 and otherwise min(N,1/(2|x|)). This explicit zero branch is essential: totalized division by zero would incorrectly erase resonance. For bin b>0, b<=2qx gives x>0 and reciprocal<=q/b. For b<=-2,2qx<b+1 gives x<0 and reciprocal<=q/(-b-1). The endpoint shift by1 is necessary on the negative side. Both central bins-1 and0 cost N. All bin costs are nonnegative for N>=0,q>0.

Pointwise cost bounds are summed on every original index. Injectivity identifies this sum with a sum on the actual bin image. The proved image inclusion and nonnegative costs then enlarge to the full[-q,q] interval. No near-resonant frequency or short-block endpoint is dropped.

## Exact Fourier and weighted consumers
fourierChordCap(N,c,t) is N when the actual period-one Fourier phase equals1, otherwise min(N,2/|e(c*t)-1|). If centeredValue(c*t) is nonzero, the previous exact chord lower bound applies to that literal centered representative and produces nonresonance. If it is zero, the universal length cost suffices. Therefore the exact chord kernel is bounded by the exact reciprocalCap for all frequencies, with no exception omitted.

The complete short-block theorem sums the actual kernel on every integer c in[lo,hi], assuming coprime a,q, q>0, |t-a/q|<=q^-2 and2(hi-lo)<=q. Individual frequencies need NOT be nonmultiples and may be arbitrarily large because only their pairwise differences require the controlled range.

Finally the original arbitrary weighted interval theorem uses the same kernel: its resonant branch is the predecessor universal weighted-length bound; its nonresonant branch is the actual Abel cancellation bound. Under an actual uniform variation cost V, every weighted term is bounded by V times its kernel, and the whole block is bounded by V times the explicit bin sum. The weight g(c,j) and starting point m(c) may depend arbitrarily on c. This is not a product-weight argument or a definition of a new minor remainder.

## Boundary and validation
The explicit bin sum is harmonic-shaped. The exact Fraction regression checks its elementary harmonic identity, but that identity and any logarithmic estimate are not yet new Lean claims. Nor have all original displacements been partitioned into blocks or the required approximation denominators produced over the full minorDomain. Higher/mixed weight control and a power-saving complete original correlation budget remain open. The exact finite tests check full injections, pointwise bin costs, complete reciprocal sums, retained resonances and four necessity controls, not Lean, the analytic chord proof or global decay.
