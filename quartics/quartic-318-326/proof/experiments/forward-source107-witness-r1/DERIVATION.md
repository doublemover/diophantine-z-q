# Actual same-index witness through literal source row 106

This successor adds five sources to the frozen 46-source full-density/CRT packet. The existing 46 Lean sources are copied unchanged. It constructs 56 additional literal rows, extending first51 coverage to first107 of the 288 original source rows. The remaining181 rows, prime-pattern producer and final `HasSolution` consumer remain separate. Hosted Lean elaboration and recursive axiom checking are pending; no local Lean build was run.

## Denominators on actual charts

The new `CompressedChartDomains318` consumes original `chartU h`, `chartV h`, their actual reciprocal-curve equation, and the already constructed compression parameter `shiftWitness`. Its anchor A is the original ordinate expression. Its anchor B is the existing `k^2 + m s + D u^2 s^2` expression. The exact compression identity and norm-square obstruction imply B is nonzero. The G Padé argument is `(d u^2 s^2)^2`, not an arbitrary field element; therefore the pinned square-domain nonvanishing theorem applies. G's numerator is independently nonzero in Q(sqrt(2)).

The common alternate logarithm is `(k s/B) (PG/QG)`. Its remaining possible zero is s=0. This exceptional branch is identified, rather than discarded: if the compression parameter of a coherent nonzero h-chart is zero, the compression equation gives `1/u^2=k^2` and the ordinate identity gives `v/u^3=k m`. The actual reciprocal point is consequently exactly the original generator P. The coherent chart-point theorem then gives hP=P, which contradicts the already proved infinite order of P when h is not 1. Thus h distinct from 0 and 1 constructs a nonzero common logarithm. No full-source solution is assumed in this argument.

For every alternate chart, the actual equation `v^2+(d u^2)^2=1` discharges QJ's circle-domain hypothesis. Identity alternate charts are retained. The J numerator and the lower-order first alternate polynomial are also proved nonzero. Original chart ordinates are nonzero by the existing actual coherent-chart theorem. These are all denominators used in the new ratios.

## Exact Padé and ratio filling

`PadeRatioWitness318` sets exactly coordinates90 through117. It does not change any coordinate read by the first51 source rows. Its `Relations` predicate records the six groups of elementary field identities used to verify the emitted quadratic rows: the common G polynomial, common logarithm, first alternate polynomial, three J polynomials, four primary ratios, and four alternate ratios. These are not left as caller-supplied source solutions. `ActualPadeRatios318.construct` defines each field value by the original rational formula, and `construct_relations` proves the identities by nonzero division.

`ActualPadeRatios318.actual_relations` then discharges every division premise from the literal earlier witness at the same h. In particular its source-coordinate views u, v, shift, fV, B and Padé argument are proved equal to the exact coherent/compressed fields, not merely assigned a common name. The first alternate polynomial retains the asymmetric lower-order formula `1-(v-1)/5`; the other three use PJ/QJ. Primary and alternate ratio indices retain h and h-1 respectively.

All rows51 through78 are verified against `Raw318FinalReplay.r51` through `r78`, including their exact rational coefficients and half-scaled imaginary square gate. The application is forward construction, not a converse decoder supplied with the full source as a premise. First51 preservation is checked by the actual coordinate supports.

## Detector and product gates

`DetectorGateWitness318` evaluates coordinates118 through145 in the original row order. Each expression is the exact negative of the corresponding residual with its new output set to zero; references to earlier generated coordinates use their already defined values. All rows79 through106 are individually verified as literal residual equalities. Since first79 rows use only coordinates below118, they are preserved. The resulting assignment preserves input slot zero and satisfies every first107 literal row.

## Same actual CRT index

`Source107CRTWitness318.select_prefix` calls the original full-density CRT producer with bound B+1. The resulting common h is therefore distinct from 0 and 1, discharging the only excluded common-log identity branch. The same h retains all three congruences, the original nonzero point, scalar threshold `1/(100 sqrt(7))`, fixed strictly positive margins, and fixed signed roots. Those margins imply the nonzero guards required by the first107 constructor. The new assignment is used in the actual source-row conclusion and input equation. No different index or reassignment of a chart is introduced.

The original arithmetic moduli hypotheses are unchanged: positivity, four coprimality conditions, gcd(Mminus,L)=16, and 64 dividing L and h0. No prime-pattern result is assumed silently, and producing these data is not claimed here. The final source system still has181 further rows to construct.

## Validation and evidence

`check_literal_rows.py` independently expands the raw emitted rows over Q(sqrt(2)) using SymPy. All28 Padé/ratio row polynomials agree coefficient-for-coefficient with their stated field identities, including the asymmetric first alternate polynomial. It also verifies the triangular output support of all28 detector gates and the exact coordinate-support bounds used for first51/first79 preservation. These checks support the formula transfer but do not replace Lean elaboration or the field nonvanishing proof.

The packet records source-copy hashes, baseline dependency pins, a recursive axiom audit source, a nine-obligation application contract, and SHA256 sums. Static source-policy/dependency closure and Python regression checks are separate from hosted Lean acceptance. No `sorry`, new axiom, assumed final conclusion, or altered source residual is introduced. The original prior source-completeness passages were reviewed in quartic_v10.tex (sections v9-completeness and v9-deep-completeness); this is a forward formalization of their actual chart/ratio/gate step, not a claim of a new historical gap.
