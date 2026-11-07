# Independent review of actual local different bounds

Accepted at the stated scope. All six frozen modules and the exhaustive audit were copied and freshly rebuilt with strict kernel checking. The final snapshot passes 21 recursively audited declarations, including 15 public theorems, with standard axioms only. The copies match the final author receipt `9b9d13c45353a30424fa13bdb56021460b99415564aba5f7a69ddaee38ba231f` exactly. This includes `different_ideal_eq_pow`, not the earlier 20-declaration snapshot.

## Mathematical checks

1. For a nonzero nonunit x of A, its reciprocal cannot lie in the image of A in its fraction field: injectivity converts a proposed preimage into an inverse of x. For n=[L:K], characteristic zero and positive finite dimension ensure n is nonzero, and the actual field trace of 1/(nx) is exactly 1/x.
2. The codifferent obstruction uses Mathlib's actual trace-dual characterization of `differentIdeal`. If the different lay in (nx), the inverse of nx belongs to the inverse principal fractional ideal and would have trace in A, contradicting the previous fact. The principal ideal is proved nonzero before the characterization is applied. No detached numerical different bound is supplied.
3. DVR ideal order is correctly reversed: noncontainment of the different in (nx) yields `v(different) < v(n)+v(x)`, not the opposite inequality. Associated generators have the same actual additive valuation. The checked `idealOrderIsoENat` is the actual ideal/exponent correspondence.
4. The integer-valuation identity handles the prime-to-p factor by Bezout in the actual local ring. A nonunit p prevents the p term in the Bezout relation from being a unit, forcing the coprime factor to be a unit. Exact p-power divisibility of the nonzero integer supplies the maximal exponent. Thus `v_B(n)=v_p(n)*v_B(p)` has the correct normalization.
5. The ENat-to-Nat conversion never silently maps infinity to zero: the actual strict bound and characteristic-zero nonvanishing establish finiteness first. The actual different is separately proved nonzero, and `different_ideal_eq_pow` identifies it with the maximal ideal raised to the declared natural exponent.
6. The vertical estimate keeps the exact assumptions p prime, p nonunit, p<=d, and [L:K]<=d. The p-adic order is bounded by Nat.log p d, and p<=d supplies log>=1. Hence `(v_p(n)+1) <= 2 floor(log d/log p)`, giving the stated bound with the actual v_B(p). The extra ramification factor e*e_p is used only through its explicit actual valuation identity.
7. In the horizontal case, degree-unit status makes v_B(n)=0. The strict inequality gives the integer bound r<=v_B(x)-1, so choosing a base uniformizer gives r<=e-1. Positivity needed for natural subtraction follows from the strict inequality, rather than being guessed.

## Remaining geometric realization

The actual completed local rings and their fraction-field extension must satisfy the stated integral-closure and DVR hypotheses. The theorem does not claim that an arbitrary localization at one prime is the entire integral closure of the uncompleted base. The geometric application must supply the completed local extension, identify its different exponent with the canonical-differential coefficient, bound local degree by cover degree, provide the branch-prime restriction, identify v_B(p)=e*e_p, and establish degree-unit status in residue characteristic zero.

These are exposed geometric/model inputs. The proof does not construct the regular model, canonical bundle or projection formula, and does not conclude the full five-contact theorem. It genuinely removes the trace/different, local valuation and coefficient inequalities from that remaining application.

## Replay

Run `bash local-different-review/run.sh`. `receipt.json` and `REVIEWED_SHA256SUMS` bind the copied sources, full replay log, author receipt, and the exact Mathlib different and DVR sources reread during this review. No original source or repository file was changed.
