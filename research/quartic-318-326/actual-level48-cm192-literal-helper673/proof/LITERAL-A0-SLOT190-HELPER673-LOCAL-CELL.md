# A literal a=0 slot-190 local cell for helper 673

The fixed-helper setup has a concrete local cell at $I=673$ on the **published actual scalar anchor and its literal detector prefix**, not on a free numerical Ready example. At this cell the actual slot 190 has square companion residue, and the five contact forms can be prescribed square with the order-only denominator prime nonsquare. The same two other detector slots have regular unit fold residues on that cell. This packet verifies the local input to the fixed-helper source refinement. It does not materialize that global key or its final common index, the selected $n$, or the supersingular Hecke product.

## Exact source

Use the published $a=0$, old $q=1041427$ scalar-prefix snapshot, checksum **5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7**. Its $J,h_*$ and original nonzero real scalar/guard margins are retained source data. The old $q$ in that snapshot is **not** identified with the as-yet unchosen order-only denominator prime of the new linear-q key. For the literal labels use the pinned fixed-scalar prefix: $i=6^{15}3^{65536}J$, $s=1+i$, $k=2(s-2)$, and labels
$$
  3723,\quad s,\quad U_s(k+1),\quad U_s(k)/(s-2),
  \qquad U_s(j+2)=sU_s(j+1)-U_s(j),\quad U_s(0)=0,\ U_s(1)=1.
$$
The last entry is computed modulo a larger modulus before dividing its denominator's nonunit part. No expanded Lucas integer is needed.

The two embeddings at 673 are $\sqrt2=\pm283$. On each arm use the actual source elliptic curve and generator
$y^2=x^3-(3-\sqrt2)^2x$, $R=(1+\sqrt2,2\sqrt2)$.
Their orders are independently *computed* as $314,314$. The retained $h_*$ is $290\bmod314$, with labels $(269,107,313,307)\bmod314$. The fixed c-scales are $(1,293,123)$, all units. The twelve nonzero normalized contact roots, four in each scale (the zero root is shared), are distinct modulo 673. Thus this prime does not force a denominator in the slope clearing; that clearing may be chosen a 673-unit.

## The exact chosen residue

At $t=61\bmod673$ the replay evaluates both arms of the actual coherent charts, all used Padé/shift divisions, guard traces $(546,24,537,651)$, the literal 16 signed/nonsquared leaf coefficients, and the recurrence $X_j=X_{j-1}^2+\mathrm{leaf}_j$. The three rows list the real and imaginary fold, its trace quotient, the literal pole $b_j$, and $1-b_j/17$:
$$
 (94,91,367,628,162),\quad
 (165,78,272,84,194),\quad
 (329,352,376,472,92).
$$
All pole denominators used in these probes are units. The first companion value $162=145^2\bmod673$ is a nonzero square. The five unscaled terms $t-a_i$ are all nonzero nonsquares. Taking the new denominator-prime residue $q_*=5$, a nonsquare, the five target norm residues up to the unavoidable common square $(D_{\rm clr}Q)^2$ are $305,644,310,243,355$, all squares; all form residues on the other two rows are nonzero as well. $I=673$ is prime, is $1\bmod24$, and $(17/673)=-1$. This is the exact incidence vector $\{17,q\}$ for the future slot-190 selected first arm, not an arithmetic assertion about the other two helpers or about their $\theta$ classes.

All these equalities persist when the source index is varied in $h\equiv290\bmod314$ with the same fixed labels and $t\equiv61\bmod673$: each finite chart is a rational function of the two reduction points, and every used inverse is a unit. The old retained progression agrees with this period at $h_*$; one may refine it by the period without taking a different scalar anchor.

What remains global is to integrate this local cell into the **row-specific** fixed Gaussian ray at 673, retaining the other old wheels, once the actual linear-q key and single common index are selected. The generic fixed-helper argument handles such a residue table without including 673 as a divisor of $Q$; the slot-190 Selmer extension uses only aggregate $(\theta/673)=+1$, which the displayed square residue ensures for any continued source in this cell. Neither an actual new $u,q$ nor the normal-form Hecke operators at the resulting prime supports are supplied here.

## Exact arithmetic sources

The attached old-prefix data are byte-identical to the published snapshot. The gate-expression file contains only the literal definitions 118–138 of DetectorGateWitness318.lean (source SHA **5c6c61539543b60806bada94c2af35681ef98796d38e795c05ea74cb081a724d**). The same formulas for the other parts are CoherentMultipleCharts318.lean SHA **01443a070ea295862a1c06111e8803651d6766afead3c3918797aa5718ba9bc9**, CoherentMultiplePrefix318.lean SHA **54c2bffb492db9c8f7ae7ec30a3c6d6f7bab17de617f3f90a5b9a2ac2a63ba46**, ActualPadeRatios318.lean SHA **536503bb576c233ab948145db9d323ea5f28b5c96bacb6b1953fced45ea74244**, and ActualDetectorFold318.lean SHA **1bb3b85f8bc3ca7bd58c252ebda8b416b7011905a212a6aae7ec9c1ee5513cf5**. No Lean build is run by the standalone finite Python replay.
