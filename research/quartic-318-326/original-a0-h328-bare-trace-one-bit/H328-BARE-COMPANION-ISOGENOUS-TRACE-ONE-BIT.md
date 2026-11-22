# One integral trace index for the bare fixed companion on the old actual scalar

Keep the prepared original \(a=0\) scalar at \(h=328655617654071015360\), with its own archived fixed \(J\), labels, and real guards. Its actual \(\delta=1-b/17\) is positive and has \(\delta\equiv6\bmod7\), as certified on the old orbit. This is not the newer \(h=473592745039516333133760\) or a separately chosen index on any fresh three-detector key.

Use the fixed \(t_*=18\) first choice and its exact known \(P\) of ordered class \((\beta,1)\) on \(F=E_n:y^2=x(x-n)(x+3n)\). Here \(\beta=204618888056724185\), \(n=\beta(1-324\beta)(1-2916\beta)\) is the archived fully factored squarefree integer and \(F(\mathbb Q)\) has proved rank one. The actual raw companion asks for the bare \(x\)-squareclass \(\beta\) on \(E_d\), \(d=n\delta\). Put \(K=\mathbb Q(\sqrt{\delta})\) and
\[
 G_0:y^2=x(x^2-4nx+16n^2),\quad
 G:y^2=x(x^2-4dx+16d^2),\quad R=\phi_0(P),
\]
with \(\phi_0:F\to G_0\) the zero-root 2-isogeny and \(\hat\phi_0\) its dual. The isomorphism \(j:G_K\to (G_0)_K\), \((x,y)\mapsto(x/\delta,y/(\delta\sqrt\delta))\), is anti-equivariant. The exact relative isogeny gate identifies the desired bare lift with \(R\in\operatorname{Tr}_{K/\mathbb Q}G_0(K)\), and the old \(2\)-Selmer local admission means \(R\) is an everywhere-local trace.

## The complementary torsion direction fails at the literal prime 7

We show \(T_0=(0,0)\) of \(G_0\) is **not** a local trace at 7. The source replay gives exactly \(v_7(n)=1\) and the nonsquare unit \(\delta=6\bmod7\), so \(K_7/\mathbb Q_7\) is unramified quadratic. In contrast \(-3\) is a square at 7, with Hensel root \(\omega\equiv37\bmod49\): \(2^2\equiv-3\bmod7\), derivative \(4\) is a unit, and \(37^2\equiv-3\bmod49\). Thus all roots
\[
 e_0=0,\qquad e_1=2n(1+\omega),\qquad e_2=2n(1-\omega)
\]
are already in \(\mathbb Q_7\); all pairwise differences have depth one. The attached replay checks the marked finite residues. Since the local extension is unramified, the same valuation assertions hold over \(K_7\).

Use the two Kummer functions \(x-e_0,x-e_1\), with the standard specialized value at a root. The valuation parities of the four rational local \(2\)-torsion points and identity are
\[
                 O:(0,0),\quad T_0:(0,1),\quad
                 T_1:(1,0),\quad T_2:(1,1).
\]
For example the first pair at \(T_0\) uses the product of the two other differences, of depth two, and the second uses \(-e_1\), of depth one. The other rows use these same root and derivative conventions. At an odd-residue local field the index of doubling on the elliptic group equals its \(2\)-torsion cardinality: doubling is an isomorphism on a sufficiently small open formal subgroup and the resulting finite quotient has equal kernel and cokernel size. Thus these four distinct parity pairs exhaust both local groups modulo doubling. In particular any \(V\in G_0(K_7)\) is \(T+2W\) for a torsion representative already defined over \(\mathbb Q_7\). Its trace is \(2\operatorname{Tr}W\) since \(2T=0\). The local trace subgroup is exactly the rational doubles (the reverse inclusion follows by taking a rational \(W\)), and \(T_0\) is not a rational double by its displayed parity pair. This is an obstruction to the **torsion discrepancy**, not to the local trace of \(R\).

## Both directions for the integral index

The curve \(G_0\) is rationally isogenous to \(F\), hence has rank one. Its only nontrivial rational \(2\)-torsion is \(T_0\) because the other two roots require \(\sqrt{-3}\). Thus \(G_0(\mathbb Q)/2G_0(\mathbb Q)\) has dimension two. The rational \(R\) is not a double: if \(R=2S\), then \(P-\hat\phi_0S\) belongs to \(\ker\phi_0=\{O,(0,0)\}\) on \(F\). The \(x\)-class on \(F\) is trivial on the dual image, whereas the two kernel classes are \(1,-3\); neither is the exact positive nonsquare \(\beta=[x(P)]\). Moreover \(R\) and \(T_0\) are distinct modulo doubles because \(R\) is already locally a trace and \(T_0\) is not one at 7. They are a basis of the actual rational quotient.

Let \(L_G\subset G_0(\mathbb Q)\) be the everywhere-local trace subgroup. Rational doubles are global traces. The torsion failure at 7 and the admission of \(R\) yield
\[
              L_G/2G_0(\mathbb Q)=\{0,\ R\bmod2G_0(\mathbb Q)\}.
\]
Every global trace lies in \(L_G\), so modulo doubles its image has order one or two. On \(M=G_0(K)\), the rational and anti-invariant subgroups are \(G_0(\mathbb Q)\) and \(jG(\mathbb Q)\) respectively, including torsion. Trace induces the exact isomorphism
\[
 \frac{G_0(K)}{G_0(\mathbb Q)+jG(\mathbb Q)}
       \ \simeq\ \frac{\operatorname{Tr} G_0(K)}{2G_0(\mathbb Q)}.
\]
The kernel statement is immediate: if \(\operatorname{Tr}V=2W\) with \(W\) rational, \(V-W\) is anti-invariant; conversely both summands have traces in the rational doubles. Hence the index is exactly \(1\) or \(2\), without a hypothesis on the rank of the anti-invariant subgroup. When it is \(2\), any representative \(V\) outside the sum has trace \(R+2W\) for a rational \(W\); replacing \(V\) by \(V-W\) gives trace **equal** to \(R\). Conversely a trace equal to \(R\) certifies index two since \(R\) is not a double. Thus this index alone, on the **isogenous** fixed first curve rather than \(F\), is a definitive test for the given bare companion.

For clarity the corresponding relative subgroup of \(\Sha(G/\mathbb Q)\) has order \(2/I\), where \(I\) is this unevaluated index, and if nontrivial its generator is the bare pushed obstruction. Twisted inflation–restriction identifies this subgroup with \(L_G/\operatorname{Tr}G_0(K)\), by the ordinary relative cocycle \(R\) and the same local comparison. There is no finiteness claim for the whole Sha. The exact first rank-one theorem pertains to \(F\), and does not compute this integral index. No point outside the eigensum or certificate that the eigensum has odd index is supplied. This does not assert anything for another \(h\) where the literal 7-adic squareclass may differ.

## Exact pins and replay

- Old first-rank/companion replay SHA-256 7c94388b54349fe6247aa8baace6cbba3f94db8f3c6e2f8e4717308d5cf96d0f, used unmodified in the original-a0-h328-t18-known-nine-pure-second-r1 sibling. Its source paper SHA-256 57875a3c1c2d7a5c8e57fcd46b4f978e95895c9a511f830f59561a590bb2cf65 certifies the fixed rank/basis, complete \(n\) factors, and old local admission.
- Exact relative bare isogeny gate, author manifest 173d6f342c7a87f71430fe6cb7b2799cc02da878f771095c55cef238d6f3c158; exact fixed-secant paper abdda9ebcde0564d9902fd3d352e4cea8d757f7561709bf6688588d192fbdb81. Only the general maps and relative criterion are reused at this old literal index.
- The separate ordered trace paper for this same old indexed scalar, SHA-256 e092b81496bd0d1bd01d1c107d969aab7f1f0e812be001bbfcdc0079d725200b, did not decide the raw companion.

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_h328_bare_trace_p7.py | cmp - EXACT-H328-BARE-TRACE-P7.json
~~~

No new prime, literal orbit value, point, Lean build or remote action.
