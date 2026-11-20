# Independent finite F53 projection review

Scope: one exact low-level Γ₀(48) row from the marked finite curve
\(E_0:y^2=x^3+1\) and cyclic subgroups \(C_{16},C_3\), not the full
high-level modular parametrization, trace, or a nonvanishing proof.

Source SHA256
517efc3d3466ba24df78d47e593d46aab7ac7fdc37a6ca36a9e2ca040854689c;
exact JSON SHA256
fefb5114278577b338659305ee8ca41b4aa950c732c7e6012c09550d83374750.
Independent stdlib replay was byte-identical. Changing only the
erroneous +4 in the second level-8 map made the first literal fiber
empty. See [Colò, Appendix A, pp. 231–238, 246–247](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf).

For the marked order-2 point \((r,0)\) on the short cubic, translating
\(x\) by \(r\) gives \(y^2=x(x^2+ax+b)\) with \(a=3r, b=3r^2+A\).
The marked parameter is \(t_2=256b/(a^2-4b)\); the invariant \(a^2/b\)
determines the generic marked pair up to scaling. The ordered source
and target \(j\)-values are \((t_2+256)^3/t_2^2\) and
\((t_2+16)^3/t_2\), both checked directly along the actual Vélu map.

The second level-8 map pulls \(t_4\) back to \(t_4(q^2)\), with sole
pole of order two at infinity in the cusp diagram. Its quadratic in
\(t_8=q^{-1}-4+4q+O(q^3)\) is therefore \(t_8^2+8t_8\); the
printed +4 would leave a \(-4q^{-1}\) term. The ordered level-16
maps are \(t_{16}^2/(t_{16}+2)\) and \(t_{16}(t_{16}+4)\).

The two marked coordinates are computed before and after quotienting
by the actual \(C_3\), with a unique top chart solution. At the source
cusp \(\infty\), \(x_{48}\sim q^{-1}\) and
\((y_{48}-2x_{48}-1)/x_{48}=t_{16}(3z)\sim q^{-3}\), so
\(y_{48}/x_{48}^4\to1\). The literal quotient has \(X\to3,Y\to0\);
this is why the implemented basepoint is \((3,0)\). For \(u^2=22\)
the exact raw value is \((44+30u,49+28u)\), and the based value is
\((43+47u,15+18u)\).

The implemented \(\omega=-4-9W-(1+W)F\) has trace 1 and norm
\(61+53=114\), using \(W^2+W+1=0, FW=W^2F, F^2=-53\).
Its differential is \((1+u)/2\) because \(dW=(-1-u/9)/2\), \(dF=0\).
The finite loop tests exact orders and eigenvalue 30438 for the
two retained subgroup generators. No complete class orbit or
\(17^2 19^2\) orientation was proved here; no Lean was run.
