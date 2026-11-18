# Factorization-free single-square implementation of the marked test

With R,D,H=3D/R as in the main file, a rational point of δ_R exists exactly when
there are v,w in Q with v≠0 and
    
    w² = D (v²+3/R)² + 16v².

Indeed choose V=Dv², Y=Dv w. Then Y²=V(V²+(16+2H)V+H²). On its degree-two dual isogeny to J_R, U=x+4=(Y/(2V))², x=(V+H)²/(4V), and x−H=(V−H)²/(4V). These formulas also directly make the desired three squareclasses, with y the rational signed product of their roots (taking a factor of D). Here V>0 and V=H would imply v²=3/R of odd 17-adic valuation, so no zero factor. Conversely take x=D h₁², x−H=D h₂², x+4=h₃² for a non-torsion rational lift of δ_R. Set v=h₁+h₂≠0; then H=D(h₁+h₂)(h₁−h₂), so with V=Dv² one has h₁=(V+H)/(2D v), giving x=(V+H)²/(4V). The choice w=2v h₃ satisfies the test because 4v²(x+4)=D(v²+H/D)²+16v². The treatment of torsion representatives and avoidance of boundary follow from the main proof. Only the known rational R is used in specifying the test, without extracting either squarefree representative. The quartic is not known to have a rational point at the indexed scalar or contacts.
