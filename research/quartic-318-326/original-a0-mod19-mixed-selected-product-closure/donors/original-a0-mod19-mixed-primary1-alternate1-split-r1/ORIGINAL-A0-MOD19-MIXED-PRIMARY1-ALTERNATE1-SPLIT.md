# One actual mixed primary-1 × alternate-1 transition and its two Jacobian factors

Keep the same genuine symbolic fresh input-zero original key and sharp compact labels (N,n,N,N). Use one actual unit scale, in particular slot 190. Choose the isolated primary-1 pole on the plus arm as in the reviewed primary divisor proof, and the isolated alternate-1 pole on the minus arm using the conjugate of the reviewed fixed Padé root in the distinct alternate-only proof. The choices are independent after the unramified arm split; all bound and regularity exclusions remain those of the two respective donor selections. This is one geometric closed intersection of the actual arm coordinates, not a freely selected model for their folded variables.

At the chosen primary centre p₁ is the only pole, and on the opposite alternate centre a₁ is the only pole. Both are simple and lift as horizontal coordinate divisors, say x=0 and y=0. The intrinsic P₀=p₀=p₂=p₃ on the primary arm is regular and nonzero by the permitted preimage exclusions. In the plus split fold the leaf at stage 12 is (p₁−conj(a₁))² and thus sees both simple poles; the same stage of the minus split fold is wholly regular. The last leaf (J−1)², with J=P₀²(5−2p₁), sees only the primary pole on the plus arm. All other additive leaves in both folds are regular before their weights. In particular this is not the case where the two poles enter separate folds.

Let π=19, x=π^d X, y=π^d Y at the last transition scale 2d=v₁₉(Z) of the actual common leaf-12 and leaf-16 weight. On the special transition torus write U=A/X and V=B/Y, where A,B are the respective nonzero simple pole leading residues multiplied by the square root of the stripped weight (extend constants finitely). The exact recurrence now gives the initial strip polynomials

    bar(f_+) = (1+(U−V)²)^16 + α U²,       α=4 P₀(P_+)^4 ≠0,
    bar(f_−) = 1.

Indeed the stage through 11 is 1 in both folds. The cross-term at stage 12 is kept, and the four subsequent squarings produce the displayed sixteenth power. The weighted last leaf on the plus arm then adds 4P₀(P_+)^4 U²; it contains no alternate pole. This follows from the literal split leaf computation in the exact donors.

On trace cancellation put z=U−V and replace U by y_C=sqrt(−α) U (geometric constants). The linear coordinate change from U,V is invertible, and gives the function field of the fixed hyperelliptic curve

    C_15: y_C² = (1+z²)^16 + 1.

The torus omits U=0 and V=0, which do not contain this curve: on U=0 the nonzero polynomial (1+z²)^16+1 has only finitely many roots, and on V=0 one gets the nonzero polynomial (1+U²)^16+αU²+1 (degree 32). There is no additional square cover to take after this change since U,V already were the actual inverse chart parameters. The right side has degree 32 and is squarefree, its derivative being 32z(1+z²)^15 with candidate common zeros giving values 2 or 1. The smooth compactification is geometrically integral of genus 15. On the actual trace torus f_+=−1 and f_−=1, and the trace has nonzero derivative at fixed z in U since 2αU≠0. Thus it is a genuine simple-cancellation curve there, not a high-collision common zero. This does not resolve chart closures at an omitted coordinate.

For the quotient structure label the hyperelliptic involution ι:(z,y_C)→(z,−y_C) and σ:(z,y_C)→(−z,y_C). The two degree-two quotients by σ and ισ, respectively, are

    C_7: Y² = x^16+1,             x=1+z², Y=y_C,
    C_8: W² = (x−1)(x^16+1),      x=1+z², W=z y_C .

Their affine defining polynomials are squarefree, because x=1 is not a root of x^16+1 and 19 does not divide 16. Their genera are 7 and 8. Pullbacks of their holomorphic differentials are 2z(1+z²)^i dz/y_C for 0≤i≤6 and 2(1+z²)^i dz/y_C for 0≤i≤7. These span all fifteen differentials by their different parity and respective triangular leading powers of z. Equivalently the two pullbacks on Jacobians are the distinct ± eigenspaces for σ, with dimensions adding to 15. The sum is therefore an isogeny from Jac(C_7)×Jac(C_8) to Jac(C_15), already on the fixed displayed model over F₁₉. A finite extension needed to identify the actual trace chart with that model is fine for geometric quotients.

The genus-seven factor is covered by the degree-16 Fermat curve via Y=w^8 on x^16+1=w^16. The genus-eight factor is the new fixed arithmetic test; this paper makes no claim about its ordinary elliptic factors. In particular genus 15 itself does not imply presence or absence of a suitable elliptic quotient. Only this one mixed transition torus is treated; its axes, infinity, and all other pole types are outside its geometric assertion.

Exact donors: isolated primary-1 manifest 02046fb7d8068bab9d564039451c0c75db471d899651cce916455681cdd8f15c; exact pure alternate Padé root and pole-selection manifest 1ab2200b55d26821056b2af85e0de933179c9442cc8ecfefef2baab025edacde; late-leaf expansion 4e670532e6319522eb0f78327591a6c248722ff3f4ef2459b3a1dbcca89b5ad0; compact full-support manifest 9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5; actual unit-scale manifest 9467d1bdd442c1f58b405878c8092282b100c8f3af68021af830b61bdabbc9e1. No arithmetic search, numerical key or coherent map.
