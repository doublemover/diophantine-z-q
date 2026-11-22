# The asymmetric λ=0 coordinate end of the selected mixed infinity corner

Use the same actual compact source, selected plus primary-1 × minus alternate-1 poles, literal 19-unit scale, and first horizontal blowup of the exact inverse coordinates r=1/U (primary) and s=1/V (alternate). This closes the single coordinate end λ=s/r=0. Unlike the other end, the surviving degree-32 term is driven by the alternate pole while the separate last leaf still involves the primary pole. No symmetry between those leaves is assumed.

In the r-chart put λ=s/r, so s=rλ; the named geometric direction is π=r=λ=0, with π=19. The chart is regular as the original étale pullback of the horizontal coordinate blowup. Its fibre above the chosen raw point is the actual affine chart of the exceptional projective line. The exact shared-leaf difference is now

    Δ=U−V=(λ−1)/s.

Use the literal expansion and its coefficient domains from the diagonal proof,

    f_+=Δ^32+Σ_(j=0)^15 b_j Δ^(2j)+(H−M/r)²,

with b_j,H regular, M=2P₀² on the selected primary arm, and G=f_- regular with reduction 1. In this chart the correct strip is by s^32, **not** by the primary coordinate r^32. It gives

    F=s^32 f_+
      =(λ−1)^32 + Σ b_j s^(32−2j)(λ−1)^(2j)
                   + r^30 λ^32 (Hr−M)².

The last exponent is the exact factor s^32/r²=(rλ)^32/r². Integrality at λ=r=0 therefore holds despite the unequal role of the last primary leaf. The leading term is 1 at the direction; all other terms vanish. Thus F and F+s^32 G are units near this point, and the exact trace contact

    c_fold=κ F G/(F+s^32 G)

is regular and divisible by π^e with e=v₁₉(κ)>0. The literal square cover δ=1−β c_fold² is finite étale on this regular neighborhood and has residual square-root values ±1 at the named geometric point. Its normalized geometric fibre over the direction consists of two points, not a Kummer curve. There is no parity requirement on e.

By BLR extension a rational map to the good elliptic target is a morphism on this regular normalization, so the main graph at the direction cannot give any positive-dimensional elliptic image. The proper first blowup comparison applies to valuations centred at this direction. This is a proof for λ=0 with its own actual normalization; the λ=∞ direction is a separate proof and uses a different strip.

Exact binding: inverse pole coordinates and weighted primary J identity manifest 0c23f97db63715427e3c64265bb48e8b1f470d0838f5fd73fb1c664a4518752b; degree-32 exact polynomial expansion and diagonal normalization manifest 21d23fb408c6ab318dd7c1b5abd4a5262fde983f77d2fe477293e6b99d7a1014 / note ff0df8a143af59ce37ec23d473f6e01be47ee4a9c341302a6289b0add510ce55; independent other-end λ=∞ manifest 341cb7daabed2e1cf94942acf1223791496c41095c20e7913dab52d7de4ce883; actual good-target manifest e9a3423e5bf681944b8a70529990763bfce3f8e2db92fe8b1b5bdb64fb4b9e7f; [BLR, Néron Models §8.4 Cor. 6](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf). No arithmetic scan or global map claim.
