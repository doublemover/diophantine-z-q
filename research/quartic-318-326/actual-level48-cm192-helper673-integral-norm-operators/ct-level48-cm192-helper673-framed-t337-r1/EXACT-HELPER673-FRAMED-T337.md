# The fixed degree-337 operator on the framed supersingular fibre at 673

This is a numerical reference operator for the previously constructed framed fibre at 673. It is not an original detector twist, its signed intersection product, or a rational mark. The fixed reference prime is $337=9^2+16^2$.

Use the same 56 short Weierstrass models, the same model order, and the same ordered 32- and 3-bases as the degree-17 table. The input SHA-256 bindings in the replay identify both its Python definitions and its JSON. Work in $\mathbf F_{673^4}$ with the old field generator raised to the eighth power, so that $z^4=118$. This retains the old bases without any coordinate re-selection. All model coefficients lie in $\mathbf F_{673^2}$; for these nonspecial supersingular models their 673-squared Frobenius is $\pm[673]$. Therefore on the fourth-degree field the annihilator is $673^2-1$, a number of valuation precisely one at 337. The replay constructs two independent rational points of exact order 337 on each model; independence is checked by testing the new point against the entire first cyclic subgroup. The 338 cyclic lines are exactly $\langle P+iQ\rangle$ for $i\in\mathbf F_{337}$ and $\langle Q\rangle$. Their 56,784 kernel abscissae (one for each nonzero point up to sign) are all checked distinct. They belong to the quadratic subfield, as is also forced by $673\equiv-1\pmod {337}$ and scalar quadratic Frobenius.

On $E:y^2=G(x)=x^3+Ax+B$, a kernel pair with abscissa $r$ contributes to the normalized Vélu abscissa the rational function

$$
 \frac{2G'(r)}{x-r}+\frac{4G(r)}{(x-r)^2}.
$$

Indeed, add the two chord–tangent formulas for the translates by $(r,\pm\sqrt{G(r)})$ and subtract both kernel abscissae. Since a normalized Vélu isogeny preserves the invariant differential, the ordinate is $y$ times the derivative of its abscissa. The target coefficients subtract respectively $10\sum_r G'(r)$ and $14\sum_r(5r^3+3Ar+2B)$. Kernel denominators at the four marked basis points never vanish because their orders divide 96. The code evaluates in batches, explicitly checks the target equation and its scale to the stored model, and extracts all four target basis coordinate vectors. The choice of square root of the scaling factor changes only the single common sign, recorded by the existing table convention.

The exact JSON has 56 rows of 338 labelled cyclic isogenies, hence 18,928 edges. Dual reversal (composition the scalar 337 up to the common sign) and Frobenius equivariance are checked on every row with the same matrix and orientation convention as degree 17. A complete stdlib replay took 33 seconds with six workers in the author run; individual rows can also be replayed by giving their zero-based indices. A successful all-row output is byte-deterministic. This fixes only one reference operator, not the aggregate over any selected detector.
