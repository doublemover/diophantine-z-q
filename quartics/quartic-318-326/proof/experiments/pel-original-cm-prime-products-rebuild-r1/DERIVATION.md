# Exact product identities before group relations

For z in I_m and w in I_n, write their real parts m*a and n*c and210=mn*q. Their product has real part mn*(a*c-q*im(z)*im(w)), so it lies in I_mn. Native Ideal.mul_le makes this universal over the full product ideal.

For the reverse inclusion use the already proved actual two-generator presentation I_mn=(mn,theta). The generator mn is the product of the two integer generators. The products m*theta and theta*n lie in I_m I_n; an explicit integer Bezout equation A*m+C*n=1 combines them to theta. Thus both inclusions are produced, with all hypotheses supplied concretely in the actual table.

Apply the exact full integer-ring map to this identity. Native Ideal.map_mul and the proved kernel-map identity yield the same product formula in the actual O_K. No index comparison replaces ideal equality.

For d=210 the kernel consists of elements210*a+s*theta. Each equals theta*(s-a*theta), using theta squared=-210; conversely theta is in the kernel. Therefore I_210 is the actual principal ideal(theta). Combine products2*3,6*5,30*7 with supplied Bezout pairs(-1,1),(1,-1),(4,-17) to prove the full four-prime product principal. Additional pair products2*5 and3*5 are supplied for the later independent-class lower bound.

Finally use the actual nonzero-ideal monoid and ClassGroup.mk0 multiplicativity, with native mk0_eq_one_iff, to derive the all-four relation. The already produced class squares make inverses equal themselves, so the fourth class is the product of the first three. Full class-group generation still requires the native Minkowski prime-ideal classification described separately in the non-admitted recovery plan.
