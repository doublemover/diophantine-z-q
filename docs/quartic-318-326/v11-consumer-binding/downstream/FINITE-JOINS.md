# Additional finite joins found during the downstream inventory

This supplements, without changing, receipt.json. It prevents existing algebraic proofs from being mistaken for fresh global gaps. It also checks the elementary local arithmetic of the final correction. No complete witness-existence theorem or new Lean replay is claimed.

## Normalized pole coordinates already have an exact reverse map

The published component files OrdinaryPoleNormalization.lean and ThreeHelperPoleNormalization.lean were read in full. FinalComponentsAudit.lean imports both and lists their axiom audits at lines 235-237 and 266-270.

ThreeHelperPoleNormalization.existential_equivalence is quantified over every b in an arbitrary field, including b=0. The map from the current normalized witnesses to its old equations is

old_p = p, old_e = b*e, old_s = b*s, old_q = b*q.

The first residual changes by factor b and the second by b^3. For b nonzero the inverse divides e,s,q by b and leaves p unchanged. At b=0 both existential gadgets receive explicit zero witnesses. three_helper_equivalence then assigns h=e*(17-b), ss=s^2 and t=(ss-h)*(ss+3h), and yields exactly the lifted first residual and 17*q^2-b*t=0 in the current builder. This is an existing complete finite existential comparison, not an assumed arithmetic existence theorem.

For the V11 preparation-zero predicate, B=17b, U=b and h_old=e_old*(B-b^2). Its displayed first equation is p_old^2=B*(1-e_old)*(1+3e_old). Set the old component e-coordinate to B*e_old, retaining p_old,s_old,q_old. Multiplying the first displayed residual by B gives OrdinaryPoleNormalization.oldFirst, and the second residual is already oldSecond. For the completeness application b>0, B is nonzero, so this is an exact comparison. Together with the existing ThreeHelper theorem this supplies the normalized conic algebra used by the final builder. The remaining work is constructing the actual compatible b and arithmetic pole witnesses, then joining these already available maps into every source row.

## Final local correction checked directly

Let z be any integer, beta=3723(2z+1)^2 and r=(beta-1)(beta-2401)(32beta+343)(2beta-1). Then beta>=3723, so r is positive and exceeds 10. In particular none of its four factors vanishes, including z=0 or z=-1.

At 2, beta=3 mod8. Thus the first two factors have valuation one; the last two are odd, and v2(r)=2. The odd numbers (beta-1)/2 and (beta-2401)/2 differ by 1200, a multiple of 8, so their product is an odd square modulo 8. The last two factors are 7 and 5 modulo 8. Consequently r/4=3 mod8.

At 3, beta=0, so r=(-1)*(-1)*1*(-1)=2 mod3. At 17, beta=0 and 2401=4,343=3 modulo17, so r=(-1)*(-4)*3*(-1)=5 mod17. These are units.

The actual correction is a=114444r=4*9*17^2*11*r. Therefore:

- v2(a)=4 and the odd unit is 11*(r/4)=1 mod8.
- v3(a)=2 and its unit is (4*17^2*11)*2=1 mod3.
- v17(a)=2 and its unit is (4*9*11)*5=8 mod17, a square because 5^2=8 mod17.

Hence a is a nonzero square in each of Q2,Q3,Q17, with valuations 4,2,2. This verifies the final correction rather than the historical 28611 or old nested input. It uses the standard elementary local-square criteria, not RC or Kato.

Now suppose the actual simultaneous construction supplies rational W with 0<W<2 and v_p(W)=0 for every p dividing a. Then b=a(W/(1+a))^2 has square reduced denominator: if p divides a, 1+a and W are units and v_p(b)=v_p(a)>=0; otherwise v_p(b)=2v_p(W)-2v_p(1+a) is even. Thus every negative valuation is even. At 2,3,17 the values remain 4,2,2 and b is a square. Also 0<b<4/a<17. These are exactly the preparation-zero numerical hypotheses.

The unresolved input in this last paragraph is essential: the needed W must arise from the final scalar/point choices and be a unit at all primes of a while the same choices meet the detector, guard, anchor and ray conditions. Merely proving these conditional local facts does not produce that common W or complete the 288-row assignment.
