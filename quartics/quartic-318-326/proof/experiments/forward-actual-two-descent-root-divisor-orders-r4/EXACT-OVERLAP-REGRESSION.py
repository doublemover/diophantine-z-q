"""Finite ring checks of the exact overlap identities, not Lean verification."""
from collections import Counter
import json

def run():
    counts=Counter(); wrong_direction=False; wrong_scale=False
    for p in [7,11,13,17,19]:
        inv=lambda z:pow(z,-1,p)
        for n in range(p):
            for x in range(1,p):
                rhs=x*(x-n)*(x+3*n)%p
                for y in range(1,p):
                    if y*y%p != rhs:continue
                    u=x*inv(y)%p;v=inv(y);e=v*inv(u**3%p)%p
                    assert e and u and v
                    invu=e*u*u*inv(v)%p
                    assert u*invu%p==1
                    counts['original_overlap_points']+=1
                    if n==0:counts['zero_parameter_points']+=1
                    for a in [0,n,-3*n]:
                        f=(x-a)%p;d=(u-a*v)*inv(u)%p;pole=d*inv(e)%p
                        assert f and d and pole
                        assert f*u*u%p==pole
                        assert f*inv(pole)%p==invu*invu%p
                        root_unit=pole*invu*invu%p
                        assert root_unit==f
                        assert invu*invu*inv(root_unit)%p==inv(pole)
                        counts['three_root_pole_and_inverse_checks']+=1
                        wrong_direction |= f*pole%p != invu*invu%p
                        for b in [0,1,2,p-1]:
                            for c in [0,1,3,p-1]:
                                av=b*invu%p;aw=c*invu%p
                                assert av*aw%p==(b*c)*(f*inv(pole))%p
                                assert av*aw*inv(root_unit)%p==b*c*inv(pole)%p
                                counts['exact_matched_square_values']+=1
                                if not b or not c:counts['zero_section_values']+=1
                                wrong_scale |= av*aw*inv(root_unit)%p != b*c*pole%p
    assert wrong_direction and wrong_scale
    counts['negative_controls']=2
    return {'status':'PASS','scope':'Exact finite-ring identity regression; not Lean or whole-proof validation','counts':dict(counts)}
if __name__=='__main__':
    from pathlib import Path
    result=run();Path(__file__).with_name('EXACT-OVERLAP-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
