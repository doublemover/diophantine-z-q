"""Exact finite floor/boundary/translation checks; not a Lean proof."""
from fractions import Fraction as F
from itertools import product
import math,json

def check():
    cases=0
    for x in product((F(-3,2),F(-1),F(0),F(1,2),F(1)),repeat=5):
        z=tuple(-math.floor(a) for a in x)
        y=tuple(a+b for a,b in zip(x,z))
        assert all(0<=a<1 for a in y)
        for i in range(5):
            for d in (-2,-1,1,2):
                yy=list(y); yy[i]+=d
                assert not all(0<=a<1 for a in yy)
        cases+=1
    return {'exact_floor_boundary_cases':cases,'nontrivial_coordinate_translate_rejections':20*cases,'status':'PASS finite regression only'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
