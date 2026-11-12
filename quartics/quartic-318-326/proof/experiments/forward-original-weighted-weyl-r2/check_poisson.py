#!/usr/bin/env python3
"""Finite numerical check of same normalized five-coordinate Poisson input.
Not a proof, truncation certificate, or replacement for Lean source.
"""
import cmath,math,json
from pathlib import Path

def one_dim(alpha,M=64,N=16384):
    R=.8;dx=2*R/N;s=0j
    for j in range(1,N):
        x=-R+j*dx
        bump=math.exp(-1/(1-(x/R)**2))
        # Exact finite character sum, evaluated by Dirichlet kernel.
        den=math.sin(math.pi*x)
        ker=2*M+1 if abs(x)<1e-14 else math.sin((2*M+1)*math.pi*x)/den
        s+=bump*cmath.exp(2j*math.pi*alpha*x*x)*ker*dx
    return s
rows=[]
for k,beta in [(318,0.0),(318,0.01),(326,-0.013)]:
    vals=[one_dim(beta),one_dim(-beta),one_dim(-beta*k)]
    dual=vals[0]**2*vals[1]**2*vals[2]
    primal=math.exp(-5)
    err=abs(dual-primal)
    assert err<2e-7,(k,beta,err)
    rows.append({'kappa':k,'beta':beta,'primal':primal,'dual_truncated_real':dual.real,'dual_truncated_imag':dual.imag,'absolute_error':err,'frequency_box':64,'quadrature_steps':16384})
out={'status':'PASS','cases':len(rows),'same_original_input':'W(x)=product exp(-1/(1-(x_i/0.8)^2)) on all |x_i|<0.8; positive phase2pi*i*beta*(a²+b²-c²-d²-kappa*w²); negative Fourier character; product Lebesgue volume','rows':rows,'scope':'Finite numerical regression only. Truncation is not certified here; source proves absolute summability and exact inversion independently. No Lean execution.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS3 smooth original Poisson regressions',max(x['absolute_error'] for x in rows))
