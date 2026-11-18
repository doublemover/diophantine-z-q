"""Check against the pinned repository, and exhaust finite local data and CRT examples.
Run: python verify_source.py /path/to/repository ; no Lean execution."""
import pathlib,json,sys,hashlib,subprocess,math,itertools
root=pathlib.Path(__file__).parent
orig=json.loads((root/'ORIGINALS.json').read_text())
for f,s in orig['sha256'].items():
    assert hashlib.sha256(subprocess.check_output(['git','-C',sys.argv[1],'show',orig['git']+':'+f])).hexdigest()==s
def prime(n):
    return n>=2 and all(n%i for i in range(2,math.isqrt(n)+1))
def v2(n):return (n&-n).bit_length()-1
# Exact small genuine 9 mod16 / (1+3i) mod7 representatives:
picked=[]
for a in range(-1000,1001):
 if a%16!=9 or a%7!=1: continue
 for b in range(-1000,1001):
  if b%16 or b%7!=3: continue
  p=a*a+b*b
  if not prime(p):continue
  lo=(a-1)**2+b*b;hi=(a+1)**2+b*b
  assert v2(lo)==6 and v2(hi)==2 and (lo%7,hi%7)==(2,6) and p%8==1
  if math.gcd(lo,hi)==4 and all(math.gcd(z,n)==(4 if (v2(z)==2 or v2(n)==2) else 64) for _,x,y in picked for z,n in itertools.product((lo,hi),(x,y))):
   picked.append((p,lo,hi))
  if len(picked)>=5:break
 if len(picked)>=5:break
assert len(picked)>=2
L=64*7; Pi=math.prod(p for p,_,_ in picked)
Mm=math.lcm(*(x//4 for _,x,_ in picked));Mp=math.lcm(*(y//4 for _,_,y in picked))
assert [math.gcd(Pi,Mp),math.gcd(Pi,L),math.gcd(Mm,Mp),math.gcd(Mp,L),math.gcd(Mm,L)]==[1,1,1,1,16]
print(json.dumps({'pinned_repo_members':len(orig['sha256']),'finite_crt_check_primes':[p for p,_,_ in picked],'gcd_vector':[1,1,1,1,16],'fixture_not_an_original_grid':True},sort_keys=True,indent=2))
