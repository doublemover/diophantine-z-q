from fractions import Fraction as Q
from pathlib import Path
import json,itertools
checks=0
for c,t,R,I in itertools.product((Q(1),Q(2),Q(-3),Q(2,5)),(Q(-2),Q(1,3),Q(2),Q(5,7)),(Q(1),Q(-2),Q(3,5)),(Q(0),Q(1),Q(-4,3))):
 P=c*c*t;D=P-1;F=P*(P+Q(1,2))*(P+1)*(P-Q(1,2399))*(P+Q(32,407))
 if not F or not D:continue
 W=c**10*D**2/F;T=(R*R-2*I*I)/(2*R);Z=T*T*F/(c**10*D**6)
 assert -Q(1,2)*R*R+R*T+I*I==0
 assert W*D**4*Z==T*T
 assert -(W*D**3*Z)+P*W*D**3*Z-(T*T)==0
 checks+=3
result={'status':'PASS','literal_trace_pole_and_contact_checks':checks}
Path(__file__).with_name('DETECTOR284-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
