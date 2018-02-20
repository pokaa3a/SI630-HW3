from __future__ import division
FD=None
Fb=open
Ft=ValueError
Fm=int
FK=sorted
FC=print
FO=len
FQ=StopIteration
FA=range
FY=str
Fr=isinstance
FG=tuple
Fs=False
FM=float
Fl=max
FL=True
Fc=input
Fh=enumerate
FX=map
Fu=set
Fp=sum
import sys
FP=sys.stdin
FR=sys.exit
FN=sys.argv
Fa=sys.stderr
import math
FH=math.pow
Fd=math.log
import timeit
Fo=timeit.Timer
import random
Fi=random.seed
FU=random.random
import glob
Fj=glob.glob
from operator import itemgetter
class qC:
 q=FD
 F=FD
 I=FD
 def __init__(self,i):
  J.total=0
  J.postags={}
  for W in Fb(i,'r'):
   W=W[:-1]
   (S,k)=W.split()
   if k in J.postags:
    raise Ft("each postag should occur exactly once")
   J.postags[k]=Fm(S)
   J.total+=Fm(S)
  J.qL()
 def qL(J):
  for k in J.postags.keys():
   J.postags[k]=Fd(J.postags[k]/J.total,2)
 def qc(J):
  for k in J.postags.keys():
   yield(k,J.postags[k])
 def qh(J):
  if J.mostLikelyTag is FD:
   (J.mostLikelyTag,a)=FK(J.postags.items(),key=itemgetter(1)).pop()
  return J.mostLikelyTag
class FW:
 N=-1
 R={} #rules
 P={} #lhsRules
 d={} #rhs
 H={} #lhsCount
 o=0 #lhdTotalCount
 
 U='<Unary>' 
 def __init__(J,filelist):
  for i in filelist:
   FC("#reading grammar file:",i,file=Fa)
   j=0
   for W in Fb(i,'r'):
    W=W[:-1]
    j+=1
    if W.find('#')!=-1:
     W=W[:W.find('#')]
    W=W.strip()
    if W=="":
     continue
    f=W.split()
    if FO(f)>4:
     raise Ft("Error: more than two symbols in right hand side at line %d: %s"%(j,' '.join(f)))
    if FO(f)<3:
     raise Ft("Error: unexpected line at line %d: %s"%(j,' '.join(f)))
    (S,D,b)=(Fm(f[0]),f[1],f[2])
    if FO(f)<4:
     t=J.U
    else:
     t=f[3]
    if D==b and t==J.U:
     FC("#Ignored cycle",D,"->",b,file=Fa)
     continue
    J.N+=1
    J.R[J.N]=(D,(b,t),S,FD)
    if D in J.P:J.P[D].append(J.N)
    else:J.P[D]=[J.N]
    if(b,t)in J.d:
     J.d[b,t].append(J.N)
    else:
     J.d[b,t]=[J.N]
    if D in J.H:
     J.H[D]+=S
    else:
     J.H[D]=S
    J.o+=S
 def qX(J,m):
  if m in J.R:
   (D,d,S,a)=J.R[m]
   if a is not FD:
    return a
   else:
    a=Fd(S/J.H[D],2)
    J.R[m]=(D,d,S,a)
    return a
  else:
   raise Ft("rule number %d not found"%m)
 def qu(J,m):
  a=J.qX(m)
  return J.R[m]

 def qp(J,b,t): # ruleIterator
  if(b,t)in J.d:
   for m in J.d[b,t]:
    yield m
  else:
   raise FQ
 def qf(J,D):
  if D in J.H:
   return Fd(J.H[D]/J.o,2)
  else:
   raise Ft("%s: missing lhs"%D)
 def __str__(J):
  K=""
  for i in FA(0,J.N+1):
   a=J.qX(i)
   (D,(b,t),S,a)=J.R[i]
   K+=" ".join([D,b,t,FY(S),FY(a),"\n"])
  for i in J.H.keys():
   FC("#Prior:",i,J.qf(i))
  return K
class FS:
 C=FD 
 O=FD 
 Q=FD 

 def __init__(J,O,Q,limit=1e-300):
  J.C=limit
  J.O=O
  J.Q=Q
 def qg(J,tree):
  Y=[]
  if Fr(tree,FG):
   (D,r,G)=tree
   for n in(J.qg(r),J.qg(G)):
    Y.extend(n)
  else:
   if tree is not J.O.U:
    Y=[tree]
  return Y
 def qe(J,parsetree=Fs):
  s=J.qT(J.Q)
  M=J.qy(s)
  return M if parsetree else J.qg(M)
 def qT(J,D):
  r=FU()
  l=Fd(r,2)
  L=0.0
  c=FD
  for r in J.O.P[D]:
   a=J.O.qX(r)
   h=FH(2,a)
   if l<Fd(h+L,2):
    c=r
    break
   else:
    L+=h
  if c is FD:
   raise Ft("no rule found for %s"%D)
  return c
 def qw(J,sym):
  return sym if sym not in J.O.P else J.qy(J.qT(sym))
 def qy(J,m):
  (D,(b,t),S,a)=J.O.R[m]
  r=J.qw(b)
  G=J.O.U if t is J.O.U else J.qw(t)
  return(D,r,G)
class Fk:
 O=FD #gram
 X=FD # chart
 u=FD #unseen
 p=0 #verbose
 f=Fs #usePrior
 g=Fs #usePruning
 e=Fd(0.0001,2)
 T=FM('1e-323')
 w=Fd(T,2) # _LOG
 def __init__(J,O,verbose=0):
  J.O=O
  J.p=verbose
 def qz(J,i,j):
  if J.g==Fs:
   return 0
  y=0
  if(i,j)in J.X:
   z=J.X[i,j]
   V=FD
   n=FD
   for D in z.keys():
    (a,x)=z[D]
    V=Fl(a,V)
    if V==a:
     n=D
   E={}
   if J.f:
    v=V+J.e+J.O.qf(n)
   else:
    v=V+J.e
   for D in z.keys():
    (a,x)=z[D]
    B=a
    if J.f:
     a+=J.O.qf(D)
    if a<v:
     FC(Fa,"#pruning:",i,j,D,a,v,file=Fa)
     y+=1
     continue
    E[D]=(B,x)
   J.X[i,j]=E
  return y
 def qV(J,i,j,D,a,x):
  if(i,j)in J.X:
   if D in J.X[i,j]:
    qF=J.qE(i,j,D)
    if a<qF:
     return Fs
  else:
   J.X[i,j]={}
  J.X[i,j][D]=(a,x)
  if J.p>1:
   FC(Fa,"#inserted",i,j,D,a,file=Fa)
  return FL
 def qn(J,i,j):
  qI=[entry for entry in J.qx(i,j)]
  for d in qI:
   qJ=J.qE(i,j,d)
   for m in J.O.qp(d,J.O.U):
    (D,(b,t),S,a)=J.O.qu(m)
    if D==d:
     raise Ft("Found a cycle",D,"->",d)
    x=(-1,d,J.O.U)
    if J.qV(i,j,D,a+qJ,x):
     qI.append(D)
 def qx(J,i,j):
  if(i,j)in J.X:
   for qW in J.X[i,j].keys():
    yield qW
  else:
   raise FQ
 def qE(J,i,j,D):
  if(i,j)in J.X:
   return J.X[i,j][D][0]
  else:
   raise
 def qv(J,Fc):
  J.X={}
  y=0
  for(i,qS)in Fh(Fc):
   j=i+1
   if(qS,J.O.U)in J.O.d:
    for m in J.O.d[(qS,J.O.U)]:
     (D,d,S,a)=J.O.qu(m)
     J.qV(i,j,D,a,FD)
   else:
    FC("#using unseen part of speech for",qS,file=Fa)
    if J.u is FD:
     raise Ft("cannot find terminal symbol",qS)
    else:
     for(k,a)in J.u.tagsForUnseen():
      J.qV(i,j,k,a,FD)
   J.qn(i,j)
  N=FO(Fc)+1
  for j in FA(2,N):
   for i in FA(j-2,-1,-1):
    for k in FA(i+1,j):
     for b in J.qx(i,k):
      for t in J.qx(k,j):
       qk=J.qE(i,k,b)
       qa=J.qE(k,j,t)
       for m in J.O.qp(b,t):
        (D,d,S,a)=J.O.qu(m)
        x=(k,b,t)
        J.qV(i,j,D,a+qk+qa,x)
    J.qn(i,j)
    y+=J.qz(i,j)
  if J.p>0:
   FC("#number of items pruned:",y,file=Fa)
  qN=J.w
  N=FO(Fc)
  if(0,N)in J.X:
   if Q in J.X[0,N]:
    (qN,x)=J.X[0,N][Q]
  if J.p>0:
   FC("#sentence log prob = ",qN,file=Fa)
  return qN
 def qB(J,Fc,Q):
  k="X" if J.u is FD else J.u.getMostLikelyTag()
  qR=FX(lambda z:"("+k+" "+z+")",Fc)
  return "("+Q+" "+" ".join(qR)+")"
 def Fq(J,Fc,startsym='TOP'):
  N=FO(Fc)
  if(0,N)in J.X:
   if startsym in J.X[0,N]:
    return J.FI(Fc,0,N,startsym)
  FC("#No parses found for:"," ".join(Fc),file=Fa)
  return J.qB(Fc,startsym)
 def FI(J,Fc,i,j,sym):
  if(i,j)in J.X:
   if sym in J.X[i,j]:
    (a,x)=J.X[i,j][sym]
    if x==FD:
     return "("+sym+" "+Fc[i]+")"
    (k,qP,qd)=x
    if k==-1:
     r=J.FI(Fc,i,j,qP)
     G=""
    else:
     r=J.FI(Fc,i,k,qP)
     G=J.FI(Fc,k,j,qd)
    return "("+sym+" "+r+" "+G+")"
  raise Ft("cannot find span:",i,j,sym)
if __name__=="__main__":
 import getopt
 qH="\n        ".join([FN[0],"[-h|--help]              # [ ] are optional arguments","[-v|--verbose level]","[-s|--start] startsymbol","[-i|--parse]","[-o|--generate number]   # use either --parse or --generate","-g|--grammar file1[,file2,file3,...] or -g|--grammar \"*.gr\" do *not* use simply *.gr"])
 qo=["parse","generate","verbose","help","prior","pruning","grammar=","beam=","start=","unseen="]
 try:
  qU,qi=getopt.getopt(FN[1:],"io:v:hrpg:b:s:u:",qo)
 except getopt.GetoptError as qj:
  FC(FY(qj),file=Fa)
  FC(qH,file=Fa)
  FR(2)
 Fi()
 qv=Fs
 qe=Fs
 p=0
 f=Fs
 g=Fs
 qD=FD
 e=Fd(0.0001,2)
 Q='TOP'
 qb=FD
 for o,a in qU:
  if o in('-i','--parse'):
   qv=FL
  if o in('-o','--generate'):
   qe=FL
   qt=Fm(a)
  if o in('-v','--verbose'):
   p=Fm(a)
  if o in('-h','--help'):
   FC(qH,file=Fa)
   FR()
  if o in('-r','--prior'):
   f=FL
  if o in('-p','--pruning'):
   g=FL
  if o in('-g','--grammar'):
   qD=[f for i in a.split(',')for f in Fj(i)]
   qD=[f for f in Fu(qD)]
   FC("#loading grammar files:",', '.join(qD),file=Fa)
  if o in('-b','--beam'):
   e=Fd(FM(a),2)
  if o in('-s','--start'):
   Q=a
  if o in('-u','--unseen'):
   qb=a
 if qD is FD:
  FC(qH,file=Fa)
  FR(2)
 if not qv and not qe:
  FC(qH,file=Fa)
  FR(2)
 O=FW(qD)
 if qe:
  qm=FS(O,Q)
  for i in FA(qt):
   FC(" ".join(qm.qe()))
 if qv:
  qK=Fk(O,p)
  qK.f=f
  qK.g=g
  qK.e=e
  if qb is not FD:
   qK.u=qC(qb)
  qO={}
  qQ=0
  qA=FD
  for W in FP:
   W=W[:-1]
   Fc=W.split()
   qY=FO(Fc)
   if qY<=0:
    continue
   if W[0]=='#':
    FC("#skipping comment line in input:",W,file=Fa)
    continue
   qQ+=qY
   qN=qK.qv(Fc)
   qA=qN if qA is FD else qA+qN
   FC(qK.Fq(Fc,Q))
   if p>0:
    qr=qK.p
    qG=Fo("parser.parse(input)","from __main__ import parser; parser.p=0; input=%r"%Fc)
    qs=qG.timeit(number=2)
    if qY in qO:
     qO[qY].append(qs)
    else:
     qO[qY]=[qs]
    qO[qY].sort()
    FC("#parsing time: length=%d secs=%0.3f"%(qY,qs),file=Fa)
    qK.p=qr
  if qQ>0:
   FC("#-cross entropy (bits/word): %g"%(qA/qQ),file=Fa)
  if p>0:
   if FO(qO.keys())>0:
    FC("# LEN SECS MAX MIN",file=Fa)
   for qY in qO.keys():
    qM=FO(qO[qY])
    ql=FM(Fp(qO[qY])/qM)
    FC>>Fa,qY,ql,qO[qY][0],qO[qY][qM-1]
# Created by pyminifier (https://github.com/liftoff/pyminifier)
