(* ::Package:: *)

ClearAll[Evaluate[Context[]<>"*"]];
$Path=DeleteDuplicates@Append[$Path,NotebookDirectory[]];
<<UnitTesting`
<<AngularMomentum`


(* ::Subsection:: *)
(*Unit Tests*)


initialiseTests[];


addTest[toTJ[sum[cg[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]cg[{d,\[Delta]},{e,\[Epsilon]},{f,\[Phi]}],\[Alpha],\[Beta],\[Gamma]]],
	sum[Sqrt[2c+1]Sqrt[2f+1](-1)^(-a+b-\[Gamma]-d+e-\[Phi])tj[{a,\[Alpha]},{b,\[Beta]},{c,-\[Gamma]}]tj[{d,\[Delta]},{e,\[Epsilon]},{f,-\[Phi]}],\[Alpha],\[Beta],\[Gamma]]
];
addTest[toCG[toTJ[sum[cg[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]cg[{d,\[Delta]},{e,\[Epsilon]},{f,\[Phi]}],\[Alpha],\[Beta],\[Gamma]]]],
	sum[cg[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]cg[{d,\[Delta]},{e,\[Epsilon]},{f,\[Phi]}],\[Alpha],\[Beta],\[Gamma]]
];

declareQNInteger[{Hidden`t[a,b],Hidden`tp[a,b],Hidden`t[a,b,c,d]}];
declareQNHalfInteger/@{Hidden`t[a],Hidden`tp[a],Hidden`t[a,b,c]};

addTest[MemberQ[AngularMomentum`Private`$integerQN,Hidden`t[a,b]],True];
addTest[MemberQ[AngularMomentum`Private`$integerQN,Hidden`tp[a,b]],True];
addTest[MemberQ[AngularMomentum`Private`$integerQN,Hidden`t[a,b,c,d]],True];
addTest[MemberQ[AngularMomentum`Private`$halfintegerQN,Hidden`t[a,b]],False];
addTest[MemberQ[AngularMomentum`Private`$halfintegerQN,Hidden`tp[a,b]],False];
addTest[MemberQ[AngularMomentum`Private`$halfintegerQN,Hidden`t[a,b,c,d]],False];
addTest[MemberQ[AngularMomentum`Private`$integerQN,Hidden`t[a]],False];
addTest[MemberQ[AngularMomentum`Private`$integerQN,Hidden`tp[a]],False];
addTest[MemberQ[AngularMomentum`Private`$integerQN,Hidden`t[a,b,c]],False];
addTest[MemberQ[AngularMomentum`Private`$halfintegerQN,Hidden`t[a]],True];
addTest[MemberQ[AngularMomentum`Private`$halfintegerQN,Hidden`tp[a]],True];
addTest[MemberQ[AngularMomentum`Private`$halfintegerQN,Hidden`t[a,b,c]],True];

(*testExpr[1]=sum[(-1)^\[Mu] (2 \[Mu]+1)sj[{a,b,\[Mu]},{c,d,t}]sj[{c,d,\[Mu]},{b,a,tp}],\[Mu],t];
testExpr[2]=sum[(-1)^\[Mu] (2u+1)(2 \[Mu]+1)sj[{a,b,\[Mu]},{a,b,u}]sj[{a,b,\[Mu]},{b,a,up}],\[Mu],u];
testExpr[3]=sum[cg[{a,\[Alpha]},{b,\[Beta]},{m,\[Mu]}]cg[{a,\[Alpha]},{b,\[Beta]},{mp,\[Mu]p}],\[Alpha],\[Beta]];
testExpr[4]=sum[cg[{a,\[Alpha]},{b,\[Beta]},{m,\[Mu]}]cg[{a,\[Alpha]p},{b,\[Beta]p},{m,\[Mu]}],m,\[Mu]];
*)
(*testExpr[5]=sum[cg[{1/2,mt[a]},{1/2,mt[b]},{t[a,b],mt[a,b]}] cg[{1/2,mtp[a]},{1/2,mtp[b]},{tp[a,b],mtp[a,b]}] cg[{t[a,b],mt[a,b]},{1/2,mt[c]},{t[a,b,c],mt[a,b,c]}] cg[{tp[a,b],mtp[a,b]},{1/2,mtp[c]},{tp[a,b,c],mtp[a,b,c]}] KroneckerDelta[mt[c],mtp[c]] sum[3 cg[{1/2,mt[b]},{1,\[Mu]},{1/2,mtp[b]}] cg[{1/2,mtp[a]},{1,\[Mu]},{1/2,mt[a]}],\[Mu]],mt[a],mt[b],mt[c],mt[a,b],mtp[a],mtp[b],mtp[c],mtp[a,b]];
testExpr[6]=sum[cg[{1/2,mt[a]},{1/2,mt[b]},{t[a,b],mt[a,b]}] cg[{1/2,mtp[a]},{1/2,mtp[b]},{tp[a,b],mtp[a,b]}] cg[{t[a,b],mt[a,b]},{1/2,mt[c]},{t[a,b,c],mt[a,b,c]}] cg[{tp[a,b],mtp[a,b]},{1/2,mtp[c]},{tp[a,b,c],mtp[a,b,c]}] KroneckerDelta[mt[a],mtp[a]] sum[3 cg[{1/2,mt[c]},{1,\[Mu]},{1/2,mtp[c]}] cg[{1/2,mtp[b]},{1,\[Mu]},{1/2,mt[b]}],\[Mu]],mt[a],mt[b],mt[c],mt[a,b],mtp[a],mtp[b],mtp[c],mtp[a,b]];
*)
(*declareQNHalfInteger[{mt[a],mt[b],mt[c],mtp[a],mtp[b],mtp[c],t[a,b,c],mt[a,b,c],tp[a,b,c],mtp[a,b,c]}];*)
(*declareQNInteger[{t,tp,t[a,b],mt[a,b],tp[a,b],mtp[a,b]}];*)
declareIndexedAM[t]
declarePrimed[{m,\[Mu],\[Alpha],\[Beta]}];
declareQNInteger[{a,ap,\[Alpha],\[Alpha]p,b,bp,\[Beta],\[Beta]p,c,cp,\[Gamma],,\[Gamma]p,d,dp,\[Delta],e,f,g,h,j,k,l,m,n,o,p,\[Psi],q,\[Kappa],r,\[Rho],s,\[Sigma],t,tp,\[Tau],m,\[Mu],mp,\[Mu]p,u,up,v,w,x,xp,y}];



beginTestModule["Varshalovich"];
testEqn[1][exp]=sum[(-1)^(a-\[Alpha])tj[{a,\[Alpha]},{a,-\[Alpha]},{c,\[Gamma]}],\[Alpha]];
testEqn[1][res]=Sqrt[2 a +1] KroneckerDelta[c,0] KroneckerDelta[\[Gamma],0];
testEqn[2][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa])tj[{a,-\[Alpha]},{p,\[Psi]},{q,\[Kappa]}]tj[{p,-\[Psi]},{q,-\[Kappa]},{ap,\[Alpha]p}],\[Psi],\[Kappa]];
testEqn[2][res]=(-1)^(ap+\[Alpha]p)1/(2 ap +1) conTri[ap,p,q] KroneckerDelta[a,ap] KroneckerDelta[\[Alpha],\[Alpha]p];
testEqn[3][exp]=sum[(-1)^(q-\[Kappa])(2 q +1)tj[{a,-\[Alpha]},{b,-\[Beta]},{q,\[Kappa]}]tj[{q,-\[Kappa]},{a,\[Alpha]p},{b,\[Beta]p}],q,\[Kappa]];
testEqn[3][res]=(-1)^(a+\[Alpha]p+b+\[Beta]p) KroneckerDelta[\[Alpha],\[Alpha]p] KroneckerDelta[\[Beta],\[Beta]p];
testEqn[4][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho])tj[{p,\[Psi]},{a,\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{b,\[Beta]},{r,-\[Rho]}]tj[{r,\[Rho]},{c,\[Gamma]},{p,-\[Psi]}],\[Kappa],\[Psi],\[Rho]];
testEqn[4][res]=(-1)^(a+b+c)tj[{a,-\[Alpha]},{c,-\[Gamma]},{b,-\[Beta]}] sj[{a,b,c},{r,p,q}];
testEqn[5][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho]+s-\[Sigma]+t-\[Tau])tj[{p,\[Psi]},{a,-\[Alpha]},{q,\[Kappa]}]tj[{q,-\[Kappa]},{r,\[Rho]},{t,\[Tau]}]tj[{r,-\[Rho]},{ap,\[Alpha]p},{s,\[Sigma]}]tj[{s,-\[Sigma]},{p,-\[Psi]},{t,-\[Tau]}],\[Psi],\[Kappa],\[Rho],\[Sigma],\[Tau]];
testEqn[5][res]=(-1)^(a+\[Alpha])/(2a+1)sj[{a,p,q},{t,r,s}]KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],\[Alpha]p];
testEqn[6][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho]+s-\[Sigma])tj[{p,\[Psi]},{a,\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{b,\[Beta]},{r,-\[Rho]}]tj[{r,\[Rho]},{s,\[Sigma]},{p,-\[Psi]}]tj[{s,-\[Sigma]},{c,\[Gamma]},{d,\[Delta]}],\[Psi],\[Kappa],\[Rho],\[Sigma]];
testEqn[6][res]=sum[(-1)^(a+b+c+d+s+\[Sigma])sj[{a,b,s},{r,p,q}]tj[{a,-\[Alpha]},{s,-\[Sigma]},{b,-\[Beta]}]tj[{s,\[Sigma]},{c,-\[Gamma]},{d,-\[Delta]}],set[\[Sigma]]];
testEqn[7][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho]+s-\[Sigma])tj[{p,\[Psi]},{a,\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{b,\[Beta]},{r,-\[Rho]}]tj[{r,\[Rho]},{c,\[Gamma]},{s,-\[Sigma]}]tj[{s,\[Sigma]},{d,\[Delta]},{p,-\[Psi]}],\[Psi],\[Kappa],\[Rho],\[Sigma]];
(*testEqn[7][res]=sum[(-1)^(s+a+d+q+AngularMomentum`Private`varK[1]+AngularMomentum`Private`varK[2])(2 AngularMomentum`Private`varK[1]+1)sj[{a,AngularMomentum`Private`varK[1],d},{s,p,q}]sj[{b,AngularMomentum`Private`varK[1],c},{s,r,q}]sj[{a,\[Alpha]},{AngularMomentum`Private`varK[1],-AngularMomentum`Private`varK[2]},{d,\[Delta]}]tj[{b,\[Beta]},{AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]},{c,\[Gamma]}],set[AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]]];*)
testEqn[7][res]=sum[(-1)^(r+c+d+p+AngularMomentum`Private`varK[1]+AngularMomentum`Private`varK[2])(2 AngularMomentum`Private`varK[1]+1)sj[{a,b,AngularMomentum`Private`varK[1]},{r,p,q}]sj[{c,d,AngularMomentum`Private`varK[1]},{p,r,s}]tj[{a,\[Alpha]},{AngularMomentum`Private`varK[1],-AngularMomentum`Private`varK[2]},{b,\[Beta]}]tj[{d,\[Delta]},{AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]},{c,\[Gamma]}],set[AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]]];

(*6j symbols *)
testEqn[8][exp]=sum[(2x+1)sj[{a,b,x},{a,b,c}],x];
testEqn[8][res]= conTri[a,b,c];
testEqn[9][exp]=sum[(-1)^(a+b+x)(2x+1)sj[{a,b,x},{b,a,c}],x];
testEqn[9][res]=Sqrt[2a+1]Sqrt[2b+1]KroneckerDelta[c,0];
testEqn[10][exp]=sum[(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{a,b,q}],x];
testEqn[10][res]=1/(2p+1)KroneckerDelta[p,q] conTri[a,d,p]conTri[b,c,p];
testEqn[11][exp]=sum[(-1)^(p+q+x)(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{b,a,q}],x];
testEqn[11][res]=sj[{a,c,q},{b,d,p}];
testEqn[12][exp]=sum[(-1)^(a+b+c+d+e+f+p+q+r+x)(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{b,a,r}],x];
testEqn[12][res]=sj[{a,d,p},{q,r,e}]sj[{b,c,p},{q,r,f}];
testEqn[13][exp]=sum[(-1)^(2x)(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{a,b,r}],x];
testEqn[13][res]=nj[{a,r,f},{p,b,c},{d,e,q}];


addFn=(addTest[simplifyAMSum[#1,Print->False],#2]&)@@({testEqn[#][exp],testEqn[#][res]})&;
addFn/@Table[i,{i,13}];

endTestModule[];


runTests[msgSuccess->None];


(* ::Subsection:: *)
(*Should yield error messages*)


declarePrimed[u];
declareQNHalfInteger[{a,b,c,d,\[Alpha],\[Beta],\[Gamma]}];
declareQNInteger[{u,up,\[Mu],\[Xi],t,tp}];
Print["should yield an undeclared symbol (consistencyCheck::notfound) error"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{X,\[Xi]}]//consistencyCheck;
Print["should yield an error due to unfulfilled triangular condition for {a,b,c} and {\[Alpha],\[Beta],\[Beta]}"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Beta]}]//consistencyCheck;
Print["should yield an error as {b,\[Mu]} and {u,\[Beta]} do not match"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Mu]},{u,\[Beta]}]//consistencyCheck;
Print["should complain about conditions that cannot be fulfilled. The reason are undefined symbols (axx,bxx,\[Alpha]xx,\[Beta]xx)"];
AngularMomentum`Private`cleanupNewVariables[
	tj[{axx,\[Alpha]xx},{bxx,\[Beta]xx},{var[1],var[2]}]//.var[i_]:> AngularMomentum`Private`var[i]
];


(* ::Subsection:: *)
(*TraditionalForm Output*)


tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]
%//TraditionalForm
cg[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]
%//TraditionalForm
sj[{a,b,c},{d,e,f}]
%//TraditionalForm
nj[{a,b,c},{d,e,f},{g,h,i}]
%//TraditionalForm
nj[{a,b,c},{d,sh[l,m,\[Theta],\[Phi]],f},{g,h,i}]
%//TraditionalForm
conTri[a,b,c]
%//TraditionalForm
conZero[\[Alpha],\[Beta],-\[Gamma]]
%//TraditionalForm
AngularMomentum`Private`varK[3]
%//TraditionalForm


(* ::Subsection:: *)
(*misc*)


simplifyAMSum[sum[(2x+1)nj[{a,f,x},{d,q,e},{p,c,b}]sj[{a,f,x},{e,b,s}],x],Print->False]//TraditionalForm
simplifyAMSum[sum[(-1)^x(2x+1)nj[{a,f,x},{d,q,e},{p,c,b}]sj[{a,f,x},{b,e,s}],x],Print->False]//TraditionalForm
simplifyAMSum[sum[(-1)^x(2x+1)nj[{d,q,e},{a,f,x},{p,c,b}]sj[{a,f,x},{e,b,s}],x],Print->False]//TraditionalForm
simplifyAMSum[sum[(2 x+1)(2 y+1) nj[{a,b,x},{c,d,y},{e,f,j}]nj[{a,b,x},{c,d,y},{g,h,j}],x,y],Print->False]//TraditionalForm
simplifyAMSum[sum[(-1)^(y)(2x+1)(2y+1)nj[{a,b,x},{c,d,y},{e,f,j}]nj[{a,b,x},{c,d,y},{g,h,j}],x,y],Print->False]//TraditionalForm
simplifyAMSum[sum[(-1)^(y)(2x+1)(2y+1)nj[{a,b,x},{c,d,y},{p,q,r}]sj[{x,y,r},{j,h,g}]sj[{a,b,x},{h,g,e}]sj[{c,d,y},{j,g,f}],x,y],Print->False]//TraditionalForm


declareIndexedAM[t]
declarePrimed[{m,\[Mu],\[Alpha],\[Beta]}];
declareQNInteger[{a,ap,\[Alpha],\[Alpha]p,b,bp,\[Beta],\[Beta]p,c,cp,\[Gamma],,\[Gamma]p,d,dp,\[Delta],e,f,g,h,j,k,l,m,n,o,p,\[Psi],q,\[Kappa],r,\[Rho],s,\[Sigma],t,tp,\[Tau],m,\[Mu],mp,\[Mu]p,u,up,v,w,x,xp,y}];
simplifyAMSum[sum[(-1)^(p+q-e-f)(2 x+1)nj[{a,b,p},{c,d,q},{e,f,x}]sj[{p,q,x},{k,l,g}]sj[{e,f,x},{k,l,h}],x],OnlySums->{x},Print->True]//TraditionalForm


declareIndexed[{l,m}];
(res[0]=integrate[sh[l[1],m[1],\[Theta],\[Phi]]sh[l[2],m[2],\[Theta],\[Phi]]sh[l[3],m[3],\[Theta],\[Phi]]sh[l[4],m[4],\[Theta],\[Phi]]Sin[\[Theta]],set[\[Phi],\[Theta],x]])//TraditionalForm
i=1;(res[i]=simplifySHIntegral[res[i-1],Integrate->True])//TraditionalForm
i=2;res[i-1]//toTJ//TraditionalForm


declareIndexedAM[{k,x,v,z,l}];
declareQNInteger[{k,kp,v,mk[1],mkp[1],mk[2],mkp[2],mv,x,xp,mx,mxp,l,lp,ml,mlp,z,mz}];
expr[0]=sum[(-1)^(x+xp+mx+mxp+mv+mz+ml+mlp+l+lp)tj[{k,mk[1]},{kp,mkp[1]},{v,-mv}]tj[{x,-mx},{xp,-mxp},{v,mv}]
tj[{l-k,mk[2]},{lp-kp,mkp[2]},{z,-mz}]tj[{x,mx},{xp,mxp},{z,mz}]
tj[{k,mk[1]},{l-k,mk[2]},{l,-ml}]tj[{kp,mkp[1]},{lp-kp,mkp[2]},{lp,-mlp}]
,set[mk[1],mkp[1],mk[2],mkp[2],mx,mxp,mz,mv]];

expr[0]//TraditionalForm
(expr[1]=simplifyAMSum[expr[0],OnlySums->{mx,mxp},Print->False])//TraditionalForm
(expr[2]=simplifyAMSum[expr[1],OnlySums->{mk[1],mkp[1],mkp[2],mk[2]},Print->False])//TraditionalForm
(expr[3]=simplifyAMSum[expr[2],OnlySums->{AngularMomentum`Private`varK[2],mz},Print->False])//TraditionalForm
simplifyAMSum[expr[3],Print->False]//TraditionalForm


(*
testExpr[5]//TraditionalForm
SetOptions[simplifyAMSum,Print-> True,TimingComplete->False];
testExpr[5]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False,TimingComplete->False];
*)


(*
testExpr[6]//TraditionalForm
SetOptions[simplifyAMSum,Print-> True,TimingComplete->False];
testExpr[6]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False,TimingComplete->False];
*)


(*
$ContextPath=DeleteDuplicates@Append[$ContextPath,"AngularMomentum`Private`"];
$halfintegerQN
$integerQN
$ContextPath=DeleteCases[$ContextPath,"AngularMomentum`Private`"];
declareQNHalfInteger[{p,\[Psi],s,\[Sigma],a,ap,\[Alpha],\[Alpha]p}];
declareQNInteger[{q,\[Kappa],t,\[Tau],r,\[Rho]}];
testSpeed[1]=sum[(-1)^(\[Psi]+\[Kappa]+\[Rho]+\[Sigma]+\[Tau])tj[{p,-\[Psi]},{a,-\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{r,-\[Rho]},{t,-\[Tau]}]tj[{r,\[Rho]},{ap,\[Alpha]p},{s,-\[Sigma]}]tj[{s,\[Sigma]},{p,\[Psi]},{t,\[Tau]}],\[Psi],\[Kappa],\[Rho],\[Sigma],\[Tau]];
SetOptions[simplifyAMSum,Print-> True];
testSpeed[1]//TraditionalForm
testSpeed[1]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False];
*)


(*
declareQNHalfInteger[{a,\[Alpha]}];
declareQNInteger[{m,\[Mu]}];
SetOptions[simplifyAMSum,Print-> True];
sum[f[\[Beta]](-1)^(\[Alpha]) tj[{a,-\[Alpha]},{m,\[Mu]},{a,\[Alpha]}],\[Alpha],\[Beta]]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False];
*)


(*
declareIndexedAM[t]
declareIndexed[{\[Mu],k}]
declareQNHalfInteger[{mt[a],mt[b],mt[c],mtp[a],mtp[b],mtp[c],t[a,b,c],mt[a,b,c],tp[a,b,c],mtp[a,b,c]}];
declareQNInteger[{\[Mu][1,3],\[Mu][2,4],k[1],k[2],t,tp,t[a,b],mt[a,b],tp[a,b],mtp[a,b]}];
texpr=sum[(-1)^(k[2]+mtp[a,b]+mtp[c])
tj[{t[a,b],mt[a,b]},{1/2,mt[c]},{t[a,b,c],-mt[a,b,c]}]
tj[{1/2,mt[c]},{1,\[Mu][1,3]},{1/2,-mtp[c]}]
tj[{tp[a,b],mtp[a,b]},{1/2,mtp[c]},{tp[a,b,c],mtp[a,b,c]}]
tj[{1,\[Mu][2,4]},{k[1],-k[2]},{t[a,b],mt[a,b]}]
tj[{tp[a,b],-mtp[a,b]},{k[1],k[2]},{1,\[Mu][1,3]}],
set[mt[c],mt[a,b],mtp[c],mtp[a,b],k[2]]];
texpr//TraditionalForm
AngularMomentum`Private`prepare3jmSign[texpr//.AngularMomentum`Private`simplifyFactorRules]//TraditionalForm
*)
