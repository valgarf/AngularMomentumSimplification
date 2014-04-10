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
testExpr[5]=sum[cg[{1/2,mt[a]},{1/2,mt[b]},{t[a,b],mt[a,b]}] cg[{1/2,mtp[a]},{1/2,mtp[b]},{tp[a,b],mtp[a,b]}] cg[{t[a,b],mt[a,b]},{1/2,mt[c]},{t[a,b,c],mt[a,b,c]}] cg[{tp[a,b],mtp[a,b]},{1/2,mtp[c]},{tp[a,b,c],mtp[a,b,c]}] KroneckerDelta[mt[c],mtp[c]] sum[3 cg[{1/2,mt[b]},{1,\[Mu]},{1/2,mtp[b]}] cg[{1/2,mtp[a]},{1,\[Mu]},{1/2,mt[a]}],\[Mu]],mt[a],mt[b],mt[c],mt[a,b],mtp[a],mtp[b],mtp[c],mtp[a,b]];
testExpr[6]=sum[cg[{1/2,mt[a]},{1/2,mt[b]},{t[a,b],mt[a,b]}] cg[{1/2,mtp[a]},{1/2,mtp[b]},{tp[a,b],mtp[a,b]}] cg[{t[a,b],mt[a,b]},{1/2,mt[c]},{t[a,b,c],mt[a,b,c]}] cg[{tp[a,b],mtp[a,b]},{1/2,mtp[c]},{tp[a,b,c],mtp[a,b,c]}] KroneckerDelta[mt[a],mtp[a]] sum[3 cg[{1/2,mt[c]},{1,\[Mu]},{1/2,mtp[c]}] cg[{1/2,mtp[b]},{1,\[Mu]},{1/2,mt[b]}],\[Mu]],mt[a],mt[b],mt[c],mt[a,b],mtp[a],mtp[b],mtp[c],mtp[a,b]];
declareIndexedAM[t]
declarePrimed[{m,\[Mu],\[Alpha],\[Beta]}];
declareQNHalfInteger[{a,\[Alpha],\[Alpha]p,b,\[Beta],\[Beta]p,mt[a],mt[b],mt[c],mtp[a],mtp[b],mtp[c],t[a,b,c],mt[a,b,c],tp[a,b,c],mtp[a,b,c]}];
declareQNInteger[{d,c,\[Gamma],m,\[Mu],mp,\[Mu]p,u,up,t,tp,t[a,b],mt[a,b],tp[a,b],mtp[a,b]}];

(*
addTest[simplifyAMSum[testExpr[1],Print->False],
	sum[(-1)^(t+tp) sj[{a,c,tp},{b,d,t}],set[t]]
];
addTest[simplifyAMSum[testExpr[2],Print->False],
	(-1)^(a+b) Sqrt[2a+1] Sqrt[2b+1] KroneckerDelta[0,up]
];

addTest[simplifyAMSum[testExpr[3],Print->False],
	KroneckerDelta[\[Mu],\[Mu]p]KroneckerDelta[m,mp]
];

addTest[simplifyAMSum[testExpr[4],Print->False],
	KroneckerDelta[\[Alpha],\[Alpha]p]KroneckerDelta[\[Beta],\[Beta]p]
];*)


beginTestModule["Varshalovich"];
testEqn[1][exp]=sum[(-1)^(a-\[Alpha])tj[{a,\[Alpha]},{a,-\[Alpha]},{c,\[Gamma]}],\[Alpha]];
testEqn[1][res]=Sqrt[2 a +1] KroneckerDelta[c,0] KroneckerDelta[\[Gamma],0];

addFn=addTest[simplifyAMSum[testEqn[#][exp],Print->False],testEqn[#][res]]&;
addFn/@Table[i,{i,1}];

endTestModule[];


runTests[];


(* ::Subsection:: *)
(*Should yield error messages*)


declarePrimed[u]
declareQNHalfInteger[{a,b,c,d,\[Alpha],\[Beta],\[Gamma]}];
declareQNInteger[{u,up,\[Mu],\[Xi],t,tp}];
Print["should yield an undeclared symbol (consistencyCheck::notfound) error"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{X,\[Xi]}]//consistencyCheck
Print["should yield an error due to unfulfilled triangular condition for {a,b,c} and {\[Alpha],\[Beta],\[Beta]}"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Beta]}]//consistencyCheck
Print["should yield an error as {b,\[Mu]} and {u,\[Beta]} do not match"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Mu]},{u,\[Beta]}]//consistencyCheck


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


(* ::Subsection:: *)
(*misc*)


testExpr[4]//TraditionalForm
SetOptions[simplifyAMSum,Print-> True];
testExpr[4]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False];


testExpr[5]//TraditionalForm
SetOptions[simplifyAMSum,Print-> True,TimingComplete->False];
testExpr[5]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False,TimingComplete->False];




testExpr[6]//TraditionalForm
SetOptions[simplifyAMSum,Print-> True,TimingComplete->False];
testExpr[6]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False,TimingComplete->False];


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



declareQNHalfInteger[{a,\[Alpha]}];
declareQNInteger[{m,\[Mu]}];
SetOptions[simplifyAMSum,Print-> True];
sum[f[\[Beta]](-1)^(\[Alpha]) tj[{a,-\[Alpha]},{m,\[Mu]},{a,\[Alpha]}],\[Alpha],\[Beta]]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False];



