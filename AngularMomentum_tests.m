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

testExpr[1]=sum[(-1)^\[Mu] (2 \[Mu]+1)sj[{a,b,\[Mu]},{c,d,t}]sj[{c,d,\[Mu]},{b,a,tp}],\[Mu],t];
testExpr[2]=sum[(-1)^\[Mu] (2u+1)(2 \[Mu]+1)sj[{a,b,\[Mu]},{a,b,u}]sj[{a,b,\[Mu]},{b,a,up}],\[Mu],u];
declareQNHalfInteger[{a,b,c,d}];
declareQNInteger[{u,up,\[Mu],t,tp}];

addTest[simplifyAMSum[testExpr[1],Print->False],
	sum[(-1)^(t+tp) sj[{a,c,tp},{b,d,t}],set[t]]
];
addTest[simplifyAMSum[testExpr[2],Print->False],
	(-1)^(a+b) Sqrt[2a+1] Sqrt[2b+1] KroneckerDelta[0,up]
];


runTests[];


(* ::Subsection:: *)
(*Should yield error messages*)


declarePrimed[u]
declareQNHalfInteger[{a,b,c,d,\[Alpha],\[Beta]}];
declareQNInteger[{u,up,\[Mu],\[Gamma],t,tp}];
Print["should yield an undeclared symbol (consistencyCheck::notfound) error"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{X,\[Gamma]}]//consistencyCheck
Print["should yield an error due to unfulfilled triangular condition for {a,b,c} and {\[Alpha],\[Beta],\[Beta]}"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Beta]}]//consistencyCheck
Print["should yield an error as {b,\[Gamma]} and {u,\[Beta]} do not match"];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Gamma]},{u,\[Beta]}]//consistencyCheck


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


declareIndexedAM[t]
declareQNInteger[{t[a,b],mt[a,b],tp[a,b],mtp[a,b],\[Mu]}];
declareQNHalfInteger[{mt[a],mt[b],mt[c],mtp[a],mtp[b],mtp[c],t[a,b,c],mt[a,b,c],tp[a,b,c],mtp[a,b,c]}];
testExpr=sum[cg[{1/2,mt[a]},{1/2,mt[b]},{t[a,b],mt[a,b]}] cg[{1/2,mtp[a]},{1/2,mtp[b]},{tp[a,b],mtp[a,b]}] cg[{t[a,b],mt[a,b]},{1/2,mt[c]},{t[a,b,c],mt[a,b,c]}] cg[{tp[a,b],mtp[a,b]},{1/2,mtp[c]},{tp[a,b,c],mtp[a,b,c]}] KroneckerDelta[mt[c],mtp[c]] sum[3 cg[{1/2,mt[b]},{1,\[Mu]},{1/2,mtp[b]}] cg[{1/2,mtp[a]},{1,\[Mu]},{1/2,mt[a]}],\[Mu]],mt[a],mt[b],mt[c],mt[a,b],mtp[a],mtp[b],mtp[c],mtp[a,b]]//toTJ//simplifyAMSum;
testExpr//TraditionalForm
testExpr//AngularMomentum`Private`prepare3jmSign//TraditionalForm
((testExpr//.AngularMomentum`Private`prepareSymbolOrderlessRules)//
		AngularMomentum`Private`prepare3jmSign)//.
		AngularMomentum`Private`cleanupSymbolOrderlessRules//TraditionalForm
		



declarePrimed[{m,\[Mu]}];
declareQNInteger[{m,\[Mu],mp,\[Mu]p}];
declareQNHalfInteger[{a,\[Alpha],b,\[Beta]}];
testExpr[3]=sum[cg[{a,\[Alpha]},{b,\[Beta]},{m,\[Mu]}]cg[{a,\[Alpha]},{b,\[Beta]},{mp,\[Mu]p}],\[Alpha],\[Beta]];
testExpr[3]//TraditionalForm
SetOptions[simplifyAMSum,Print-> True];
testExpr[3]//simplifyAMSum//TraditionalForm
SetOptions[simplifyAMSum,Print-> False];


transFunc[0][expr_]:=(expr*mX[\[Alpha]]*mX[\[Beta]]*mX[\[Gamma]]//.AngularMomentum`Private`simplifyFactorRules);
transFunc[1][expr_]:=(expr*mX[\[Alpha]]*mX[\[Beta]]*mX[\[Xi]]//.AngularMomentum`Private`simplifyFactorRules);
compFunc[expr_]:=10 Count[expr,x_/;MemberQ[{mX[\[Alpha]],mX[\[Beta]],mX[\[Gamma]]},x],{0,Infinity}];
Simplify[mX[\[Alpha]]mX[\[Beta]],TransformationFunctions->{transFunc[0],transFunc[1]},ComplexityFunction->compFunc]
mX[\[Alpha]]mX[\[Beta]]transFunc[0]



