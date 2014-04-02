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
declareQNHalfInteger[{a,b,c,d,t,tp}];
declareQNInteger[{u,up,\[Mu]}];

addTest[simplifyAMSums[testExpr[1],Print->False],
	sum[(-1)^(t+tp) sj[{a,c,tp},{b,d,t}],t]
];
addTest[simplifyAMSums[testExpr[2],Print->False],
	(-1)^(a+b) Sqrt[2a+1] Sqrt[2b+1] KroneckerDelta[0,up]
];


runTests[];


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





declarePrimed[u]
declareQNHalfInteger[{a,b,c,d,t,tp,\[Alpha],\[Beta]}];
declareQNInteger[{u,up,\[Mu],\[Gamma]}];
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{u,\[Gamma]}]//extractConditions//TraditionalForm
testExpr[2]*tj[{a,\[Alpha]},{b,\[Beta]},{u,\[Gamma]}]//consistencyCheck


conX@@@Map[rs,{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}},{2}]


Or@@(MemberQ[#,u] && MemberQ[#,\[Gamma]]&)/@{AngularMomentum`Private`$integerQN,AngularMomentum`Private`$halfintegerQN}


Drop[Flatten@Position[{1,1,1,1,1/2+\[Beta],f},x_/;!EvenQ[2*x],{1}],1]
