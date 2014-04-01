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
sum[cg[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]cg[{d,\[Delta]},{e,\[Epsilon]},{f,\[Phi]}],\[Alpha],\[Beta],\[Gamma]]];
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





(*transTJ[tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]]:= tj[{c,\[Gamma]},{a,\[Alpha]},{b,\[Beta]}];
declareQNHalfInteger/@{a,c};
declareQNInteger/@{b,d};
trans[1]@trans[0][(-1)^(3a+5b+4c+d)]
Simplify[(-1)^(3a+5b+4c+d) u[a,b,c],TransformationFunctions->{trans[0],trans[1]}]
Simplify[-mX[a] mX[b] mX[d] u[a,b,c],
	TransformationFunctions->{trans[0],trans[1],trans[3],trans[2]},
	ComplexityFunction->(Count[#,(-1)^n_.,{0,Infinity}] - 1 Count[#,triX[___],{0,Infinity}] - 2 Count[#,v[___],{0,Infinity}] &)
]*)


declareQNHalfInteger[{a,b}];
declareQNInteger[{t,tp,\[Mu]}];
testExpr[1]=sum[(-1)^\[Mu] (2 \[Mu]+1)sj[{a,b,\[Mu]},{c,d,t}]sj[{c,d,\[Mu]},{b,a,tp}],\[Mu],t];
testExpr[2]=sum[(-1)^\[Mu] (2t+1)(2 \[Mu]+1)sj[{a,b,\[Mu]},{a,b,t}]sj[{a,b,\[Mu]},{b,a,tp}],\[Mu],t];
testExpr[1]//TraditionalForm
testExpr[1]//simplifyAMSums//TraditionalForm
testExpr[2]//TraditionalForm
testExpr[2]//simplifyAMSums//TraditionalForm
AngularMomentum`Private`$integerQN
AngularMomentum`Private`$halfintegerQN



