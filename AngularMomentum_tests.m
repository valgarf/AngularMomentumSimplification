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





trans[0]=#//.{
		(-1)^(a_):>mX[a],
		mX[n_. a_+ b_]:> mX[a]^n mX[b],
		mX[-a_]^n_:> mX[a]^(-n),
		mX[a_]^n_:> mX[a]^Mod[n,4]/; (n>= 4||n<0) && MemberQ[AngularMomentum`Private`$halfintegerQN,a],
		mX[a_]^n_:> mX[a]^Mod[n,2]/; n!=0 && n!=1 &&MemberQ[AngularMomentum`Private`$integerQN,a],
		mX[a_]^n_:> -mX[a]^Mod[n,2]/; 2<=n<4 && MemberQ[AngularMomentum`Private`$halfintegerQN,a],
		mX[a_]^0:> 1,
		mX[1]->(-1),
		mX[-1]->(-1),
		mX[1/2]->(I),
		mX[-1/2]->(-I)		
	}&;
trans[2]=#//.{
		sum[a_,b___]:> sum[a,set[b]] /;FreeQ[{b},set]
		(*sum[,set[\[Psi]_,\[Kappa]_,summation___]*)
	}&;
trans[3]=#/.{triX[a_,b_,c_]:> 2 v[a,b,c]}&;
trans[1]=#//.{
		mX[a_]:>(-1)^a,
		-(-1)^a_:> (-1)^(a+1),
		I (-1)^a_:> (-1)^(a+1/2)
	}&;

transTJ[tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]]:= tj[{c,\[Gamma]},{a,\[Alpha]},{b,\[Beta]}];
declareQNHalfInteger/@{a,c};
declareQNInteger/@{b,d};
trans[1]@trans[0][(-1)^(3a+5b+4c+d)]
Simplify[(-1)^(3a+5b+4c+d) u[a,b,c],TransformationFunctions->{trans[0],trans[1]}]
Simplify[-mX[a] mX[b] mX[d] u[a,b,c],
	TransformationFunctions->{trans[0],trans[1],trans[3],trans[2]},
	ComplexityFunction->(Count[#,(-1)^n_.,{0,Infinity}] - 1 Count[#,triX[___],{0,Infinity}] - 2 Count[#,v[___],{0,Infinity}] &)
]

Simplify[b tj[{2,2},{3,3},{1,1}],
	TransformationFunctions->{transTJ},
	ComplexityFunction->((#//.(m_ tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:>\[Gamma])) /.a_:> 10/;a\[NotElement]Integers&)
]


g[a]h[-a]/.g[-u_]h[u_]:>X


(-1)^(b_-a_)/.-a_:> ua_


test[Signature[{a,c,b}],set[a,c,b]]/.test[Signature[{a,b,c}],set[a,b,c]]:> X


sum[(-1)^(-\[Psi]-\[Kappa])tj[{a,\[Alpha]},{p,\[Psi]},{q,\[Kappa]}]tj[{ap,\[Alpha]p},{p,-\[Psi]},{q,-\[Kappa]}],\[Psi],\[Kappa]]//.AngularMomentum`Private`prepareSymbolsOrderless
rule=(sum[(-1)^(-\[Psi]_-\[Kappa]_)tj[{a_,\[Alpha]_},{q_,\[Psi]_},{p_,\[Kappa]_}]tj[{ap_,\[Alpha]p_},{q_,-\[Psi]_},{p_,-\[Kappa]_}],\[Psi]_,\[Kappa]_]:> X//.AngularMomentum`Private`prepareSymbolsOrderless)



