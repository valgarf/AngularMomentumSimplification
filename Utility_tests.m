(* ::Package:: *)

ClearAll[Evaluate[Context[]<>"*"]];
$Path=DeleteDuplicates@Append[$Path,NotebookDirectory[]];
<<UnitTesting`
<<Utility`


(* ::Subsection:: *)
(*Unit Tests*)


initialiseTests[];


beginTestModule["Utility Tests"];
addTest[FreeQAll[f[g[a]]*b*Exp[c],{u,v,w}],True];
addTest[FreeQAll[f[g[a]]*b*Exp[c],{u,v,g,w}],False];
addTest[FreeQAll[f[g[a]]*b*Exp[c],{u,v,-b,w}],True];
addTest[FreeQAllUnsigned[f[g[a]]*b*Exp[c],{u,v,-b,w}],False];
addTest[FreeQAllUnsigned[f[g[a]]*b*Exp[c],{u,v,-w}],True];
addTest[FreeQNone[f[g[a]]*b*Exp[c],{f,a,w}],False];
addTest[FreeQNone[f[g[a]]*b*Exp[c],{f,a,c}],True];
addTest[FreeQNone[f[g[a]]*b*Exp[c],{f,-a,c}],False];
addTest[FreeQNoneUnsigned[f[g[a]]*b*Exp[c],{f,-a,c}],True];
addTest[FreeQNoneUnsigned[f[g[a]]*b*Exp[c],{f,-a,c,-w}],False];
addTest[EvenPermutations[{1,2,3}],{{1,2,3},{2,3,1},{3,1,2}}];
addTest[OddPermutations[{1,2,3}],{{1,3,2},{2,1,3},{3,2,1}}];
addTest[EvenPermutations[{b,a}],{{b,a}}];
addTest[OddPermutations[{b,a}],{{a,b}}];
addTest[alternative[a,b]*c,alternative[a c,b c],equivalenceFunction-> (HoldForm[#1===#2]&)];
addTest[alternative[f[a],g[b]]*alternative[u,v],alternative[f[a]u,f[a]v,g[b]u,g[b]v],equivalenceFunction-> (HoldForm[#1===#2]&)];
addTest[alternative[f[a],g[b]]-alternative[u,v],alternative[f[a]-u,f[a]-v,g[b]-u,g[b]-v],equivalenceFunction-> (HoldForm[#1===#2]&)];
addTest[sum[alternative[a,b],c,d],alternative[sum[a,c,d],sum[b,c,d]],equivalenceFunction-> (HoldForm[#1===#2]&)];
addTest[f[alternative[a,b],c,d],alternative[f[a,c,d],f[b,c,d]],equivalenceFunction-> (HoldForm[#1=!=#2]&)];
addTest[tochar[5],e];
addTest[tonum[tochar[9]],9];
addTest[tonum[tochar[26]],26];
addTest[tonum[o],15];
addTest[tochar[tonum[k]],k];
addTest[removeSign[-a],a];
addTest[removeSign[a],a];
addTest[removeSign[-f[-a]],f[-a]];
addTest[removeSign[f[-a]],f[a]];
addTest[sign[-a],-1];
addTest[sign[a],1];
addTest[sign[-f[a]],-1];
addTest[sign[f[-a]],1];
addTest[sum[f[a,b,c],a,-b,-c],sum[f[a,b,c],a,b,c]];
addTest[sum[f[a,b,c],set[a,-b,-c]],sum[f[a,b,c],set[a,b,c]]];
addTest[set@@(sum[f[a,b,c],a,b,c]//invertArguments[b,c]),
	set[sum[f[a,b,c],a,b,c],sum[f[a,-b,c],a,b,c],sum[f[a,b,-c],a,b,c],sum[f[a,-b,-c],a,b,c]]
];
addTest[set@@getAllVariables[f[g[a]]*Exp[u]*(1+x)/y^2],set@@{a,u,x,y}];
addTest[removeBlanks[f[a_,b_]*c_ Exp[d_]],f[a,b]*c Exp[d]];
SetOptions[addTest,equivalenceFunction->(HoldForm[#1===#2]&)];
addTest[ruleSplit[f[a_,b_]:> a^2],{"rd",f[a_,b_],Hold[a^2]}];
addTest[ruleSplit[f[a_,b_]-> u^2],{"r",f[a_,b_],Hold[u^2]}];
addTest[ruleSplit[f[a_,b_]:>  a^3/;b>0],{"rdc",f[a_,b_],Hold[a^3],Hold[b>0]}];
addTest[ruleJoin[ruleSplit[f[a_,b_]:> a^2]],f[a_,b_]:> a^2];
addTest[ruleJoin[ruleSplit[f[a_,b_]-> u^2]],f[a_,b_]-> u^2];
addTest[ruleJoin[ruleSplit[f[a_,b_]:>  a^3/;b>0]],f[a_,b_]:>  a^3/;b>0];
addTest[normalizeSumRule[sum[f[a_,b_,c_](-1)^(c_),set[a_,b_]]:> g[c]],
	sum[f[a_,b_,c_],set[a_,b_]]:>(-1)^(-c) g[c]
];
addTest[normalizeSumRule[sum[f[a_,b_,c_](-1)^(c_),set[a_,b_]]:> sum[g[b,c],set[a]]],
	sum[f[a_,b_,c_],set[a_,b_]]:>sum[(-1)^(-c) g[b,c],set[a]]
];
addTest[normalizeSumRule[sum[f[a_,b_,c_](-1)^(c_)g[b_,e_]h[e_]u[d_],set[a_,b_]]:> sum[G[b,c],set[a]]],
	sum[f[a_,b_,c_]g[b_,e_]u[d_],set[a_,b_]]:>sum[h[e]^(-1)((-1)^(-c) G[b,c]),set[a]]
];
addTest[normalizeSumRule[sum[-f[a_,b_,c_],set[a_,b_]]:> sum[G[b,c],set[a]]],
	sum[f[a_,b_,c_],set[a_,b_]]:>sum[- G[b,c],set[a]]
];
SetOptions[addTest,equivalenceFunction->(#1==#2&)];
endTestModule[];


runTests[msgSuccess-> None];


(* ::Subsection:: *)
(*TraditionalForm Output*)


declareIndexedAM[s]
sum[SphericalHarmonicY[l,m,\[Theta],\[Phi]],b,c,d]
%//TraditionalForm
sum[SphericalHarmonicY[l,m,\[Theta],\[Phi]],set[d,c,b]]
%//TraditionalForm
integrate[f[a,b],a,b]
%//TraditionalForm
integrate[SphericalHarmonicY[l,m,\[Theta],\[Phi]],set[\[Theta],\[Phi]]]
%//TraditionalForm
s[a,b]
%//TraditionalForm
sp[a,b]
%//TraditionalForm
ms[a,b]
%//TraditionalForm
msp[a,b]
%//TraditionalForm
sp
%//TraditionalForm



