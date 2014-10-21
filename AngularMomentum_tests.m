(* ::Package:: *)

ClearAll[Evaluate[Context[]<>"*"]];
$Path=DeleteDuplicates@Append[$Path,NotebookDirectory[]];
<<UnitTesting`
<<AngularMomentum`


(* ::Subsection::Closed:: *)
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
declareQNInteger[{a,ap,\[Alpha],\[Alpha]p,b,bp,\[Beta],\[Beta]p,c,cp,\[Gamma],\[Gamma]p,d,dp,\[Delta],\[Delta]p,e,f,g,h,j,k,l,m,n,o,p,\[Psi],q,\[Kappa],r,\[Rho],s,\[Sigma],t,tp,\[Tau],m,\[Mu],mp,\[Mu]p,u,up,v,w,x,xp,y,l[1],l[2],l[3],l[4],m[1],m[2],m[3],m[4]}];



beginTestModule["Varshalovich"];
beginTestModule["Symbols"];
testEqn[1][exp]=sum[tj[{a,\[Alpha]},{b,\[Beta]},{0,\[Gamma]}]^3,set[\[Gamma]]];
testEqn[1][res]= KroneckerDelta[a,b]KroneckerDelta[\[Alpha],-\[Beta]]/(Sqrt[2 a+1])^3 (-1)^(a + \[Alpha]);
testEqn[2][exp]=sum[(-1)^(a-\[Alpha])tj[{a,\[Alpha]},{a,-\[Alpha]},{c,\[Gamma]}],\[Alpha]];
testEqn[2][res]=Sqrt[2 a +1] KroneckerDelta[c,0] KroneckerDelta[\[Gamma],0];
testEqn[3][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa])tj[{a,-\[Alpha]},{p,\[Psi]},{q,\[Kappa]}]tj[{p,-\[Psi]},{q,-\[Kappa]},{ap,\[Alpha]p}],\[Psi],\[Kappa]];
testEqn[3][res]=(-1)^(ap+\[Alpha]p)1/(2 ap +1) conTri[ap,p,q] KroneckerDelta[a,ap] KroneckerDelta[\[Alpha],\[Alpha]p];
testEqn[4][exp]=sum[(-1)^(q-\[Kappa])(2 q +1)tj[{a,-\[Alpha]},{b,-\[Beta]},{q,\[Kappa]}]tj[{q,-\[Kappa]},{a,\[Alpha]p},{b,\[Beta]p}],q,\[Kappa]];
testEqn[4][res]=(-1)^(a+\[Alpha]p+b+\[Beta]p) KroneckerDelta[\[Alpha],\[Alpha]p] KroneckerDelta[\[Beta],\[Beta]p];
testEqn[5][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho])tj[{p,\[Psi]},{a,\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{b,\[Beta]},{r,-\[Rho]}]tj[{r,\[Rho]},{c,\[Gamma]},{p,-\[Psi]}],\[Kappa],\[Psi],\[Rho]];
testEqn[5][res]=tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}] sj[{a,b,c},{r,p,q}];
testEqn[6][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho]+s-\[Sigma]+t-\[Tau])tj[{p,\[Psi]},{a,-\[Alpha]},{q,\[Kappa]}]tj[{q,-\[Kappa]},{r,\[Rho]},{t,\[Tau]}]tj[{r,-\[Rho]},{ap,\[Alpha]p},{s,\[Sigma]}]tj[{s,-\[Sigma]},{p,-\[Psi]},{t,-\[Tau]}],\[Psi],\[Kappa],\[Rho],\[Sigma],\[Tau]];
testEqn[6][res]=(-1)^(ap+\[Alpha]p)/(2ap+1)sj[{ap,p,q},{t,r,s}]KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],\[Alpha]p];
testEqn[7][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho]+s-\[Sigma])tj[{p,\[Psi]},{a,\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{b,\[Beta]},{r,-\[Rho]}]tj[{r,\[Rho]},{s,\[Sigma]},{p,-\[Psi]}]tj[{s,-\[Sigma]},{c,\[Gamma]},{d,\[Delta]}],\[Psi],\[Kappa],\[Rho],\[Sigma]];
testEqn[7][res]=sum[(-1)^(c+d+\[Sigma])sj[{a,b,s},{r,p,q}]tj[{a,-\[Alpha]},{b,-\[Beta]},{s,-\[Sigma]}]tj[{s,\[Sigma]},{c,-\[Gamma]},{d,-\[Delta]}],set[\[Sigma]]];
testEqn[8][exp]=sum[(-1)^(p-\[Psi]+q-\[Kappa]+r-\[Rho]+s-\[Sigma])tj[{p,\[Psi]},{a,\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{b,\[Beta]},{r,-\[Rho]}]tj[{r,\[Rho]},{c,\[Gamma]},{s,-\[Sigma]}]tj[{s,\[Sigma]},{d,\[Delta]},{p,-\[Psi]}],\[Psi],\[Kappa],\[Rho],\[Sigma]];
(*testEqn[8][res]=sum[(-1)^(r+c+d+p+AngularMomentum`Private`varK[1]+AngularMomentum`Private`varK[2])(2 AngularMomentum`Private`varK[1]+1)sj[{a,b,AngularMomentum`Private`varK[1]},{r,p,q}]sj[{c,d,AngularMomentum`Private`varK[1]},{p,r,s}]tj[{a,\[Alpha]},{AngularMomentum`Private`varK[1],-AngularMomentum`Private`varK[2]},{b,\[Beta]}]tj[{d,\[Delta]},{AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]},{c,\[Gamma]}],set[AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]]];*)
testEqn[8][res]=sum[(-1)^(a+d+q+s+AngularMomentum`Private`varK[1]+AngularMomentum`Private`varK[2])(2 AngularMomentum`Private`varK[1]+1)sj[{a,d,AngularMomentum`Private`varK[1]},{s,q,p}]sj[{b,c,AngularMomentum`Private`varK[1]},{s,q,r}]tj[{a,\[Alpha]},{AngularMomentum`Private`varK[1],-AngularMomentum`Private`varK[2]},{d,\[Delta]}]tj[{b,\[Beta]},{AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]},{c,\[Gamma]}],set[AngularMomentum`Private`varK[1],AngularMomentum`Private`varK[2]]];

(*6j symbols *)
testEqn[9][exp]=sum[sj[{a,b,0},{d,e,f}]^5,set[f]];
testEqn[9][res]=sum[conTri[a,e,f]KroneckerDelta[a,b]KroneckerDelta[d,e]/(Sqrt[2 a+1]Sqrt[2e+1])^5 (-1)^(a +e +f),set[f]];		
testEqn[10][exp]=sum[(2x+1)sj[{a,b,x},{a,b,c}],x];
testEqn[10][res]= conTri[a,b,c];
testEqn[11][exp]=sum[(-1)^(a+b+x)(2x+1)sj[{a,b,x},{b,a,c}],x];
testEqn[11][res]=Sqrt[2a+1]Sqrt[2b+1]KroneckerDelta[c,0];
testEqn[12][exp]=sum[(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{a,b,q}],x];
testEqn[12][res]=1/(2p+1)KroneckerDelta[p,q] conTri[a,d,p]conTri[b,c,p];
testEqn[13][exp]=sum[(-1)^(p+q+x)(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{b,a,q}],x];
testEqn[13][res]=sj[{a,c,q},{b,d,p}];
testEqn[14][exp]=sum[(-1)^(a+b+c+d+e+f+p+q+r+x)(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{b,a,r}],x];
testEqn[14][res]=sj[{a,d,p},{q,r,e}]sj[{b,c,p},{q,r,f}];
testEqn[15][exp]=sum[(-1)^(2x)(2x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{a,b,r}],x];
testEqn[15][res]=nj[{a,r,f},{p,b,c},{d,e,q}];
(*
testEqn[16][exp]=sum[(-1)^(a+b+c+d+e+f+g+h+p+q+r+s+x)(2 x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{g,h,r}]sj[{g,h,x},{b,a,s}],x];
testEqn[16][res]=(sum[(-1)^(2*var[1]+a+b+e+f)(2 var[1]+1)nj[{s,h,b},{g,r,f},{a,e,var[1]}]sj[{b,f,var[1]},{q,p,c}]sj[{a,e,var[1]},{q,p,d}],var[1]]/.{var[1]->AngularMomentum`Private`varK[2]});
testEqn[17][exp]=sum[(2 x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{g,h,r}]sj[{g,h,x},{a,b,s}],x];
testEqn[17][res]=(sum[(2 var[1]+1) nj[{a,f,var[1]},{d,q,e},{p,c,b}]nj[{a,f,var[1]},{h,r,e},{s,g,b}],var[1]]/.{var[1]->AngularMomentum`Private`varK[3]});
*)
(*9j symbols *)
testEqn[16][exp]=Null;
testEqn[16][res]=Null;
testEqn[17][exp]=Null;
testEqn[17][res]=Null;
testEqn[18][exp]=Null;
testEqn[18][res]=Null;
testEqn[19][exp]=Null;
testEqn[19][res]=Null;
testEqn[20][exp]=Null;
testEqn[20][res]=Null;
testEqn[21][exp]=Null;
testEqn[21][res]=Null;
testEqn[22][exp]=Null;
testEqn[22][res]=Null;
testEqn[23][exp]=Null;
testEqn[23][res]=Null;
testEqn[24][exp]=Null;
testEqn[24][res]=Null;


addFn=(addTest[simplifyAMSum[#1,Print->False],#2]&)@@({testEqn[#][exp],testEqn[#][res]})&;
addFn/@Table[i,{i,17}];



(* ::Text:: *)
(*Symbol tests that need additional options:*)


addTest[simplifyAMSum[
sum[(-1)^(a+b+c+d+e+f+g+h+p+q+r+s+x)(2 x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{g,h,r}]sj[{g,h,x},{b,a,s}],x],
Print->False,OnlySums->{x}],
sum[(-1)^(a+b+e+f)nj[{a,g,s},{AngularMomentum`Private`varK[3],f,b},{e,r,h}]sj[{a,d,p},{q,AngularMomentum`Private`varK[3],e}]sj[{b,c,p},{q,AngularMomentum`Private`varK[3],f}](1+2 AngularMomentum`Private`varK[3]),set[AngularMomentum`Private`varK[3]]]];

addTest[simplifyAMSum[
sum[(2 x+1)sj[{a,b,x},{c,d,p}]sj[{c,d,x},{e,f,q}]sj[{e,f,x},{g,h,r}]sj[{g,h,x},{a,b,s}],x],
Print->False,OnlySums->{x}],
sum[(2 AngularMomentum`Private`varK[4]+1) nj[{a,AngularMomentum`Private`varK[4],f},{p,b,c},{d,e,q}]nj[{a,s,h},{AngularMomentum`Private`varK[4],b,e},{f,g,r}],set[AngularMomentum`Private`varK[4]]]];

endTestModule[];


beginTestModule["Spherical Harmonics"];

declareIndexed[{\[Theta],\[Phi],l,m}];
testSHEqn[0]=integrate[sh[l[1],m[1],\[Theta],\[Phi]]sh[l[2],m[2],\[Theta],\[Phi]]sh[l[3],m[3],\[Theta],\[Phi]]sh[l[4],m[4],\[Theta],\[Phi]]Sin[\[Theta]],set[\[Phi],\[Theta],x]];
testSHEqn[1]=integrate[sh[l[1],m[1],\[Theta][1],\[Phi][1]]sh[l[2],m[2],\[Theta][1],\[Phi][1]]sh[l[3],m[3],\[Theta][2],\[Phi][2]]sh[l[4],m[4],\[Theta][2],\[Phi][2]]Sin[\[Theta][1]]Sin[\[Theta][2]],set[\[Phi][1],\[Theta][1],\[Phi][2],\[Theta][2],x]];

addTest[simplifySHIntegral[testSHEqn[0],Integrate->True],
sum[integrate[1/(4\[Pi])(-1)^(AngularMomentum`Private`varM[1]) Sqrt[1+2 l[1]]Sqrt[1+2 l[2]] tj[{l[1],0},{l[2],0},{AngularMomentum`Private`varL[1],0}] tj[{l[1],m[1]},{l[2],m[2]},{AngularMomentum`Private`varL[1],-AngularMomentum`Private`varM[1]}] tj[{l[3],0},{l[4],0},{AngularMomentum`Private`varL[1],0}] tj[{l[3],m[3]},{l[4],m[4]},{AngularMomentum`Private`varL[1],AngularMomentum`Private`varM[1]}]Sqrt[1+2 AngularMomentum`Private`varL[1]] Sqrt[1+2 l[3]] Sqrt[1+2 l[4]] Sqrt[1+2 AngularMomentum`Private`varL[1]],set[x]],set[AngularMomentum`Private`varL[1],AngularMomentum`Private`varM[1]]]
];

addTest[simplifySHIntegral[testSHEqn[0],Integrate->False],
sum[integrate[1/(2Sqrt[\[Pi]])(-1)^(AngularMomentum`Private`varM[2]) Sqrt[1+2 l[1]]Sqrt[1+2 l[2]] sh[l[3],m[3],\[Theta],\[Phi]] sh[l[4],m[4],\[Theta],\[Phi]] sh[AngularMomentum`Private`varL[2],AngularMomentum`Private`varM[2],\[Theta],\[Phi]] Sin[\[Theta]] tj[{l[1],0},{l[2],0},{AngularMomentum`Private`varL[2],0}] tj[{l[1],m[1]},{l[2],m[2]},{AngularMomentum`Private`varL[2],-AngularMomentum`Private`varM[2]}]Sqrt[1+2 AngularMomentum`Private`varL[2]],set[x,\[Theta],\[Phi]]],set[AngularMomentum`Private`varL[2],AngularMomentum`Private`varM[2]]]];

addTest[simplifySHIntegral[testSHEqn[0],Integrate->False,ReduceProducts->True],
sum[integrate[1/(8 \[Pi]^(3/2))(-1)^(AngularMomentum`Private`varM[3]+AngularMomentum`Private`varM[4]+AngularMomentum`Private`varM[5]) Sqrt[1+2 l[1]]Sqrt[1+2 l[2]]Sqrt[1+2 l[3]]Sqrt[1+2 l[4]] sh[AngularMomentum`Private`varL[5],AngularMomentum`Private`varM[5],\[Theta],\[Phi]] Sin[\[Theta]] tj[{l[1],0},{l[2],0},{AngularMomentum`Private`varL[3],0}] tj[{l[1],m[1]},{l[2],m[2]},{AngularMomentum`Private`varL[3],-AngularMomentum`Private`varM[3]}] tj[{l[3],0},{l[4],0},{AngularMomentum`Private`varL[4],0}] tj[{l[3],m[3]},{l[4],m[4]},{AngularMomentum`Private`varL[4],-AngularMomentum`Private`varM[4]}] tj[{AngularMomentum`Private`varL[3],0},{AngularMomentum`Private`varL[4],0},{AngularMomentum`Private`varL[5],0}] tj[{AngularMomentum`Private`varL[3],AngularMomentum`Private`varM[3]},{AngularMomentum`Private`varL[4],AngularMomentum`Private`varM[4]},{AngularMomentum`Private`varL[5],-AngularMomentum`Private`varM[5]}] (1+2 AngularMomentum`Private`varL[3]) (1+2 AngularMomentum`Private`varL[4])Sqrt[1+2 AngularMomentum`Private`varL[5]],set[x,\[Theta],\[Phi]]],set[AngularMomentum`Private`varL[3],AngularMomentum`Private`varL[4],AngularMomentum`Private`varL[5],AngularMomentum`Private`varM[3],AngularMomentum`Private`varM[4],AngularMomentum`Private`varM[5]]]
];

addTest[simplifySHIntegral[integrate[sh[l[1],m[1],\[Theta],\[Phi]] Sin[\[Theta]],set[\[Phi],\[Theta],x]],Integrate->True],
integrate[Sqrt[4 \[Pi]] KroneckerDelta[l[1],0]KroneckerDelta[m[1],0],set[x]]
];

addTest[simplifySHIntegral[integrate[sh[l[1],m[1],\[Theta],\[Phi]] sh[l[2],m[2],\[Theta],\[Phi]]Sin[\[Theta]],set[\[Phi],\[Theta],x]],Integrate->True],
integrate[(-1)^m[2] KroneckerDelta[l[1],l[2]]KroneckerDelta[m[1],-m[2]],set[x]]
];

addTest[simplifySHIntegral[testSHEqn[1],Integrate->True],
integrate[(-1)^(m[2]+m[4]) KroneckerDelta[l[1],l[2]] KroneckerDelta[l[3],l[4]] KroneckerDelta[m[1],-m[2]] KroneckerDelta[m[3],-m[4]],set[x]]
];

addTest[simplifySHIntegral[testSHEqn[1],Integrate->True,OnlyIntegrals->{\[Theta][1]}],
integrate[(-1)^m[2] KroneckerDelta[l[1],l[2]] KroneckerDelta[m[1],-m[2]] sh[l[3],m[3],\[Theta][2],\[Phi][2]] sh[l[4],m[4],\[Theta][2],\[Phi][2]] Sin[\[Theta][2]],set[x,\[Theta][2],\[Phi][2]]]
];

addTest[simplifySHIntegral[testSHEqn[1],Integrate->True,IgnoreIntegrals->{\[Theta][1]}],
integrate[(-1)^m[4] KroneckerDelta[l[3],l[4]] KroneckerDelta[m[3],-m[4]] sh[l[1],m[1],\[Theta][1],\[Phi][1]] sh[l[2],m[2],\[Theta][1],\[Phi][1]] Sin[\[Theta][1]],set[x,\[Theta][1],\[Phi][1]]]
];

endTestModule[];
endTestModule[];


runTests[msgSuccess->None];


(* ::Subsection::Closed:: *)
(*Should yield error messages*)


declarePrimed[u];
declareQNHalfInteger[{hi1,hi2,hi3,hi4,hi5,hi6}];
declareQNInteger[{i1,i2,i3,i4,i5,i6}];
Print["should yield an undeclared symbol (consistencyCheck::notfound) error"];
tj[{hi1,hi2},{hi3,hi4},{UNDEC,i1}]//consistencyCheck;
Print["should yield an error due to unfulfilled triangular condition for {hi1,,hi2,hi3} and {hi4,hi5,hi6}"];
tj[{hi1,hi4},{hi2,hi5},{hi3,hi6}]//consistencyCheck;
Print["should yield an error as {hi2,i2} and {i1,hi4} do not match"];
tj[{hi1,hi3},{hi2,i2},{i1,hi4}]//consistencyCheck;
Print["should complain about conditions that cannot be fulfilled. The reason are undefined symbols (axx,bxx,\[Alpha]xx,\[Beta]xx)"];
AngularMomentum`Private`cleanupNewVariables[
	tj[{axx,\[Alpha]xx},{bxx,\[Beta]xx},{var[1],var[2]}]//.var[i_]:> AngularMomentum`Private`var[i]
];


(* ::Subsection::Closed:: *)
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


declareIndexed[{\[Theta],\[Phi],l,m}];
testExprSHX=integrate[sh[l[1],m[1],\[Theta][1],\[Phi][1]]sh[l[2],m[2],\[Theta][1],\[Phi][1]]sh[l[3],m[3],\[Theta][2],\[Phi][2]]sh[l[4],m[4],\[Theta][2],\[Phi][2]]Sin[\[Theta][1]]Sin[\[Theta][2]],set[\[Phi][1],\[Theta][1],\[Phi][2],\[Theta][2],x]];
simplifySHIntegral[testExprSHX,Integrate->True]
%//TraditionalForm
simplifySHIntegral[testExprSHX,Integrate->True,OnlyIntegrals->{\[Theta][1]}]
%//TraditionalForm
simplifySHIntegral[testExprSHX,Integrate->True,IgnoreIntegrals->{\[Theta][1]}]
%//TraditionalForm



ClearAll[Evaluate[Context[]<>"*"]];
$Path=DeleteDuplicates@Append[$Path,NotebookDirectory[]];
<<UnitTesting`
<<AngularMomentum`
declareIndexedAM[t]
declarePrimed[{m,\[Mu],\[Alpha],\[Beta]}];
declareQNInteger[{a,ap,\[Alpha],\[Alpha]p,b,bp,\[Beta],\[Beta]p,c,cp,\[Gamma],\[Gamma]p,d,dp,\[Delta],\[Delta]p,e,\[Epsilon],f,g,h,j,k,l,m,mp,\[Mu],\[Mu]p,n,o,p,\[Psi],q,\[Kappa],r,\[Rho],s,\[Sigma],t,tp,\[Tau],u,up,\[Nu],v,w,x,xp,y,l[1],l[2],l[3],l[4],m[1],m[2],m[3],m[4]}];


testExprFast[4]=sum[(-1)^(\[Kappa]+\[Psi])tj[{p,-\[Psi]},{a,-\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{r,\[Rho]},{b,-\[Beta]}]tj[{s,\[Sigma]},{c,\[Gamma]},{r,-\[Rho]}]tj[{s,\[Sigma]},{p,-\[Psi]},{d,\[Delta]}],set[\[Psi],\[Kappa],\[Rho],\[Sigma]]];
testExprFast[5]=sum[(-1)^(\[Kappa])tj[{p,-\[Psi]},{a,-\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{r,\[Rho]},{b,-\[Beta]}]tj[{s,\[Sigma]},{c,\[Gamma]},{r,-\[Rho]}]tj[{s,\[Sigma]},{t,-\[Tau]},{d,\[Delta]}]tj[{t,\[Tau]},{p,-\[Psi]},{e,\[Epsilon]}],set[\[Psi],\[Kappa],\[Rho],\[Sigma],\[Tau]]];
testExprFast[6]=sum[(-1)^(\[Kappa]+\[Psi])tj[{p,-\[Psi]},{a,-\[Alpha]},{q,-\[Kappa]}]tj[{q,\[Kappa]},{r,\[Rho]},{b,-\[Beta]}]tj[{s,\[Sigma]},{c,\[Gamma]},{r,-\[Rho]}]tj[{s,\[Sigma]},{t,-\[Tau]},{d,\[Delta]}]tj[{t,\[Tau]},{u,-\[Nu]},{e,\[Epsilon]}]tj[{u,\[Nu]},{p,-\[Psi]},{e,\[Epsilon]}],set[\[Psi],\[Kappa],\[Rho],\[Sigma],\[Tau],\[Nu]]];
testExprFast[4]//TraditionalForm
testExprFast[4]=simplifyAMSum[testExprFast[4],OnlySums->{\[Kappa],\[Rho],\[Sigma],\[Psi]},Print->False]//TraditionalForm
testExprFast[5]//TraditionalForm
testExprFast[5]=simplifyAMSum[testExprFast[5],OnlySums->{\[Kappa],\[Rho],\[Sigma],\[Psi],\[Tau]},Print->False]//TraditionalForm
testExprFast[6]//TraditionalForm
testExprFast[6]=simplifyAMSum[testExprFast[6],OnlySums->{\[Kappa],\[Rho],\[Sigma],\[Psi],\[Tau],\[Nu]},Print->False]//TraditionalForm


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
