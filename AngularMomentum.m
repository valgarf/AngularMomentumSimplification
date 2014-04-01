(* ::Package:: *)

(* ::Section:: *)
(*Initialise*)


BeginPackage["AngularMomentum`",{"Utility`"}]
ClearAll[Evaluate[Context[]<>"*"]];


sh::usage=
"Replacement for the built-in Function SphericalHarmonicY.
";

cg::usage=
"Replacement for the built-in Function ClebschGordan.
";

tj::usage=
"Replacement for the built-in Function ThreeJSymbol.
";

sj::usage=
"Replacement for the built-in Function SixJSymbol.
";

nj::usage=
"nj[{a,b,c},{d,e,f},{g,h,i}] represents a 9j Symbol
";

toCG::usage=
"Converts all 3J symbols (tj) to Clebsch-Gordan Coefficients (cg).
";

toTJ::usage=
"Converts all Clebsch-Gordan Coefficients (cg) to 3J symbols (tj).
";

declareQNInteger::usage=
"Declares a quantum number to be an integer. 
(This is used by the internal simplifaction mechanisms).
";

declareQNHalfInteger::usage=
"Declares a quantum number to be a half-integer. 
(This is used by the internal simplifaction mechanisms).
";

rotateSymbols::usage=
"Rotates the 3j,6j and 9j symbols so that the given arguments are in the lower right. If a symbol depends on multiple arguments, The first argument will be in the lower-right and the second argument will be to the left or above the first one.
";

simplifyAMSums::usage=
"
";


Begin["`Private`"]
ClearAll[Evaluate[Context[]<>"*"]];


(* ::Section:: *)
(*Helper Functions*)


$integerQN={1};
$halfintegerQN={1/2,Global`half};

declareQNInteger::doubledefinition="Symbol `1` has been declared a half-integer quantum number already";
declareQNHalfInteger::doubledefinition="Symbol `1` has been declared an integer quantum number already";
SetAttributes[declareQNInteger,Listable];
SetAttributes[declareQNHalfInteger,Listable];

declareQNInteger[x_]:=Module[{},
	If[MemberQ[$halfintegerQN,x],
		Message[declareQNInteger::doubledefinition,x];
		Return[None];
	];
	$integerQN=DeleteDuplicates@Append[$integerQN,x];
	
	Return[x];
];

declareQNHalfInteger[x_]:=Module[{},
	If[MemberQ[$integerQN,x],
		Message[declareQNHalfInteger::doubledefinition,x];
		Return[None];
	];
	$halfintegerQN=DeleteDuplicates@Append[$halfintegerQN,x];
	Return[x];
];

toTJ[expr_]:=expr//.{
	cg[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:>Sqrt[2 c+1](-1)^(-a+b-\[Gamma]) tj[{a,\[Alpha]},{b,\[Beta]},{c,-\[Gamma]}]
};

toCG[expr_]:=expr//.{
	tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:>1/Sqrt[2 c+1](-1)^(a-b-\[Gamma]) cg[{a,\[Alpha]},{b,\[Beta]},{c,-\[Gamma]}]
};

cg/:MakeBoxes[cg[{j1_,m1_},{j2_,m2_},{j_,m_}], fmt:TraditionalForm]:=
StyleBox[RowBox[{"c","(",GridBox[Map[MakeBoxes[#,fmt]&,{{j1,j2},{m1,m2}},{2}]],"|",GridBox[Map[MakeBoxes[#,fmt]&,{{j},{m}},{2}]],")"}],SpanMaxSize->\[Infinity]];

nj/:MakeBoxes[nj[a__], fmt:TraditionalForm]:=
StyleBox[RowBox[{"{",GridBox[Map[MakeBoxes[#,fmt]&,{a},{2}]],"}"}],SpanMaxSize->\[Infinity]];

sj/:MakeBoxes[sj[a__], fmt:TraditionalForm]:=MakeBoxes[SixJSymbol[a],fmt];
tj/:MakeBoxes[tj[a__], fmt:TraditionalForm]:=MakeBoxes[ThreeJSymbol[a],fmt];
sh/:MakeBoxes[sh[a__], fmt:TraditionalForm]:=MakeBoxes[SphericalHarmonicY[a],fmt];

SetAttributes[triX,Orderless]
SetAttributes[zeroX,Orderless]
SetAttributes[sjOL,Orderless]
SetAttributes[tjOL,Orderless]


(* ::Section:: *)
(*Transformation rules*)


(* ::Subsection:: *)
(*Preparation*)


prepareFactorRules={
		(-1)^(a_):>mX[a]
	};

prepareSumRules={
		sum[a_,b___]:> sum[a,set[b]] /;FreeQ[{b},set]
	};

prepareSymbolOrderlessRules={
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> tjOL[{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}},{{c,\[Gamma]},{a,\[Alpha]},{b,\[Beta]}},{{b,\[Beta]},{c,\[Gamma]},{a,\[Alpha]}}],
		sj[{a_,b_,c_},{d_,e_,f_}]:> sjOL[set[a,b,c],set[a,e,f],set[d,b,f],set[d,e,c]],
		nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> njOL[set[set[a,e,j],set[b,f,g],set[c,d,h]],set[set[a,b,c],set[d,e,f],set[g,h,j],set[a,d,g],set[b,e,h],set[c,f,j]]]
	};

(*prepareSymbolsOrderlessRule={
		sj[{a_,b_,c_},{d_,e_,f_}]:> sjOL[set[a,b,c],set[a,e,f],set[d,b,f],set[d,e,c]],
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> tjOL[_,set[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]]
(*?(MatchQ[EvenPermutations[{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}}],#]&)*)
	};*)


(* ::Subsection:: *)
(*Simplification*)


simplifyFactorRules={
		(-1)^(a_):>mX[a],
		mX[a_ + b_]:> mX[a] mX[b],
		mX[n_Integer a_]:> mX[a]^n,
		mX[-a_]^n_:> mX[a]^(-n),
		mX[a_]^n_:> mX[a]^Mod[n,4]/; (n>= 4||n<0) && MemberQ[$halfintegerQN,a],
		mX[a_]^n_:> mX[a]^Mod[n,2]/; n!=0 && n!=1 && MemberQ[$integerQN,a],
		mX[a_]^n_:> -mX[a]^Mod[n,2]/; 2<=n<4 && MemberQ[$halfintegerQN,a],
		mX[a_]^0:> 1,
		mX[0]-> 1,
		mX[1]->(-1),
		mX[-1]->(-1),
		mX[1/2]->(I),
		mX[-1/2]->(-I)		
	};



(* ::Subsection:: *)
(*Cleanup*)


cleanupSumRules={
		sum[a_,set[b___]]:> sum[a,b],
		sum[a_]:> a	
	};
cleanupFactorRules={
		mX[a_]:>(-1)^a,
		-(-1)^a_:> (-1)^(a+1),
		I (-1)^a_:> (-1)^(a+1/2)
	};
cleanupSymbolOrderlessRules={
		tjOL[{{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}},{{c_,\[Gamma]_},{a_,\[Alpha]_},{b_,\[Beta]_}},{{b_,\[Beta]_},{c_,\[Gamma]_},{a_,\[Alpha]_}}]:>tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}],
		sjOL[set[a_,b_,c_],set[a_,e_,f_],set[d_,b_,f_],set[d_,e_,c_]]:> sj[{a,b,c},{d,e,f}],
		njOL[set[set[a_,e_,j_],set[b_,f_,g_],set[c_,d_,h_]],set[set[a_,b_,c_],set[d_,e_,f_],set[g_,h_,j_],set[a_,d_,g_],set[b_,e_,h_],set[c_,f_,j_]]]:> nj[{a,b,c},{d,e,f},{g,h,j}]
	};



(* ::Section::Closed:: *)
(*Rotation of Symbols*)


rotTJ[k1_,keep_]:={
tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> (-1)^(a+b+c)tj[{a,\[Alpha]},{c,\[Gamma]},{b,\[Beta]}]/;
((FreeQ[{c,\[Gamma]},removeSign[k1]]&&!FreeQ[{b,\[Beta]},removeSign[k1]])||(FreeQ[{c},removeSign[k1]]&&!FreeQ[{b},removeSign[k1]]))&&FreeQAll[{b,\[Beta],c,\[Gamma]},keep],
tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> (-1)^(a+b+c)tj[{b,\[Beta]},{a,\[Alpha]},{c,\[Gamma]}]/;
((FreeQ[{b,\[Beta]},removeSign[k1]]&&!FreeQ[{a,\[Alpha]},removeSign[k1]])||(FreeQ[{b},removeSign[k1]]&&!FreeQ[{a},removeSign[k1]]))&&FreeQAll[{a,\[Alpha],b,\[Beta]},keep],
(*tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:>(-1)^(a+b+c)tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]/;
FreeQAll[{\[Alpha],\[Beta],\[Gamma]},keep]&&!FreeQ[{\[Gamma]},removeSign[k1]]&&sign[\[Gamma]]*sign[k1]==-1*)
tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:>(-1)^(a+b+c)tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]/;sign[\[Gamma]]==-1
};

rotSJ[k1_,keep_]:={
sj[{a_,b_,c_},{d_,e_,f_}]:>  sj[{a,c,b},{d,f,e}]/;
((!FreeQ[{e},k1]&&FreeQ[{f},k1])||(!FreeQ[{b},k1]&&FreeQ[{c,f},k1]))&&FreeQAll[{b,c,e,f},keep],
sj[{a_,b_,c_},{d_,e_,f_}]:>  sj[{c,b,a},{f,e,d}]/;
((!FreeQ[{d},k1]&&FreeQ[{f},k1])||(!FreeQ[{a},k1]&&FreeQ[{c,f},k1]))&&FreeQAll[{a,c,d,f},keep],
sj[{a_,b_,c_},{d_,e_,f_}]:>  sj[{b,a,c},{e,d,f}]/;
((!FreeQ[{d},k1]&&FreeQ[{e},k1])||(!FreeQ[{a},k1]&&FreeQ[{b,e},k1]))&&FreeQAll[{a,b,d,e},keep],
sj[{a_,b_,c_},{d_,e_,f_}]:>  sj[{a,e,f},{d,b,c}]/;
(FreeQ[{e,f},k1]&&!FreeQ[{b,c},k1])&&FreeQAll[{b,c,e,f},keep],
sj[{a_,b_,c_},{d_,e_,f_}]:>  sj[{d,b,f},{a,e,c}]/;
(FreeQ[{d,f},k1]&&!FreeQ[{a,c},k1])&&FreeQAll[{a,c,d,f},keep],
sj[{a_,b_,c_},{d_,e_,f_}]:>  sj[{d,e,c},{a,b,f}]/;
(FreeQ[{d,e},k1]&&!FreeQ[{a,b},k1])&&FreeQAll[{a,b,d,e},keep]
};

rotNJ[k1_,keep_]:={
nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> (-1)^(a+b+c+d+e+f+g+h+j)nj[{a,c,b},{d,f,e},{g,j,h}]/;
((!FreeQ[{h},k1]&&FreeQ[{j},k1])||(!FreeQ[{e},k1]&&FreeQ[{f,j},k1])||(!FreeQ[{b},k1]&&FreeQ[{c,f,j},k1]))&&FreeQAll[{b,e,h,c,f,j},keep],
nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> (-1)^(a+b+c+d+e+f+g+h+j)nj[{c,b,a},{f,e,d},{j,h,g}]/;
((!FreeQ[{g},k1]&&FreeQ[{j},k1])||(!FreeQ[{d},k1]&&FreeQ[{f,j},k1])||(!FreeQ[{a},k1]&&FreeQ[{c,f,j},k1]))&&FreeQAll[{a,d,g,c,f,j},keep],
nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> (-1)^(a+b+c+d+e+f+g+h+j)nj[{b,a,c},{e,d,f},{h,g,j}]/;
((!FreeQ[{g},k1]&&FreeQ[{h},k1])||(!FreeQ[{d},k1]&&FreeQ[{e,h},k1])||(!FreeQ[{a},k1]&&FreeQ[{b,e,h},k1]))&&FreeQAll[{a,d,g,b,e,h},keep],
nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> (-1)^(a+b+c+d+e+f+g+h+j)nj[{g,h,j},{d,e,f},{a,b,c}]/;
(!FreeQ[{a,b,c},k1]&&FreeQ[{g,h,j},k1])&&FreeQAll[{a,b,c,g,h,j},keep],
nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> (-1)^(a+b+c+d+e+f+g+h+j)nj[{a,b,c},{g,h,j},{d,e,f}]/;
(!FreeQ[{d,e,f},k1]&&FreeQ[{g,h,j},k1])&&FreeQAll[{d,e,f,g,h,j},keep],
nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> (-1)^(a+b+c+d+e+f+g+h+j)nj[{d,e,f},{a,b,c},{g,h,j}]/;
(!FreeQ[{a,b,c},k1]&&FreeQ[{d,e,f},k1])&&FreeQAll[{a,b,c,d,e,f},keep]
};

rotAll[k1_,keep_]:=Join[rotTJ[k1,removeSign/@keep],rotSJ[k1,keep],rotNJ[k1,keep]];
rotAll[k1_]:=rotAll[k1,{}];
rotCompleteHelper[{}]:=#&;
rotCompleteHelper[k_]:=rotCompleteHelper[Drop[k,-1]][#]//.rotAll[Last[k],Drop[k,-1]]&;
rotateSymbols[k__]:=rotCompleteHelper[{k}];


(* ::Section:: *)
(*Simplifying Sums of 3jm, 6j and 9j Symbols*)


(* ::Subsection:: *)
(*Raw Rules*)


(* ::Subsubsection:: *)
(*6J*)


simplify6jRawRules={
		sum[m_.(2 x_+1)sj[{a_,b_,x_},{a_,b_,c_}],x_,u___]
			:> sum[m (-1)^(2c),u]
				/;FreeQAll[{m,u,a,b,c},{x}],
		sum[m_. (-1)^(a_+b_+x_)(2 x_+1)sj[{a_,b_,x_},{b_,a_,c_}],x_,u___]
			:> sum[m Sqrt[2a+1]Sqrt[2b+1]KroneckerDelta[c,0],u]
				/;FreeQAll[{m,u,a,b,c},{x}],
		sum[m_.(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{a_,b_,q_}],x_,u___]
			:> sum[m 1/(2p+1)KroneckerDelta[p,q],u]
				/;FreeQAll[{m,u,a,b,c,d,p,q},{x}],
		sum[m_. (-1)^(p_+q_+x_)(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{b_,a_,q_}],x_,u___]
			:> sum[m  sj[{c,a,q},{d,b,p}],u]/;FreeQAll[{m,u,a,b,c,d,p,q},{x}]
	};
simplify6jRawRules//TraditionalForm


(* ::Subsection:: *)
(*Expanded Rules*)


simplifySymbolRules=Join[simplify6jRawRules]//.
		Join[prepareFactorRules,prepareSumRules,prepareSymbolOrderlessRules]//.
		Join[simplifyFactorRules]//
		normalizeSumRule;
simplifySymbolRules//TraditionalForm			


(* ::Subsection:: *)
(*Functions*)




simplifyAMSums[expr_]:=Module[{prev,result},
	result=expr//.Join[prepareFactorRules,prepareSumRules,prepareSymbolOrderlessRules];
	prev=None;	
	While[prev=!=result,
		Print[TraditionalForm[result//.Join[cleanupSumRules,cleanupFactorRules,cleanupSymbolOrderlessRules]]];
		prev=result;
		result=prev/.Join[simplifyFactorRules,simplifySymbolRules];		
	];	
	Return[result//.Join[cleanupSumRules,cleanupFactorRules,cleanupSymbolOrderlessRules]];
];


(* ::Section:: *)
(*Cleanup*)


End[]


EndPackage[]
