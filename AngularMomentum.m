(* ::Package:: *)

(* ::Section:: *)
(*Package Initialise*)


$Path=DeleteDuplicates@Append[$Path,ToFileName[{NotebookDirectory[]}]];
BeginPackage["AngularMomentum`",{"Utility`"}]
ClearAll[Evaluate[Context[]<>"*"]];


sh::usage=
"sh is a replacement for the built-in Function SphericalHarmonicY."

cg::usage=
"cg is a replacement for the built-in Function ClebschGordan."

tj::usage=
"tj is a replacement for the built-in Function ThreeJSymbol."

sj::usage=
"sj is a replacement for the built-in Function SixJSymbol."

nj::usage=
"nj[{a,b,c},{d,e,f},{g,h,i}] represents a 9j Symbol"

toCG::usage=
"toCG[expr] converts all 3J symbols (tj) to Clebsch-Gordan Coefficients (cg)."

toTJ::usage=
"toTJ[expr] converts all Clebsch-Gordan Coefficients (cg) to 3J symbols (tj)."

conTri::usage=
"conTri[a,b,c] represents a triangular condtion for a,b and c"

conZero::usage=
"conZero[\[Alpha],\[Beta],\[Gamma]] represents the condition \[Alpha]+\[Beta]+\[Gamma]=0."

declareQNInteger::usage=
"declareQNInteger[qn] declares a quantum number to be an integer. 
(This information is then used by the internal simplifaction mechanisms)."

declareQNHalfInteger::usage=
"declareQNHalfInteger[qn] declares a quantum number to be a half-integer. 
(This information is then used by the internal simplifaction mechanisms)."

rotateSymbols::usage=
"rotateSymbols[symb1,...] returns a function that rotates the 3j, 6j and 9j symbols so that the given arguments are in the lower right. If a symbol depends on multiple arguments, The first argument will be in the lower-right and the second argument will be to the left or above the first one.
Usage: expr // rotateSymbols[symb1,symb2,...]"

simplifyAMSum::usage=
"simplifyAMSum[expr] can simplify sums of 3j, 6j, and 9j symbols. For complex expressions it might not finish. It is advised to run simplifyAMSum[expr,Print->True], which prints the expression it is working on.
Possible options:
  Print            -> True|False (default: False)
  TimingComplete   -> True|False (default: False)
  IgnoreSums       -> list of summation indices (default: {})
  OnlySums         -> list of summation indices (default: all occurring sums)
  NoSymbols        -> True|False (default: False)
Print: Setting this option to \"True\" prints all intermediate expressions used during the simplification
TimingComplete: Setting this option to \"True\" prints times needed for various steps (useful for profiling only)
IgnoreSums: None of the summation indices given in this list are considered
OnlySums: If this option is supplied only the summation indices given are considered
NoSymbols: Setting this option to \"True\" prevents simplification of any 3j,6j or 9j symbol.
 "
expand9j::usage="
Expands all 9j symbols in 6j symbols."

extractConditions::usage=
"extractConditions[expr] extracts all condtions (conTri/conZero) from the expression"

consistencyCheck::usage=
"consistencyCheck[expr] checks the expressions for consistency using available conditions and complaining about missing information."

getLastExpression::usage=
"Returns the last expression the simplifyAMSum function worked on."

simplifySHIntegral::usage=
"simplifySHIntegral[expr] can simplify integrals of spherical harmonics. Most likely the Integrate->True option should be supplied.
Possible options:
  Integrate        -> True|False (default: False)
  IgnoreIntegrals  -> list of integration variables (default: {})
  OnlyIntegrals    -> list of integration variables (default: all occurring sums)  
  ReduceProducts   -> Ture|False (default: False)
  
Integrate: Setting this option to \"True\" performs integrals if possible
IgnoreIntegrals: None of the integration variables are considered
OnlyIntegrals: If this option is supplied only the integration variables given are considered
ReduceProducts: Setting this option to \"True\" simplifies products of spherical harmonics without integrating them. Should only be used when Integrate->False
"


Begin["`Private`"]
ClearAll[Evaluate[Context[]<>"*"]];


(* ::Section:: *)
(*Helper Functions*)


$integerQN={1};
$halfintegerQN={1/2,Global`half};
Utility`Private`$offset[Global`varK]=0;


declareQNInteger::doubledefinition="Symbol `1` has been declared a half-integer quantum number already";
declareQNHalfInteger::doubledefinition="Symbol `1` has been declared an integer quantum number already";
SetAttributes[declareQNInteger,Listable];
SetAttributes[declareQNHalfInteger,Listable];

Options[declareQNInteger]={Overwrite->False};
declareQNInteger[x_,OptionsPattern[]]:=Module[{},
	If[MemberQ[$halfintegerQN,x],
		If[OptionValue[Overwrite],
		(*then*)
			$halfintegerQN=DeleteCases[$halfintegerQN,x],
		(*else*)
			Message[declareQNInteger::doubledefinition,x];
			Return[None];
		];
	];
	$integerQN=DeleteDuplicates@Append[$integerQN,x];
	
	Return[x];
];

Options[declareQNHalfInteger]={Overwrite->False};
declareQNHalfInteger[x_,OptionsPattern[]]:=Module[{},
	If[MemberQ[$integerQN,x],
		If[OptionValue[Overwrite],
		(*then*)
			$integerQN=DeleteCases[$integerQN,x],
		(*else*)
			Message[declareQNHalfInteger::doubledefinition,x];
			Return[None];
		];
	];
	$halfintegerQN=DeleteDuplicates@Append[$halfintegerQN,x];
	Return[x];
];

extractConditions[expr_]:=Module[{
		elements={}
	},
	elements=Cases[expr,sj[__]|tj[__]|nj[__]|cg[__]|sjOL[__]|njOL[__]|conTri[__]|conZero[__],{0,Infinity}];
	elements=elements//.{
			sj[{a_,b_,c_},{d_,e_,f_}]:> {conTri[a,b,c],conTri[a,e,f],conTri[d,b,f],conTri[d,e,c]},
			tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> {conTri[a,b,c],conZero[\[Alpha],\[Beta],\[Gamma]]},
			cg[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> {conTri[a,b,c],conZero[\[Alpha],\[Beta],-\[Gamma]]},
			nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> {conTri[a,b,c],conTri[d,e,f],conTri[g,h,j],conTri[a,d,g],conTri[b,e,h],conTri[c,f,j]},
			sjOL[a__]:>({a}/.set-> conTri),
			njOL[u_,set[a__]]:>({a}/.set-> conTri)
		};
	elements=DeleteDuplicates@Flatten[elements];
	Return[elements];
];

consistencyCheck::projection="Symbols \"`1`\" and \"`2`\" have not been declared consistently, e.g. one might be an integer and the other is a half-integer";
consistencyCheck::notfound="Symbol \"`1`\" has not been declared an integer or half-integer quantum number. Please use the functions declareQNInteger and declareQNHalfInteger.";
consistencyCheck::halfinteger="Condition \"`1`\" cannot be fulfilled as the sum of the arguments cannot yield an integer";
(*consistencyCheck::multiplesums="Expression has multiple sums. Cannot prepare factors";*)
consistencyCheck[expr_]:=Module[{conditions,symbols,notfound,sums,replaceknownsymbols,result=True},
(*	sums=Cases[expr,sum[__],{0,Infinity}];
	If[Length[sums]>1,
		Message[consistencyCheck::multiplesums];
		result=False;
	];
*)
	replaceknownsymbols=Join[(#->1/2)&/@$halfintegerQN,(#->0)&/@$integerQN];
	conditions=extractConditions[expr];
	symbols=DeleteDuplicates@(removeSign/@Flatten[conditions//.{conTri[a__]:>{a}, conZero[a__]:>{a}}]);

	(*check for undeclared symbols*)
	notfound=Flatten@Position[ (IntegerQ[Abs[2 #/.replaceknownsymbols]]&)/@symbols,False];
	Do[Message[consistencyCheck::notfound,symbols[[i]]],{i,notfound}];

	(*Check that a+b+c is an integer for conTri[a,b,c] and conZero[a,b,c]*)
	notfound=Drop[#,1]&@Flatten@Position[
		conditions/.replaceknownsymbols/.
			{conTri[a__]:> Total[{a}], conZero[a__]:> Total[{a}]}
		,
		x_/;!EvenQ[2*x]
		,
		{1}
	];

	If[Length[notfound]>0,result=False];

	Do[Message[consistencyCheck::halfinteger,TraditionalForm[conditions[[i]]]],{i,notfound}];

	(*Check that angular momentum quantum number and the correspondng
	 projection quantum number are both integers or both half-integers.*)
	conditions=Cases[expr,tj[__]|cg[__],{0,Infinity}];
	conditions=DeleteDuplicates@Flatten[conditions//.{			
			tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> conX@@@Map[removeSign,{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}},{2}],
			cg[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> conX@@@Map[removeSign,{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}},{2}]
		}];
	notfound=Flatten@Position[
			conditions//.replaceknownsymbols//.
				{conX[a_,\[Alpha]_]:>True /;
		((IntegerQ[2 a] && !IntegerQ[a]) && (IntegerQ[2 \[Alpha]] && !IntegerQ[\[Alpha]])) ||
		(IntegerQ[a]  &&  IntegerQ[\[Alpha]])
		(*Or@@(MemberQ[#,a] && MemberQ[#,\[Alpha]]&)/@{$integerQN,$halfintegerQN}*)
				}/. 
				{conX[___]-> False},
			False];
	conditions=conditions/.{conX[a_,b_]:> {a,b}};
	If[Length[notfound]>0,result=False];
	Do[Message[consistencyCheck::projection,
			TraditionalForm[conditions[[i]][[1]]],
			TraditionalForm[conditions[[i]][[2]]]
		],{i,notfound}];	

	Return[result];
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

conTri/:MakeBoxes[conTri[a__], fmt:TraditionalForm]:=
StyleBox[RowBox[{"\[EmptyUpTriangle]","{",Sequence@@(MakeBoxes[#,fmt]&/@{a}),"}"}],SpanMaxSize->\[Infinity]];
conZero/:MakeBoxes[conZero[a_,b_,c_], fmt:TraditionalForm]:=MakeBoxes[KroneckerDelta[a+b+c,0],fmt];

Global`varK/: MakeBoxes[Global`varK[a_], fmt:TraditionalForm]:=SubscriptBox["K",a];
Global`varL/: MakeBoxes[Global`varL[a_], fmt:TraditionalForm]:=SubscriptBox["L",a];
Global`varM/: MakeBoxes[Global`varM[a_], fmt:TraditionalForm]:=SubscriptBox["M",SubscriptBox["L",a]];
Utility`$indexed[Global`varK]=True;
Utility`$indexed[Global`varM]=True;
Utility`$indexed[Global`varL]=True;


sj/:MakeBoxes[sj[a__], fmt:TraditionalForm]:=MakeBoxes[SixJSymbol[a],fmt];
tj/:MakeBoxes[tj[a__], fmt:TraditionalForm]:=MakeBoxes[ThreeJSymbol[a],fmt];
sh/:MakeBoxes[sh[a__], fmt:TraditionalForm]:=MakeBoxes[SphericalHarmonicY[a],fmt];

(*SetAttributes[triX,Orderless]
SetAttributes[zeroX,Orderless]*)
SetAttributes[conTri,Orderless]
SetAttributes[conZero,Orderless]
SetAttributes[sjOL,Orderless]


(* ::Section:: *)
(*General Transformation Rules*)


(* ::Subsection:: *)
(*Preparation*)


prepareSumRules={
		sum[a_,b___]:> sum[a,set[b]] /;FreeQ[{b},set]
	};

prepareIntegrateRules={
		integrate[a_,b___]:> integrate[a,set[b]] /;FreeQ[{b},set]
	};

prepareSymbolOrderlessRules={
		sj[{a_,b_,c_},{d_,e_,f_}]:> sjOL[set[a,b,c],set[a,e,f],set[d,b,f],set[d,e,c]],
		nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> njOL[set[set[a,e,j],set[b,f,g],set[c,d,h]],set[set[a,b,c],set[d,e,f],set[g,h,j],set[a,d,g],set[b,e,h],set[c,f,j]]]
	};

prepareSHRules={
		Conjugate[sh[l_,ml_,\[Theta]_,\[Phi]_]]:> (-1)^ml sh[l,-ml,\[Theta],\[Phi]]
	};



(* ::Subsection:: *)
(*Simplification*)


simplifyFactorRules={
		(-1 b_)^a_:> mX[a](b)^a,
		(-1)^(a_):>mX[a],
		mX[a_ + b_]:> mX[a] mX[b],
		mX[n_Integer a_]:> mX[a]^n,
		mX[n_Integer]:> mX[1]^n /; n<-1 || n>1,
		mX[-a_]^n_:> mX[a]^(-n),
		mX[a_]^n_:> mX[a]^Mod[n,2] /; n!=0 && n!=1 && (MemberQ[$integerQN,Verbatim[a]] || IntegerQ[a]),
		mX[a_]^n_:> (-1)^(Floor[n/2])mX[a]^Mod[n,2] /; n!=0 && n!=1 && (MemberQ[$halfintegerQN,Verbatim[a]] || (IntegerQ[2 a] && !IntegerQ[a])),
		mX[a_]^0:> 1,
		mX[]-> 1,
		mX[0]-> 1,
		mX[1]->(-1),
		mX[-1]->(-1),
		mX[1/2]->(I),
		mX[-1/2]->(-I),
		Sqrt[a_./(2 x_+1)]:>Sqrt[a]/Sqrt[2 x+1],
		Sqrt[(2 x_+1)/a_]:>Sqrt[2 x+1]/Sqrt[a],
		Sqrt[(2 x_+1)(2 y_+1)]:>Sqrt[2 x+1]Sqrt[2 y+1]
	};

simplifyCollectSumRules={
		(*Shortest[a_] sum[b_,set[c__]]:> sum[a b,set[c]]/;FreeQAll[{a},{c}],*)
		sum[a_,set[u__]] sum[b_,set[v__]]:> sum[a b,set[u,v]]/;FreeQAll[{a},{v}]&&FreeQAll[{b},{u}]
	};

simplifyCollectIntegrateRules={
		a_ integrate[b_,set[c___]]:> integrate[a b,set[c]]/;FreeQAll[{a},{c}],
		integrate[a_,set[u___]] integrate[b_,set[v___]]:> integrate[a b,set[u,v]]/;FreeQAll[{a},{v}]&&FreeQAll[{b},{u}]
	};

simplifyConditionOrderlessRules={
		sjOL[set[a_,b_,c_],u__]conTri[a_,b_,c_]:> sjOL[set[a,b,c],u],
		njOL[u__,set[set[a_,b_,c_],v__]]conTri[a_,b_,c_]:> njOL[u,set[set[a,b,c],v]],
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]conTri[a_,b_,c_]:> tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}],
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]conZero[\[Alpha]_,\[Beta]_,\[Gamma]_]:> tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]
	};



(* ::Subsection:: *)
(*Cleanup*)


cleanupSumRules={
		sum[a_]:> a,
		sum[a_,set[]]:> a	
	};
cleanupFactorRules={
		mX[a_]:>(-1)^a,
		-(-1)^a_:> (-1)^(a+1),
		I (-1)^a_:> (-1)^(a+1/2)
	};
cleanupSymbolOrderlessRules={
		sjOL[set[a_,b_,c_],set[a_,e_,f_],set[d_,b_,f_],set[d_,e_,c_]]:> sj[{a,b,c},{d,e,f}],
		njOL[set[set[a_,e_,j_],set[b_,f_,g_],set[c_,d_,h_]],set[set[a_,b_,c_],set[d_,e_,f_],set[g_,h_,j_],set[a_,d_,g_],set[b_,e_,h_],set[c_,f_,j_]]]:> nj[{a,b,c},{d,e,f},{g,h,j}]
	};



(* ::Section::Closed:: *)
(*Rotation of Symbols (currently not used)*)


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


(* ::Subsubsection::Closed:: *)
(*OLD / NOT USED ANYMORE*)


simplify3jmRawRulesOLD={
		sum[m_. (-1)^(a_+\[Alpha]_)tj[{a_,-\[Alpha]_},{a_,\[Alpha]_},{c_,\[Gamma]_}],\[Alpha]_,u___]
			:> sum[m Sqrt[2 a+1]KroneckerDelta[c,0]KroneckerDelta[\[Gamma],0],u]
				/;FreeQAll[{m,u,a,c,\[Gamma]},{\[Alpha]}],
		sum[m_. (-1)^(p_+\[Psi]_+q_+\[Kappa]_)tj[{a_,\[Alpha]_},{p_,-\[Psi]_},{q_,\[Kappa]neg_}]tj[{p_,\[Psi]_},{q_,\[Kappa]_},{ap_,\[Alpha]p_}],\[Psi]_,\[Kappa]uns_,u___]
			:> sum[m (-1)^(a-\[Alpha])1/(2 a+1)KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],-\[Alpha]p],u]
				/;FreeQAll[{m,u,a,\[Alpha],ap,\[Alpha]p,p,q},{\[Psi],\[Kappa]uns}]&&ensureSignQ[\[Kappa],\[Kappa]neg,\[Kappa]uns],
		sum[m_. (-1)^(q_+\[Kappa]_)(2q_+1)tj[{a_,\[Alpha]_},{b_,\[Beta]_},{q_,-\[Kappa]_}]tj[{q_,\[Kappa]_},{a_,\[Alpha]p_},{b_,\[Beta]p_}],q_,\[Kappa]_,u___]
			:> sum[m (-1)^(a-\[Alpha]+b-\[Beta])KroneckerDelta[\[Beta],-\[Beta]p]KroneckerDelta[\[Alpha],-\[Alpha]p],u]
				/;FreeQAll[{m,u,a,\[Alpha],\[Alpha]p,b,\[Beta],\[Beta]p},{q,\[Kappa]}],
		sum[m_. (-1)^(p_+q_+r_+\[Psi]_+\[Kappa]_+\[Rho]_)tj[{p_,\[Psi]neg_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,\[Rho]neg_},{c_,\[Gamma]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]uns_,\[Rho]uns_,u___]
			:> sum[m tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]sj[{a,b,c},{r,p,q}],u]
				/;FreeQAll[{m,u,p,q,r,a,b,c,\[Alpha],\[Beta],\[Gamma]},{\[Kappa],\[Psi]uns,\[Rho]uns}]&&ensureSignQ[\[Psi],\[Psi]neg,\[Psi]uns]&&ensureSignQ[\[Rho],\[Rho]neg,\[Rho]uns],
		sum[m_. (-1)^(p_+q_+r_+s_+t_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_+\[Tau]_)tj[{p_,\[Psi]neg_},{a_,\[Alpha]_},{q_,\[Kappa]neg_}]tj[{q_,\[Kappa]_},{r_,\[Rho]neg_},{t_,\[Tau]neg_}]tj[{r_,\[Rho]_},{ap_,\[Alpha]p_},{s_,\[Sigma]neg_}]tj[{s_,\[Sigma]_},{p_,\[Psi]_},{t_,\[Tau]_}],\[Psi]uns_,\[Kappa]uns_,\[Rho]uns_,\[Sigma]uns_,\[Tau]uns_,u___]
			:> sum[m (-1)^(a+\[Alpha])/(2a+1)sj[{q,p,a},{s,r,t}]KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],-\[Alpha]p],u]
				/;FreeQAll[{m,u,p,q,r,s,t,a,ap,\[Alpha],\[Alpha]p},{\[Psi]uns,\[Kappa]uns,\[Rho]uns,\[Sigma]uns,\[Tau]uns}]&&ensureSignQ[\[Psi],\[Psi]neg,\[Psi]uns]&&ensureSignQ[\[Kappa],\[Kappa]neg,\[Kappa]uns]&&ensureSignQ[\[Rho],\[Rho]neg,\[Rho]uns]&&ensureSignQ[\[Sigma],\[Sigma]neg,\[Sigma]uns]&&ensureSignQ[\[Tau],\[Tau]neg,\[Tau]uns]
	};

simplify6jRawRulesOLD={
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


(* ::Subsubsection:: *)
(*3jm*)


simplify3jmRawRules={
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{0,0}]^n_.:> KroneckerDelta[a,b]KroneckerDelta[\[Alpha],-\[Beta]]/(Sqrt[2 a+1])^n (-1)^(n a - n \[Alpha]),		
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{0,\[Gamma]_}]^n_.:> KroneckerDelta[\[Gamma],0] KroneckerDelta[a,b]KroneckerDelta[\[Alpha],-\[Beta]]/(Sqrt[2 a+1])^n (-1)^(n a - n \[Alpha]),
		sum[(-1)^(a_+\[Alpha]_)tj[{a_,-\[Alpha]_},{a_,\[Alpha]_},{c_,\[Gamma]_}],\[Alpha]_]
			:> Sqrt[2 a+1]KroneckerDelta[c,0]KroneckerDelta[\[Gamma],0],
		sum[(-1)^(p_+\[Psi]_+q_+\[Kappa]_)tj[{a_,\[Alpha]_},{p_,-\[Psi]_},{q_,-\[Kappa]_}]tj[{p_,\[Psi]_},{q_,\[Kappa]_},{ap_,\[Alpha]p_}],\[Psi]_,\[Kappa]_]
			:> (-1)^(a-\[Alpha])1/(2 a+1)KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],-\[Alpha]p]conTri[a,p,q],
		sum[(-1)^(\[Xi]_)(2x_+1)tj[{a_,\[Alpha]_},{c_,\[Gamma]_},{x_,\[Xi]_}]tj[{x_,-\[Xi]_},{b_,\[Beta]_},{d_,\[Delta]_}]sj[{b_,d_,x_},{c_,a_,q_}],x_,\[Xi]_]
			:>sum[(-1)^(2a+b+d+q-var[1])tj[{a,\[Alpha]},{b,\[Beta]},{q,-var[1]}]tj[{q,var[1]},{d,\[Delta]},{c,\[Gamma]}],var[1]]
		(*sum[(-1)^(q_+\[Kappa]_)tj[{a_,\[Alpha]_},{b_,\[Beta]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{d_,\[Delta]_},{c_,\[Gamma]_}],\[Kappa]_]
			\[RuleDelayed]sum[(-1)^(2a+var[1]-var[2])(2 var[1]+1)tj[{a,\[Alpha]},{c,\[Gamma]},{var[1],-var[2]}]
				tj[{var[1],var[2]},{d,\[Delta]},{b,\[Beta]}]sj[{b,d,var[1]},{c,a,q}],set[var[1],var[2]]]
*)
		(*the last one takes a very long time when loading the package:*)
		(*,sum[(-1)^(p_+q_+r_+s_+t_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_+\[Tau]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{s_,\[Sigma]_}]tj[{s_,-\[Sigma]_},{d_,\[Delta]_},{t_,\[Tau]_}]tj[{t_,-\[Tau]_},{e_,\[Epsilon]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_,\[Sigma]_,\[Tau]_]
			:> sum[(-1)^(t-p-b-a-d-c+var[1]-var[2]+var[3]-var[4])(2 var[1]+1)(2 var[3]+1)
					tj[{a,\[Alpha]},{b,\[Beta]},{var[1],var[2]}]tj[{var[1],-var[2]},{e,\[Epsilon]},{var[3],-var[4]}]tj[{var[3],var[4]},{c,\[Gamma]},{d,\[Delta]}]
					sj[{a,b,var[1]},{r,p,q}]sj[{var[1],e,var[3]},{t,r,p}]sj[{var[3],c,d},{s,t,r}],
				var[1],var[2],var[3],var[4]]*)

	};
(*old rules that could be used in simplify3jmRawRules (which makes the whole thing extremely slow)
simplify3jmOldRules={
		sum[(-1)^(p_+q_+r_+\[Psi]_+\[Kappa]_+\[Rho]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_]
			:> tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]sj[{a,b,c},{r,p,q}],
		sum[(-1)^(p_+q_+r_+s_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{s_,\[Sigma]_}]tj[{s_,-\[Sigma]_},{d_,\[Delta]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_,\[Sigma]_]
			:> sum[(-1)^(s-a-d-q+var[1]-var[2])(2 var[1]+1)tj[{a,\[Alpha]},{var[1],-var[2]},{d,\[Delta]}]tj[{b,\[Beta]},{var[1],var[2]},{c,\[Gamma]}]sj[{a,var[1],d},{s,p,q}]sj[{b,var[1],c},{s,r,q}],var[1],var[2]]
};
*)

(*one needs to maintain the special symmetries here!*)
simplify3jmLongRules={
		sum[(-1)^(p_+q_+r_+\[Psi]_+\[Kappa]_+\[Rho]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_]
			:> tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]sj[{a,b,c},{r,p,q}],
		sum[(-1)^(p_+q_+r_+s_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{s_,\[Sigma]_}]tj[{s_,-\[Sigma]_},{d_,\[Delta]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_,\[Sigma]_]
			:> sum[(-1)^(s-a-d-q+var[1]-var[2])(2 var[1]+1)tj[{a,\[Alpha]},{var[1],-var[2]},{d,\[Delta]}]tj[{b,\[Beta]},{var[1],var[2]},{c,\[Gamma]}]sj[{a,var[1],d},{s,p,q}]sj[{b,var[1],c},{s,r,q}],var[1],var[2]],
		sum[(-1)^(p_+q_+r_+s_+t_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_+\[Tau]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{s_,\[Sigma]_}]tj[{s_,-\[Sigma]_},{d_,\[Delta]_},{t_,\[Tau]_}]tj[{t_,-\[Tau]_},{e_,\[Epsilon]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_,\[Sigma]_,\[Tau]_]
			:> sum[(-1)^(t-p-b-a-d-c+var[1]-var[2]+var[3]-var[4])(2 var[1]+1)(2 var[3]+1)tj[{a,\[Alpha]},{b,\[Beta]},{var[1],var[2]}]tj[{var[1],-var[2]},{e,\[Epsilon]},{var[3],-var[4]}]tj[{var[3],var[4]},{c,\[Gamma]},{d,\[Delta]}]sj[{a,b,var[1]},{r,p,q}]sj[{var[1],e,var[3]},{t,r,p}]sj[{var[3],c,d},{s,t,r}],var[1],var[2],var[3],var[4]],
		sum[(-1)^(p_+q_+r_+s_+t_+u_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_+\[Tau]_+\[Nu]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{s_,\[Sigma]_}]tj[{s_,-\[Sigma]_},{d_,\[Delta]_},{t_,\[Tau]_}]tj[{t_,-\[Tau]_},{e_,\[Epsilon]_},{u_,\[Nu]_}]tj[{u_,-\[Nu]_},{f_,\[Phi]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_,\[Sigma]_,\[Tau]_,\[Nu]_]
			:> sum[(-1)^(var[1]-var[2]+var[3]-var[4]+var[5]-var[6])(2 var[1]+1)(2 var[3]+1)(2 var[5]+1)tj[{a,\[Alpha]},{var[1],var[2]},{b,\[Beta]}]tj[{c,\[Gamma]},{var[3],var[4]},{d,\[Delta]}]tj[{e,\[Epsilon]},{var[5],var[6]},{f,\[Phi]}]tj[{var[1],-var[2]},{var[3],-var[4]},{var[5],-var[6]}]sj[{a,var[1],b},{r,q,p}]sj[{c,var[3],d},{t,s,r}]sj[{e,var[5],f},{p,u,t}]sj[{var[1],var[3],var[5]},{t,p,r}],var[1],var[2],var[3],var[4],var[5],var[6]]
};


(* ::Subsubsection:: *)
(*6J*)


simplify6jRawRules={
		sj[{a_,b_,0},{d_,e_,f_}]^n_.:> conTri[a,d,f] KroneckerDelta[a,b]KroneckerDelta[d,e]/(Sqrt[2 a+1]Sqrt[2d+1])^n (-1)^(n (a +e +f)),		
		sum[(2 x_+1)sj[{a_,b_,x_},{a_,b_,c_}],x_]
			:> (-1)^(2c)conTri[a,b,c],				
		sum[(-1)^(a_+b_+x_)(2 x_+1)sj[{a_,b_,x_},{b_,a_,c_}],x_]
			:> Sqrt[2a+1]Sqrt[2b+1]KroneckerDelta[c,0],
		sum[(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{a_,b_,q_}],x_]
			:> 1/(2p+1)KroneckerDelta[p,q]conTri[a,d,p]conTri[c,b,p],
		sum[(-1)^(p_+q_+x_)(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{b_,a_,q_}],x_]
			:> sj[{c,a,q},{d,b,p}],
		sum[(-1)^(a_+b_+c_+d_+e_+f_+p_+q_+r_+x_)(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{e_,f_,q_}]sj[{e_,f_,x_},{b_,a_,r_}],x_]
			:> sj[{p,q,r},{e,a,d}]sj[{p,q,r},{f,b,c}],
		sum[(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{e_,f_,q_}]sj[{e_,f_,x_},{a_,b_,r_}],x_]
			:> facX[x] nj[{a,f,r},{d,q,e},{p,c,b}],
		sum[(-1)^(a_+b_+c_+d_+e_+f_+g_+h_+p_+q_+r_+s_+x_)(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{e_,f_,q_}]sj[{e_,f_,x_},{g_,h_,r_}]sj[{g_,h_,x_},{b_,a_,s_}],x_]
			:> sum[(-1)^(2*var[1]+a+b+e+f)(2 var[1]+1)facX[x] nj[{s,h,b},{g,r,f},{a,e,var[1]}]sj[{b,f,var[1]},{q,p,c}]sj[{a,e,var[1]},{q,p,d}],var[1]],
		sum[(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{e_,f_,q_}]sj[{e_,f_,x_},{g_,h_,r_}]sj[{g_,h_,x_},{a_,b_,s_}],x_]
			:> sum[(2 var[1]+1) nj[{a,f,var[1]},{d,q,e},{p,c,b}]nj[{a,f,var[1]},{h,r,e},{s,g,b}],var[1]]
	};



(* ::Subsubsection:: *)
(*9J*)


simplify9jRawRules={
		nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,0}]^n_.:> KroneckerDelta[c,f]KroneckerDelta[g,h]sj[{a,b,c},{e,d,g}]^n /(Sqrt[2c+1]Sqrt[2g+1])^n (-1)^(n (b+c+d+g)),
		sum[(2 x_+1)nj[{a_,f_,x_},{d_,q_,e_},{p_,c_,b_}]sj[{a_,f_,x_},{e_,b_,s_}],x_]
			:> (-1)^(2s)sj[{a,b,s},{c,d,p}]sj[{c,d,s},{e,f,q}],
		sum[(2 x_+1)(2 y_+1) nj[{a_,b_,x_},{c_,d_,y_},{e_,f_,j_}]nj[{a_,b_,x_},{c_,d_,y_},{g_,h_,j_}],x_,y_]
			:> 1/((2e+1)(2f+1))KroneckerDelta[e,g]KroneckerDelta[f,h]conTri[a,c,e]conTri[b,d,h]conTri[g,f,j],
		sum[(-1)^(y_)(2 x_+1)(2 y_+1) nj[{a_,b_,x_},{c_,d_,y_},{e_,f_,j_}]nj[{a_,b_,x_},{c_,d_,y_},{g_,h_,j_}],x_,y_]
			:> (-1)^(2b+f+h)nj[{a,d,g},{c,b,h},{e,f,j}],
		sum[(-1)^(y_)(2 x_+1)(2 y_+1)nj[{a_,b_,x_},{c_,d_,y_},{p_,q_,r_}]sj[{x_,y_,r_},{j_,h_,g_}]sj[{a_,b_,x_},{h_,g_,e_}]sj[{c_,d_,y_},{j_,g_,f_}],x_,y_]
			:> (-1)^(a-b+d+e-j-p+r)nj[{e,b,h},{f,d,j},{p,q,r}]sj[{a,c,p},{f,e,g}],
(* infinite loop:*)
		sum[(-1)^(p_+q_-e_-f_)(2 x_+1)nj[{a_,b_,p_},{c_,d_,q_},{e_,f_,x_}]sj[{p_,q_,x_},{k_,l_,g_}]sj[{e_,f_,x_},{k_,l_,h_}],x_]
			:> sum[(-1)^(b+g-c-h)(2 var[1]+1) nj[{d,f,b},{q,k,g},{c,h,var[1]}]sj[{b,g,var[1]},{l,a,p}]sj[{c,h,var[1]},{l,a,e}],var[1]],
		sum[(-1)^(p_+q_-r_-s_)(2 x_+1)nj[{a_,b_,p_},{c_,d_,q_},{r_,s_,x_}]nj[{e_,f_,p_},{g_,h_,q_},{r_,s_,x_}],x_]
			:> sum[(-1)^(b+g-c-f)(2 var[1]+1) nj[{a,p,b},{r,e,g},{c,f,var[1]}]nj[{d,s,b},{q,h,g},{c,f,var[1]}],var[1]]

};


(* ::Subsection:: *)
(*Private Helper Functions Involving 3jm, 6j or 9j symbols*)


addConditions[expr_]:=Module[{},
	expr/.{tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:>tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]conZero[\[Alpha],\[Beta],\[Gamma]]/;\[Alpha]==0 || \[Beta]==0 || \[Gamma]==0
		}//.conZero[0,a_,b_]:>KroneckerDelta[a,b]
(*		
	conditions=extractConditions[expr];
	conditions=Cases[conditions,conTri[0,a_,b_]:> KroneckerDelta[a,b]];
	conditions=Select[conditions,FreeQ[expr,#]&&FreeQ[expr,(#/.KroneckerDelta[a_,b_]:>KroneckerDelta[-a,-b])]&];	
*)
];
(*
prepare3jmSignAll[expr_,{}]:=expr;
prepare3jmSign[expr_]:=expr/.{sum[a_,set[b___]]:>sum[prepare3jmSignAll[a,{b}],set[b]]};
prepare3jmSignAll[expr_,l_]:=Module[{tmpFunc,tmpRule,result,transFunc,compFunc},
	tmpFunc={
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]tj[{ap_,\[Alpha]p_},{bp_,\[Beta]p_},{cp_,\[Gamma]p_}]:>mX[a]mX[b]mX[c]tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]tj[{ap,\[Alpha]p},{bp,\[Beta]p},{cp,\[Gamma]p}]/;
		!FreeQ[{\[Alpha],\[Beta],\[Gamma]},#]&&!FreeQ[{\[Alpha]p,\[Beta]p,\[Gamma]p},#]&&OrderedQ[{tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}],tj[{ap,\[Alpha]p},{bp,\[Beta]p},{cp,\[Gamma]p}]}],
		tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]tj[{ap_,\[Alpha]p_},{bp_,\[Beta]p_},{cp_,\[Gamma]p_}]:>mX[a]mX[b]mX[c]tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]tj[{ap,\[Alpha]p},{bp,\[Beta]p},{cp,\[Gamma]p}]/;
		!FreeQ[{\[Alpha],\[Beta],\[Gamma]},#]&&!FreeQ[{\[Alpha]p,\[Beta]p,\[Gamma]p},#]&&!OrderedQ[{tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}],tj[{ap,\[Alpha]p},{bp,\[Beta]p},{cp,\[Gamma]p}]}]
	}&;	
	transFunc=ruleToFunction/@Flatten[tmpFunc/@l,1];	
	compFunc[newexpr_]:=30*Count[
							Cases[newexpr/.
								{tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> XX[\[Alpha]]XX[\[Beta]]XX[\[Gamma]]},
							XX[a_]^n_./;MemberQ[l,removeSign[a]],{0,Infinity}]
							,
							XX[_]^n_/;n>1
						]+LeafCount[newexpr];
	(*tmp=Flatten[tmpFunc/@l,1];*)
	result=Simplify[expr,TransformationFunctions->transFunc,ComplexityFunction->compFunc];
	(*Print[Trace[Simplify[expr,TransformationFunctions->transFunc,ComplexityFunction->compFunc]]];*)
	
	Return[result];	
];
*)
prepare3jmSign::wrongsign="Cannot correctly set 3jm signs.";
prepare3jmSign[expr_]:=expr/.{sum[a_,set[b___]]:>sum[prepare3jmSignHelper[a,{b}],set[b]]};
prepare3jmSignHelper[expr_,l_]:=Module[{tmp},
	tmp=prepare3jmSignAll[expr,{},l];
	If[!tmp[[1]],
		Message[prepare3jmSign::wrongsign];
		Return[expr],
	(*else*)
		Return[tmp[[2]]]
	];
]
prepare3jmSignAll[expr_,solved_,todo_]:=Module[{possible,i,chosen,succeed,result,tmp},
(*Print[StringForm["Called with: `` (solved) `` (todo)",solved,todo]];*)
	If[Length[todo]==0,Return[{True,expr}]];
	possible=DeleteDuplicates@Flatten[Cases[expr,tj[{a$X_,\[Alpha]$X_},{b$X_,\[Beta]$X_},{c$X_,\[Gamma]$X_}]/;!FreeQ[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},solved]:> {\[Alpha]$X,\[Beta]$X,\[Gamma]$X},{0,Infinity}],1];
	possible=Intersection[possible,todo];
	If[Length[possible]==0,possible=todo];
	succeed=False;
	i=1;
	While[!succeed,
		If[i>Length[possible], Break[]];
		chosen=possible[[i]];
		i=i+1;
(*Print[chosen];*)
		result=expr/.{
			(tj[{a$X_,\[Alpha]$X_},{b$X_,\[Beta]$X_},{c$X_,\[Gamma]$X_}]/;FreeQAll[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},solved]&&!FreeQ[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},chosen])
			(tj[{ap$X_,\[Alpha]p$X_},{bp$X_,\[Beta]p$X_},{cp$X_,\[Gamma]p$X_}]/;!FreeQ[{\[Alpha]p$X,\[Beta]p$X,\[Gamma]p$X},chosen]):>
				mX[a$X]mX[b$X]mX[c$X]tj[{a$X,-\[Alpha]$X},{b$X,-\[Beta]$X},{c$X,-\[Gamma]$X}]tj[{ap$X,\[Alpha]p$X},{bp$X,\[Beta]p$X},{cp$X,\[Gamma]p$X}]/;					
					!Xor[FreeQ[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},-chosen],FreeQ[{\[Alpha]p$X,\[Beta]p$X,\[Gamma]p$X},-chosen]]
			}//.simplifyFactorRules;
		tmp=Cases[result,X$X_
			(tj[{a$X_,\[Alpha]$X_},{b$X_,\[Beta]$X_},{c$X_,\[Gamma]$X_}]/;!FreeQ[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},chosen])
			(tj[{ap$X_,\[Alpha]p$X_},{bp$X_,\[Beta]p$X_},{cp$X_,\[Gamma]p$X_}]/;!FreeQ[{\[Alpha]p$X,\[Beta]p$X,\[Gamma]p$X},chosen])/;					
					!Xor[FreeQ[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},-chosen],FreeQ[{\[Alpha]p$X,\[Beta]p$X,\[Gamma]p$X},-chosen]],
				{0,Infinity}];
		If[Length[tmp]>0,
			Continue[];
		];
		If[Length[Cases[result,mX[chosen]]]==0,
			result=result/.{
			(tj[{a$X_,\[Alpha]$X_},{b$X_,\[Beta]$X_},{c$X_,\[Gamma]$X_}]/;FreeQAll[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},solved]&&!FreeQ[{\[Alpha]$X,\[Beta]$X,\[Gamma]$X},chosen])
			(tj[{ap$X_,\[Alpha]p$X_},{bp$X_,\[Beta]p$X_},{cp$X_,\[Gamma]p$X_}]/;!FreeQ[{\[Alpha]p$X,\[Beta]p$X,\[Gamma]p$X},chosen]):>
				mX[\[Alpha]$X]mX[\[Beta]$X]mX[\[Gamma]$X]tj[{a$X,\[Alpha]$X},{b$X,\[Beta]$X},{c$X,\[Gamma]$X}]tj[{ap$X,\[Alpha]p$X},{bp$X,\[Beta]p$X},{cp$X,\[Gamma]p$X}]
			};
		];
(*Print[StringForm["solved: `` -> ``",chosen,TraditionalForm[result]]];*)
		tmp=prepare3jmSignAll[result,Append[solved,chosen],DeleteCases[todo,chosen]];
		If[tmp[[1]]==True,
			succeed=True;
			result=tmp[[2]];
			(*,Print[StringForm["my bad, try again: ``",chosen]];*)
		];
	];
	If [succeed,
		Return[{True,result}],
		Return[{False,expr}]		
	];
];
(*
prepare3jmFactor::multiplesums="Expression has multiple sums. Cannot prepare factors";
prepare3jmFactor[expr_]:=Module[{variableList,sumExpr,finalSumExpr,transFunc,factorList,compFunc2,functions},
	variableList=Cases[expr,sum[__],{0,Infinity}];
	If[Length[variableList]>1,Message[prepare3jmFactor::multiplesums];Return[expr]];
	If[Length[variableList]==0,Return[expr]];
	sumExpr=variableList[[1]];
	variableList=sumExpr/.{sum[a_,set[b__]]:>{b}};
	factorList=Cases[extractConditions[sumExpr],conZero[a__]/;!FreeQAll[{a},variableList]]/.
		{conZero[a_,b_,c_]:>mX[a]mX[b]mX[c]};
	transFunc[i_]:=(#/.
					{sum[a$X_,set[b$X__]]:>sum[a$X factorList[[i]],set[b$X]] }//.
					simplifyFactorRules)&;
	compFunc2[newexpr_]:=-20 Count[newexpr,x_/;MemberQ[(mX/@variableList),x],{0,Infinity}]+LeafCount[newexpr];
	functions=Table[transFunc[i],{i,Length[factorList]}];
	finalSumExpr=Simplify[sumExpr,TransformationFunctions->functions,ComplexityFunction->compFunc2];
	Return[expr/.sumExpr->finalSumExpr];
];*)

cleanupNewVariables::undeclared="Cannot resolve the following conditions ``";
cleanupNewVariables[expr_]:=Module[{addOffset,result,constants,conditions},
	result=replaceUnique[expr,var,Global`varK];	
	(*addOffset=Length[DeleteDuplicates@Cases[expr,var[_],{0,Infinity}]];
	result=expr/.{var[i_]:> Global`varK[i+$offset]};
	$offset=$offset+addOffset;*)
	constants=DeleteDuplicates@Cases[result,Global`varK[_],{0,Infinity}];
	conditions=Select[extractConditions[result],!FreeQ[#,Global`varK]&];
	(*While[Length[conditions]>0,*)
		conditions=conditions//.{
			conZero[u__]:> conTri[u],
			conTri[-a_,b__]:> conTri[a,b],
			conTri[a_,b__]:> conTri[iX,b] /; (MemberQ[$integerQN,Verbatim[a]] || IntegerQ[a]),
			conTri[a_,b__]:> conTri[hX,b] /; (MemberQ[$halfintegerQN,Verbatim[a]] || (IntegerQ[2*a] && !IntegerQ[a])),
			conTri[hX,hX,Global`varK[i_]]:> Module[{},declareQNInteger[Global`varK[i]];Sequence[]],
			conTri[iX,iX,Global`varK[i_]]:> Module[{},declareQNInteger[Global`varK[i]];Sequence[]],
			conTri[iX,hX,Global`varK[i_]]:> Module[{},declareQNHalfInteger[Global`varK[i]];Sequence[]],
			conTri[hX,hX,iX]:> Sequence[],
			conTri[iX,iX,iX]:> Sequence[]
		};
	conditions=Cases[conditions,conTri[__]];
	If[Length[conditions]>0,Message[cleanupNewVariables::undeclared,conditions]];
	(*];*)
(*Select[,con_/;!FreeQ[con,constantK]];*)

	Return[result];
]

createAlternativeRules3jm::error="Could not process rule `1`";
createAlternativeRules3jm[rule_]:=Module[{ruleList,rulePattern,ruleResult,rulePatternList},
	ruleList=ruleSplit[rule];
	rulePattern=ruleList[[2]];
	rulePatternList=rulePattern/.
		{tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> alternative[tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}],(-1)^(a+b+c)tj[{b,\[Beta]},{a,\[Alpha]},{c,\[Gamma]}]]}/.
		alternative-> List;
	If[Head[rulePatternList]===List,
		Return[ruleJoin[ReplacePart[ruleList,2-> #]]&/@rulePatternList];			
		,
		Message[createAlternativeRules3jm::error,rule];
		Return[{rule}];
	];
];

createAlternativeRules9j::error="Could not process rule `1`";
createAlternativeRules9j[rule_]:=Module[{ruleList,rulePattern,ruleResult,rulePatternList},
	ruleList=ruleSplit[rule];
	rulePattern=ruleList[[2]];
	rulePatternList=rulePattern/.
		{nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> alternative[nj[{a,b,c},{d,e,f},{g,h,j}],(-1)^(a+b+c+d+e+f+g+h+j)nj[{a,b,c},{g,h,j},{d,e,f}]]}/.
		alternative-> List;
	If[Head[rulePatternList]===List,
		Return[ruleJoin[ReplacePart[ruleList,2-> #]]&/@rulePatternList];			
		,
		Message[createAlternativeRules9j::error,rule];
		Return[{rule}];
	];
];

facX[]:=1;
facX[a_]:=1/;MemberQ[$integerQN,Verbatim[a]];
facX[a_]:=-1/;MemberQ[$halfintegerQN,Verbatim[a]];

refineSymbolRule::ruletype="Cannot handle a non-delayed rule";
refineSymbolRule::wrongfactors="Rule `1` is missing a factor.";
Options[refineSymbolRule]={Include3jm->True}
refineSymbolRule[rule_,OptionsPattern[]]:=Module[{
			ruleList,ruleType,rulePattern,ruleResult,ruleConditon,ruleConditionList,
			m,u,
			variables,summation,invertVariables,
			tmp,result,
			tmpList,tmpRule,tmpFunc,countMX,counts
		},
(*preparing factors and the sum expression*)
	result=rule//.prepareSumRules//.simplifyFactorRules//.prepareSymbolOrderlessRules;

(*splitting the rule into individual parts*)
	ruleList=ruleSplit[result];
	ruleType=ruleList[[1]];
	rulePattern=ruleList[[2]];
	ruleResult=ruleList[[3]];

(*We can only handle delayed rules with / without a condition. 
If no condition is present we will surely add one during this function*)
	If[ruleType=="r" || ruleType=="rc",
		Message[refineSymbolRule::ruletype]; 
		Return[result];
	];
	If[ruleType=="rdc",
		ruleConditionList={ruleList[[4]]};
	,
		ruleConditionList={};
		If[ruleType=="rd", ruleType="rdc"]; (*rule type must handle a condition*)
	];

(*Add condition: All other variables must be free of the summation variables*)
	variables=getAllVariables[rulePattern];
	If[FreeQ[rulePattern,sum],
		summation={},
		(*else*)
		summation=removeBlanks/@(rulePattern/.sum[a_,set[b___]]:> {b})
	];
	AppendTo[variables,m];AppendTo[variables,u];
	variables=Complement[variables,summation];
	AppendTo[ruleConditionList,fqa[variables,summation]/.
			{fqa[a_,b_]:> Hold[FreeQAll[a,b]]}
	];

(*We add "m_." and "u___" that match additional unrelated factors and summation variables, respectively*)
	If[FreeQ[rulePattern,sum],
		rulePattern=sum[rulePattern,set[]];
	];
	rulePattern=rulePattern/.
		sum[a_,set[b___]]:>sum[Optional[pat[m,Blank[]]]a,set[b,pat[u,BlankNullSequence[]]]]/.
		pat-> Pattern;
	If[FreeQ[ruleResult,sum],
		ruleResult=Replace[ruleResult,Hold[a_]:> Hold[sum[a,set[]]]];
	];
	ruleResult=ruleResult/.
		sum[a_,set[b___]]:>sum[m a,set[b,u]];
If[OptionValue[Include3jm],

(*We also add alternatives to accept versions with a minus sign (3jm only)*)
	(*select variables that might have minus signs*)
	invertVariables=DeleteDuplicates@removeBlanks@Flatten[Cases[rulePattern,tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> removeSign/@{\[Alpha],\[Beta],\[Gamma]},{0,Infinity}],1];
	invertVariables=Intersection[invertVariables,summation];
	(*Check for correct factors - for every of the selected variables a mX[<variable>] must be present*)
	countMX=Count[rulePattern,Verbatim[mX[Pattern[#,Blank[]]]],{0,Infinity}]&;
	counts=countMX/@invertVariables;
	counts=counts/.{1-> True,_Integer->False};
	If[!And@@counts,Message[refineSymbolRule::wrongfactors,rule]];
	(*create rules to transform patterns, results and conditions using the special matching procedure for these variables*)
	(*we ignore the first element in the list: it would duplicate rules*)
	If[Length[invertVariables]>0,
		invertVariables=Drop[invertVariables,1]
	];
		(*starting with the result*)
	tmpList[1]=Times@@(facX[ToExpression[ToString[#]<>"neg"]]&/@invertVariables);
	tmpRule[1]=(sum[a_,set[b___]]:> sum[a #,set[b]]&)[tmpList[1]];	
	ruleResult=ruleResult/.tmpRule[1];
		(*changing the pattern*)
	tmpList[2]=unsM[#]&/@invertVariables;
	tmpRule[2]=({sum[a_,set[Sequence@@(Verbatim[Pattern[#,Blank[]]]&/@invertVariables),b___]]:>sum[a,set[##,b]]})&[Sequence@@tmpList[2]];
	tmpFunc[2]={Verbatim[mX[Pattern[#,Blank[]]]]:>mX[unsM[#]],-Verbatim[Pattern[#,Blank[]]]:>speM[-#],Verbatim[Pattern[#,Blank[]]]:>speM[#]}&;
	rulePattern=rulePattern/.tmpRule[2]/.Flatten[tmpFunc[2]/@invertVariables,1];
		(*changing the conditions*)
	tmpFunc[3]=Rule[#,Sequence[ToExpression[ToString[#]<>"pos"],ToExpression[ToString[#]<>"neg"]]]&;
	tmpRule[3]=tmpFunc[3]/@invertVariables;
	ruleConditionList=ruleConditionList/.tmpRule[3];

(*Match all even permutations of 3jm symbols*)
	rulePattern=rulePattern/.{tj[a__]:> evenPermM[tj[a]]};
];
(*Construct the condition and the resulting rule*)		
	ruleConditon=First[ruleConditionList//.{Hold[a_],Hold[b_],c___}:> {Hold[(a) && (b)],c}];
	result=ruleJoin[{ruleType,rulePattern,ruleResult,ruleConditon}];	
	
(*Return normalized version *)	
	Return[normalizeSumRule[result]];	
];


(* ::Subsection:: *)
(*Expanded Rules*)


simplifySymbolRules=refineSymbolRule/@Join[
		simplify6jRawRules,
		Flatten[createAlternativeRules9j/@simplify9jRawRules,1],
		Flatten[createAlternativeRules3jm/@simplify3jmRawRules,1]
	];
simplifySymbolRulesDispatch=Dispatch[simplifySymbolRules];
(*simplifySymbolRules//TraditionalForm*)


(* ::Subsection:: *)
(*Functions*)


find3jmCycles[expr_]:=Module[{result={},
		summation,symbols,vars,removeSymbols,
		graph,vertices,edges,allloops,loopLength,loop,loopVertices,loopVars,
		tmp,tmpfun,tmprule,
		tjrule,tjrulereplace},
(*
DeleteDuplicates@Flatten@
*)
	summation=DeleteDuplicates@Flatten@Cases[expr,sum[_,set[y__]]|sum[_,y__]:>{y},{0,Infinity}];
	symbols=Cases[expr,tj[___],Infinity];
	vars=symbols//.tj[{_,\[Alpha]_},{_,\[Beta]_},{_,\[Gamma]_}]:>removeSign/@{\[Alpha],\[Beta],\[Gamma]};
(*removeSymbols=Flatten[(#[[1]]&)/@Select[Tally[Flatten[symbols]],#[[2]]\[NotEqual]2&]];
tmpfun=!FreeQAll[#,summation]&&FreeQAll[#,removeSymbols]&;
edges=(Select[#,tmpfun]&)/@symbols;
edges=Select[edges,Length[#]>0&];*)
	edges=Flatten[(#[[1]]&)/@Select[Tally[Flatten[vars]],#[[2]]==2&&!FreeQ[summation,#[[1]]]&]];
	tmpfun[sym_]:=(!FreeQ[#,sym]&);
	edges=({Select[symbols,tmpfun[#]],#}&)/@edges;
	edges=Labeled[#[[1]][[1]]<->#[[1]][[2]],#[[2]]]&/@edges;
	graph=Graph[symbols,edges,VertexLabels->"Name"];
(*
Print[graph];
*)
	allloops=FindCycle[graph,Infinity,All];
	loopLength=Min[Length/@allloops];
	If[loopLength<3 || loopLength>6,
		Return[expr]
	];
	loop=Select[allloops,(Length[#]==loopLength)&][[1]];
(*
Print[loop];
*)
	loopVertices=loop//.a_<->b_:>a;
	loopVars=loop//.tj[{_,\[Alpha]_},{_,\[Beta]_},{_,\[Gamma]_}]:>set@@removeSign/@{\[Alpha],\[Beta],\[Gamma]};
	loopVars=loopVars//.set[a_,__]<->set[a_,__]/;!FreeQ[summation,a]:>a;
(*
Print[loopVertices];
Print[loopVars];
*)
	tmp={};
	For[i=1,i<=Length[loopVars],i++,
		AppendTo[tmp,{loopVertices[[i]],loopVars[[-1]],loopVars[[1]]}];
		loopVars=RotateLeft[loopVars];
	];
	tmprule[{tjexpr_,sleft_,sright_}]:=tjexpr/.{
		tj[{a_,\[Alpha]_/;!FreeQ[\[Alpha],sleft]},{b_,\[Beta]_},{c_,\[Gamma]_/;!FreeQ[\[Gamma],sright]}]:>(tjexpr->tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]),
		tj[{a_,\[Alpha]_/;!FreeQ[\[Alpha],sleft]},{c_,\[Gamma]_/;!FreeQ[\[Gamma],sright]},{b_,\[Beta]_}]:>(tjexpr->tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]AngularMomentum`Private`mX[a]AngularMomentum`Private`mX[b]AngularMomentum`Private`mX[c]),
		tj[{b_,\[Beta]_},{a_,\[Alpha]_/;!FreeQ[\[Alpha],sleft]},{c_,\[Gamma]_/;!FreeQ[\[Gamma],sright]}]:>(tjexpr->tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]AngularMomentum`Private`mX[a]AngularMomentum`Private`mX[b]AngularMomentum`Private`mX[c]),
		tj[{c_,\[Gamma]_/;!FreeQ[\[Gamma],sright]},{a_,\[Alpha]_/;!FreeQ[\[Alpha],sleft]},{b_,\[Beta]_}]:>(tjexpr->tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]),
		tj[{b_,\[Beta]_},{c_,\[Gamma]_/;!FreeQ[\[Gamma],sright]},{a_,\[Alpha]_/;!FreeQ[\[Alpha],sleft]}]:>(tjexpr->tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]),
		tj[{c_,\[Gamma]_/;!FreeQ[\[Gamma],sright]},{b_,\[Beta]_},{a_,\[Alpha]_/;!FreeQ[\[Alpha],sleft]}]:>(tjexpr->tj[{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}]AngularMomentum`Private`mX[a]AngularMomentum`Private`mX[b]AngularMomentum`Private`mX[c])
	};
(*
Print[tmp];
Print[tmprule/@tmp];
*)
	result=expr//.(tmprule/@tmp);
	
	For[i=1,i<=Length[loopVars],i++,		
		If[Length[Cases[result,tj[{_,loopVars[[i]]},__],{0,Infinity}]]>0,
			result=result/.loopVars[[i]]->-loopVars[[i]];
		];
	];
	result=result//.AngularMomentum`Private`simplifyFactorRules;
	tjrule=AngularMomentum`Private`simplify3jmLongRules[[loopLength-2]];
	(*
tjrulereplace=Thread[Verbatim/@
		{Pattern[AngularMomentum`Private`\[Psi],Blank[]],AngularMomentum`Private`\[Kappa]_,AngularMomentum`Private`\[Rho]_,AngularMomentum`Private`\[Sigma]_,AngularMomentum`Private`\[Tau]_,AngularMomentum`Private`\[Nu]_}[[1;;loopLength]]->RotateRight[loopVars]];
*)
	tjrulereplace=Thread[Verbatim[Pattern[#,Blank[]]]&/@
		{AngularMomentum`Private`\[Psi],AngularMomentum`Private`\[Kappa],AngularMomentum`Private`\[Rho],AngularMomentum`Private`\[Sigma],AngularMomentum`Private`\[Tau],AngularMomentum`Private`\[Nu]}[[1;;loopLength]]->RotateRight[loopVars]];
(*
Print[tjrulereplace];
*)
	tjrule=tjrule//.tjrulereplace;
(*
Print[TraditionalForm[tjrule]];
*)
	tjrule=AngularMomentum`Private`refineSymbolRule[tjrule,Include3jm->False];
(*
Print[TraditionalForm[tjrule]];
*)
	Return[result/.tjrule];
];


Options[simplifyAMSum]={Print->False,Timing-> False,TimingComplete->False,IgnoreSums->{},OnlySums->{},NoSymbols->False};
simplifyAMSum[expr_,OptionsPattern[]]:=Module[{
		prev,result,ignoredPart,ignored,onlysums,summation,used,
		prepareRules=Join[prepareSumRules,prepareSymbolOrderlessRules,simplifyCollectSumRules,simplifySumRules,simplifyFactorRules],
		simplifyRules=Join[simplifyFactorRules,simplifySumRules,simplifyConditionOrderlessRules],
		cleanupRules=Join[cleanupSumRules,cleanupFactorRules,cleanupSymbolOrderlessRules],
		cleanupFn,
		t1,t2,t3,t4,tmp
	},
	If[OptionValue[NoSymbols],
		Return[toTJ[expr]//.prepareRules//.simplifyRules//.cleanupRules];
	];
	cleanupFn=(*If[Length[ignored]==0,
		#//.simplifyRules//.cleanupRules,*)
		ignoredPart/.{sum[a_,set[u___]]:> sum[a #,set[u]]}//.simplifyRules//.cleanupRules
		(*]*)&;
	consistencyCheck[expr];
	result=toTJ[expr]//.prepareRules;
	ignored=OptionValue[IgnoreSums];
	onlysums=OptionValue[OnlySums];
	summation=Flatten[Cases[result,sum[a_,set[u__]]:> {u},{0,Infinity}]];
	If[Length[onlysums]>0,
		ignored=Complement[summation,onlysums];
	];
	ignored=Intersection[summation,ignored];
	used=Complement[summation,ignored];

	(*Print[summation];
	Print[ignored];
	Print[used];	*)
	(*If[Length[ignored]>0,*)
		
		tmp={result/.sum[a_,set[u___]]:>a,sum[1,set@@used],sum[1,set@@ignored]};
		tmp=tmp//.{
				{Shortest[x_] y_.,sum[a_,set[u___]],sum[b_,set[v___]]}:>{y,sum[a,set[u]],sum[x b,set[v]]}/;FreeQAll[x,Join[used,onlysums]],
				{Shortest[x_] y_.,sum[a_,set[u___]],sum[b_,set[v___]]}:>{y,sum[x a,set[u]],sum[b,set[v]]}/;!FreeQAll[x,Join[used,onlysums]]
			};
		result=tmp[[2]];
		ignoredPart=tmp[[3]];
(*		Print[TraditionalForm[tmp[[1]]]];
		Print[TraditionalForm[tmp[[2]]]];
		Print[TraditionalForm[tmp[[3]]]];
		Print[TraditionalForm[result]];
		Return[expr];
		Print[TraditionalForm[result]];
		Print[TraditionalForm[ignoredPart]];*)
(*	];	*)
	prev=None;
	While[prev=!=result,
		(*result=addConditions[result];*)
		$lastexpression=cleanupFn[result];
		If[Length[onlysums]>0,
			summation=Flatten[Cases[result,sum[a_,set[u__]]:> {u},{0,Infinity}]];
			ignored=Complement[summation,onlysums];
			ignored=Intersection[summation,ignored];
			used=Complement[summation,ignored];
			tmp={result/.sum[a_,set[u___]]:>a,sum[1,set@@used],ignoredPart/.{sum[a_,set[u___]]:> sum[a ,set@@Union[{u},ignored]]} };
			tmp=tmp//.{
				{Shortest[x_] y_.,sum[a_,set[u___]],sum[b_,set[v___]]}:>{y,sum[a,set[u]],sum[x b,set[v]]}/;FreeQAll[x,Join[used,onlysums]],
				{Shortest[x_] y_.,sum[a_,set[u___]],sum[b_,set[v___]]}:>{y,sum[x a,set[u]],sum[b,set[v]]}/;!FreeQAll[x,Join[used,onlysums]]
			};
			result=tmp[[2]];
			ignoredPart=tmp[[3]];
		];
		If[OptionValue[Print],
			(*If[Length[ignored]>0,*)
				Print[
					TraditionalForm[$lastexpression],
					"working on:",
					TraditionalForm[result//.cleanupRules]
				](*,
				Print[TraditionalForm[$lastexpression]]
			]*)
		];
		prev=result;
		tmp=Timing[prepare3jmSign[prev]];
		t1=tmp[[1]];
		result=tmp[[2]];
		(*result=addConditions[result];*)
		If[OptionValue[TimingComplete],Print[StringForm["prepared 3jm signs :`` ",t1]]];
		tmp=Timing[result//.simplifyRules];		
		t2=tmp[[1]];
		result=tmp[[2]];
		If[OptionValue[TimingComplete],Print[StringForm["pre-simplification :`` ",t2]]];
		If[OptionValue[TimingComplete],Print[StringForm["`` ",result]]];
		tmp=Timing[cleanupNewVariables[find3jmCycles[result]]];
		If[tmp[[2]]===result,
			tmp=Timing[cleanupNewVariables[result/.simplifySymbolRulesDispatch]]			
		];		
		t3=tmp[[1]];
		result=tmp[[2]];
		If[OptionValue[Timing]||OptionValue[TimingComplete],
			If[t1+t2+t3>0,
				Print[StringForm["Timing: ``  ``  `` (``%  ``%  ``%)",t1,t2,t3,100*t1/(t1+t2+t3),100*t2/(t1+t2+t3),100*t3/(t1+t2+t3)]];
				,
				Print["Timing :0"];
			];
		];
		result=result//.simplifyRules;
	];	
	Return[cleanupFn[result]];
];

getLastExpression:=$lastexpression;


expand9j[expr_]:=Module[{result,symbols9j,sym,rhs},
	result=expr;
	symbols9j=DeleteDuplicates@Cases[result,nj[__],{0,Infinity}];
	For[i=1,i<=Length[symbols9j],i++,
		sym=symbols9j[[i]];
		rhs=sym/.{nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:>sum[(-1)^(2 var[1])(2 var[1]+1)
				sj[{a,b,c},{f,j,var[1]}]sj[{d,e,f},{b,var[1],h}]sj[{g,h,j},{var[1],a,d}],set[var[1]]]
		};
		rhs=replaceUnique[rhs,var,Global`varK];
		result=result/.sym->rhs;
	];
	result=simplifySumIntegrate[result];
	Return[result];
];


(* ::Section:: *)
(*Simplifying Integrals with Spherical Harmonics*)


(* ::Subsection:: *)
(*Raw Rules*)


simplifySHRawRules={
	integrate[sh[l_,ml_,\[Theta]_,\[Phi]_]Sin[\[Theta]_],\[Theta]_,\[Phi]_]:> Sqrt[4 \[Pi]] KroneckerDelta[l,0]KroneckerDelta[ml,0],
	integrate[sh[l1_,ml1_,\[Theta]_,\[Phi]_]sh[l2_,ml2_,\[Theta]_,\[Phi]_]Sin[\[Theta]_],\[Theta]_,\[Phi]_]:> (-1)^ml2 KroneckerDelta[l1,l2]KroneckerDelta[ml1,-ml2],
	integrate[sh[l1_,ml1_,\[Theta]_,\[Phi]_]sh[l2_,ml2_,\[Theta]_,\[Phi]_]sh[l3_,ml3_,\[Theta]_,\[Phi]_]Sin[\[Theta]_],\[Theta]_,\[Phi]_]:> Sqrt[2l1+1]Sqrt[2l2+1]Sqrt[2l3+1]/Sqrt[4\[Pi]]tj[{l1,ml1},{l2,ml2},{l3,ml3}]tj[{l1,0},{l2,0},{l3,0}],
    integrate[Sin[\[Theta]_],\[Theta]_,\[Phi]_]:> 4 \[Pi]
};


(* ::Subsection:: *)
(*Private Helper Functions*)


cleanupNewSHVariables[expr_]:=Module[{result,variables},
	result=replaceUnique[expr,varl,Global`varL];
	result=replaceUnique[result,varm,Global`varM];	
	declareQNInteger[DeleteDuplicates@Cases[result,Global`varL[_]|Global`varM[_],{0,Infinity}]];
	Return[result];
];

refineSHRule::ruletype="Cannot handle a non-delayed rule";
refineSHRule[rule_]:=Module[{
			ruleList,ruleType,rulePattern,ruleResult,ruleConditon,ruleConditionList,
			m,u,
			variables,integration,result			
		},
(*preparing factors and the sum expression*)
	result=rule//.prepareIntegrateRules;

(*splitting the rule into individual parts*)
	ruleList=ruleSplit[result];
	ruleType=ruleList[[1]];
	rulePattern=ruleList[[2]];
	ruleResult=ruleList[[3]];

(*We can only handle delayed rules with / without a condition. 
If no condition is present we will surely add one during this function*)
	If[ruleType=="r" || ruleType=="rc",
		Message[refineSHRule::ruletype]; 
		Return[result];
	];
	If[ruleType=="rdc",
		ruleConditionList={ruleList[[4]]};
	,
		ruleConditionList={};
		If[ruleType=="rd", ruleType="rdc"]; (*rule type must handle a condition*)
	];

(*Add condition: All other variables must be free of the summation variables*)
	variables=getAllVariables[rulePattern];
	integration=removeBlanks/@(rulePattern/.integrate[a_,set[b___]]:> {b});
	AppendTo[variables,m];AppendTo[variables,u];
	variables=Complement[variables,integration];
	AppendTo[ruleConditionList,fqa[variables,integration]/.
			{fqa[a_,b_]:> Hold[FreeQAll[a,b]]}
	];

(*We add "m_." and "u___" that match additional unrelated factors and summation variables, respectively*)
	rulePattern=rulePattern/.
		integrate[a_,set[b___]]:>integrate[Optional[pat[m,Blank[]]]a,set[b,pat[u,BlankNullSequence[]]]]/.
		pat-> Pattern;
	If[FreeQ[ruleResult,integrate],
		ruleResult=Replace[ruleResult,Hold[a_]:> Hold[integrate[a,set[]]]];
	];
	ruleResult=ruleResult/.
		integrate[a_,set[b___]]:>integrate[m a,set[b,u]];

(*Construct the condition and the resulting rule*)		
	ruleConditon=First[ruleConditionList//.{Hold[a_],Hold[b_],c___}:> {Hold[(a) && (b)],c}];
	result=ruleJoin[{ruleType,rulePattern,ruleResult,ruleConditon}];	
	
(*Return result *)	
	Return[result];	
];


(* ::Subsection:: *)
(*Expanded Rules*)


simplifySHRulesIntegrate=refineSHRule/@simplifySHRawRules;
simplifySHRulesProduct={
	sh[l1_,m1_,\[Theta]_,\[Phi]_]sh[l2_,m2_,\[Theta]_,\[Phi]_]:>
		sum[1/Sqrt[4\[Pi]]Sqrt[2l1+1]Sqrt[2l2+1]/Sqrt[2 varl[1]+1]
		cg[{l1,0},{l2,0},{varl[1],0}]cg[{l1,m1},{l2,m2},{varl[1],varm[1]}]
		sh[varl[1],varm[1],\[Theta],\[Phi]],set[varl[1],varm[1]]]
};
simplifySHRules={
	sh[l1_,m1_,\[Theta]_,\[Phi]_]sh[l2_,m2_,\[Theta]_,\[Phi]_]sh[l3_,m3_,\[Theta]_,\[Phi]_]sh[l4_,m4_,\[Theta]_,\[Phi]_]:>
		sum[1/Sqrt[4\[Pi]]Sqrt[2l1+1]Sqrt[2l2+1]/Sqrt[2 varl[1]+1]
		cg[{l1,0},{l2,0},{varl[1],0}]cg[{l1,m1},{l2,m2},{varl[1],varm[1]}]
		sh[varl[1],varm[1],\[Theta],\[Phi]]sh[l3,m3,\[Theta],\[Phi]]sh[l4,m4,\[Theta],\[Phi]],set[varl[1],varm[1]]],
	sh[l1_,m1_,\[Theta]_[r1_+r2_],\[Phi]_[r1_+r2_]]sh[l2_,m2_,\[Theta]_[r1_+r2_],\[Phi]_[r1_+r2_]]:>
		sum[1/Sqrt[4\[Pi]]Sqrt[2l1+1]Sqrt[2l2+1]/Sqrt[2 varl[1]+1]
		cg[{l1,0},{l2,0},{varl[1],0}]cg[{l1,m1},{l2,m2},{varl[1],varm[1]}]
		sh[varl[1],varm[1],\[Theta][r1+r2],\[Phi][r1+r2]],set[varl[1],varm[1]]],
	sh[l1_,m1_,\[Theta]_[a_ r_],\[Phi]_[a_ r_]]:>sh[l1,m1,\[Theta][r],\[Phi][r]]/;NumericQ[a]&&a>0,
	sh[l1_,m1_,\[Theta]_[a_ r_],\[Phi]_[a_ r_]]:>(-1)^l1 sh[l1,m1,\[Theta][r],\[Phi][r]]/;NumericQ[a]&&a<0,
	sh[l1_,m1_,\[Theta]_[-a_. r_],\[Phi]_[-a_. r_]]:>(-1)^l1 sh[l1,m1,\[Theta][r],\[Phi][r]]/;NumericQ[a]&&a>0,
	sh[l1_,m1_,\[Theta]_[-r_],\[Phi]_[-r_]]:>(-1)^l1 sh[l1,m1,\[Theta][r],\[Phi][r]],
	sh[l1_,m1_,\[Theta]_[a_+b_],\[Phi]_[a_+b_]]sh[l2_,m2_,\[Theta]_[c_+d_],\[Phi]_[c_+d_]]/; Not[Or[And[a === c, b === d], And[a === d, b === b]]]:>
	shkeep[l1,m1,\[Theta][a+b],\[Phi][a+b]]sh[l2,m2,\[Theta][c+d],\[Phi][c+d]],
	shkeep->sh,
	sh[l1_,m1_,\[Theta]_[r1_+r2_],\[Phi]_[r1_+r2_]]:>
		sum[sh[varl[1],varm[1],\[Theta][r1],\[Phi][r1]]sh[l1-varl[1],varm[2],\[Theta][r2],\[Phi][r2]]
		Sqrt[4\[Pi] Binomial[2 l1 +1,2 varl[1]]]/Sqrt[2 varl[1]+1]
		Abs[r1]^varl[1] Abs[r2]^(l1-varl[1])Abs[r1+r2]^(-l1)
		cg[{varl[1],varm[1]},{l1-varl[1],varm[2]},{l1,m1}]
			,set[varl[1],varm[1],varm[2]]]
};


(* ::Subsection:: *)
(*Functions*)


Options[simplifySHIntegral]={Integrate->False,IgnoreIntegrals->{},OnlyIntegrals->{},ReduceProducts->False,Print->False};
simplifySHIntegral[expr_,OptionsPattern[]]:=Module[{
		prepareRules=Join[prepareIntegrateRules,prepareSumRules,prepareSHRules],
		simplifyRules=Join[simplifyFactorRules,simplifySumRules,simplifyIntegrateRules,simplifyConditionOrderlessRules],
		cleanupRules=Join[cleanupSumRules,cleanupFactorRules,cleanupSymbolOrderlessRules],
		result,prev,rulesInUse,
		ignoreIntegrals,onlyIntegrals
	},
	ignoreIntegrals=OptionValue[IgnoreIntegrals];
	onlyIntegrals=OptionValue[OnlyIntegrals];
	rulesInUse=simplifySHRules;	
	If[OptionValue[Integrate],
		rulesInUse=Join[rulesInUse,simplifySHRulesIntegrate];
	];
	If[OptionValue[ReduceProducts],
		rulesInUse=Join[simplifySHRulesProduct,rulesInUse];
	];
	result=toTJ[expr//.prepareRules//.simplifyRules];
	prev=None;
	While[prev=!=result,
		prev=result;
		If[OptionValue[Print],
			Print[result//TraditionalForm];
		];
		If[Length[onlyIntegrals]>0,
			result=keepNotInvolving[result,Sequence@@onlyIntegrals,OnlyHeads->{sh}],
			result=keepInvolving[result,Sequence@@ignoreIntegrals,OnlyHeads->{sh}]
		];
		result=toTJ[keepClean[ReplaceAll[result,rulesInUse]]];	
		result=cleanupNewSHVariables[result];
		result=result//.simplifyRules;		
	];
	Return[result//.cleanupRules];
];


(* ::Section:: *)
(*Package Cleanup*)


End[]


EndPackage[]
