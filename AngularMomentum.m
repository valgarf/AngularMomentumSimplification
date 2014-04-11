(* ::Package:: *)

(* ::Section:: *)
(*Package Initialise*)


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
"simplifyAMSum[expr] can simplify sums of 3j, 6j, and 9j symbols. For complex expressions it might not finish. It is advised to run simplifyAMSum[expr,Print->True], which prints the expression it is working on."

extractConditions::usage=
"extractConditions[expr] extracts all condtions (conTri/conZero) from the expression"

consistencyCheck::usage=
"consistencyCheck[expr] checks the expressions for consistency using available conditions and complaining about missing information."


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
consistencyCheck[expr_]:=Module[{conditions,symbols,notfound},
	conditions=extractConditions[expr];
	symbols=DeleteDuplicates@(removeSign/@Flatten[conditions//.{conTri[a__]:>{a}, conZero[a__]:>{a}}]);

	(*check for undeclared symbols*)
	notfound=Flatten@Position[(MemberQ[$integerQN,#]||MemberQ[$halfintegerQN,#]&)/@symbols,False];
	Do[Message[consistencyCheck::notfound,symbols[[i]]],{i,notfound}];

	(*Check that a+b+c is an integer for conTri[a,b,c] and conZero[a,b,c]*)
	notfound=Drop[#,1]&@Flatten@Position[
		conditions/.
			Join[(#->1/2)&/@$halfintegerQN,(#->0)&/@$integerQN]/.
			{conTri[a__]:> Total[{a}], conZero[a__]:> Total[{a}]}
		,
		x_/;!EvenQ[2*x]
		,
		{1}
	];

	Do[Message[consistencyCheck::halfinteger,TraditionalForm[conditions[[i]]]],{i,notfound}];

	(*Check that angular momentum quantum number and the correspondng
	 projection quantum number are both integers or both half-integers.*)
	conditions=Cases[expr,tj[__]|cg[__],{0,Infinity}];
	conditions=DeleteDuplicates@Flatten[conditions//.{			
			tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> conX@@@Map[removeSign,{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}},{2}],
			cg[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> conX@@@Map[removeSign,{{a,\[Alpha]},{b,\[Beta]},{c,\[Gamma]}},{2}]
		}];
	notfound=Flatten@Position[
			conditions//.
				{conX[a_,\[Alpha]_]:>True /; Or@@(MemberQ[#,a] && MemberQ[#,\[Alpha]]&)/@{$integerQN,$halfintegerQN}}/.
				{conX[___]-> False},
			False];
	conditions=conditions/.{conX[a_,b_]:> {a,b}};
	Do[Message[consistencyCheck::projection,
			TraditionalForm[conditions[[i]][[1]]],
			TraditionalForm[conditions[[i]][[2]]]
		],{i,notfound}];	
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

prepareSymbolOrderlessRules={
		sj[{a_,b_,c_},{d_,e_,f_}]:> sjOL[set[a,b,c],set[a,e,f],set[d,b,f],set[d,e,c]],
		nj[{a_,b_,c_},{d_,e_,f_},{g_,h_,j_}]:> njOL[set[set[a,e,j],set[b,f,g],set[c,d,h]],set[set[a,b,c],set[d,e,f],set[g,h,j],set[a,d,g],set[b,e,h],set[c,f,j]]]
	};



(* ::Subsection:: *)
(*Simplification*)


simplifyFactorRules={
		(-1)^(a_):>mX[a],
		mX[a_ + b_]:> mX[a] mX[b],
		mX[n_Integer a_]:> mX[a]^n,
		mX[n_Integer]:> mX[1]^n /; n<-1 || n>1,
		mX[-a_]^n_:> mX[a]^(-n),
		mX[a_]^n_:> mX[a]^Mod[n,2] /; n!=0 && n!=1 && MemberQ[$integerQN,Verbatim[a]],
		mX[a_]^n_:> (-1)^(Floor[n/2])mX[a]^Mod[n,2] /; n!=0 && n!=1 && MemberQ[$halfintegerQN,Verbatim[a]],
		mX[a_]^0:> 1,
		mX[]-> 1,
		mX[0]-> 1,
		mX[1]->(-1),
		mX[-1]->(-1),
		mX[1/2]->(I),
		mX[-1/2]->(-I)		
	};

simplifySumRules={
		KroneckerDelta[-a_,-b_]:> KroneckerDelta[a,b],
		sum[a_ KroneckerDelta[Except[_?NumberQ,b_],c_],set[b_,d___]]:> sum[(a/.b-> c),set[d]]/;!StringMatchQ[ToString[c],RegularExpression[".*p.*"]]||StringMatchQ[ToString[b],RegularExpression[".*p.*"]],
		sum[a_ KroneckerDelta[Except[_?NumberQ,b_],c_],set[d___]]:> sum[(a/.b-> c) KroneckerDelta[b,c],set[d]]/;FreeQAll[{d},{b,c}]&&!FreeQ[a,b]&&!FreeQ[a,c]&&(!StringMatchQ[ToString[c],RegularExpression[".*p.*"]]||StringMatchQ[ToString[b],RegularExpression[".*p.*"]]),
		sum[a_ sum[b_,set[c___]],set[d___]]:> sum[a b,set[c,d]]
	};

simplifyCollectSumRules={
		a_ sum[b_,set[c___]]:> sum[a b,set[c]]/;FreeQAll[{a},{c}],
		sum[a_,set[u___]] sum[b_,set[v___]]:> sum[a b,set[u,v]]/;FreeQAll[{a},{v}]&&FreeQAll[{b},{u}]
	};

simplifyConditionOrderlessRules={
		sjOL[set[a_,b_,c_],u__]conTri[a_,b_,c_]:> sjOL[set[a,b,c],u],
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
		sum[(-1)^(a_+\[Alpha]_)tj[{a_,-\[Alpha]_},{a_,\[Alpha]_},{c_,\[Gamma]_}],\[Alpha]_]
			:> Sqrt[2 a+1]KroneckerDelta[c,0]KroneckerDelta[\[Gamma],0],
		sum[(-1)^(p_+\[Psi]_+q_+\[Kappa]_)tj[{a_,\[Alpha]_},{p_,-\[Psi]_},{q_,-\[Kappa]_}]tj[{p_,\[Psi]_},{q_,\[Kappa]_},{ap_,\[Alpha]p_}],\[Psi]_,\[Kappa]_]
			:> (-1)^(a-\[Alpha])1/(2 a+1)KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],-\[Alpha]p]conTri[a,p,q],				
		sum[(-1)^(q_+\[Kappa]_)(2q_+1)tj[{a_,\[Alpha]_},{b_,\[Beta]_},{q_,-\[Kappa]_}]tj[{q_,\[Kappa]_},{a_,\[Alpha]p_},{b_,\[Beta]p_}],q_,\[Kappa]_]
			:>(-1)^(a-\[Alpha]+b-\[Beta])KroneckerDelta[\[Beta],-\[Beta]p]KroneckerDelta[\[Alpha],-\[Alpha]p],				
		sum[(-1)^(p_+q_+r_+\[Psi]_+\[Kappa]_+\[Rho]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,\[Kappa]_}]tj[{q_,-\[Kappa]_},{b_,\[Beta]_},{r_,\[Rho]_}]tj[{r_,-\[Rho]_},{c_,\[Gamma]_},{p_,\[Psi]_}],\[Kappa]_,\[Psi]_,\[Rho]_]
			:> tj[{a,-\[Alpha]},{b,-\[Beta]},{c,-\[Gamma]}]sj[{a,b,c},{r,p,q}]
(*,	sum[(-1)^(p_+q_+r_+s_+t_+\[Psi]_+\[Kappa]_+\[Rho]_+\[Sigma]_+\[Tau]_)tj[{p_,-\[Psi]_},{a_,\[Alpha]_},{q_,-\[Kappa]_}]tj[{q_,\[Kappa]_},{r_,-\[Rho]_},{t_,-\[Tau]_}]tj[{r_,\[Rho]_},{ap_,\[Alpha]p_},{s_,-\[Sigma]_}]tj[{s_,\[Sigma]_},{p_,\[Psi]_},{t_,\[Tau]_}],\[Psi]_,\[Kappa]_,\[Rho]_,\[Sigma]_,\[Tau]_]
			:> (-1)^(a+\[Alpha])/(2a+1)sj[{q,p,a},{s,r,t}]KroneckerDelta[a,ap]KroneckerDelta[\[Alpha],-\[Alpha]p]*)
	};


(* ::Subsubsection:: *)
(*6J*)


simplify6jRawRules={
		sum[(2 x_+1)sj[{a_,b_,x_},{a_,b_,c_}],x_]
			:> (-1)^(2c)conTri[a,b,c],				
		sum[(-1)^(a_+b_+x_)(2 x_+1)sj[{a_,b_,x_},{b_,a_,c_}],x_]
			:> Sqrt[2a+1]Sqrt[2b+1]KroneckerDelta[c,0],
		sum[(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{a_,b_,q_}],x_]
			:> 1/(2p+1)KroneckerDelta[p,q]conTri[a,d,p]conTri[c,b,p],
		sum[(-1)^(p_+q_+x_)(2 x_+1)sj[{a_,b_,x_},{c_,d_,p_}]sj[{c_,d_,x_},{b_,a_,q_}],x_]
			:> sj[{c,a,q},{d,b,p}]
	};



(* ::Subsection:: *)
(*Private Helper Functions Involving 3jm, 6j or 9j symbols*)


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
	tmp=Flatten[tmpFunc/@l,1];
	result=Simplify[expr,TransformationFunctions->transFunc,ComplexityFunction->compFunc];
	
	Return[result];	
];

prepare3jmFactor::multiplesums="Expression has multiple sums. Cannot prepare factors";
prepare3jmFactor[expr_]:=Module[{variableList,sumExpr,finalSumExpr,transFunc,factorList,compFunc,functions},
	variableList=Cases[expr,sum[__],{0,Infinity}];
	If[Length[variableList]>1,Message[prepare3jmFactor::multiplesums];Return[expr]];
	If[Length[variableList]==0,Return[expr]];
	sumExpr=variableList[[1]];
	variableList=sumExpr/.{sum[a_,set[b__]]:>{b}};
	factorList=Cases[extractConditions[sumExpr],conZero[a__]/;!FreeQAll[{a},variableList]]/.
		{conZero[a_,b_,c_]:>mX[a]mX[b]mX[c]};
	transFunc[i_]:=(#/.
					{sum[a_,set[b__]]:>sum[a factorList[[i]],set[b]] }//.
					simplifyFactorRules)&;
	compFunc[newexpr_]:=-20 Count[newexpr,x_/;MemberQ[(mX/@variableList),x],{0,Infinity}]+LeafCount[newexpr];
	functions=Table[transFunc[i],{i,Length[factorList]}];
	finalSumExpr=Simplify[sumExpr,TransformationFunctions->functions,ComplexityFunction->compFunc];
	Return[expr/.sumExpr->finalSumExpr];
];

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

facX[]:=1;
facX[a_]:=1/;MemberQ[$integerQN,Verbatim[a]];
facX[a_]:=-1/;MemberQ[$halfintegerQN,Verbatim[a]];

refineSymbolRule::ruletype="Cannot handle a non-delayed rule";
refineSymbolRule::wrongfactors="Rule `1` is missing a factor.";
refineSymbolRule[rule_]:=Module[{
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
	summation=removeBlanks/@(rulePattern/.sum[a_,set[b___]]:> {b});
	AppendTo[variables,m];AppendTo[variables,u];
	variables=Complement[variables,summation];
	AppendTo[ruleConditionList,fqa[variables,summation]/.
			{fqa[a_,b_]:> Hold[FreeQAll[a,b]]}
	];

(*We add "m_." and "u___" that match additional unrelated factors and summation variables, respectively*)
	rulePattern=rulePattern/.
		sum[a_,set[b___]]:>sum[Optional[pat[m,Blank[]]]a,set[b,pat[u,BlankNullSequence[]]]]/.
		pat-> Pattern;
	If[FreeQ[ruleResult,sum],
		ruleResult=Replace[ruleResult,Hold[a_]:> Hold[sum[a,set[]]]];
	];
	ruleResult=ruleResult/.
		sum[a_,set[b___]]:>sum[m a,set[b,u]];

(*We also add alternatives to accept versions with a minus sign (3jm only)*)
	(*select variables that might have minus signs*)
	invertVariables=DeleteDuplicates@removeBlanks@Flatten[Cases[rulePattern,tj[{a_,\[Alpha]_},{b_,\[Beta]_},{c_,\[Gamma]_}]:> removeSign/@{\[Alpha],\[Beta],\[Gamma]},{0,Infinity}],1];
	invertVariables=Intersection[invertVariables,summation];
	(*Check for correct factors - for every of the selected variables a mX[<variable>] must be present*)
	countMX=Count[rulePattern,Verbatim[mX[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"#", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]],{0,Infinity}]&;
	counts=countMX/@invertVariables;
	counts=counts/.{1-> True,_Integer->False};
	If[!And@@counts,Message[refineSymbolRule::wrongfactors,rule]];
	(*create rules to transform patterns, results and conditions using the special matching procedure for these variables*)
		(*starting with the result*)
	tmpList[1]=Times@@(facX[ToExpression[ToString[#]<>"neg"]]&/@invertVariables);
	tmpRule[1]=(sum[a_,set[b___]]:> sum[a #,set[b]]&)[tmpList[1]];	
	ruleResult=ruleResult/.tmpRule[1];
		(*changing the pattern*)
	tmpList[2]=unsM[#]&/@invertVariables;
	tmpRule[2]=({sum[a_,set[Sequence@@(Verbatim[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"#", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]&/@invertVariables),b___]]:>sum[a,set[##,b]]})&[Sequence@@tmpList[2]];
	tmpFunc[2]={Verbatim[mX[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"#", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]]:>mX[unsM[#]],-Verbatim[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"#", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]:>speM[-#],Verbatim[\!\(\*
TagBox[
StyleBox[
RowBox[{"Pattern", "[", 
RowBox[{"#", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]:>speM[#]}&;
	rulePattern=rulePattern/.tmpRule[2]/.Flatten[tmpFunc[2]/@invertVariables,1];
		(*changing the conditions*)
	tmpFunc[3]=Rule[#,Sequence[ToExpression[ToString[#]<>"pos"],ToExpression[ToString[#]<>"neg"]]]&;
	tmpRule[3]=tmpFunc[3]/@invertVariables;
	ruleConditionList=ruleConditionList/.tmpRule[3];
(*Match all even permutations of 3jm symbols*)
	rulePattern=rulePattern/.{tj[a__]:> evenPermM[tj[a]]};

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
		Flatten[createAlternativeRules3jm/@simplify3jmRawRules,1]
	];
simplifySymbolRulesDispatch=Dispatch[simplifySymbolRules];



(* ::Subsection:: *)
(*Functions*)


Options[simplifyAMSum]={Print->False,Timing-> False,TimingComplete-> False};
simplifyAMSum[expr_,OptionsPattern[]]:=Module[{
		prev,result,
		prepareRules=Join[prepareSumRules,prepareSymbolOrderlessRules,simplifyCollectSumRules,simplifySumRules],
		simplifyRules=Join[simplifyFactorRules,simplifySumRules,simplifyConditionOrderlessRules],
		cleanupRules=Join[cleanupSumRules,cleanupFactorRules,cleanupSymbolOrderlessRules],
		t1,t2,t3,t4,tmp
	},
	consistencyCheck[expr];
	result=toTJ[expr]//.prepareRules;		
	prev=None;
	While[prev=!=result,
		If[OptionValue[Print],Print[TraditionalForm[result//.cleanupRules]]];
		prev=result;
		tmp=Timing[prepare3jmSign[prev]];
		t1=tmp[[1]];
		result=tmp[[2]];
		If[OptionValue[TimingComplete],Print[StringForm["prepared 3jm signs :`` ",t1]]];
		tmp=Timing[prepare3jmFactor[result]];
		t2=tmp[[1]];
		result=tmp[[2]];
		If[OptionValue[TimingComplete],Print[StringForm["prepared 3jm factors :`` ",t2]]];
		tmp=Timing[result//.simplifyRules];		
		t3=tmp[[1]];
		result=tmp[[2]];
		If[OptionValue[TimingComplete],Print[StringForm["pre-simplification :`` ",t3]]];
		If[OptionValue[TimingComplete],Print[StringForm["`` ",result]]];
		tmp=Timing[result/.simplifySymbolRulesDispatch];		
		t4=tmp[[1]];
		result=tmp[[2]];
		If[OptionValue[Timing]||OptionValue[TimingComplete],
			If[t1+t2+t3+t4>0,
				Print[StringForm["Timing: ``  ``  ``  `` (``%  ``%  ``%  ``%)",t1,t2,t3,t4,100*t1/(t1+t2+t3+t4),100*t2/(t1+t2+t3+t4),100*t3/(t1+t2+t3+t4),100*t4/(t1+t2+t3+t4)]];
				,
				Print["Timing :0"];
			];
		];
		result=result//.simplifyRules;
	];	
	Return[result//.cleanupRules];
];


(* ::Section:: *)
(*Package Cleanup*)


End[]


EndPackage[]
