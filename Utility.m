(* ::Package:: *)

BeginPackage["Utility`"]
ClearAll[Evaluate[Context[]<>"*"]];

FreeQAll::usage=
"Checks if all expressions a are independent of all elements in the list b.

Arguments:

a: sequence of expressions
b: list of elements

Returns: True if all expressions are free of all elements, False otherwise
";

FreeQAllUnsigned::usage=
"Removes minus signs that may be in front of parameters in the list b, then invokes FreeQAll
Equivalent to FreeQAll[a,removeSign/@b].

Arguments:

a: sequence of expressions
b: list of elements

Returns: True if all expressions are free of all elements, False otherwise
";

FreeQNone::usage=
"Checks if the sequence of expressions a depends on all elements in the list b

Arguments:

a: sequence of expressions
b: list of elements

Returns: True if the sequence depends on all the elements froom list b, False otherwise.
";

FreeQNoneUnsigned::usage=
"Removes minus signs that may be in front of parameters in the list b, then invokes FreeQNone
Equivalent to FreeQNone[a,removeSign/@b].

Arguments:

a: sequence of expressions
b: list of elements

Returns: True if the sequence depends on all the elements froom list b, False otherwise.
";

EvenPermutations::usage=
"Returns all even permutations of the input list.
";

OddPermutations::usage=
"Returns all odd permutations of the input list.
";

alternative::usage=
"denotes a set of alternative versions of an expression. All of these versions should be identical. It is used in pattern matching: A specific pattern has to match one of the alternative versions. The function is automatically pulled out of an expression, e.g. a*alternative[b,c] becomes alternative[a*b,a*c]\!\(\*
StyleBox[\".\", \"Text\"]\)\!\(\*
StyleBox[\" \", \"Text\"]\)All the functions alternative should be pulled out of must be listed in $altFunctionList.
";

$altFunctionList::usage=
"Used to identify the functions, alternative should be pulled out of. Append your own functions to this list, if you want them to work with alternative.

default: {sum}
";

set::usage=
"used to represent an Orderless set as opposed to a List, which imposes a specific order.
";

tochar::usage=
"transforms the numbers 1-26 to characters a-z
";

tonum::usage=
"transforms the characters a-z to numbers 1-26
";

removeSign::usage=
"remove a minus sign in front of the input parameter x. Differs from \"abs\"\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\",\nFontSlant->\"Italic\"]\)as it uses pattern matching to remove the sign. If the input is -a, it will result in a\!\(\*
StyleBox[\".\", \"Code\"]\)
";

sign::usage=
"Returns +1 or -1 depending on the sign of the input paramter x. Differs from Sign as it uses pattern matching to determine the sign.
";

sum::usage=
"replacement for the built-in \"Sum\". This version does not try to evaluate its arguments, reducing the use of Hold / HoldForm and so on. Signs in front of summation variables are removed, e.g. sum[f[g],-g] becomes sum[f[g],g]. This behaviour is different from the built-in \"Sum\" as the latter produces an error message in such a case. This function should only be used for indefinite sums.
";

integrate::usage=
"replacement for the built-in \"Integrate\". This version does not try to evaluate its arguments, reducing the use of Hold / HoldForm and so on. This function should only be used for indefinite integrals.
";

invertArguments::usage=
"returns a function which returns a list of different versions of the expression. In these versions some of the provided arguments have minus signs added. All possible cases are constructed, e.g. f[a] g[b] h[a] // invertArguments[a,b] becomes {f[a] g[b] h[a], f[-a] g[b] h[-a], f[a] g[-b] h[a], f[-a] g[-b] h[-a]} This is used for extending some of the rules with fixed arguments to their negative versions.
";

getAllVariables::usage=
"Returns all the variables of an expression (It takes all objects with the Head _Symbol that can be found at the leafs of the tree-like structure that represents all Mathematica expressions. It ignores Symbols with the attribute \"Constant\", e.g. \"E\".
";

removeBlanks::usage=
"Removes blanks (Blank[...]) from an expression, e.g. a_ becomes a.
";

ruleSplit::usage=
"splits a (delayed) rule into a list of parts. This list has three or four parts, which are from left to right:

The type of the rule, which is one of the following:
 - \"r\": a simple rule (a->b)
 - \"rd\": a delayed rule (a:>b)
 - \"rc\": a rule with a condition (a->b/;c)
 - \"rdc\": a delayed rule with a condition (a:>b/;c)

The pattern, e.g. f[a_]:>a^2 has the pattern f[a_]

The result of the rule, e.g. a^2 for the rule given above

The condition of the rule, if there is one. In the case a:>b/;a>0 this part would be a>0
";

ruleJoin::usage=
"Creates a (delayed) rule from its parts. This is the counterpart to ruleSplit, e.g. ruleJoin[ruleSplit[rule]]=rule, if one inputs a rule that can be splitted.
";

normalizeSumRule::usage=
"simplifies the input rule if the rule involved a sum. It identifies factors that are independent of the summation variables and moves them to the right-hand side of the rule.
";

declareIndexed::usage="";
declarePrimed::usage="";
declareIndexedPrimed::usage="";
declareIndexedAM::usage="";


Begin["`Private`"]
ClearAll[Evaluate[Context[]<>"*"]];


$altFunctionList={sum};
SetAttributes[set,Orderless]
SetAttributes[conX,HoldAll]
SetAttributes[rX,{HoldRest,SequenceHold}]
SetAttributes[rdX,{HoldRest,SequenceHold}]
SetAttributes[alternative,{Orderless,Flat,OneIdentity}]

FreeQAll[a___,b_]:=And@@(FreeQ[{a},#]&/@b);

FreeQNone[a___,b_]:=And@@(!FreeQ[{a},#]&/@b);

FreeQAllUnsigned[a___,b_]:=FreeQAll[a,removeSign/@b];

FreeQNoneUnsigned[a___,b_]:=FreeQNone[a,removeSign/@b];

EvenPermutations[lst_]:=Select[Permutations[lst],Signature[#]*Signature[lst]==1&];

OddPermutations[lst_]:=Select[Permutations[lst],Signature[#]*Signature[lst]==-1&];

alternative/:alternative[a__]alternative[b__]:=alternative@@Flatten[{a}*#&/@{b},1] ;
alternative/:a_ alternative[b__]:=alternative@@(a*{b});
alternative/:alternative[a__]+alternative[b__]:=alternative@@Flatten[{a}+#&/@{b},1] ;
alternative/:f_[a___,alternative[b__],c___]/;MemberQ[$altFunctionList,f]:=alternative@@(f[a,#,c]&/@{b});

tochar[jj_]:={Global`a,Global`b,Global`c,Global`d,Global`e,Global`f,Global`g,Global`h,Global`i,Global`j,Global`k,Global`l,Global`m,Global`n,Global`o,Global`p,Global`q,Global`r,Global`s,Global`t,Global`u,Global`v,Global`w,Global`x,Global`y,Global`z}[[jj]];

tonum[jj_]:=Position[{Global`a,Global`b,Global`c,Global`d,Global`e,Global`f,Global`g,Global`h,Global`i,Global`j,Global`k,Global`l,Global`m,Global`n,Global`o,Global`p,Global`q,Global`r,Global`s,Global`t,Global`u,Global`v,Global`w,Global`x,Global`y,Global`z},jj][[1]][[1]]

removeSign[x_]:= x/.- u_:> u;

sign[x_]:= If[MatchQ[x,-_],-1,1];

sum[a_,u___,-b_,v___]:=sum[a,u,b,v];
sum[a_,set[-b_,u___]]:=sum[a,set[b,u]];
sum/:MakeBoxes[sum[a_,set[b___]], fmt:TraditionalForm]:=MakeBoxes[Sum[a,b],fmt];
sum/:MakeBoxes[sum[a__], fmt:TraditionalForm]:=MakeBoxes[Sum[a],fmt];

integrate/:MakeBoxes[integrate[a_,set[b___]], fmt:TraditionalForm]:=MakeBoxes[Integrate[a,b],fmt];
integrate/:MakeBoxes[integrate[a__], fmt:TraditionalForm]:=MakeBoxes[Integrate[a],fmt];

invertArgumentsHelper[expr_,arg_]:= Flatten[expr/.{{arg-> arg},{arg-> -arg}},1];
invertArgumentsHelper[expr_,arg_,remainder__]:=invertArgumentsHelper[ Flatten[expr/.{{arg-> arg},{arg-> -arg}},1],remainder];
invertArguments[arg___]:=invertArgumentsHelper[#,arg]&;

getAllVariables[expr___]:=DeleteDuplicates@Cases[{expr},x_Symbol/;FreeQ[Attributes[x],Constant],Infinity];

removeBlanks[a___]:= a/.Pattern-> pat//.pat[x_,Blank[]]:> x/.pat-> Pattern;

ruleSplit[rule_]:=rule/.Condition-> conX/.RuleDelayed[a_,conX[b_,c_]]:> {"rdc",a,Hold[b],Hold[c]}/.RuleDelayed[a_,b_]:> {"rd",a,Hold[b]}/.Rule[a_,conX[b_,c_]]:> {"rc",a,Hold[b],Hold[c]}/.Rule[a_,b_]:> {"r",a,Hold[b]}/.conX-> Condition;

ruleJoin[ruleList_]:=
Switch[ruleList[[1]],
	"rdc", rd[ruleList[[2]],con[ruleList[[3]],ruleList[[4]]]],
	"rd", rd[ruleList[[2]],ruleList[[3]]],
	"rc", r[ruleList[[2]],con[ruleList[[3]],ruleList[[4]]]],
	"r", r[ruleList[[2]],ruleList[[3]]]
]/.{con[Hold[a_],Hold[b_]]:> conX[a,b],rd[a_,Hold[b_]]:> rdX[a,b],r[a_,Hold[b_]]:> rX[a,b]}/.{rd-> rdX,r-> rX}//.{conX-> Condition,rdX-> RuleDelayed,rX-> Rule};

SetAttributes[normalizeSumRule,Listable];
normalizeSumRule[rule_]:=Module[{ruleList,rulePattern,ruleResult,ruleParts,result},
	ruleList=ruleSplit[rule];
	rulePattern=ruleList[[2]];
	ruleResult=ruleList[[3]];
	i=0;
	While[i<2^16,
		i++;
		ruleParts=rulePattern/.{
			sum[a_ b_,set[c__]]:> {sum[b,set[c]],1/a}/;FreeQAll[removeBlanks[a],removeBlanks[{c}]]&& FreeQNone[removeBlanks[b],removeBlanks[getAllVariables[a]]]
		};
		If[rulePattern=!=ruleParts,
			rulePattern=ruleParts[[1]];
			ruleResult=(removeBlanks[ruleParts[[2]]] ruleResult)/.a_ Hold[b_]:> Hold[a b]/.Hold[a_ sum[b_,c___]]:> Hold[ sum[a b,c]];
			,
			Break[];
		];
	];
	ruleList[[2]]=rulePattern;
	ruleList[[3]]=ruleResult;
	Return[ruleJoin[ruleList]];
];

declareIndexed[x_]:=Module[{},
	x/:MakeBoxes[x[a__], fmt:TraditionalForm]:=SubscriptBox[MakeBoxes[x,fmt],RowBox[Riffle[MakeBoxes[#,fmt]&/@{a},"\[InvisibleComma]"]]];
];

declarePrimedHelper[x_,xp_]:=Module[{},
	xp/:MakeBoxes[xp, fmt:TraditionalForm]:=SuperscriptBox[MakeBoxes[x,fmt],"\[Prime]"];
];

declareIndexedPrimedHelper[x_,xp_]:=Module[{},
	xp/:MakeBoxes[xp[a__], fmt:TraditionalForm]:=SubsuperscriptBox[MakeBoxes[x,fmt],RowBox[Riffle[MakeBoxes[#,fmt]&/@{a},"\[InvisibleComma]"]],"\[Prime]"];
];

declareIndexedAMHelper[x_,mx_,mxp_]:=Module[{},
	mx/:MakeBoxes[mx[a__], fmt:TraditionalForm]:=SubscriptBox[MakeBoxes[Global`m,fmt],SubscriptBox[MakeBoxes[x,fmt],RowBox[Riffle[MakeBoxes[#,fmt]&/@{a},"\[InvisibleComma]"]]]];
	mxp/:MakeBoxes[mxp[a__], fmt:TraditionalForm]:=SubsuperscriptBox[MakeBoxes[Global`m,fmt],SubscriptBox[MakeBoxes[x,fmt],RowBox[Riffle[MakeBoxes[#,fmt]&/@{a},"\[InvisibleComma]"]]],"\[Prime]"];
];

declareIndexedPrimed[x_]:=Module[{xp=ToExpression[ToString[x]<>"p"]},
	declareIndexed[x];
	declareIndexedPrimedHelper[x,xp];
	declarePrimedHelper[x,xp];
];

declareIndexedAM[x_]:=Module[{
			xp=ToExpression[ToString[x]<>"p"],
			mx=ToExpression["m"<>ToString[x]],
			mxp=ToExpression["m"<>ToString[x]<>"p"]
		},
	declareIndexed[x];
	declareIndexedPrimedHelper[x,xp];
	declarePrimedHelper[x,xp];
	declareIndexedAMHelper[x,mx,mxp];
];

declarePrimed[x_]:=Module[{xp=ToExpression[ToString[x]<>"p"]},
	declarePrimedHelper[x,xp];
];


End[]


EndPackage[]
