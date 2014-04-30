(* ::Package:: *)

BeginPackage["Utility`"]
ClearAll[Evaluate[Context[]<>"*"]];


FreeQAll::usage=
"FreeQAll[expr1,...,listOfElements] Checks if all expressions expr1,... are independent of all elements in listOfSymbols.

Arguments:

expr1,...: sequence of expressions
listOfElements: list of elements

Returns: True if all expressions are free of all elements, False otherwise."

FreeQAllUnsigned::usage=
"FreeQAllUnsigned[expr1,...,listOfElements]  removes minus signs that may be in front of parameters in listOfElements, then invokes FreeQAll.
Equivalent to FreeQAll[a,removeSign/@b].

Arguments:

expr1,...: sequence of expressions
listOfElements: list of elements

Returns: True if all expressions are free of all elements, False otherwise"

FreeQNone::usage=
"FreeQNone[expr1,...,listOfElements] checks if the sequence of expressions (expr1,...) depends on all elements in listOfElements

Arguments:

expr1,...: sequence of expressions
listOfElements: list of elements

Returns: True if {expr1,...} depends on all the elements from listOfElements, False otherwise."

FreeQNoneUnsigned::usage=
"FreeQNoneUnsigned[expr1,...,listOfElements] removes minus signs that may be in front of parameters in listOfSymbols, then invokes FreeQNone
Equivalent to FreeQNone[a,removeSign/@b].

Arguments:

expr1,...: sequence of expressions
listOfElements: list of elements

Returns: True if {expr1,...} depends on all the elements from listOfElements, False otherwise."

EvenPermutations::usage=
"EvenPermutations[list] returns all even permutations of the input list."

OddPermutations::usage=
"OddPermutations[list] returns all odd permutations of the input list."

alternative::usage=
"denotes a set of alternative versions of an expression. All of these versions should be identical. It can be used in pattern matching: A specific pattern has to match one of the alternative versions. The function is automatically pulled out of an expression, e.g. a*alternative[b,c] becomes alternative[a*b,a*c]. All the functions alternative should be pulled out of must be listed in $altFunctionList."

$altFunctionList::usage=
"Used to identify the functions, alternative should be pulled out of. Append your own functions to this list, if you want them to work with alternative.

default: {sum}"

set::usage=
"used to represent an Orderless set as opposed to a List, which imposes a specific order. For example, set[a,b,c] is matched by the pattern set[c,b,a].
For transforming a list, use \"@@\":
list={a,b,c};
set@@list (results in set[a,b,c])"

tochar::usage=
"tochar[number] transforms the numbers 1-26 to characters a-z. The characters will be in global scope."

tonum::usage=
"tonum[char] transforms the characters a-z to numbers 1-26. The characters must be in global scope."

removeSign::usage=
"removeSign[symbol] removes a minus sign in front of the input symbol.
Differs from \"abs\" as it uses pattern matching to remove the sign. If the input is -a, it will result in a."

sign::usage=
"sign[symbol] Returns +1 or -1 depending on the sign of the input symbol. Differs from Sign as it uses pattern matching to determine the sign."

sum::usage=
"replacement for the built-in \"Sum\". This version does not try to evaluate its arguments, reducing the use of Hold / HoldForm and so on. Signs in front of summation variables are removed, e.g. sum[f[g],-g] becomes sum[f[g],g]. This behaviour is different from the built-in \"Sum\" as the latter produces an error message in such a case. 
This function should only be used for indefinite sums. Furthermore the order of the summation should be irrelevant."

integrate::usage=
"replacement for the built-in \"Integrate\". This version does not try to evaluate its arguments, reducing the use of Hold / HoldForm and so on. 
This function should only be used for indefinite integrals."

invertArguments::usage=
"invertArguments[arg1,...] returns a function which returns a list of different versions of the expression. In these versions some of the provided arguments have minus signs added. All possible cases are constructed, e.g. f[a] g[b] h[a] //invertArguments[a,b] becomes {f[a] g[b] h[a], f[-a] g[b] h[-a], f[a] g[-b] h[a], f[-a] g[-b] h[-a]} This can be used for extending some of the rules with fixed arguments to their negative versions."

getAllVariables::usage=
"getAllVariables[expr] Returns all the variables of an expression (It takes all objects with the Head _Symbol that can be found at the leafs of the tree-like structure that represents all Mathematica expressions. It ignores Symbols with the attribute \"Constant\", e.g. \"E\"."

removeBlanks::usage=
"removeBlanks[expr] removes blanks (Blank[...]) from an expression, e.g. a_ becomes a."

ruleSplit::usage=
"ruleSplit[rule] splits a (delayed) rule into a list of parts. This list has three or four parts, which are from left to right:

The type of the rule, which is one of the following:
 - \"r\": a simple rule (a->b)
 - \"rd\": a delayed rule (a:>b)
 - \"rc\": a rule with a condition (a->b/;c)
 - \"rdc\": a delayed rule with a condition (a:>b/;c)

The pattern, e.g. f[a_]:>a^2 has the pattern f[a_]

The result of the rule (in a surrounding Hold function), e.g. Hold[a^2] for the rule given above

The condition of the rule (in a surrounding Hold function), if there is one. In the case a:>b/;a>0 this part would be Hold[a>0]"

ruleJoin::usage=
"ruleJoin[ruleParts] Creates a (delayed) rule from its parts. This is the counterpart to ruleSplit, e.g. ruleJoin[ruleSplit[rule]]=rule, if one inputs a rule that can be splitted."

normalizeSumRule::usage=
"normalizeSumRule[rule] simplifies the input rule if the rule involves a sum. It identifies factors that are ndependent of he summation variables and moves them to the right-hand side of the rule."

declareIndexed::usage=
"declareIndexed[symbol] declares a symbol to be indexed. Afterwards expressions like symbol[a,b] will be represented with a and b as indices when using TraditionalForm"

declarePrimed::usage=
"declarePrimed[symbol] declares a primed symbol. For example, when using declarePrimed[a], the TraditionalForm of \"ap\" will be a'."

declareIndexedPrimed::usage="declareIndexed[symbol] declares a symbol and the primed symbol to be indexed. Using declareIndexed[f], expressions like f[a,b] will be represented with a and b as indices when using TraditionalForm. Furthermore fp[a,b] will be represented as f' with indices a and b."

declareIndexedAM::usage=
"declares some symbol to be an angular momentum quantum number. This involves special TraditionalForm expressions. For instance, declareIndexedAM[t] results in special representations for {tp,t[a,b],tp[a,b,c],mt[u],mtp[d,e]}"

ensureSignQ::usage=
"ensureSignQ[positive,negative,unsigned] ensures that positive==-negative and removeSign[positive]==removeSign[negative]==unsigned. The unsigned entry is optional.
For instance the pattern sum[f[apos_,aneg_],auns_] /;ensureSignQ[apos,aneg,auns] matches sum[f[a,-a],a] or sum[f[-b,b],b]. It does not match sum[f[b,-c],b], sum[f[a,-a],-a], sum[f[-a,-a],a] or sum[f[a,a],a]."

speM::usage="speM[a] is a special pattern, which provides similar features as ensureSignQ:
For instance the pattern f[speM[a],speM[-a]] matches f[a,-a] or f[-b,b]. It does not match f[b,-c], f[-a,-a] or f[a,a].
For rules, either the symbol \"apos\" or \"aneg\" is defined, when the rule matches. The other is defined as Sequence[]."

unsM::usage="unsM[a] is a special pattern, which extends speM to unsigned expressions:
For instance the pattern sum[f[speM[a],speM[-a]],uns[a]] matches sum[f[a,-a],a] or sum[f[-b,b],b]. It does not match sum[f[b,-c],b], sum[f[a,-a],-a], sum[f[-a,-a],a] or sum[f[a,a],a]."

evenPermM::usage=
"evenPermM[list] matches all even permutations of the list."

ruleToFunction::usage=
"ruleToFunction[rule] returns a function that applies the rule once."

ruleToFunctionRepeated::usage=
"ruleToFunctionRepeated[rule] returns a function that applies the rule repeatedly."

simplifySumRules::usage=
"A set of rules to simplify sums (using \"sum\" instead of the built-in Sum)"

simplifyIntegrateRules::usage=
""

simplifySeperateIntegrateRules::usage=
""

simplifySeperateIntegrate::usage=
""

replaceUnique::usage=
""


Begin["`Private`"]
ClearAll[Evaluate[Context[]<>"*"]];


$altFunctionList={sum};
SetAttributes[set,Orderless]
SetAttributes[conX,HoldAll]
SetAttributes[rX,{HoldRest,SequenceHold}]
SetAttributes[rdX,{HoldRest,SequenceHold}]
SetAttributes[alternative,{Orderless,Flat,OneIdentity}]

FreeQAll[a___,b_]:=And@@((FreeQ[{a},#]&)/@(b));

FreeQNone[a___,b_]:=And@@((!FreeQ[{a},#]&)/@(b));

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

removeSign[x_]:= Replace[x,-u_:> u];

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
normalizeSumRule[rule_]:=Module[{ruleList,rulePattern,ruleResult,ruleParts,result,keep},
	ruleList=ruleSplit[rule];
	rulePattern=ruleList[[2]];
	ruleResult=ruleList[[3]];
	If[Length[ruleList]>3,
		keep=DeleteDuplicates@Flatten@Cases[ruleList[[4]],ensureSignQ[a__]:> {a},{0,Infinity}];,
		keep={};
	];
	keep=DeleteDuplicates@Join[keep,Flatten[Cases[rulePattern,sum[a_,set[b___]]:> getAllVariables[{b}],{0,Infinity}],1]];
	i=0;
	While[i<2^16,
		i++;
		ruleParts=rulePattern/.{
			sum[a_ b_,set[c__]]:> {sum[b,set[c]],1/a}/;FreeQAll[removeBlanks[a],removeBlanks[keep]]&& FreeQNone[removeBlanks[b],removeBlanks[getAllVariables[a]]]
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

SetAttributes[declareIndexed,Listable]
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
	mx/:MakeBoxes[mx, fmt:TraditionalForm]:=SubscriptBox[MakeBoxes[Global`m,fmt],MakeBoxes[x,fmt]];
	mxp/:MakeBoxes[mxp, fmt:TraditionalForm]:=SubsuperscriptBox[MakeBoxes[Global`m,fmt],MakeBoxes[x,fmt],"\[Prime]"];
];

SetAttributes[declareIndexedPrimed,Listable]
declareIndexedPrimed[x_]:=Module[{xp=ToExpression[ToString[x]<>"p"]},
	declareIndexed[x];
	declareIndexedPrimedHelper[x,xp];
	declarePrimedHelper[x,xp];
];

SetAttributes[declareIndexedAM,Listable]
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

SetAttributes[declarePrimed,Listable]
declarePrimed[x_]:=Module[{xp=ToExpression[ToString[x]<>"p"]},
	declarePrimedHelper[x,xp];
];

ensureSignQ[x_,negx_]:=x===-negx;
ensureSignQ[x_,negx_,unsx_]:=x===-negx && (x===unsx || negx===unsx) && removeSign[unsx]===unsx;

ruleToFunction[rule_]:=(#/.rule &);
ruleToFunctionRepeated[rule_]:=(#//.rule &);

speMHelper[apos_,aneg_]:=(Alternatives[\!\(\*
TagBox[
StyleBox[
RowBox[{"-", 
RowBox[{"patX", "[", 
RowBox[{"aneg", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}]}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),\!\(\*
TagBox[
StyleBox[
RowBox[{"patX", "[", 
RowBox[{"apos", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]/;Length[{apos,aneg}]==1)//.patX-> Pattern;
speM[a_]:=Module[{
		apos=ToExpression[ToString[a]<>"pos"],
		aneg=ToExpression[ToString[a]<>"neg"]
	},
	Return[speMHelper[apos,aneg]];
];

speM[-a_]:=Module[{
		apos=ToExpression[ToString[a]<>"pos"],
		aneg=ToExpression[ToString[a]<>"neg"]
	},
	Return[speMHelper[aneg,apos]];
];

unsMHelper[apos_,aneg_]:=(Alternatives[\!\(\*
TagBox[
StyleBox[
RowBox[{"patX", "[", 
RowBox[{"apos", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),\!\(\*
TagBox[
StyleBox[
RowBox[{"patX", "[", 
RowBox[{"aneg", ",", 
RowBox[{"Blank", "[", "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]/;Length[{apos,aneg}]==1)//.patX-> Pattern;
unsM[a_]:=Module[{
		apos=ToExpression[ToString[a]<>"pos"],
		aneg=ToExpression[ToString[a]<>"neg"]
	},
	Return[unsMHelper[apos,aneg]];
];

evenPermM[l_]:=(Alternatives@@EvenPermutations[l]);
evenPermM[l__]:=(Sequence/@Alternatives@@EvenPermutations[{l}]);

simplifySumRules={
		KroneckerDelta[-a_,-b_]:> KroneckerDelta[a,b],
		KroneckerDelta[a_,-b_]:> KroneckerDelta[-a,b]/;NumericQ[a]&&!NumericQ[b],
		sum[a_ KroneckerDelta[Except[_?NumberQ,b_],c_],set[b_,d___]]:> sum[(a/.b-> c),set[d]]/;!StringMatchQ[ToString[c],RegularExpression[".*p.*"]]||StringMatchQ[ToString[b],RegularExpression[".*p.*"]],
		sum[a_ KroneckerDelta[Except[_?NumberQ,b_],c_],set[d___]]:> sum[(a/.b-> c) KroneckerDelta[b,c],set[d]]/;FreeQAll[{d},{b,c}]&&!FreeQ[a,b]&&!FreeQ[a,c]&&(!StringMatchQ[ToString[c],RegularExpression[".*p.*"]]||StringMatchQ[ToString[b],RegularExpression[".*p.*"]]),
		sum[a_ sum[b_,set[c___]],set[d___]]:> sum[a b,set[c,d]]
};

simplifyIntegrateRules={
		integrate[a_ integrate[b_,set[c___]],set[d___]]:> integrate[a b,set[c,d]],
		integrate[a_ sum[b_,set[c___]],set[d___]]:> sum[integrate[a b,set[d]],set[c]]/;FreeQAll[{c},{d}]
};

checkDependence[a_,b_,c__]:= (And@@(FreeQ[{a},#]||FreeQ[b,#]&/@{c}));
getDependent[a_,c__]:=Select[{c},(!FreeQ[{a},#])&];
getIndependent[a_,c__]:=Select[{c},(FreeQ[{a},#])&];
simplifySeperateIntegrateRules={
	integrate[Shortest[a_] b_.,set[c__]]:> a integrate[b,set[c]]/;FreeQAll[a,{c}],	
	integrate[Shortest[a_] b_,set[c__]]/;checkDependence[a,b,c] :> integrate[a,set@@getDependent[a,c]]integrate[b,set@@getIndependent[a,c]]
};

$offset[x_]:=0;
replaceUnique[expr_,old_,new_]:=Module[{addOffset,result},
	addOffset=Length[DeleteDuplicates@Cases[expr,old[_],{0,Infinity}]];
	result=expr//.old[i_]:> new[i+$offset[new]];
	$offset[new]=$offset[new]+addOffset;
	Return[result];
]


End[]


EndPackage[]
