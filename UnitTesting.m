(* ::Package:: *)

BeginPackage["UnitTesting`"];
ClearAll[Evaluate[Context[]<>"*"]];

initialiseTests::usage = 
"Must be called before using the unit testing framework. Resets the internal variables of the framework, removing all added tests and modules.

Arguments:

None
";

beginTestModule::usage=
"Starts a testing module, which has nothing to do with the standard Mathematica Module. They are simply for arganizing the test cases. After a call to this function, all future tests are automatically added to the module with the supplied name. Testing modules can be nested.

Arguments:

name: The name of the module
";

endTestModule::usage=
"Ends a module.

Arguments:

None
";

addTest::usage=
"Adds a unit test to the current test module. The expression is not yet evaluated and this function can safely be put into an initialization cell.

Arguments:

expr: The expression to evaluate when running the test
val: The value to compare the evaluated expression against

Options:

equivalenceFunction: Function that accepts two arguments and returns True or False. This function is used to compare the evaluated expression with the value. Functions that use pattern matching may mix up the automatic naming. In such a case HoldForm may help, e.g. rather use (HoldForm[ #1 =!= #2 ] &) than (#1 =!= #2 &). default: (#1 == #2 &)
name: Gives a specific name to this test. If none is given, a name is constructed from the expression, the value, and the equivalenceFunction.
";

runTests::usage=
"Runs the test cases. Depending on the number of tests this function may run for a while.

Arguments:

None
";


Begin["`Private`"];
ClearAll[Evaluate[Context[]<>"*"]];


initialiseTests:=Module[{},
	globalModule[name]="";
	globalModule[fullname]="";
	globalModule[tests]={};
	globalModule[submodules]={};
	currentModule={globalModule};
];

beginTestModule[moduleName_]:=Module[{newModule,parentName=currentModule[[1]][fullname]},
	newModule[name]=moduleName;
	newModule[fullname]=If[StringLength[parentName]>0,parentName<>"`"<>moduleName,moduleName];
	newModule[tests]={};
	newModule[submodules]={};
	AppendTo[currentModule[[1]][submodules] ,newModule];
	PrependTo[currentModule,newModule];
	Return[newModule];
];

endTestModule:=Module[{},
	currentModule=Delete[currentModule,1];
	Return[currentModule[[1]]];
];

Options[addTest]={name->None,equivalenceFunction-> (#1==#2&)};
SetAttributes[addTest,HoldAll];
addTest[expr_,val_,OptionsPattern[]]:=Module[{newTest,tags,tag,cell,positions,parentName=currentModule[[1]][fullname]},
	newTest[expression]=Hold[expr];
	newTest[value]=Hold[val];
	newTest[comparison]=OptionValue[equivalenceFunction];
	newTest[module]=currentModule[[1]];
	If[OptionValue[name]===None,
		newTest[name]=StringForm["``",newTest[comparison][HoldForm[expr],HoldForm[val]]],
		newTest[name]=OptionValue[name];
	];
	newTest[fullname]=If[StringLength[parentName]>0,StringForm["``````",parentName,"`",newTest[name]],StringForm["``",newTest[name]]];
	
	AppendTo[currentModule[[1]][tests],newTest];
	cell=EvaluationCell[];
	tags=CurrentValue[cell,CellTags];
	If[Head[tags]=!=List,tags={tags}];
	positions=Position[StringMatchQ[tags,"test[*]"],True];
	If[Length[positions]>0,
		newTest[anchor]={EvaluationNotebook[],tags[[positions[[1]][[1]]]]};		
		,
		AppendTo[tags,"test["<>ToString[$Line]<>"]"];
		newTest[anchor]={EvaluationNotebook[],"test["<>ToString[$Line]<>"]"};
		SetOptions[cell,CellTags-> tags];		
	];	
	Return[newTest];
];

Options[runTest]={
	msgSuccess->(Print[Style[StringForm["``   ``: Ok",StringJoin[Table[" ",{3*StringCount[#1[module][fullname],"`"]}]],#1[name]],Darker[Green]]]&),
	msgFailure-> (Print[Style[StringForm["``   ``: Failed (expression evaluated to \"``\") ",StringJoin[Table[" ",{3*StringCount[#1[module][fullname],"`"]}]],#1[name],#2],Red],Hyperlink["go to test",#1[anchor]](*Button["to test",NotebookLocate["UnitTesting`"<>#1[fullname]]]*)]&)
};
runTest::error="Equivalence function for test \"`1`\" did not yield a boolean value. Result of comparison: `2`";
runTest[test_,OptionsPattern[]]:=Module[{result,evaluatedExpr,evaluatedVal},
	evaluatedExpr=ReleaseHold[test[expression]];
	evaluatedVal=ReleaseHold[test[value]];
	result=ReleaseHold[test[comparison][evaluatedExpr,evaluatedVal]];
	If[result=!=True && result =!=False,
		Message[runTest::error,test[fullname],result];
		result=False;
	];
	If[result && OptionValue[msgSuccess]=!=None,OptionValue[msgSuccess][test,evaluatedExpr]];
	If[!result && OptionValue[msgFailure]=!=None,OptionValue[msgFailure][test,evaluatedExpr]];
	Return[result];
];

Options[runModule]={
	msgBegin-> (Print[Style[StringForm["``Running unit test module \"``\"",StringJoin[Table[" ",{3*StringCount[#1[fullname],"`"]}]],#1[name]],Black]]&),
	msgEnd-> (Print[Style[StringForm["``Finished unit test module \"``\": `` successful tests, `` failures",StringJoin[Table[" ",{3*StringCount[#1[fullname],"`"]}]],#1[name],#2,#3],If[#3==0,Darker[Green],Red]]]&)
}~Join~Options[runTest];
runModule[module_,opts:OptionsPattern[]]:=Module[{countSuccess=0,countFailures=0,results},
	If[OptionValue[msgBegin]=!=None&&module[fullname]!="",OptionValue[msgBegin][module]];
	results=runTest[#,FilterRules[{opts}, Options[runTest]]]&/@module[tests];
	countSuccess=Count[results,True];
	countFailures=Length[results]-countSuccess;
	results=runModule[#,opts]&/@module[submodules];
	If[Length[results]>0,
		countSuccess=countSuccess+Total[Transpose[results][[1]]];
		countFailures=countFailures+Total[Transpose[results][[2]]];
	];
	If[OptionValue[msgEnd]=!=None&&module[fullname]!="",OptionValue[msgEnd][module,countSuccess,countFailures]];
	Return[{countSuccess,countFailures}];
];

runTests[opts:OptionsPattern[]]:=Module[{countSuccess=0,countFailures=0,results},
	Print["Running unit tests..."];
	results=runModule[globalModule,opts];
	countSuccess=results[[1]];
	countFailures=results[[2]];
	Print[Style[StringForm["Unit tests Finished: `` successful tests, `` failures", countSuccess,countFailures],If[countFailures==0,Darker[Green],Red]]];
];


End[ ];


EndPackage[ ];
