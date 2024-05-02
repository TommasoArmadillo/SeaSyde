(* ::Package:: *)

(* ::Input::Initialization:: *)
(* SeaSyde is a free software: you can redistribute it and/or modify
it under the terms of the GNUeral Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>. *)

(* This software is maintained on ______________ *)

ClearSystemCache[];
Unprotect@@Names["SeaSyde`*"];
ClearAll@@Names["SeaSyde`*"];
ClearAll@@Names["SeaSyde`Private`*"];

BeginPackage["SeaSyde`"];
Print["+++++ SeaSyde` +++++\nVersion 1.1.1"];
Print["SeaSyde is a package for solving the system of differential equation associated to the Master Integrals of a given topology."];
Print["For any question or comment, please contact: \n",Hyperlink["T. Armadillo","mailto:tommaso.armadillo@uclouvain.be"],", ",Hyperlink["R. Bonciani","mailto:roberto.bonciani@roma1.infn.it"],", ",Hyperlink["S. Devoto","mailto:simone.devoto@unimi.it"],", ",Hyperlink["N. Rana","mailto:narayan.rana@unimi.it"]," or ",Hyperlink["A. Vicini","mailto:alessandro.vicini@mi.infn.it"],"."];
Print["For the latest version please see the ",Hyperlink["GitHub repository","https://github.com/TommasoArmadillo/SeaSyde"],"."];

(* Begin Documentation *)
CurrentConfiguration::usage="CurrentConfiguration[]. Returns the current configuration for all the internal parameters.";
UpdateConfiguration::usage="UpdateConfiguration[NewConfiguration_]. Updates the current configuration. NewConfiguration must be a list of replacement rules, e.g. ParameterName -> newvalue. For the complete list of the parameters and their default value please refer to the documentation.";
ReadFrom::usage="ReadFrom[\"Path/to/file.m\"]. Utility function to read the content from a file *.m";
\[Epsilon]::usage="Symbol representing the dimensional regulator.";
eps::usage="Alternative symbol for the dimensional regulator. It is converted into \[Epsilon] in the code.";
GetPoint::usage="GetPoint[]. Get the point at which the boundary conditions are imposed.";
SolutionValue::usage="SolutionValue[]. Returns the value of the solution at the centre of the series expansion (i.e. GetPoint[]). Note that all the numbers are given with InternalWorkingPrecision digits. If it is unreadble consider using //N. To see only the nth MI use SolutionValue[][[n]].";
SolutionTable::usage="SolutionValue[]. Returns the value of the solution at the centre of the series expansion (i.e. GetPoint[]) as a List. Note that all the numbers are given with InternalWorkingPrecision digits. If it is unreadble consider using //N. To see only the mth \[Epsilon]-coefficient of the nth MI use SolutionTable[][[n,m]].";
SolutionTableExplicit::usage="SolutionTableExplicit[]. Returns the value of the solution at the centre of the series expansion (i.e. GetPoint[]) as a List {..., master[[i]] -> masterValue[[i]], ...}. Note that all the numbers are given with InternalWorkingPrecision digits. If it is unreadble consider using //N.";
Solution::usage="Solution[]. Returns the full solution to the system of differential equations. Note that all the coefficient are given with InternalWorkingPrecision digits. If it is unreadble consider using //N. To see only the nth MI use Solution[][[n]].";
SolveSystem::usage="SolveSystem[var_]. Solve the system of differential equations w.r.t. the variable var. The center of the series will be the point in which the BCs are imposed (i.e. GetPoint[]).";
SetSystemOfDifferentialEquation::usage="SetSystemOfDifferentialEquation[SystemOfEqs_, BCs_, MIs_, Variables_, PointBC_, Param_:{}]. Sets all the internal variables of the package and prepare the system of differential equations. To see the format in which every argoument should be given please refer to the documentation of the package.";
GetSystemOfDifferentialEquation::usage="GetSystemOfDifferentialEquation[]. Returns the system of differential equations togheter with the boundary conditions. If there are n MIs, the first n elements of the list are the equations w.r.t. the first kinematic variable, the second n equations are the ones w.r.t. to the second kinematic variable and so on. The last n elements are the BCs of the system.";
GetSystemOfDifferentialEquationExpanded::usage="GetSystemOfDifferentialEquationExpanded[]. Returns the system of differential equations after it has been \[Epsilon]-expanded. The output list has m elements, where m is the number of order in \[Epsilon] we are considering. The m-th element of the list contains the equations relevant for that particoular order and their corresponding BCs.";
TransportBoundaryConditions::usage="TransportBoundaryConditions[PhaseSpacePoint_List]. Transport the BCs for all the variables from the starting point (i.e. GetPoint[]) to PhaseSpacePoint. PhaseSpacePoint must be a List whose length is given by the number of kinematic variables. Its first element must be the final value for the first variable, its second element the value for the second variable, and so on. After transporting the boundary conditions, the point in which they are imposed is updated to PhaseSpacePoint.";
TransportVariable::usage="TransportVariable[Var_,Destination_,Line_:{}]. Transport the BCs for the variable Var from the starting point (i.e. GetPoint[]) to Destination. Note that the Destination point can be an arbitrary complex number. If the Line parameter is given, it will follow that line. Otherwise an internal algortihm will determine the best path to avoid singularities and branch-cuts. The line object can be created through the function CreateLine.";
CreateLine::usage="CreateLine[Points_List]. Returns an object line which connects all the points in Points through segments. Points must be a list of arbitrary complex points, the first one must be the one in which the BCs are imposed (i.e. GetPoint[]), the last one must be the Destination point.";
CreateGraph::usage="CreateGraph[MiNum_,EpsOrder_,left_,right_,OtherFunctions_:{}]. Plot the O(\!\(\*SuperscriptBox[\(\[Epsilon]\), \(EpsOrder\)]\)) for the MiNum-th Master Integral from left to right. Other functions can be passed in the OtherFunctions argoument in order to be plotted in the same graph.";
CheckSingularities::usage="CheckSingularities[]. Check if the singularities have a logarithmic behaviour, i.e. if they are associated to a branch-cut. It may be very time consuming.";
(* End Documentation *)

Begin["`Private`"];

(* Switch off some warnings *)
Off[Reduce::ratnz];
Off[NSolve::ratnz];
Off[Solve::ratnz];
Off[Solve::svars];
Off[General::stop];
Off[General::munfl];
Off[NRoots`Isolate::maxit];

(* Define some variables Global so that accessing the solution one sees x and not SeaSyde`Private`x *)
eps:=\[Epsilon];
x:=Global`x;
s:=Global`s;
t:=Global`t;
y:=Global`y;
tInt:=Global`tInt;

(* Functions for analytic continuation *)
Subscript[\[Theta], p][x_]:=HeavisideTheta[x];
Subscript[\[Theta], m][x_]:=HeavisideTheta[-x];

(* Configuration *)
PackageConfiguration={
"EpsilonOrder"->2,
	"ExpansionOrder"->50,
"InternalWorkingPrecision"->250,
"ChopPrecision"->100,
"LogarithmicExpansion"->False,
"RadiusOfConvergence"-> 2,
"LogarithmicSingularities"->{},
"SafeSingularities"->{},
"Warning"->True
}//Association;

UpdateConfiguration[l_List]:=UpdateConfiguration[l//Association];
UpdateConfiguration[newConfig_Association]:=Module[{newConf,keys,key,list},
list=newConfig//Normal;
newConf=Table[(list[[i,1]]//ToString)->list[[i,2]],{i,1,Length[list]}]//Association;
keys=ToString/@Keys[newConfig];
Do[
key=keys[[i]];
If[KeyExistsQ[PackageConfiguration,key], 
PackageConfiguration[key]=newConf[key];
PrintInfo["Updated ", key, " parameter, new value -> ",newConf[key]];
,
PrintWarning["Key ",key, " does not exist!"];
];
,{i,1,Length[newConfig]}];
];

CurrentConfiguration[]:=PackageConfiguration

EpsilonOrderPrivate := PackageConfiguration["EpsilonOrder"];
ExpansionOrderPrivate := PackageConfiguration["ExpansionOrder"];
MethodIntegrationPrivate := PackageConfiguration["MethodIntegration"];
InternalWorkingPrecisionPrivate:=PackageConfiguration["InternalWorkingPrecision"];
ChopPrecisionPrivate:=PackageConfiguration["ChopPrecision"];
LogarithmicExpansionPrivate:=PackageConfiguration["LogarithmicExpansion"];
RadiusOfConvergencePrivate:=PackageConfiguration["RadiusOfConvergence"];
LogarithmicSingularities:=PackageConfiguration["LogarithmicSingularities"];
SafeSingularities:=PackageConfiguration["SafeSingularities"];
WarningFlagPrivate:=PackageConfiguration["Warning"];
MaxLogOrder=0;

(* Print informations and errors *)
PrintInfo[args__]:=Print["SeaSyde: ",args];
PrintWarning[args__]:=Print[Style["SeaSyde Warning: ",Orange],args];
PrintError[mes__]:=(Print[Style["SeaSyde ERROR: ",Red],mes];Abort[];);

(* Internal variables. The function Reset is called inside SetSystemOfDifferentialEquations *)
Reset[]:=Module[{},
SystemOfDifferentialEquation = {};
SystemEpsilonExpanded = {};
MasterIntegrals= {};
MasterIntegralsFunctions={};         (* {Subscript[B, 1][x],Subscript[B, 2][x]} *)
MasterIntegralsPrototype={};        (* {Overscript[Subscript[B, 1], 0][x]+Overscript[Subscript[B, 1], 1][x] \[Epsilon]+Overscript[Subscript[B, 1], 2][x]\[Epsilon]^2,Overscript[Subscript[B, 2], 0][x]+Overscript[Subscript[B, 2], 1][x] \[Epsilon]+ Overscript[Subscript[B, 2], 2][x] \[Epsilon]^2} *)
Singularities = {};                              (* {{singularities for variable 1}, {singularities for variable 2}} *)
MasterIntegralsMobius={};
VariablesEq={x};
CurrentBC={0};
line={tInt};
lineParam=tInt;
DeltaPrescription={};
MinEpsExponent=0;
CurrentExpansionPoint=0;
CurrentBCLineParam = 0;
NumberMasterIntegrals=1;
LastKinematicVariableUsed=x;
KinematicParameters={};
AsymptoticBoundaryConditions=False;
AsymptoticVariable=x;
CheckSingularitiesDone=False;
MaxLogOrder=0;
ErrorEstimate=0;
];

(* Set the system and get it *)
SetSystemOfDifferentialEquation[EquationsExt_,BoundaryConditionsExt_,UnknownExt_,Variable_,PointBC_,Parameters_List:{}]:=Module[{Equations=EquationsExt,BoundaryConditions=BoundaryConditionsExt,Unknown=UnknownExt,Substitutions={},multipleLists},
Reset[];

(* Variables and prescriptions *)
VariablesEq=Variable/.Global`\[Delta]->0;
PrintInfo["There are ",VariablesEq//Length," kinematics variables ",VariablesEq];
DeltaPrescription=Table[If[Arg[Coefficient[Variable[[i]],Global`\[Delta]]]>=0,1,-1],{i,1,Length[Variable]}];
PrintInfo["The Feynman prescriptions for the variables are ",Table[If[DeltaPrescription[[i]]==1,+I Global`\[Delta], -I Global`\[Delta]],{i,1,Length[DeltaPrescription]}]];

KinematicParameters=Parameters//Rationalize//SetPrec;
CurrentBC= (PointBC/.KinematicParameters)//ChopDigits//Rationalize//SetPrec;
Equations=(((#/.{Equal->Subtract})==0&)/@Equations)/.KinematicParameters//ChopDigits;

(* Check that there are no extra masters *)
CheckMasters[Equations,Unknown,VariablesEq];

Equations=IncreasePrecision[Equations,Unknown,VariablesEq];
BoundaryConditions=(((#/.{Equal->Subtract})==0&)/@BoundaryConditions)/.KinematicParameters//ChopDigits;

BoundaryConditions=ExpandAndIncreasePrecision[BoundaryConditions,Unknown,VariablesEq,CurrentBC];
(* Note that if the MI do explicitly depend on \[Epsilon] we remove it *)
Do[Substitutions=Join[{
GetName[Unknown[[i]]][var___,VariablesEq[[-1]],\[Epsilon]]->GetName[Unknown[[i]]][var,VariablesEq[[-1]]],
GetName[Unknown[[i]]][var___,PointBC[[-1]],\[Epsilon]]->GetName[Unknown[[i]]][var,PointBC[[-1]]],
Derivative[d__,last_][GetName[Unknown[[i]]]][var___,VariablesEq[[-1]],\[Epsilon]]->Derivative[d][GetName[Unknown[[i]]]][var,VariablesEq[[-1]]]
},Substitutions],{i,1,Length[Unknown]}];
Unknown=Unknown/.Substitutions;
Equations=Equations/.Substitutions;
BoundaryConditions=BoundaryConditions/.Substitutions;

MasterIntegralsFunctions=Unknown;
MasterIntegralsPrototype=Unknown;
MasterIntegrals=Unknown;
NumberMasterIntegrals=Length[MasterIntegrals];
PrintInfo["There are ",NumberMasterIntegrals, " Master Integrals"];

PrintInfo["The boundary conditions are imposed in ",(LogicalExpand[VariablesEq==CurrentBC]/.And->List)//N];
DetermineAsymptoticBC[BoundaryConditions,VariablesEq];
If[AsymptoticBoundaryConditions, 
PrintInfo["The boundary conditions are given as asymptotic limit. Note that the first solution of the system must be with respect to ", AsymptoticVariable];
,
PrintInfo["The boundary conditions are given as precise value of the solution."];
];
SystemOfDifferentialEquation=Join[Equations,BoundaryConditions];
PrintInfo["There are ",Length[Equations], " equations and ", Length[BoundaryConditions], " boundary conditions"];
Singularities=FindSingularities[Equations,VariablesEq]/.KinematicParameters//ChopDigits;
PrintInfo["The possible singularities for the kinematics variables ",VariablesEq," are respectively ",Singularities//N];

MinEpsExponent=FindMinEpsilonExponentBC[BoundaryConditions];
EpsilonExpandDiffEq[];

PrintInfo["The system of differential equation has been set and expanded in \[Epsilon]"];
multipleLists=Table[{},{i,1,Length[VariablesEq]}];
If[(MatchQ[SafeSingularities,{}]||MatchQ[SafeSingularities,multipleLists])||(MatchQ[LogarithmicSingularities,{}]||MatchQ[LogarithmicSingularities,multipleLists]),
PackageConfiguration["LogarithmicSingularities"]=Singularities;
,
CheckSingularitiesDone=True;
];
If[MatchQ[SafeSingularities,{}],PackageConfiguration["SafeSingularities"]=multipleLists;];
If[MatchQ[LogarithmicSingularities,{}],PackageConfiguration["LogarithmicSingularities"]=multipleLists;];
];

CheckMasters[equations_,masters_,variables_]:=Module[{masterList,extraMasters},
masterList=DeleteCases[Cases[equations,f_[Apply[Sequence,variables]]/;(f=!=Times&&f=!=Plus),Infinity],Derivative[__][_][Apply[Sequence,variables]]]//DeleteDuplicates;
If[!ContainsAll[masters,masterList],
extraMasters=Complement[masterList,masters];
PrintError["The set of equations contains the following masters that do not appear in the master list parameter: ",extraMasters];
];
];

IncreasePrecision[expression_,masters_,variables_,boundCond_:{}]:=Module[{kinSub={},subst={},invSub={},subD={},invSubD={},temporaryExpr},
subst=Table[GetName[masters[[i]]]->ToExpression["f"<>ToString[i]],{i,1,Length[masters]}];
invSub=Table[ToExpression["f"<>ToString[i]]->GetName[masters[[i]]],{i,1,Length[masters]}];
temporaryExpr=expression//.subst;
temporaryExpr=SetPrec[Num[temporaryExpr]];
Return[temporaryExpr//.invSub];
];

ExpandAndIncreasePrecision[expression_,masters_,variables_,boundCond_:{}]:=Module[{kinSub={},subst={},invSub={},subD={},invSubD={},temporaryExpr},
subst=Table[GetName[masters[[i]]]->ToExpression["f"<>ToString[i]],{i,1,Length[masters]}];
invSub=Table[ToExpression["f"<>ToString[i]]->GetName[masters[[i]]],{i,1,Length[masters]}];
temporaryExpr=Normal[Series[expression//.subst,{eps,0,EpsilonOrderPrivate}]];
temporaryExpr=SetPrec[Num[temporaryExpr]];
Return[temporaryExpr//.invSub];
];

EpsilonExpandDiffEq[]:=
Module[{expansionSubstitutionFunctions,expansionSubstitutionDerivatives,system,systemExpanded, orderEps=EpsilonOrderPrivate,terms,exponent},
MasterIntegralsPrototype=MasterIntegralsFunctions;
expansionSubstitutionFunctions=Table[GetName[MasterIntegralsFunctions[[i]]][var__]->Sum[\!\(\*OverscriptBox[\((GetName[MasterIntegralsFunctions[\([\)\(i\)\(]\)]])\), \((j)\)]\)[var]eps^j,{j,MinEpsExponent,orderEps}],{i,1,Length[MasterIntegralsFunctions]}];
 expansionSubstitutionDerivatives=Table[Derivative[d__][GetName[MasterIntegralsFunctions[[i]]]][var__]->Sum[Derivative[d][\!\(\*OverscriptBox[\((GetName[MasterIntegralsFunctions[\([\)\(i\)\(]\)]])\), \((j)\)]\)][var]eps^j,{j,MinEpsExponent,orderEps}],{i,1,Length[MasterIntegralsFunctions]}];
system=SystemOfDifferentialEquation/.Equal[elem_,0]->Normal[Series[elem,{eps,0,orderEps+1}]];
system=system/.Join[expansionSubstitutionFunctions,expansionSubstitutionDerivatives];
systemExpanded=Table[Table[0,Length[system]],orderEps+Abs[MinEpsExponent]+1];

Do[
(* For better handling, the first index refers to # eq while the second one get the LeftHandSide *)
terms=Series[system[[i]]//ChopDigits,{eps,0,orderEps}]//Normal//Expand;
Do[
exponent=Exponent[terms[[j]],eps];
If[exponent>EpsilonOrderPrivate,Continue[];];
If[exponent+Abs[MinEpsExponent]+1===0,Print[terms[[j]]//N];Abort[];];
systemExpanded[[exponent+Abs[MinEpsExponent]+1,i]] +=Coefficient[terms[[j]],eps,exponent];
,{j,Length[terms]}];
,{i,Length[system]}];
systemExpanded=((systemExpanded//Collect[#,{fun_[x]}]&)/.{Times[Co_,fun_[x]]:>Times[Together[ExpandAll[Co]],fun[x]]});
SystemEpsilonExpanded=Map[Function[x,Equal[x,0]],systemExpanded,{2}]//ChopDigits;
MasterIntegralsPrototype=Table[Table[\!\(\*OverscriptBox[\(GetName[MasterIntegralsFunctions[\([\)\(j\)\(]\)]]\), \(i\)]\)[(VariablesEq/.{List->Sequence})],{j,1,Length[MasterIntegralsFunctions]}],{i,MinEpsExponent,orderEps}];
];

UpdateSystemEpsilonExpanded[]:=Module[{expansionSubstitutionFunctions,newBoundaryConditions},	
SystemEpsilonExpanded=Drop[#1,-NumberMasterIntegrals]& /@SystemEpsilonExpanded;	
expansionSubstitutionFunctions=
Table[GetName[MasterIntegralsFunctions[[i]]][var__]->Sum[\!\(\*OverscriptBox[\((GetName[MasterIntegralsFunctions[\([\)\(i\)\(]\)]])\), \((j)\)]\)[var]eps^j,{j,MinEpsExponent,EpsilonOrderPrivate}],{i,1,Length[MasterIntegralsFunctions]}];
newBoundaryConditions=SystemOfDifferentialEquation[[-NumberMasterIntegrals;;-1]]/.expansionSubstitutionFunctions;
newBoundaryConditions=newBoundaryConditions/.Equal->Subtract;		
Do[		
Do[	
AppendTo[SystemEpsilonExpanded[[i+Abs[MinEpsExponent]+1]], Coefficient[newBoundaryConditions[[j]],eps,i]==0];		
,{j,1,NumberMasterIntegrals}];	
,{i,MinEpsExponent,EpsilonOrderPrivate}];
];

GetSystemOfDifferentialEquation[]:=Module[{},
SystemOfDifferentialEquation
];

GetSystemOfDifferentialEquationExpanded[]:=Module[{},
SystemEpsilonExpanded
];

(* Utility functions *)
Num:=N[#,InternalWorkingPrecisionPrivate]&;
NumAlmost:=N[#,100]&;    (* Usefull in some boundary conditions *)
ChopDigits:=Chop[#,10^-ChopPrecisionPrivate]&;
ChopExtraDigits:=Chop[#,10^(-ChopPrecisionPrivate-50)]&;
ChopLine:=Chop[#,10^(-ChopPrecisionPrivate/2)]&;
SetPrec:=ChopDigits[SetPrecision[#,InternalWorkingPrecisionPrivate]]&;
SetUltraPrec:=ChopDigits[N[Rationalize[#,10^(-InternalWorkingPrecisionPrivate-200)],InternalWorkingPrecisionPrivate+200]]&;
SetPrecNumber:=(#/.{num_Real:>SetUltraPrec[num],num_Complex:>SetUltraPrec[num]})&;
MyAsymptotic:=If[$VersionNumber>=12.1,Asymptotic,MyAsymptoticInternal];
MyLimit=If[$VersionNumber>=12.1,QuickLimit,Limit];

QuickLimit[expression_,v_->pt_]:=Module[{asympt},
asympt=Asymptotic[expression,v->pt];
Return[Limit[expression,v->pt]];
];

MyAsymptoticInternal[expression_,v_->pt_]:=Module[{result,exponent},
If[FreeQ[Quiet[expression/.v->pt],Indeterminate|Infinity|DirectedInfinity[_]|ComplexInfinity],Return[expression/.v->pt];];
If[Length[Cases[expression,Power[v,Complex[re_,im_]],Infinity]]>0,
exponent=Cases[expression,Power[v,Complex[re_,im_]]->re,Infinity]//Min//Ceiling;
,
exponent=Exponent[expression,v,Min]//Max//Ceiling;
];
result=Normal[Series[expression,{v,pt,exponent}]];
exponent=Exponent[result,v,Min];
result=Coefficient[result,v,exponent]v^exponent;
Return[result];
];

IncreaseInternalWorkingPrecision[]:=Module[{},
PackageConfiguration["InternalWorkingPrecision"]+=50;
SystemOfDifferentialEquation = SystemOfDifferentialEquation//SetPrec;
SystemEpsilonExpanded = SystemEpsilonExpanded//SetPrec;
Singularities = Singularities//SetPrec;
CurrentBC=CurrentBC//SetPrec;
CurrentExpansionPoint=CurrentExpansionPoint//SetPrec;
CurrentBCLineParam =CurrentBCLineParam//SetPrec ;
];

ReadFrom[Path_String]:=Module[{Content={}},
If[$FrontEnd=!=Null,SetDirectory[NotebookDirectory[]]];
Content=Quiet@Check[Get[Path],$Failed];
If[MatchQ[Content,$Failed], PrintError["File ", Path, " does not exists or it is empty, check if it is spelled correctly and try again."];];
PrintInfo["File ", Path, " has been correctly read."];
Content
];

FindMinEpsilonExponentEQ[Equations_]:=Module[{MinExpEQ=0},
Do[
MinExpEQ=Min[Cases[Equations//Expand,_*\[Epsilon]^b_ MasterIntegralsFunctions[[mi]]->b,Infinity]//Min,MinExpEQ];
,{mi,1,Length[Equations]}];
Return[MinExpEQ];
];

FindMinEpsilonExponentBC[Boundary_]:=Module[{MinExpBC=0},
Do[
MinExpBC=Min[Exponent[Boundary[[mi,1]],eps,Min],MinExpBC];
,{mi,1,Length[Boundary]}];
Return[MinExpBC];
];

FindSingularities[SystemEquations_,Variables_]:=Module[{Singularities,AllEquations,DenominatorEquation,SingularPoints},
AllEquations=SystemEquations/.{Equal->Subtract};
Singularities=Table[{},{i,1,Length[Variables]}];
AllEquations=DeleteCases[AllEquations,Except[Plus[_,__]]];
AllEquations=AllEquations/.\!\(\*
TagBox[
StyleBox[
RowBox[{
RowBox[{
RowBox[{"Derivative", "[", "__", "]"}], "[", "_", "]"}], "[", "__", "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)->0;
Do[
	AllEquations=Collect[AllEquations,MasterIntegralsFunctions[[i]]];
,{i,1,Length[MasterIntegralsFunctions]}];
Do[
AllEquations[[i,0]]=List;
,{i,1,Length[AllEquations]}];

AllEquations=AllEquations//Rationalize//Together//Denominator//Flatten//DeleteDuplicates//ChopDigits;
AllEquations=AllEquations/.eps->0;
Do[
If[Head[AllEquations[[i]]]===Times,AllEquations[[i]]=Apply[List,AllEquations[[i]]];];
,{i,Length[AllEquations]}];
AllEquations=AllEquations//Flatten//DeleteDuplicates;

Do[
	Do[
SingularPoints=Solve[AllEquations[[j]]==0,Variables[[i]],Complexes];	
Singularities[[i]]=Join[Singularities[[i]],SingularPoints/.{List[Rule[_,val_]]->val}];
	,{j,Length[AllEquations]}];
Singularities[[i]]=Singularities[[i]]//Flatten//Rationalize//Simplify//DeleteDuplicates//Num//DeleteDuplicates[#,(Abs[#1-#2]<1*^-15&)]&;
,{i,Length[Variables]}];
Singularities
];

DetermineAsymptoticBC[BoundaryConditionsToStudy_,VariablesOfEquations_]:=Module[{},
Do[
If[FindVar[BoundaryConditionsToStudy, VariablesOfEquations[[i]]],
AsymptoticBoundaryConditions=True;
AsymptoticVariable=VariablesOfEquations[[i]];
Break[];
];
,{i,1,Length[VariablesOfEquations]}];
];

FindVar[expr_, var_] := Module[{temp},
	temp = Hold[expr] /. var -> 0;
	If[temp === Hold[expr], False, True]
];

GetName[f_[x__]]:=f;
GetVariable[f_[var_,___]]:=var;

MyDerivative[Unknown_,variables_,line_,lineParam_,i_,f_]:=Module[{var},
var=GetVariable[Unknown[[i]]];
Return[D[Unknown[[i]],variables]->1/D[line,lineParam] Subscript[f, i]'[lineParam]];
];

(* Solve the system of differential equations *)
SolveSystem[variable_]:=SolveSeriesExpansionSafe[tInt,variable,True,False];

SolveSeriesExpansionSafe[line_,variable_,CalledFromNotebook_Symbol:True,AlreadyCalled_Symbol:False]:=Quiet[Check[
SolveSeriesExpansion[line,variable,CalledFromNotebook];
,
If[AlreadyCalled, PrintError["The increase in the precision was not sufficient. Try to increase it manually."];];
IncreaseInternalWorkingPrecision[];
PrintWarning["The InternalWorkingPrecision was too low. It has been increased to ",InternalWorkingPrecisionPrivate];
SolveSeriesExpansionSafe[line//SetPrec,variable,CalledFromNotebook,True];
,
RowReduce::luc
],RowReduce::luc];

SolveSeriesExpansion[line_,variable_,CalledFromNotebook_Symbol:True]:=Module[{EpsOrder=MinEpsExponent,Sol,Equation,EquationTmp,BoundCond,var,AlreadySolved={},tmp,numMI=Length[MasterIntegralsFunctions],lineParam=tInt,index=1,OtherVarBC={},correctionOrder,singul},

If[!MemberQ[VariablesEq,variable],PrintError["The variable ",variable," is not a valid variable!"]];

If[AsymptoticBoundaryConditions && !MatchQ[variable,AsymptoticVariable],PrintError["The boundary conditions are given as asymptotic limit for ",AsymptoticVariable,", the system can not be solved with respect to ",variable];
];
LastKinematicVariableUsed=variable;   (* This will be useful for CreateGraph *)
If[CalledFromNotebook,
Do[
If[MatchQ[variable,VariablesEq[[i]]],
CurrentExpansionPoint=Solve[line== (CurrentBC[[i]]), lineParam,WorkingPrecision->InternalWorkingPrecisionPrivate][[1,1,2]]//Chop;
CurrentBCLineParam =CurrentExpansionPoint;
Break[];
];
,{i,1,Length[VariablesEq]}];
];
Do[
If[MatchQ[variable,VariablesEq[[i]]],
Break[];
];
index += NumberMasterIntegrals;
,{i,1,Length[VariablesEq]}];

(* Correction to the order of resolution*)
correctionOrder=Min[Exponent[SystemOfDifferentialEquation[[index;;index+NumberMasterIntegrals-1]]/.{Equal->Subtract},variable,Min]];
If[correctionOrder<0,PackageConfiguration["ExpansionOrder"]-=correctionOrder;];

SeaSyde`Private`Debug`EpsOrder=MinEpsExponent;
Do[
If[CalledFromNotebook,Print["Solving equation for \[Epsilon] order ",EpsOrder];];
tmp=SystemEpsilonExpanded[[nEps]];
EquationTmp=tmp[[index;;index+NumberMasterIntegrals-1]];
BoundCond=tmp[[-NumberMasterIntegrals;;-1]];
(* Substitute other variable value *)
Do[
If[!MatchQ[variable,VariablesEq[[i]]],
OtherVarBC=Join[OtherVarBC,{VariablesEq[[i]]-> CurrentBC[[i]]}];
];
,{i,1,Length[VariablesEq]}];
Quiet[Check[
Equation=EquationTmp/.OtherVarBC;
,
Equation=SafeSubstitute[EquationTmp,OtherVarBC];
]];
BoundCond=BoundCond/.OtherVarBC;
var=MasterIntegralsPrototype[[nEps]]/.OtherVarBC;
Sol=SolveEquation[Equation,BoundCond,var,variable,EpsOrder,line, lineParam,CurrentExpansionPoint,AlreadySolved]//Num//ChopDigits;

AlreadySolved=Join[AlreadySolved,Table[var[[i]]->Sol[[i]],{i,1,Length[var]}]];
EpsOrder++;
SeaSyde`Private`Debug`EpsOrder++;
,{nEps,1,Length[SystemEpsilonExpanded]}];
MasterIntegrals=MasterIntegralsFunctions/.Table[GetName[MasterIntegralsFunctions[[i]]][var__]->Sum[\!\(\*OverscriptBox[\((GetName[MasterIntegralsFunctions[\([\)\(i\)\(]\)]])\), \((j)\)]\)[var]eps^j,{j,MinEpsExponent,EpsilonOrderPrivate}],{i,1,Length[MasterIntegralsFunctions]}];
MasterIntegrals=MasterIntegrals/.OtherVarBC;
MasterIntegrals=MasterIntegrals/.AlreadySolved;
MasterIntegrals=AnalyticContinuation[MasterIntegrals,variable,line,CurrentExpansionPoint];
(* Correction due to the order *)
If[correctionOrder<0,PackageConfiguration["ExpansionOrder"]+=correctionOrder;ClearSeries[MasterIntegrals,variable,ExpansionOrderPrivate];];
If[CalledFromNotebook,
Do[
If[MatchQ[VariablesEq[[ind]],variable],singul=Singularities[[ind]]/.GetPoint[];Break[];];
,{ind,Length[VariablesEq]}];
Print["I solved the system of equation. The error estimate is: ",EstimateError[variable],". The radius of convergence is: ",ExpectedConvergenceRadius[line/.lineParam->CurrentExpansionPoint,singul,variable]//N];];
];

SafeSubstitute[expression_,replacement_]:=Module[{finalExpr,coefficientDer},
finalExpr=expression/.{Derivative[der__][fun_][var__]->SeaSydeDerivative Derivative[der][fun][var],Equal->Subtract};
Do[
coefficientDer=(Coefficient[finalExpr[[iExpr]],SeaSydeDerivative]//Rationalize//Simplify//Num)/.replacement;
finalExpr[[iExpr]]=ChopDigits[Num[Simplify[Rationalize[finalExpr[[iExpr]]/.SeaSydeDerivative->0,10^-InternalWorkingPrecisionPrivate]]/.replacement]];
finalExpr[[iExpr]]=(finalExpr[[iExpr]]+coefficientDer==0);
,{iExpr,1,Length[expression]}];
Return[finalExpr];
];

SolveEquation[EquationExt_, BoundaryConditions_,  Unknown_,KinVariable_,EpsOrder_,line_,lineParam_,PointExpansion_,AlreadySolved_:{}]:=Module[{Eq=EquationExt,newUnknown,newDerivatives,newFunctions,BC,newBC,solution={},oldVar,coeffDerivative,substitution={},numberSolved,dependencies,dependenciesNumber,numberOfEqs,eqTmp,bcTmp,funTmp,MIalreadySolved={},index,sub={lineParam->Variable`tmpVar},antiSub={Variable`tmpVar->lineParam},tmpExp=PointExpansion,equationSolved},

(* Substitute already solved equations *)
Eq=EquationExt/.AlreadySolved;

(* Substitute functions *)
newUnknown=Table[Unknown[[i]]->Subscript[f, i][lineParam],{i,1,Length[Unknown]}];
newFunctions=Table[Subscript[f, i][lineParam],{i,1,Length[Unknown]}];

newDerivatives=Table[MyDerivative[Unknown,KinVariable,line,lineParam,i,f],{i,1,Length[Unknown]}];

Eq=Eq/.Join[newUnknown,newDerivatives];

(* Substitute line *)
Eq=Eq/.Power[basePH_,exponentPH_]/;exponentPH>0:>Power[Simplify[basePH],exponentPH]//Num//ChopDigits;
Eq=Eq/.KinVariable->line;

(* Substitute BC *)
newBC=(Table[GetName[Unknown[[i]]][__]->Subscript[f, i][lineParam],{i,1,Length[Unknown]}]/.Join[{KinVariable-> (line/.{lineParam-> PointExpansion})},{lineParam->PointExpansion}]);
BC=Solve[(BoundaryConditions)/.newBC,Table[newBC[[i,2]],{i,1,Length[BoundaryConditions]}],WorkingPrecision->InternalWorkingPrecisionPrivate][[1]]/.{Rule-> Equal};
BC=Sort[BC,#1[[1,0,2]]<#2[[1,0,2]]&];
BC=BC/.{KinVariable->line};

(* Make sure the coefficient of derivatives is 1 *)
coeffDerivative=1/D[line,lineParam];
Do[
Eq[[i]]=MultiplySides[Eq[[i]],1/coeffDerivative];
Eq[[i,1]]=(Eq[[i,1]]/.Subscript[f, i]'[lineParam]->0)+Subscript[f, i]'[lineParam];
,{i,1,Length[Eq]}];

Do[If[MatchQ[VariablesEq[[i]],KinVariable],index=i;];,{i,1,Length[VariablesEq]}];
If[!CloseToSing[line/.lineParam->PointExpansion,Singularities[[index]]/.GetPoint[]],
Eq=Normal[Series[Eq/.{Subscript[f, m_][lineParam]->Subscript[f, m],Subscript[f, m_]'[lineParam]->Subscript[f, m]'},{lineParam,PointExpansion,ExpansionOrderPrivate}]]/.{Subscript[f, m_]->Subscript[f, m][lineParam],Subscript[f, m_]'->Subscript[f, m]'[lineParam]}//SetPrec;
];

(* SOLVE THE SYSTEM *)
numberSolved=0;
While[numberSolved<NumberMasterIntegrals,
dependencies=DependsOnSystem[Eq];
dependenciesNumber=Length/@dependencies;
numberOfEqs=Min[dependenciesNumber];
equationSolved={};
Do[
If[dependenciesNumber[[count1]]=!=numberOfEqs||ContainsAny[MIalreadySolved,dependencies[[count1]]],Continue[];];
SeaSyde`Private`Debug`MInumber=dependencies[[count1]];

eqTmp={};bcTmp={};

funTmp=newFunctions[[dependencies[[count1]]]]//ToListAlways;
AppendTo[equationSolved,dependencies[[count1]]];
Do[
If[dependencies[[count1]]==dependencies[[count2]],
AppendTo[eqTmp,Eq[[count2]]//ChopDigits];
AppendTo[bcTmp,BC[[count2]]//ChopDigits];
];
,{count2,count1,Length[Eq]}];
solution=SolveEquationBySeriesExpansion[eqTmp,bcTmp,funTmp,lineParam,PointExpansion,line,KinVariable];
substitution=Join[substitution,Table[Subscript[f, dependencies[[count1,index]]][lineParam]->solution[[index]],{index,1,numberOfEqs}]];
AppendTo[MIalreadySolved,dependencies[[count1]]];
MIalreadySolved=Flatten[MIalreadySolved];
numberSolved+=numberOfEqs;
,{count1,1,Length[Eq]}];

Eq=Delete[Eq,Position[dependencies,Alternatives@@equationSolved]]/.substitution;
BC=Delete[BC,Position[dependencies,Alternatives@@equationSolved]];
];

solution=Table[Subscript[f, h][lineParam],{h,NumberMasterIntegrals}]/.substitution;
(* Get back to original variables *)
oldVar=Solve[KinVariable== line,lineParam][[1]]//Expand;
solution/.oldVar
];

DependsOnEquation[equationExt_]:=Sort[DeleteDuplicates[Cases[Variables[equationExt/.Equal->Plus],(Subscript[f, num_][tInt]|Subscript[f, num_]'[tInt])->num]]];

DependsOnSystem[system_]:=DependsOnEquation/@system;

DetermineR[Equations_,var_,varNumber_]:=Module[{polynomial,minExp,solOrd,RValues={},indicial={},coefficient,polynomialTot,RValuesInt,RValuesHalf},
polynomialTot=Equations/.{Power[var,r]->1,Power[var,r+a_]->Power[l,a]}/.var->l;
Do[
polynomial=polynomialTot[[i,1]]//Expand//ChopDigits;
minExp=Exponent[polynomial,l,Min]//Chop;
coefficient=CoefficientList[Coefficient[polynomial,l,minExp],Log[l]]/.l->0;
indicial=Join[indicial,Map[Equal[#,0]&,coefficient]];
,{i,1,varNumber}];

solOrd=Solve[indicial,WorkingPrecision->10];
solOrd=DeleteCases[solOrd,Except[{___,r->_,___}]];
solOrd=solOrd/.{xx___,r->a_,yy___}->(r->Round[a,1/2]);
RValues=Sort[solOrd,#1[[2]]<#2[[2]]&];

RValuesInt=Cases[RValues,Rule[r,xx_]/;Mod[2xx,2]===1]//CleanList;
RValuesHalf=Cases[RValues,Rule[r,xx_]/;Mod[2xx,2]===0]//CleanList;

If[RValuesInt==={}&&RValuesHalf=!={},Return[RValuesHalf];];
If[RValuesInt=!={}&&RValuesHalf==={},Return[RValuesInt];];
Return[Join[RValuesInt,RValuesHalf]];
];

CleanList[list_List]:=Module[{},
If[list==={}||Length[list]===1,Return[list];];
Return[{list[[1]]}];
];

InequalityToNumber[sol_]:=Module[{\[Delta]=1*^-3,b=sol[[2]]},
If[MatchQ[sol, SubMinus[r]<_], Return[b+\[Delta]],Return[b-\[Delta]]];
];

EqualityToNumber[sol_]:=Module[{solutions=sol[[1]],val},
Do[
If[MatchQ[solutions[[i,1]],Subscript[r, _]], val=solutions[[i,2]];];
,{i,1,Length[solutions]}];
val
];

SolveFrobeniusSystem[SystemOfEquations_,Functions_,LineParam_,PointExpansion_]:=Module[{solution,completeSolution,param,numberOfParam},
completeSolution=Table[Table[0,{j,1,Length[Functions]}],{i,1,Length[Functions]}];
Do[
solution=SolveFrobenius[SystemOfEquations,Functions,LineParam,PointExpansion,counter-1];
param=solution/._*c[elem__]->c[elem]/.Plus->List//Flatten//DeleteDuplicates//DeleteCases[#,0]&;
solution=solution/.Table[param[[i]]->C[i],{i,1,Length[param]}];
numberOfParam=Length[param];
If[param==={},PrintError["Something went wrong while trying to solve the homogeneous equations."];];

Which[numberOfParam===Length[Functions],Break[];,
param==={}||numberOfParam>Length[Functions],
PrintError["Something went wrong while trying to solve the homogeneous equations for MIs: "<>ToString[SeaSyde`Private`Debug`MInumber]<>", \[Epsilon] order: "<>ToString[SeaSyde`Private`Debug`EpsOrder]<>"."];];
,{counter,Length[Functions]}];
If[numberOfParam=!=Length[Functions],PrintError["Something went wrong while trying to solve the homogeneous equations for MIs: "<>ToString[SeaSyde`Private`Debug`MInumber]<>", \[Epsilon] order: "<>ToString[SeaSyde`Private`Debug`EpsOrder]<>"."];];
Do[
Do[
completeSolution[[j,i]]=solution[[j]]/.Table[C[k]->KroneckerDelta[k,i],{k,1,Length[param]}];
,{j,1,Length[Functions]}];
,{i,1,Length[param]}];
Return[completeSolution];
];

CreateSeries[x_,x0_,i_,j_,n_]:=Sum[c[i,j,l](x-x0)^l,{l,0,n}];

SolveFrobenius[EquationExtF_,FunctionsF_,LineParamF_,PointExpansionF_,logTerms_]:=Module[{Equation = Num[EquationExtF],EquationSub,Solution,RRules,min,max,sol,coeff,order,index=1,CompleteSol,returnValue,otherSol,length=Length[FunctionsF],SolutionComplete,cnt=0,systemsEquations},
(* Expand in z=lineParam-pointExp *)

Equation=Equation/.{Subscript[f, m_][_]->Subscript[f, m],Subscript[f, m_]'[_]->Subscript[f, m]'};
Equation=Equation/.{LineParamF-> z+PointExpansionF}//Expand;     

Equation=Normal[Series[Equation,{z,0,ExpansionOrderPrivate+5}]];   

Equation=Equation/.{Subscript[f, m_]->Subscript[f, m][z],Subscript[f, m_]'->Subscript[f, m]'[z]};
SolutionComplete=Table[0,{i,length}];
Equation=Equation/.{Subscript[f, i_]->((#)^r Sum[
Sum[CreateSeries[#,0,i,count-j,ExpansionOrderPrivate+5] Log[#]^j/j!,{j,0,count}]
,{count,0,logTerms}]&)};
Equation=ClearSeries[Equation//Expand,z,ExpansionOrderPrivate+5]//ChopDigits;
RRules= DetermineR[Equation,z, length];
Do[
cnt++;
Solution=Table[((#-PointExpansionF)^r Sum[
Sum[CreateSeries[#,PointExpansionF,i,count-j,ExpansionOrderPrivate+5] Log[#-PointExpansionF]^j/j!,{j,0,count}]
,{count,0,logTerms}]&)[LineParamF],{i,FunctionsF/.Subscript[f, k_][_]->k}];
(* substitute R values in Solution and Equation *)
Solution=Solution/.rRule;
EquationSub = (Equation /.rRule)//ChopDigits;
(* Solve order by order *)
(* Note that we substitute Subscript[c, _,0]\[Rule]1 because the solution will depend by it and temporarily eliminating it we can speed up computation *)
max=ExpansionOrderPrivate;
EquationSub=EquationSub/.{Equal->Subtract}//ChopDigits;
If[Im[rRule[[2]]]=!=0,EquationSub=EquationSub/z^rRule[[2]]//Expand;];
min=Min[Exponent[EquationSub,z,Min]];
order=min;
CompleteSol={};
While[order<=  max,
coeff=Coefficient[EquationSub,z,order];
coeff=(coeff//.CompleteSol)//ChopDigits;
coeff=CoefficientList[coeff,Log[z]]//Flatten;
coeff=Expand[coeff]/.{num_Real:>SetUltraPrec[num],num_Complex:>SetUltraPrec[num]}//ChopDigits;
systemsEquations=Table[Simplify[coeff[[i]]]==0,{i,1,Length[coeff]}];
sol=MySolve[systemsEquations];

If[sol=!={}&&Length[sol]>0,
CompleteSol=Join[CompleteSol,sol[[1]]];
];
order++;
index++;
];
SolutionComplete+=((Solution//.CompleteSol)/.c[_,_,i_]/;i>= (max-r/.rRule)->0/.c[xx__]->c[xx,cnt]);
,{rRule,RRules}];
returnValue=Collect[SolutionComplete,{c[__],Log[__]}]//ChopDigits//SetPrec;
Return[returnValue];
];

SolveEquationBySeriesExpansion[EquationExt_,BoundaryConditionExt_,Functions_,LineParam_,PointExpansion_,LineParametrization_,KinVariab_]:=Module[{BoundaryCondition,BCs,Homogeneus,HomogeneusSolution,HomogeneusSolutionTmp,ParticoularSolution,Inhomogenues,CompleteSolution,InverseHomogeneusSeries,InhomogenuesSeries,Integrand,IntegratedSeries,DefiniteIntegratedSeries,points,BCPoint,CompleteAnalytic,InverseHomogeneusSolution,sub,indexKin},
(* CHECK FOR sInt != 0 *)
BoundaryCondition=BoundaryConditionExt/.{LineParam->sInt+PointExpansion}/.{Log[coeff_*sInt]->Log[coeff]+Log[sInt]}//Expand;
BoundaryCondition=Table[BoundaryCondition[[i,2]],{i,1,Length[BoundaryCondition]}];
Homogeneus=MakeHomogeneus[EquationExt,Functions]//SetPrec;
Inhomogenues=InomogeusPart[EquationExt]//SetPrec;
Inhomogenues=(Inhomogenues/.{LineParam->sInt+PointExpansion});
sub=DeleteDuplicates[Cases[Inhomogenues,Log[a_]|Power[a_,_]->a,Infinity]];
sub=Table[{Log[elem]->ChopDigits[Log[Expand[elem]]],Power[elem,exp_]->Power[ChopDigits[Expand[elem]],exp]},{elem,sub}]//Flatten;
Inhomogenues=Inhomogenues/.sub;
Inhomogenues=Inhomogenues/.{Log[x_]:>Log[Expand[x]]}/.{Power[x_,exp_]:>Power[Expand[x],exp]}//Num//SetPrec;
Inhomogenues=Inhomogenues/.{Log[coeff_*sInt]:>Log[coeff]+Log[sInt]}//Num//SetPrec;
HomogeneusSolution=SolveFrobeniusSystem[Homogeneus,Functions,LineParam,PointExpansion]//Num//SetPrec;
BCPoint=CurrentBCLineParam-PointExpansion//ChopDigits//SetPrec;
HomogeneusSolution=(HomogeneusSolution/.{LineParam->sInt+PointExpansion})//ChopDigits//SetPrec;
HomogeneusSolutionTmp=Series[SetUltraPrec[HomogeneusSolution],{sInt,0,ExpansionOrderPrivate+5}];

(* If we are onto a singular point we use a safer implementation, otherwise we use a quicker one *)
Do[If[MatchQ[VariablesEq[[i]],KinVariab],indexKin=i;];,{i,1,Length[VariablesEq]}];
If[!CloseToSing[LineParametrization/.LineParam->PointExpansion,Singularities[[indexKin]]/.GetPoint[]],
InverseHomogeneusSolution=MyInverse[HomogeneusSolutionTmp];
,
InverseHomogeneusSolution=Inverse[HomogeneusSolutionTmp];
];
InverseHomogeneusSeries=
Normal[Series[ClearSeries[ExpandAll[Normal[InverseHomogeneusSolution]],sInt,ExpansionOrderPrivate+5],{sInt,0,ExpansionOrderPrivate+5}]]//SetPrec;

Inhomogenues=Inhomogenues//Expand//ChopDigits;
InhomogenuesSeries=Table[
Collect[Inhomogenues[[i]],{Log[__],Log[__]^_},Normal[Series[#,{SeaSyde`Private`sInt,0,ExpansionOrderPrivate+3}]]&]
,{i,Length[Inhomogenues]}];
InhomogenuesSeries=InhomogenuesSeries//SetPrec//Num;
Integrand=ClearSeries[InverseHomogeneusSeries . InhomogenuesSeries//ExpandAll,sInt,ExpansionOrderPrivate+5];
IntegratedSeries= Collect[MyIntegrate[Integrand],Log[__]]//Num//ChopDigits;
ParticoularSolution=Collect[ClearSeries[HomogeneusSolution . IntegratedSeries//ExpandAll//ChopDigits,sInt,ExpansionOrderPrivate],Log[__]];
CompleteSolution=HomogeneusSolution . Table[C[i],{i,1,Length[Functions]}]+ParticoularSolution;
CompleteAnalytic=AnalyticContinuation[CompleteSolution,KinVariab,LineParametrization,PointExpansion];
BCs=DetermineBoundaryConditions[CompleteAnalytic,BoundaryCondition,BCPoint];
(CompleteSolution//ChopDigits//Expand//ClearSeries[#,sInt,ExpansionOrderPrivate]&)/.Join[BCs,{sInt->LineParam-PointExpansion}]//ChopDigits
];

MyInverse[matrix_]:=Module[{invertedMatrix,dimension,placeHolderMatrix,element,substitution,determinant,inverseDet},
dimension=Dimensions[matrix];
placeHolderMatrix=Table[element[index1,index2],{index1,dimension[[1]]},{index2,dimension[[2]]}];
substitution=Table[element[index1,index2]->matrix[[index1,index2]],{index1,dimension[[1]]},{index2,dimension[[2]]}]//Flatten;
determinant=Det[placeHolderMatrix]/.substitution;
inverseDet=Series[1/Normal[determinant]//Simplify//ChopExtraDigits,{sInt,0,ExpansionOrderPrivate+5}]//ChopDigits;
invertedMatrix=Det[placeHolderMatrix]Inverse[placeHolderMatrix]/.substitution//ChopDigits;
Return[inverseDet*invertedMatrix//ChopDigits];
];

(* Expanding *)
FastSeries[expr_,var_,center_,order_]:=Module[{list,coeff,add,sub,res,subExpToZero,subExpToOne,avoidDoubleCounting,extraOrder},
res=Expand[expr];
list=Cases[res,(Power[base_,expon_]/;(expon<0 && base=!=var)):> Power[base,expon],Infinity]//DeleteDuplicates;

subExpToZero=Map[Rule[#,0]&,list];
res=expr/.subExpToZero;
res=Expand[res];
subExpToOne=Map[Rule[#,0]&,list];
res=res/.var^b_/;b>order->0;

extraOrder=Min[Abs[Cases[Expand[expr/.subExpToOne],Power[a_,b_]:> b]],0];
sub={};
Do[
sub=Join[sub,{Rule[list[[j]],Normal[Series[list[[j]],{var,0,order+extraOrder}]]]}];
,{j,Length[list]}];	
	
avoidDoubleCounting={};
Do[	
coeff=Coefficient[expr,list[[i]]]/.avoidDoubleCounting;
add=Expand[(coeff*list[[i]])/.sub];
add=add/.var^b_/;b>order->0;
res=res+add;
avoidDoubleCounting=Join[avoidDoubleCounting,{list[[i]]:> 0}]
,{i,Length[list]}];
Return[res];
];

(* Integrating function *)
SetAttributes[{MyIntegrateAux},Listable];
IntReplacement={};
MyIntegrate[inputExt__]:=Module[{input=inputExt,LogOrd},
input=(inputExt/.Log[coeff_ *sInt]->Log[coeff]+Log[sInt])//Expand//ChopDigits;
LogOrd=Append[GetCases[{input},Log[sInt]^(k_:1)|Log[sInt]^(k_:1):>k],1]//Max;
If[LogOrd>MaxLogOrder,
UpdateIntReps[LogOrd];
];
MyIntegrateAux[input]
];
MyIntegrateAux[a_]:=MyIntegrateAux[a,sInt];
MyIntegrateAux[exp0_/;NumericQ[exp0],var_]:=var exp0;
MyIntegrateAux[exp0_,var_]:=Module[{exp=(Expand@exp0),Out,Const},
exp=exp/.Log[coeff_ *sInt]/;Abs[coeff-1]<=1*^-15->Log[sInt];
Out=exp/.var->b/.IntReplacement;
Const=(Out/.a->0);
Out-Const+b Const/.a->1/.b->var
];

UpdateIntReps[MaxOrd_]:=Module[{},
MaxLogOrder=MaxOrd;
IntReplacement=Join[
Table[Log[x]^n->a Integrate[Log[x]^n,x]/.x->b,{n,MaxLogOrder}],
Table[Log[x]^n x->a Integrate[Log[x]^n x,x]/.x->b,{n,MaxLogOrder}],
Table[Log[x]^n x^m_/;m!=-1->a Integrate[Log[x]^n x^m,x]/.x->b,{n,MaxLogOrder}],
Table[Log[x]^n/x->a Integrate[Log[x]^n x^-1,x]/.x->b,{n,MaxLogOrder}],
{x^m_/;m!=-1->a Integrate[x^m,x]/.x->b},
{x->a Integrate[x,x]/.x->b},
{1/x->a Integrate[1/x,x]/.x->b}
]//Reverse//Expand;
];

DependsQ[a_,b_]:=Length[GetCases[a,b]]>0;
GetCases[expr_,case_]:=expr//Cases[{#},case,Infinity]&//DeleteDuplicates//Sort;

(* Accessing the solution *)
Solution[]:=MasterIntegrals;
SolutionValue[]:=(MasterIntegrals/.Table[VariablesEq[[i]]->CurrentBC[[i]],{i,1,Length[VariablesEq]}])//SetPrec;
SolutionTable[]:=Table[Table[Coefficient[SolutionValue[][[i]],eps,j],{j,MinEpsExponent,EpsilonOrderPrivate}],{i,1,NumberMasterIntegrals}];
SolutionTableExplicit[]:=Table[MasterIntegralsFunctions[[j]]->(MasterIntegrals[[j]]/.Table[VariablesEq[[i]]->CurrentBC[[i]],{i,1,Length[VariablesEq]}]//SetPrec),{j,NumberMasterIntegrals}];

EstimateError[var_]:=Module[{radius,bc,sing,solutionTable,newErr,solTruncated,maxExp},
(* Find bc, singularities and radius *)
Do[
If[var===VariablesEq[[i]],
bc=CurrentBC[[i]];
sing=Singularities[[i]]/.GetPoint[];
Break[];
];
,{i,1,Length[VariablesEq]}];
radius=ExpectedConvergenceRadius[bc,sing,var];

(* solution table *)
solutionTable=Table[Table[Coefficient[Solution[][[i]],eps,j],{j,MinEpsExponent,EpsilonOrderPrivate}],{i,1,NumberMasterIntegrals}];
solTruncated=If[Length[Cases[solutionTable,Power[var,Complex[_,_]],Infinity]]>0,
maxExp=Cases[solutionTable,Power[xx_,Complex[re_,_]]/;!MatchQ[xx,Log[__]]->re,Infinity]//Max;
(solutionTable/.Power[_,Complex[re_,im_]]/;re>=(maxExp-2)->0)
,
maxExp=Cases[solutionTable,Power[xx_,re_]/;!MatchQ[xx,Log[__]]->re,Infinity]//Max;
(solutionTable/.Power[_,b_]/;b>=(maxExp-2)->0)
];

(* estimate error *)
newErr=((solutionTable-solTruncated)/.var->bc+radius )//Abs//Max;
ErrorEstimate=Max[newErr,ErrorEstimate];
If[N[ErrorEstimate]===N[0],ErrorEstimate=N[ErrorEstimate,50];,ErrorEstimate=N[ErrorEstimate];];
ErrorEstimate
];

(* Graph solution to differential equation *)
CreateGraph[MInumber_,EpsilonOrder_,left_,right_,OtherFunction_:{},AnaliticCont_:False]:=Module[{solution,coeff,plots={}},
If[AnaliticCont,
solution=MasterIntegralsMobius;
coeff=SeriesCoefficient[solution[[MInumber]],{eps,0,EpsilonOrder}];
ReImPlot[{coeff,OtherFunction},{Global`y,left,right},PlotLabel->StringForm["Master Integral `` - Order O(\!\(\*SuperscriptBox[\(\[Epsilon]\), \(``\)]\)) after Mobius Transformation",MasterIntegralsFunctions[[MInumber]],EpsilonOrder],PlotLegends->{{"Series Solution","Exact Solution"}, "ReIm"}]
,
solution=MasterIntegrals;
coeff=Coefficient[solution[[MInumber]],eps,EpsilonOrder];

If[MatchQ[OtherFunction[[0]],List]&&Length[OtherFunction]==0,
ReImPlot[Evaluate[{coeff}/.LastKinematicVariableUsed->Global`x],{Global`x,left,right},PlotLegends->{{"Series Solution"}, "ReIm"},PlotLabel->StringForm["Master Integral `` - Order O(\!\(\*SuperscriptBox[\(\[Epsilon]\), \(``\)]\))",MasterIntegralsFunctions[[MInumber]],EpsilonOrder]]
,
ReImPlot[Evaluate[{coeff,OtherFunction}/.LastKinematicVariableUsed->Global`x],{Global`x,left,right},PlotLegends->{{"Series Solution","Exact Solution"}, "ReIm"},PlotLabel->StringForm["Master Integral `` - Order O(\!\(\*SuperscriptBox[\(\[Epsilon]\), \(``\)]\))",MasterIntegralsFunctions[[MInumber]],EpsilonOrder]]
]
]
];

(* Transporting BCs *)
(* 
Line Object ={Points[p1,p2,p3], Segments[(p2-p1)t+p1, (p3-p2)t+p2],t}
*)
StraightLine[A_,B_,Param_]:={{(B - A )Param + A}};
CreateLine[PointList_List]:=CreateLine[PointList,tInt];
CreateLine[PointList_List,Param_]:=Module[{lineT={},points},
points=PointList//DropDuplicates;
Do[
lineT=Join[lineT,StraightLine[points[[i]],points[[i+1]],Param]];
,{i,1,Length[points]-1}];
{points/.{List->Points},ToSegments[lineT], lineParam}
];

DropDuplicates[pointList_List]:=Module[{res={}, check={}},
check=Table[Abs[(pointList[[i]]-pointList[[i+1]])]>=10^-$MachinePrecision,{i,1,Length[pointList]-1}];
res=Append[res,pointList[[1]]];
Do[
If[MatchQ[check[[i]],True], res=Append[res,pointList[[i+1]]];];
,{i,1,Length[check]}];
res
];

ToList[Func_[Something__]]:=List[Something];
ToSegments[List[Something__]]:=Segments[Something];

(* Update Boundary Conditions *)
UpdateBoundaryConditions[newPointBC_,Segment_,LineParam_,KinematicVar_,singularities_,FinalPoint_,oldPoint_]:=Module[{NewBoundaryConditions,ind=1,OtherVariablesBC={},closestSing=Infinity,radConvergence=1*^5,direction,sing=singularities,count,nextSing,res,l,pos},
(* If the BC were imposed as asymptotic limit now are no more *)
If[AsymptoticBoundaryConditions,AsymptoticBoundaryConditions=False];
Do[
If[MatchQ[KinematicVar,VariablesEq[[i]]],
CurrentBC[[i]]=newPointBC;
ind=i;
,
OtherVariablesBC=Append[OtherVariablesBC,VariablesEq[[i]]->CurrentBC[[i]]];
];
,{i,1,Length[VariablesEq]}];
CurrentBCLineParam=Solve[Segment== newPointBC, LineParam,WorkingPrecision->InternalWorkingPrecisionPrivate][[1,1,2]]//Chop;
(* If the starting point is a singularity move away *)
If[LogarithmicExpansionPrivate&& CloseToSing[oldPoint,sing],CurrentExpansionPoint=CurrentBCLineParam; ];
If[LogarithmicExpansionPrivate&& !CloseToSing[oldPoint,sing],
res=Table[Reduce[{sing[[i]]==Segment[[1]],Abs[Im[LineParam]]<=1*^-15},LineParam],{i,1,Length[sing]}]/.{(LineParam==val_)->Re[val],False->Infinity};
count=Count[res,Infinity];
res=Sort[res];
res=Drop[res,-count];
If[Length[res]==0,CurrentExpansionPoint=CurrentBCLineParam;,
(* nexsing *)
Do[
If[Abs[sing[[i]]-FinalPoint]<=1*^-15, nextSing=FinalPoint; Break[];];
If[res[[i]]>CurrentBCLineParam, nextSing=Segment[[1]]/.LineParam->res[[i]]; Break[];,nextSing=Segment[[1]]/.LineParam->res[[i]];];
,{i,1,Length[res]}];

If[Length[sing]==1,radConvergence=1*^5; ,
(* closestSing per nextSing *)
l=((Abs[#-nextSing]&)/@sing)//ChopDigits;
l=l/.x_/;x<1*^-15->Infinity;
pos=Position[l,Min[l]][[1,1]];
closestSing=sing[[pos]];
radConvergence=Min[Abs[closestSing-nextSing],100];

radConvergence=radConvergence/RadiusOfConvergencePrivate;
];
If[LogarithmicExpansionPrivate&& Abs[newPointBC-nextSing]<=radConvergence,
CurrentExpansionPoint=Solve[Segment[[1]]== nextSing, LineParam,WorkingPrecision->InternalWorkingPrecisionPrivate][[1,1,2]]//Chop;
,
CurrentExpansionPoint=CurrentBCLineParam;
];
];
,
CurrentExpansionPoint=CurrentBCLineParam;
];
(* Create new Boundary Conditions *)
SystemOfDifferentialEquation=Drop[SystemOfDifferentialEquation, -NumberMasterIntegrals];
NewBoundaryConditions=MasterIntegrals/.({KinematicVar->newPointBC}//SetPrec);
NewBoundaryConditions=Table[-(MasterIntegralsFunctions[[j]]/.Join[{KinematicVar->newPointBC},OtherVariablesBC])+ NewBoundaryConditions[[j]]==0,{j,1,Length[NewBoundaryConditions]}];
SystemOfDifferentialEquation=Join[SystemOfDifferentialEquation,NewBoundaryConditions];
UpdateSystemEpsilonExpanded[];
];

ExpectedConvergenceRadius[Point_,Sin_,KinematicVariable_]:=Module[{rad=1*^10,pointBoundary},
pointBoundary=Point;
Do[
If[Norm[Sin[[i]]-pointBoundary]>1*^-15,
rad = Min[rad,Abs[pointBoundary-Sin[[i]]]];
];
,{i,1,Length[Sin]}];
Return[rad*1/RadiusOfConvergencePrivate];
];

(* 
Input from reduce 
t\[Equal]1   \[Rule] t\[Rule]1
 t\[Equal]2 || t\[Equal]5     \[Rule]  t\[Rule]5
*)
Bigger[solutions_]:=Module[{},
If[MatchQ[solutions[[0]],Or],
Return[solutions[[-1]]/.Equal->Rule]
,
Return[solutions/.Equal->Rule]
]
];

MakeHomogeneus[Equation_,fun_]:=Module[{coeff1,coeff2,table},
table=Table[Equation[[ieq,1]],{ieq,Length[Equation]}];
coeff1=Table[Coefficient[table[[ieq]],fun],{ieq,Length[Equation]}];
coeff2=Table[Coefficient[table[[ieq]],D[fun,tInt]],{ieq,Length[Equation]}];
Return[Table[coeff1[[ieq]] . fun + coeff2[[ieq]] . D[fun,tInt]==0,{ieq,Length[Equation]}]];
];

InomogeusPart[equation_]:=Module[{LHS},
LHS=equation/.Equal-> Subtract;
-LHS/.{Subscript[f, _]->(0&)}
];

ClearSeries[series_,param_,orderToBeDeleted_:ExpansionOrderPrivate]:=Module[{},
If[Length[Cases[\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{"param", ",", 
RowBox[{"Complex", "[", 
RowBox[{"re_", ",", "im_"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),Infinity]]>0,
Return[series/. param^Complex[re_,im_]/;re>orderToBeDeleted->0];
];
Return[series/. param^b_/;b>orderToBeDeleted->0];
];

ToListAlways[Something_]:=If[Something[[0]]==List, Return[Something],Return[List[Something]]];

LineGood[line_,branches_,sing_,prescription_]:=Module[{segments,solu,lineIsGood=True,c1,c2,pnt},
segments=line[[2]]/.Segments->List;

(* Check if every segment *)
Do[
(* crosses singularity *)
Do[
solu=Solve[{segments[[i,1]]==sing[[j]],tInt>0,tInt< 1}];
If[Length[solu]>= 1, lineIsGood=False];
,{j,1,Length[sing]}];

(* Crosses branches *)
Do[
(* If segment and branch are parallel move over *)
c1=Coefficient[segments[[i,1]],tInt];
c2=Coefficient[branches[[j]],par];
If[Mod[Arg[c1]-Arg[c2],\[Pi]]==0,Continue[];];

(* If are not parallel check if there is intersection *)
solu=Solve[{segments[[i,1]]==branches[[j]],par\[Element]Reals,tInt>=0,tInt<=1,par>=0}];
If[Length[solu]==0,Continue[];];

(* If nor the starting point nor the final point are on the real axes line is not good *)
If[!MatchQ[solu,{{___,tInt-> 0|1,___}}],lineIsGood=False;Continue[];];

(* Take the point not zero and check that the sign of Im is opposite to prescription *)
pnt=segments[[i,1]]/.tInt->0;
If[Im[pnt]==  0, pnt=segments[[i,1]]/.tInt->1];
If[Im[pnt]*prescription<0, lineIsGood=False];
,{j,1,Length[branches]}];
,{i,1,Length[segments]}];
lineIsGood
];

FindSpecialPoint[Singularity_]:=Module[{maxRealSing=-Infinity},
Do[
If[Im[Singularity[[i]]]==0,
maxRealSing=Max[maxRealSing,Singularity[[i]]];
];
,{i,1,Length[Singularity]}];
maxRealSing+1
];

TransportBoundaryConditions[PhaseSpacePoint_List]:=Module[{},
If[Length[PhaseSpacePoint]=!=Length[VariablesEq],PrintError["Please provide a list of length: ",Length[PhaseSpacePoint]];];
Do[
TransportVariable[VariablesEq[[h]],PhaseSpacePoint[[h]]];
,{h,1,Length[PhaseSpacePoint]}];
];

TransportVariable[var_, destinationExt_,PredefinedLineExt_:{}]:=Module[{OtherVarBCs={},linea,SingularitiesForVar,SafeSingularitiesForVar,LogSingularitiesForVar,destination,PredefinedLine,BoundCond},
If[!NumericQ[destinationExt],PrintError["Destination is not a (complex) number."];];
If[AsymptoticBoundaryConditions && !MatchQ[var,AsymptoticVariable],PrintError["The boundary conditions are given as asymptotic limit for ",AsymptoticVariable,", the system can not be solved with respect to ",variable];
];
destination=destinationExt//SetPrec;
PredefinedLine=PredefinedLineExt//SetPrec;

Do[If[MatchQ[var,VariablesEq[[i]]],
BoundCond=CurrentBC[[i]];
SingularitiesForVar=Singularities[[i]];
LogSingularitiesForVar=LogarithmicSingularities[[i]];
SafeSingularitiesForVar=SafeSingularities[[i]];
,
OtherVarBCs=Join[OtherVarBCs,{VariablesEq[[i]]->CurrentBC[[i]]}];
];
,{i,1,Length[VariablesEq]}];

If[Abs[BoundCond-destination]<1*^-15 && PredefinedLine==={},
If[MasterIntegrals===MasterIntegralsFunctions,
SolveSystem[var];,
PrintInfo["The system is already solved in ",var,"=",destination//N];
];
Return[];
];

SingularitiesForVar=Sort[SingularitiesForVar/.OtherVarBCs]//DeleteDuplicates;
SafeSingularitiesForVar=Sort[SafeSingularitiesForVar/.OtherVarBCs]//DeleteDuplicates;
LogSingularitiesForVar=Sort[LogSingularitiesForVar/.OtherVarBCs]//DeleteDuplicates;

If[MatchQ[Length[PredefinedLine],0],
If[MatchQ[LogarithmicExpansionPrivate,False],
linea=DeterminePath[var,BoundCond//SetPrec,destination//SetPrec,LogSingularitiesForVar,SafeSingularitiesForVar]//SetPrec//ChopDigits;
PrintInfo["Moving following these points: ",linea[[1]]/.Points->List//N, ", avoiding singularities. Here you can see the path in the complex plane for the kinematic variable ",var];
Print[ShowPath[LogSingularitiesForVar,SafeSingularitiesForVar,linea,var]];
,
linea=DeterminePathLog[var,BoundCond,destination//SetPrec,LogSingularitiesForVar,SafeSingularitiesForVar]//SetPrec//ChopDigits;
PrintInfo["Moving following these points: ",linea[[1]]/.Points->List//N, ". NOT avoiding singularities. Here you can see the path in the complex plane for the kinematic variable ",var];
Print[ShowPath[LogSingularitiesForVar,SafeSingularitiesForVar,linea,var]];
];
SolveAlongLine[linea,var,SingularitiesForVar];
,
PrintInfo["Moving following these points: ",PredefinedLine[[1]]/.Points->List//N, ", avoiding singularities. Here you can see the path in the complex plane for the kinematic variable ",var];
Print[ShowPath[LogSingularitiesForVar,SafeSingularitiesForVar,PredefinedLine,var]];
SolveAlongLine[PredefinedLine,var,SingularitiesForVar];
];
];

ShowPath[LogSing_,SafeSing_,Path_,Variable_]:=Module[{singularity,RedLines={},Lines={},PathFound={},ListPointComplex={},ListPoint={},singComplete,PointsSing},
Do[
(*we use only horizontal branch cuts*)
singularity=LogSing[[i]];
RedLines=Append[RedLines,Line[{{(singularity//Re)-100,singularity//Im},{singularity//Re,singularity//Im}}]];
,{i,1,Length[LogSing]}];
Lines=Join[Lines,Table[Graphics[{RGBColor[1,0,0],RedLines[[i]]}],{i,1,Length[RedLines]}]];
ListPointComplex=Path[[1]]/.SeaSyde`Private`Points->List;
Do[
ListPoint=Append[ListPoint,{ListPointComplex[[i]]//Re,ListPointComplex[[i]]//Im}];
,{i,1,Length[ListPointComplex]}];
PathFound={Graphics[{RGBColor[0,0,0],Line[ListPoint]}]};
singComplete=Join[LogSing,SafeSing];
PointsSing=Table[Graphics[{RGBColor[255,0,0],Inset[Style["\[Cross]",15],{Re[singComplete[[i]]],Im[singComplete[[i]]]}]}],{i,1,Length[singComplete]}];
Show[Join[Lines,PathFound,PointsSing],Axes->True,PlotLabel->"Kinematic variable: "<>ToString[Variable],AxesLabel->{"Re "<>ToString[Variable],"Im "<>ToString[Variable]},PlotRange->{{Min[Re/@ListPointComplex]-0.5,Max[Re/@ListPointComplex]+0.5},{Min[Im/@ListPointComplex]-0.5,Max[Im/@ListPointComplex]+0.5}}]
];

SolveAlongLine[LineObject_List,KinVar_,Singul_]:=Module[{Points =ToList[LineObject[[1]]], Segments=ToList[LineObject[[2]]],LineParam=LineObject[[3]],newPoint,NewBoundaryConditions,segment,radius,newPointLineParam,oldPoint,index,lastPoint,dir,pointBoundCond,line,lasterCentre,l,pos,closestSing,rad,LogarithmicExpansionPrivateTemp,nextPT,pointBegin},

LogarithmicExpansionPrivateTemp=LogarithmicExpansionPrivate;

CurrentExpansionPoint=0;
If[LogarithmicExpansionPrivate && CloseToSing[Points[[1]],Singul],
Do[
If[MatchQ[KinVar,VariablesEq[[i]]],
pointBoundCond=CurrentBC[[i]];
Break[];
];
,{i,1,Length[VariablesEq]}];
CurrentBCLineParam=Solve[Segments[[1,1]]== pointBoundCond, LineParam,WorkingPrecision->InternalWorkingPrecisionPrivate][[1,1,2]]//Chop;
,
CurrentBCLineParam=0;
];
(* loop over segments *)
Do[
PrintInfo["Moving from the point ",KinVar,"=", Points[[i]]//N, " to ",KinVar,"=",Points[[i+1]]//N, ", along the line ",KinVar,"=",Segments[[i,1]]//N];
(* Solve system of differential equation *)
Do[
If[MatchQ[KinVar,VariablesEq[[k]]],index=k; Break[];];
,{k,1,Length[VariablesEq]}];

oldPoint=CurrentBC[[index]];
SolveSeriesExpansionSafe[Segments[[i,1]],KinVar,False,False];
pointBegin=Segments[[i,1]]/.LineParam->CurrentExpansionPoint;
radius=ExpectedConvergenceRadius[pointBegin,Singul,KinVar];
newPointLineParam=Reduce[{Norm[pointBegin-Segments[[i]]]==radius,Element[LineParam, Reals],LineParam>= 0},LineParam]//Num//Bigger;
newPoint=Segments[[i]]/.newPointLineParam;

While[Norm[oldPoint-Points[[i+1]]]>= radius ,

UpdateBoundaryConditions[newPoint[[1]],Segments[[i]],LineParam,KinVar,Singul//Sort,Points[[i+1]],oldPoint];
PrintInfo["The new point is: ",KinVar,"=",Segments[[i,1]]/.{LineParam->CurrentExpansionPoint}//N];

oldPoint=Segments[[i,1]]/.{LineParam->CurrentExpansionPoint};


SolveSeriesExpansionSafe[Segments[[i,1]],KinVar,False,False];

radius=ExpectedConvergenceRadius[oldPoint,Singul,KinVar];
newPointLineParam=Reduce[{Norm[oldPoint-Segments[[i]]]==radius,Element[LineParam, Reals],LineParam>= 0},LineParam]//Num//Bigger;
newPoint=Segments[[i]]/.newPointLineParam;
(* If the last point is a singularity and I am close to it Break[]; *)

If[CloseToSing[Points[[i+1]],Singul//Sort],
l=((Abs[#-Points[[i+1]]]&)/@Singul)//ChopDigits;
l=l/.x_/;x<1*^-15->Infinity;

(* If there is only one singularity we can jump directly on it *)
If[Min[l]===Infinity,Break[];];

pos=Position[l,Min[l]][[1,1]];
closestSing=Singul[[pos]];
rad=Abs[(closestSing-Points[[i+1]])/RadiusOfConvergencePrivate];
If[Abs[newPoint[[1]]-Points[[i+1]]]<= rad,Break[];];
];
];

If[i!=Length[Segments],
nextPT=Points[[i+1]];
If[CloseToSing[Points[[i+1]],Singul],
(*Print["newPoint ",newPoint//N];*)
UpdateBoundaryConditions[newPoint[[1]],Segments[[i]],LineParam,KinVar,Singul//Sort,Points[[i+1]],oldPoint];

PrintInfo["The new point is: ",KinVar,"=",Segments[[i,1]]/.{LineParam->CurrentExpansionPoint}//N];
oldPoint=Segments[[i,1]]/.{LineParam->CurrentExpansionPoint};
SolveSeriesExpansionSafe[Segments[[i,1]],KinVar,False,False];
radius=ExpectedConvergenceRadius[oldPoint,Singul,KinVar];
newPointLineParam=Reduce[{Norm[oldPoint-Segments[[i+1]]]==radius,Element[LineParam, Reals],LineParam>= 0},LineParam]//Num//Bigger;
nextPT=Segments[[i+1,1]]/.newPointLineParam;
];
UpdateBoundaryConditions[nextPT,Segments[[i+1]],LineParam,KinVar,Singul//Sort,Points[[i+1]],oldPoint];
];
,{i,1,Length[Segments]}];

(* I want a series centered in the last point *)
If[CloseToSing[Points[[-1]],Singul//Sort],
PackageConfiguration["LogarithmicExpansion"]=True;
line=StraightLine[newPoint[[1]],Points[[-1]],LineParam][[1]];lastPoint=newPoint[[1]];
,
line={LineParam+Points[[-1]]};lastPoint=Points[[-1]];
];
lasterCentre=(Segments[[-1,1]]/.tInt->CurrentExpansionPoint);
UpdateBoundaryConditions[lastPoint,line,LineParam,KinVar,Singul//Sort,Points[[-1]],oldPoint];
If[Abs[lasterCentre-Points[[-1]]]>1*^-15,
If[!CloseToSing[Points[[-1]],Singul],CurrentExpansionPoint=0;];
SolveSeriesExpansionSafe[line[[1]],KinVar,False,False];
];
If[CloseToSing[Points[[-1]],Singul//Sort], PackageConfiguration["LogarithmicExpansion"]=LogarithmicExpansionPrivateTemp;];

PrintInfo["I arrived at ",KinVar,"=",Points[[-1]]//N, ". The error estimate is: ",EstimateError[KinVar],". The radius of convergence is: ",ExpectedConvergenceRadius[Points[[-1]],Singul,KinVar]//N,".\nUse Solution[] or SolutionValue[] to access the solution, or CreteGraph to plot it."];
];

CloseToSing[point_,sing_]:=Module[{},
If[ContainsAny[Cases[sing, x_/;Abs[x-point]<= 1*^-15-> True],{True}], True,False]
];

AnalyticContinuation[Series_,KinematicVariable_,LineParametriz_,PointExp_]:=Module[{prescription,currentBoundary},
If[!LogarithmicExpansionPrivate,Return[Series];];
Do[
If[
MatchQ[KinematicVariable,VariablesEq[[k]]],
prescription=DeltaPrescription[[k]];
currentBoundary=CurrentBC[[k]];
Break[];
];
,{k,1,Length[VariablesEq]}];
If[Abs[Im[LineParametriz/.tInt->PointExp]]=!=0,Return[Series];];
If[prescription===1,Return[Series];];
Return[Series/.{Log[arg__]->Log[arg]-2\[Pi] I Subscript[\[Theta], m][arg],Power[arg__,Rational[a_,2]]->(Subscript[\[Theta], p][arg]-Subscript[\[Theta], m][arg])Power[arg,Rational[a,2]]}];
];

NotCloseToSing[From_,To_,Singularities_]:=Module[{Result=True},
Do[
If[Re[From]<Re[To] &&Re[From]<Re[Singularities[[i]]]&&Re[Singularities[[i]]]<Re[To],Result=False;];
If[Re[To]<Re[From] &&Re[To]<Re[Singularities[[i]]]&&Re[Singularities[[i]]]<Re[From], Result=False;];
,{i,1,Length[Singularities]}];
Result
];

GetPoint[]:=Table[VariablesEq[[i]]->CurrentBC[[i]],{i,1,Length[VariablesEq]}];

CheckSingularities[]:=Module[{currBCforOtherVar={},sing,singLess={},singMore={},singComplex={},currBcforVar,LogarithmicSingularitiesTmp,SafeSingularitiesTmp},
(* Reset just in case *)
LogarithmicSingularitiesTmp={};
SafeSingularitiesTmp={};

(* Spread singularities *)
SpreadSingularities[];

(* Save current configuration ad position *)
SaveCurrentState[];
PackageConfiguration["LogarithmicExpansion"]=False;

Do[
PrintInfo["Checking the logarithmic behaviour for all the singularities for the kinematic variable ",VariablesEq[[ic]]];
PrintInfo["The possible singularities are in ", Singularities[[ic]]//N];

LogarithmicSingularitiesTmp=Append[LogarithmicSingularitiesTmp,{}];
SafeSingularitiesTmp=Append[SafeSingularitiesTmp,{}];

(* Find some useful information *)
currBCforOtherVar={};
Do[
If[MatchQ[VariablesEq[[ic]],VariablesEq[[jc]]],
currBcforVar=CurrentBC[[jc]];
,
currBCforOtherVar=Append[currBCforOtherVar,VariablesEq[[jc]]-> CurrentBC[[jc]]];
];
,{jc,1,Length[VariablesEq]}];
sing={Singularities[[ic]],Singularities[[ic]]/.currBCforOtherVar};

(* Divide into real>BC, real<BC and complex *)
singMore={};
singLess={};
singComplex={};
Do[
If[Im[sing[[2,lc]]]==0,
If[Re[sing[[2,lc]]]>=currBcforVar,
singMore=Append[singMore,{sing[[1,lc]],sing[[2,lc]]}];
,
singLess=Append[singLess,{sing[[1,lc]],sing[[2,lc]]}];
];
,
singComplex=Append[singComplex,sing[[1,lc]]];
];
,{lc,1,Length[sing[[1]]]}];

(* Check real more *)
singMore=Sort[singMore,#1[[2]]<#2[[2]]&];
singMore=Table[singMore[[k,1]],{k,1,Length[singMore]}];
Do[
If[IsSingularityLogarithmic[singMore[[jc]],VariablesEq[[ic]]],
LogarithmicSingularitiesTmp[[ic]]=Append[LogarithmicSingularitiesTmp[[ic]],singMore[[jc]]]; PrintInfo["The singularity ",singMore[[jc]]//N," for the variable ",VariablesEq[[ic]]," is LOGARITHMIC"];
,
SafeSingularitiesTmp[[ic]]=Append[SafeSingularitiesTmp[[ic]],singMore[[jc]]];PrintInfo["The singularity ",singMore[[jc]]//N," for the variable ",VariablesEq[[ic]]," is SAFE"];
];
,{jc,1,Length[singMore]}];
RestoreState[];

(* check real less *)
singLess=Sort[singLess,#1[[2]]>#2[[2]]&];
singLess=Table[singLess[[k,1]],{k,1,Length[singLess]}];
Do[
If[IsSingularityLogarithmic[singLess[[jc]],VariablesEq[[ic]]],
LogarithmicSingularitiesTmp[[ic]]=Append[LogarithmicSingularitiesTmp[[ic]],singLess[[jc]]];
PrintInfo["The singularity ",singLess[[jc]]//N," for the variable ",VariablesEq[[ic]]," is LOGARITHMIC"];
,
SafeSingularitiesTmp[[ic]]=Append[SafeSingularitiesTmp[[ic]],singLess[[jc]]];
PrintInfo["The singularity ",singLess[[jc]]//N," for the variable ",VariablesEq[[ic]]," is SAFE"];
];
,{jc,1,Length[singLess]}];
RestoreState[];

(* check complex *)
Do[
If[IsSingularityLogarithmic[singComplex[[jc]],VariablesEq[[ic]]],
LogarithmicSingularitiesTmp[[ic]]=Append[LogarithmicSingularitiesTmp[[ic]],singComplex[[jc]]];
PrintInfo["The singularity ",singComplex[[j]]//N," for the variable ",VariablesEq[[ic]]," is LOGARITHMIC"];
,
SafeSingularitiesTmp[[ic]]=Append[SafeSingularitiesTmp[[ic]],singComplex[[jc]]];
PrintInfo["The singularity ",singComplex[[jc]]//N," for the variable ",VariablesEq[[ic]]," is SAFE"];
];
RestoreState[];
,{jc,1,Length[singComplex]}];

,{ic,1,Length[VariablesEq]}];

RestoreLogarithmicExpansion[];
PrintInfo["LogarithmicSingularities ->",LogarithmicSingularitiesTmp//Rationalize];
PrintInfo["SafeSingularities -> ",SafeSingularitiesTmp//Rationalize];
PackageConfiguration["LogarithmicSingularities"]=LogarithmicSingularitiesTmp;
PackageConfiguration["SafeSingularities"]=SafeSingularitiesTmp;
];

SaveCurrentState[]:=Module[{},
SystemOfDifferentialEquationBackup = SystemOfDifferentialEquation;
SystemEpsilonExpandedBackup = SystemEpsilonExpanded;
MasterIntegralsBackup= MasterIntegrals;
MasterIntegralsMobiusBackup=MasterIntegralsMobius;
CurrentBCBackup=CurrentBC;
lineBackup=line;
lineParamBackup=lineParam;
CurrentExpansionPointBackup=CurrentExpansionPoint;
CurrentBCLineParamBackup=CurrentBCLineParam;
LastKinematicVariableUsedBackup=LastKinematicVariableUsed;
KinematicParametersBackup=KinematicParameters;
AsymptoticBoundaryConditionsBackup=AsymptoticBoundaryConditions;
AsymptoticVariableBackup=AsymptoticVariable;
LogarithmicExpansionPrivateBackup=LogarithmicExpansionPrivate;
];

RestoreLogarithmicExpansion[]:=Module[{},
PackageConfiguration["LogarithmicExpansion"]=LogarithmicExpansionPrivateBackup;
];

RestoreState[]:=Module[{},
SystemOfDifferentialEquation=SystemOfDifferentialEquationBackup;
SystemEpsilonExpanded=SystemEpsilonExpandedBackup ;
MasterIntegrals=MasterIntegralsBackup;
MasterIntegralsMobius=MasterIntegralsMobiusBackup;
CurrentBC=CurrentBCBackup;
line=lineBackup;
lineParam=lineParamBackup;
CurrentExpansionPoint=CurrentExpansionPointBackup;
CurrentBCLineParam=CurrentBCLineParamBackup;
LastKinematicVariableUsed=LastKinematicVariableUsedBackup;
KinematicParameters=KinematicParametersBackup;
AsymptoticBoundaryConditions=AsymptoticBoundaryConditionsBackup;
AsymptoticVariable=AsymptoticVariableBackup;
];

IsSingularityLogarithmic[singExt_,var_]:=Module[{sing,currBCforVar,currBCforOtherVar={},index=1,rad,sol1,sol2,singExact},
PrintInfo["Checking sing ", singExt//N, " for variable ",var];

Do[
If[MatchQ[var,VariablesEq[[i]]],
currBCforVar=CurrentBC[[i]];
singExact=DeleteCases[Singularities[[i]],singExt];
index=i;
,
currBCforOtherVar=Append[currBCforOtherVar,VariablesEq[[i]]-> CurrentBC[[i]]];
];
,{i,1,Length[VariablesEq]}];
sing=singExt/.currBCforOtherVar;

(* Find closest sing \[Rule] find radius *)
singExact=(Abs[#-sing]/RadiusOfConvergencePrivate)&/@(singExact/.currBCforOtherVar);
rad=Min[singExact//Min,0.5];

TransportVariable[var, sing+rad];
sol1=SolutionTable[];
TransportVariable[var, sing+rad, CreateLine[{sing+rad, sing+rad+rad I, sing-rad+rad I,sing-rad-rad I, sing+rad-rad I,sing+rad}]];
sol2=SolutionTable[];
If[((sol1-sol2)//Abs//Max)>1*^-10,Return[True];];
Return[False];
];

FindLog[expr_] := Module[{temp},
temp = Hold[expr] /. Log[_] -> 0;
If[(temp === Hold[expr]), False,True]
];

FindSqrt[expr_] := Module[{temp},
temp = Hold[expr] /. Sqrt[_] -> 0;
If[(temp === Hold[expr]), False,True]
];

SpreadSingularities[]:=Module[{varBC,currBC,index,currBCforOtherVar={},currentSing,Destination=CurrentBC,var,counter,offset=0},
PrintInfo["Checking if some singularities overlap"];
Do[
currBCforOtherVar={};
Do[
If[MatchQ[VariablesEq[[i]],VariablesEq[[j]]],
currentSing=Singularities[[j]];
var=VariablesEq[[j]];
,
currBCforOtherVar=Append[currBCforOtherVar,VariablesEq[[j]]-> CurrentBC[[j]]];
];
,{j,1,Length[VariablesEq]}];

(* Guardo le singolarit\[AGrave] per le altre variabili, se con la BC attuale ho dei doppioni, cambio *)
counter=1;
While[counter<=100 && !MatchQ[(currentSing/.currBCforOtherVar)//N,DeleteDuplicates[(currentSing/.currBCforOtherVar)//N]],
(* cambia sing *)
varBC=currBCforOtherVar[[1,1]];
currBC=currBCforOtherVar[[1,2]];
currBCforOtherVar=Delete[currBCforOtherVar,1];
If[currBC>=0, currBC=currBC+1.;,currBC=currBC-1.;];
currBCforOtherVar=Insert[currBCforOtherVar,varBC->currBC,1];
counter++;
];

offset=0;
Do[
If[MatchQ[var,VariablesEq[[j]]],offset=1;Continue[];];
Destination[[j]]=currBCforOtherVar[[j-offset,2]];
,{j,1,Length[VariablesEq]}];

,{i,1,Length[VariablesEq]}];

PrintInfo["Transporting Boundary conditions to ",Table[VariablesEq[[i]]-> Destination[[i]]//N,{i,1,Length[VariablesEq]}]];
Do[
If[Abs[Destination[[i]]-CurrentBC[[i]]]>1*^-15, TransportVariable[VariablesEq[[i]],Destination[[i]]];];
,{i,1,Length[VariablesEq]}];
];

(*Selects,among SingVert,the Vertical branches that are possible obstacles in going from'From' to'Destination'*)
CheckVerticalBranch[From_,Destination_,SingVert_]:=Module[{out={}},
Do[
If[(Re[From]<=Re[SingVert[[i]]]<=Re[Destination]||Re[Destination]<=Re[SingVert[[i]]]<=Re[From])&&((Abs[Im[SingVert[[i]]]]<=Abs[Im[From]]||Abs[Im[SingVert[[i]]]]<=Abs[Im[Destination]])&&(If[Im[From]*Im[Destination]>0,Im[From]*Im[SingVert[[i]]]>0,True])),
out=Join[out,{SingVert[[i]]}];
];
,{i,1,Length[SingVert]}];
out
];

(*Selects,among SingHor,the Horizontal branches that are possible obstacles in going from'From' to'Destination'*)
CheckHorizontalBranch[From_,Destination_,SingHor_]:=Module[{out={}},
Do[
If[(Im[From]<=Im[SingHor[[i]]]<=Im[Destination]||Im[Destination]<=Im[SingHor[[i]]]<=Im[From])&& (Re[SingHor[[i]]]>=Re[Destination]|| Re[SingHor[[i]]]>=Re[From]),
out=Join[out,{SingHor[[i]]}];
];
,{i,1,Length[SingHor]}];
out
];

(*Checks that the vertical path between'from' to'to' is not along a vertical branch generated by the singularities in'Sing'.If'to' is the same as'destination',simply checks if any of the singularities are on the path,not if the path is on the branch*)
CheckNotOnBranchV[from_,to_,Destination_,Sing_]:=Module[{flag=True},
If[to==Destination,
Do[
If[Re[from]==Re[Sing[[i]]]&&Re[to]==Re[Sing[[i]]]&&(Abs[Im[from]]<Abs[Im[Sing[[i]]]]<Abs[Im[to]]||Abs[Im[to]]<Abs[Im[Sing[[i]]]]<Abs[Im[from]]),
flag=False];
,{i,1,Length[Sing]}],
Do[
If[Re[from]==Re[Sing[[i]]]&&Re[to]==Re[Sing[[i]]]&& (Abs[Im[Sing[[i]]]]<=Abs[Im[to]]||Abs[Im[Sing[[i]]]]<=Abs[Im[from]]),
flag=False];
,{i,1,Length[Sing]}]
];
flag
];

(*Checks that the horizontal path between'from' to'to' is not along a horizontal branch generated by the singularities in'Sing'.If'to' is the same as'destination',simply checks if any of the singularities are on the path,not if the path is on the branch*)
CheckNotOnBranchH[from_,to_,Destination_,Sing_]:=Module[{flag=True},
If[to==Destination,
Do[
If[Im[from]==Im[Sing[[i]]]&&Im[to]==Im[Sing[[i]]]&&(Re[from]<Re[Sing[[i]]]<Re[to]||Re[to]<Re[Sing[[i]]]<Re[from]),flag=False];
,{i,1,Length[Sing]}],
Do[
If[Im[from]==Im[Sing[[i]]]&&Im[to]==Im[Sing[[i]]]&&(Re[from]<=Re[Sing[[i]]]||Re[to]<=Re[Sing[[i]]]),flag=False];
,{i,1,Length[Sing]}]
];
flag
];

(*Selects the singularities among the ones in'Sing' that are on the path from'from' to'to'.*)CheckNotOnSafeV[from_,to_,Sing_]:=Module[{output={}},Do[If[Re[from]==Re[Sing[[i]]]&&Re[to]==Re[Sing[[i]]]&&(Im[from]<=Im[Sing[[i]]]<=Im[to]||Im[to]<=Im[Sing[[i]]]<=Im[from]),output=Join[output,{Sing[[i]]}]];,{i,1,Length[Sing]}];
output];
CheckNotOnSafeH[from_,to_,Sing_]:=Module[{output={}},Do[If[Im[from]==Im[Sing[[i]]]&&Im[to]==Im[Sing[[i]]]&&(Re[from]<=Re[Sing[[i]]]<=Re[to]||Re[to]<=Re[Sing[[i]]]<=Re[from]),output=Join[output,{Sing[[i]]}]];,{i,1,Length[Sing]}];
output];

DeterminePath[Var_,FromExt_,DestinationExt_,LogSingExt_,SafeSingExt_:{}]:=
Module[{LogSing,LogSingIm,LogSingRe,SafeSing,Sing,Prescription,CorrStart=0,CorrEnd=0,Corr,Height,maxReSing=-Infinity,moreRight,moreLeft,pointsList={},From=FromExt,Destination=DestinationExt,HeightStart,HeightEnd,tmp,offsetStart=0,offsetEnd=0,prescrStart=1,prescrEnd=1,offset=0,sgnStart=1,sgnEnd=1,sgn=1},
LogSing=LogSingExt//SetPrec;
SafeSing=DeleteCases[SafeSingExt,x_/;(x==From||x==Destination)]//SetPrec;
Sing=Join[LogSing,SafeSing];

(* I\[Delta] prescription *)
Do[If[VariablesEq[[i]] == Var, Prescription =DeltaPrescription[[i]]], {i, 1, Length[VariablesEq]}];
If[Prescription===-1,
From=Conjugate[From];
Destination=Conjugate[Destination];
LogSing=Conjugate[LogSing];
SafeSing=Conjugate[SafeSing];
Sing=Conjugate[Sing];
];

LogSing=DeleteCases[LogSing,x_/;Re[x]<Min[Re[From],Re[Destination]]];
SafeSing=DeleteCases[SafeSing,x_/;Re[x]<Min[Re[From],Re[Destination]]];

AppendTo[pointsList,From];

(* Find Corridors *)
LogSingIm=Sort[LogSing//Im]//DeleteDuplicates;
AppendTo[LogSingIm,Infinity];
PrependTo[LogSingIm,-Infinity];

While[Im[From]>= LogSingIm[[CorrStart+1]],CorrStart++;];
While[Im[Destination]>= LogSingIm[[CorrEnd+1]],CorrEnd++;];

If[CorrStart===1,offsetStart=1;sgnStart=-1;];
If[CorrEnd===1,offsetEnd=1;sgnEnd=-1;];

(* Start & End in the same corridor *)
If[CorrStart===CorrEnd,
(* Is there a singularity between them *)
If[Length[Cases[Sing, x_/;((Min[Re[From],Re[Destination]]<Re[x]< Max[Re[From],Re[Destination]])&&(Min[Im[From],Im[Destination]]-0.5<Im[x]<Max[Im[From],Im[Destination]]+0.5))]]>0,
(* are both in the central third? *)
Height=Min[LogSingIm[[CorrStart+1]]-LogSingIm[[CorrStart]],1];
If[Abs[LogSingIm[[CorrStart]]]=!=Infinity&&Abs[LogSingIm[[CorrStart]]]=!=Infinity&&(LogSingIm[[CorrStart]]+Height/3<=Im[From]<=LogSingIm[[CorrStart+1]] -Height/3)&&(LogSingIm[[CorrStart]]+Height/3<=Im[Destination]<=LogSingIm[[CorrStart+1]] -Height/3),
pointsList={From,Destination};
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
,
pointsList={From,Re[From]+I  (Im[From]+Height/2),Re[Destination]+ I (Im[From]+Height/2),Destination};
(*pointsList={From,Re[From]+I  (LogSingIm[[CorrStart+offsetStart]]+sgnStartHeight/2),Re[Destination]+ I (LogSingIm[[CorrStart+offsetStart]]+sgnStartHeight/2),Destination};*)
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
];
,
pointsList={From,Destination};
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
];
];
(* They are not in the same corridor *)
tmp=LogSingIm[[Min[CorrStart,CorrEnd]+1;;Max[CorrStart,CorrEnd]]];
Do[maxReSing=Max[Cases[LogSing,x_/;Abs[Im[x]-tmp[[i]]]<=1*^-15]//Re//Max,maxReSing],{i,1,Length[tmp]}];
HeightStart=Min[LogSingIm[[CorrStart+1]]-LogSingIm[[CorrStart]],1];
HeightEnd=Min[LogSingIm[[CorrEnd+1]]-LogSingIm[[CorrEnd]],1];

(* One or both of them to the right *)
If[Re[From]>= Re[Destination],
moreRight=From;moreLeft=Destination;Corr=CorrEnd;Height=HeightEnd;offset=offsetEnd;sgn=sgnEnd;,
moreRight=Destination;moreLeft=From;Corr=CorrStart;Height=HeightStart;offset=offsetStart;sgn=sgnStart;
];

(* change into 0.5 *)
If[Re[moreRight]>=( maxReSing+1/2),
(* If the smallest one is to the left of maxReSing+1, check is it is in the third *)
If[(Re[moreLeft]<( maxReSing+1/2))&&!(LogSingIm[[Corr]]+Height/3<=Im[moreLeft]<=LogSingIm[[Corr+1]] -Height/3),
If[moreLeft===From,
pointsList={From,Re[From]+I (LogSingIm[[Corr+offset]]+sgn Height/2),Re[moreRight]+(LogSingIm[[Corr+offset]]+sgn Height/2)prescrEnd I,Destination};
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
];
pointsList={From,Re[moreRight]+(LogSingIm[[Corr+offset]]+sgn Height/2) I,Re[Destination]+I (LogSingIm[[Corr+offset]]+sgn Height/2),Destination};
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
];
pointsList={From,Re[moreRight]+Im[moreLeft]I,Destination};
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
];

HeightStart=Min[LogSingIm[[CorrStart+1]]-LogSingIm[[CorrStart]],1];
HeightEnd=Min[LogSingIm[[CorrEnd+1]]-LogSingIm[[CorrEnd]],1];
If[Abs[Im[From]-LogSingIm[[CorrStart+1]]]<=HeightStart/2||Abs[Im[From]-LogSingIm[[CorrStart]]]<=HeightStart/2, 
 AppendTo[pointsList,Re[From]+ I (LogSingIm[[CorrStart+offsetStart]]+sgnStart HeightStart/2)];
AppendTo[pointsList,maxReSing+0.5+ I (LogSingIm[[CorrStart+offsetStart]]+sgnStart HeightStart/2)];
,
AppendTo[pointsList,maxReSing+0.5+ I Im[From]];
];

If[Abs[Im[Destination]-LogSingIm[[CorrEnd+1]]]<=HeightEnd/2||Abs[Im[Destination]-LogSingIm[[CorrEnd]]]<=HeightEnd/2, 
 AppendTo[pointsList,maxReSing+0.5+ I (LogSingIm[[CorrEnd+offsetEnd]]+sgnEnd HeightEnd/2)];
AppendTo[pointsList,Re[Destination] +I  (LogSingIm[[CorrEnd+offsetEnd]]+sgnEnd HeightEnd/2)];
,
AppendTo[pointsList,maxReSing+0.5+ I Im[Destination]];
];
AppendTo[pointsList,Destination];
If[Prescription===-1,Return[CreateLine[Conjugate[pointsList]]];];
Return[CreateLine[pointsList]];
];

(* DeterminePathLog *)
DeterminePathLog[Var_,From_,Destination_,SingExt_,SafeSingExt_:{}]:=Module[{upMargin, downMargin,leftMargin,rightMargin,singBox={},tempStart,pointsList={From},counter=0},
(* If start and end have the same imaginary part, than the path is a horizontal straight line *)
If[Im[From]==Im[Destination], Return[CreateLine[{From,Destination}]];];
(* Find all the singularities in the right-infinite box *)
upMargin=Max[Im[From],Im[Destination]];
downMargin=Min[Im[From],Im[Destination]];
leftMargin=Min[Re[From],Re[Destination]];
rightMargin=Max[Re[From],Re[Destination]];
Do[
If[Re[SingExt[[i]]]>= leftMargin && downMargin<= Im[SingExt[[i]]]<= upMargin, singBox=Append[singBox,SingExt[[i]]]];
,{i,1,Length[SingExt]}];

Do[
If[leftMargin<=Re[SafeSingExt[[i]]]<= rightMargin && downMargin<= Im[SafeSingExt[[i]]]<= upMargin, singBox=Append[singBox,SafeSingExt[[i]]]];
,{i,1,Length[SafeSingExt]}];

If[MatchQ[singBox,{}],Return[DeterminePath[Var,From,Destination,SingExt,SafeSingExt]];];

tempStart=From;
singBox=Append[singBox,Destination];

While[tempStart!=Destination && counter< 100,
singBox=Sort[singBox,myDistance[#1,tempStart]<myDistance[#2,tempStart]&];
pointsList=Append[pointsList,singBox[[1]]];
tempStart=singBox[[1]];
singBox=Drop[singBox,1];
counter++;
];
If[counter>=100,Print["Error counter ", counter]];
Return[CreateLine[pointsList]];
];

myDistance[sing_,point_]:=Module[{},
If[Re[sing]>= Re[point],Return[Abs[Im[point]-Im[sing]]];];
Return[Abs[point-sing]];
];

DetermineBoundaryConditions[completeSolutions_,boundaryConditions_,point_]:=Module[{result={}},
If[IsNumeric[boundaryConditions],
result=DetermineNumericBoundaryConditions[completeSolutions,boundaryConditions,point];
Return[result];
];
result=DetermineAsymptoticBoundaryConditions[completeSolutions/.result,boundaryConditions,point];

If[Length[result]=!=Length[boundaryConditions]||FreeQ[result,C[_]],PrintError["I was not able to fix the boundary conditions for MI: "<>ToString[SeaSyde`Private`Debug`MInumber]<>", \[Epsilon] order: "<>ToString[SeaSyde`Private`Debug`EpsOrder]<>". Aborting the computation."];];
Return[result];
];

IsNumeric[list_List]:=!MemberQ[NumericQ/@list,False];

DetermineNumericBoundaryConditions[completeSolutionNum_,boundaryConditionNum_,pointBCNum_,alreadyFixedConstants_:0]:=Module[{limits,maxLog,logCoeff,solLog={},resultNumeric,equationsCoeffs,unknowns,asymptotic},
asymptotic=MyAsymptotic[ChopDigits[completeSolutionNum]//SetPrec,sInt->pointBCNum];
limits=MyLimit[ChopDigits[completeSolutionNum]//SetPrec,sInt->pointBCNum];
If[FindVar[limits, Infinity]||FindVar[limits, ComplexInfinity]||FindVar[limits,DirectedInfinity[_]]||FindVar[limits,Indeterminate],
maxLog=Exponent[asymptotic,Log[sInt]]//Max;
logCoeff=Table[LogicalExpand[Coefficient[asymptotic,Log[sInt],i]==0],{i,0,maxLog+1}]/.{And->List}//Flatten//DeleteCases[#,True]&;
unknowns=DeleteCases[Table[If[FindVar[asymptotic,C[i]],C[i]],{i,1,Length[boundaryConditionNum]}],Null];
solLog=Solve[SetPrecNumber[logCoeff],unknowns,Complexes,WorkingPrecision->InternalWorkingPrecisionPrivate];
If[solLog==={},
PrintError["I was not able to fix the boundary conditions for MI: "<>ToString[SeaSyde`Private`Debug`MInumber]<>", \[Epsilon] order: "<>ToString[SeaSyde`Private`Debug`EpsOrder]<>". Aborting the computation."];
];
solLog=First[solLog];
limits=MyLimit[(completeSolutionNum/.solLog//Expand//ChopDigits),sInt->pointBCNum];
];

equationsCoeffs=DeleteCases[Table[limits[[i]]==boundaryConditionNum[[i]],{i,1,Length[limits]}],False];
resultNumeric=Solve[SetPrecNumber[equationsCoeffs],Complexes,WorkingPrecision->InternalWorkingPrecisionPrivate]//ChopDigits;
If[resultNumeric=!={},resultNumeric=Join[resultNumeric[[1]],solLog];];
If[(alreadyFixedConstants+Length[resultNumeric])===Length[boundaryConditionNum],Return[resultNumeric];];
If[alreadyFixedConstants>0,PrintError["I was not able to fix the boundary conditions for MI: "<>ToString[SeaSyde`Private`Debug`MInumber]<>", \[Epsilon] order: "<>ToString[SeaSyde`Private`Debug`EpsOrder]<>". Aborting the computation."];];
If[WarningFlagPrivate,PrintWarning["The boundary conditions are not sufficient for determining the complete solution. They will be considered as an asymptotic expansion."];];

resultNumeric=Join[resultNumeric,DetermineNumericBoundaryConditions[D[completeSolutionNum/.resultNumeric,sInt],Table[0,{i,Length[boundaryConditionNum]}],pointBCNum,Length[resultNumeric]]];
Return[resultNumeric];
];

DetermineAsymptoticBoundaryConditions[completeSolutionAsy_,boundaryConditionAsy_,pointBCAsy_]:=Module[{termsType,coeffTerms,solveCoefficients},
termsType=Num[Expand[completeSolutionAsy-boundaryConditionAsy//Expand//ChopDigits]]/.{Plus->List}/.{_Real->1,_Complex->1,C[_]->1}//Flatten//DeleteDuplicates;
termsType=DeleteCases[termsType,elem_/;(Limit[elem,sInt->pointBCAsy]==0||elem==1)];
coeffTerms=GetCoefficient[completeSolutionAsy-boundaryConditionAsy//Expand//ChopDigits,termsType];
coeffTerms=DeleteCases[coeffTerms,elem_/;Limit[elem,sInt->pointBCAsy]==0];
coeffTerms=Equal[#,0]&/@coeffTerms;
solveCoefficients=Solve[SetPrecNumber[coeffTerms]];
If[Length[solveCoefficients]=!=Length[boundaryConditionAsy]||solveCoefficients==={},PrintError["I was not able to fix the boundary conditions for MI: "<>ToString[SeaSyde`Private`Debug`MInumber]<>", \[Epsilon] order: "<>ToString[SeaSyde`Private`Debug`EpsOrder]<>". Aborting the computation."];];
solveCoefficients=First[solveCoefficients];
Return[solveCoefficients];
];

GetCoefficient[expressionGC_,type_]:=Module[{coefficients={}},
Do[
If[FreeQ[type[[ind]],Log[_]],
AppendTo[coefficients,Coefficient[#,sInt,Exponent[type[[ind]],sInt]]&/@expressionGC];
,
AppendTo[coefficients,Coefficient[expressionGC,type[[ind]]]];
];

,{ind,1,Length[type]}];
coefficients=DeleteCases[Flatten[coefficients],0];
Return[coefficients];
];

MySolve[linearSystemOfEquations_]:=Module[{rank,unknownCoefficients,solutionSystem,matrixSystem,rowreduced,reducedsystem,solveFor},
unknownCoefficients=Cases[linearSystemOfEquations,c[__],Infinity]//DeleteDuplicates//Sort//Reverse;
matrixSystem=CoefficientArrays[linearSystemOfEquations,unknownCoefficients]//Normal//Last;
rowreduced=RowReduce[matrixSystem,Tolerance->10^(-ChopPrecisionPrivate)]//ChopDigits;
reducedsystem=DeleteCases[Map[Equal[#,0]&,rowreduced . unknownCoefficients],True];

Check[
solutionSystem=Solve[reducedsystem]/.{num_Real:>SetUltraPrec[num],num_Complex:>SetUltraPrec[num]};
,
PrintError["Error while solving the linear system in SolveFrobenius!"];
];
Return[solutionSystem];
];

End[];
EndPackage[];



