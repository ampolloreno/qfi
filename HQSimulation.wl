(* ::Package:: *)

(* ::Section:: *)
(*Prologue*)


BeginPackage["HQSimulation`"];
Needs["PhysicsConstants`"];


SEQSolve::usage="Solve\[LetterSpace]SEQ[H,vec,{tstart,tfin}] returns the solution the Schrodinger equation using Hamiltonian H (with optional time dependence) from time tstart to tfin, with initial conditions \[Psi](tstart)=vec.\nIf, rather than vec, you pass a list {\!\(\*SubscriptBox[\(vec\), \(1\)]\),\!\(\*SubscriptBox[\(vec\), \(2\)]\),...,\!\(\*SubscriptBox[\(vec\), \(n\)]\)}, Solve\[LetterSpace]SEQ will return a list of n solutions, one for each starting state.";
SEQSolveEV::usage="Fill in"
MEQSolve::usage="Fill in"

MutuallyUnbiasedBases::usage="Returns a maximal set of mutually unbiased bases, direct producted into the bosonic vaccum.  As an optional arument, you can set MotionalOp \[Rule] A, and the code will retun MUBs direct producted into the (normalized) state A|vacuum>."
ComputationalBasis::usage="Fill in"
AverageInfidelity::usage="AverageFidelity[H1,{t1min,t1max},H2,{t2min,t2max}] computes the average fidelity of U2 relative to U1, where each unitary corresponds to the time evolution of the respective Hamiltonian and time range. Note: This code assumes that one of the unitaries produces pure spin states." 

SpinStates::usage="test";
ConstructBasis::usage="Builds many body Hilbert space";
GetOperators::usage="fill in"
NumModes::usage="Number of bosonic modes";
NumSpins::usage="Number of spins";
GetPosFast::usage="Get position from symbolic vector";
GetVecFast::usage="Get symbolic vector from position";
BasisFuncQ::usage="Test whether vector is in the current Hilbert space";
HSdim::usage="Hilbert space dimension";
MakeAllOps::usage="Build all operators";
OpA::usage="OpA[j] is the annihilation operator for mode j=1,2,3,...";
OpAdag::usage="OpAdag[j] is the creation operator for mode j=1,2,3,...";
OpN::usage="OpN[j] is the number operator for mode j=1,2,3,...";
OpR::usage="Creates position operators given information about an ion chain";
OpSwap::usage="OpSwap[j,\[Alpha]=0,1,2,...,\[Beta]=0,1,2,...] is the transition operator |\[Beta]\[RightAngleBracket]\[LeftAngleBracket]\[Alpha]| for ion j=1,2,3,...";
ME::usage="Truncated matrix exponentials"
OpId::usage="Identity operator"
MakeFunc::usage="fill in"
MakeFuncExplicitTD::usage="fill in"
TrMotion::usage="TrMotion[\[Rho]] performs a partial trace over the bosonic degrees of freedom, leaving behind a reduced spin density matrix. The argument \[Rho] must be an (HSdim \[Times] HSdim) density matrix on the full spin-boson Hilbert space"

(*TransferMatrix::usage="Fill in"*)
GetChannel::usage="fill in"
AverageFidelity::usage="fill in"
ProcessFidelity::usage="fill in"

From\[Rho]GetL::usage="Fill in"


ChannelForm::usage="fill in"
Progress::usage="Option for solving the Schrodinger Equation"
Display::usage="Option to display globally defined operators"
MotionalOp::usage="Option to specify an operator A in order to initiate the bosonic degrees of freedom in A|vac\[RightAngleBracket] when computing fidelities."
PackedArray::usage="Fill in"
FinalState::usage="Option for SEQSolve. If FinalState\[Rule]True, then rather than returning an interpolation function NDSolve will just return the wavefunction at the final time."
OpVals::usage="Fill in"


Begin["`Private`"];


(* ::Section:: *)
(*Basis creation function*)


Clear[ConstructBasis]
ConstructBasis[SpinStates_,ModeCutoffs_]:=Module[{veclist,DigitVals,DigitList,BaseList,GetVec,pos,i,j,vec,IndList,CheckFunc,checktab,testvec,repeats},


(*Clear some objects that will be set globally when this function is called*)
Clear[HSdim,NumSpins,NumModes,BasisFuncQ,GetVecFast,GetPosFast];

HSdim=Times@@Join[SpinStates,ModeCutoffs+1];
spinstates=SpinStates;
NumSpins=Length[SpinStates];
NumModes=Length[ModeCutoffs];
BasisFuncQ[vec_]:=And@@Thread[ConstantArray[0,NumSpins+NumModes]<=vec<=Join[SpinStates-1,ModeCutoffs]];

DigitVals=Reverse[DigitList=Table[Product[Join[SpinStates,ModeCutoffs+1,{1}][[i]],{i,NumSpins+NumModes+1,NumSpins+NumModes+2-j,-1}],{j,1,NumSpins+NumModes}]];
GetPosFast=Compile[{{vec,_Integer,1}},DigitVals.vec+1];
BaseList=MixedRadix[Join[SpinStates,ModeCutoffs+1]];
GetVec[pos_]:=PadLeft[IntegerDigits[pos-1,BaseList],NumSpins+NumModes];
veclist=Table[GetVec[pos],{pos,HSdim}];
GetVecFast[pos_]:=veclist[[pos]];

]


(* ::Section:: *)
(*Operator primitives*)


(* ::Subsection:: *)
(*creation/annihilation/number operators*)


(* ::Text:: *)
(*adag`op[\[Alpha]] implements the creation operator on mode \[Alpha].  Together with it's Hermitian conjugate  a`op[\[Alpha]], it can be used to compose arbitrary bosonic operators*)


adagGetMatrixElement[j_,\[Alpha]_]:=Module[{vec0,vec1,val},

vec0=GetVecFast[j];
vec1=adagsymbolic[\[Alpha]][vec0];
val=Sqrt[vec1[[NumSpins+\[Alpha]]]];
If[BasisFuncQ[vec1],Return[{GetPosFast[vec1],j}->(val//N)],Return[0]];

]

Options[MakeBosonOps]={PackedArray->False};
MakeBosonOps[opts:OptionsPattern[]]:=Module[{\[Alpha]},

PhononAdd=Table[Join[Table[0,{\[Beta],NumSpins}],Table[If[\[Beta]==\[Alpha],1,0],{\[Beta],NumModes}]],{\[Alpha],NumModes}];
adagsymbolic[\[Beta]_][vec_]:=vec+PhononAdd[[\[Beta]]];

\[Alpha]=1;While[\[Alpha]<=NumModes,

adagmes[\[Alpha]]=DeleteCases[(adagGetMatrixElement[#,\[Alpha]]&)/@Range[HSdim],0];

(*OpAdagtemp[\[Alpha]]=SparseArray[adagmes[\[Alpha]],{HSdim,HSdim}];
OpAtemp[\[Alpha]]=Transpose[OpAdagtemp[\[Alpha]]];*)

OpAdag[\[Alpha]]=SparseArray[adagmes[\[Alpha]],{HSdim,HSdim}];
If[OptionValue[PackedArray]==True,OpAdag[\[Alpha]]=Developer`ToPackedArray[Normal[OpAdag[\[Alpha]]]//N]];

OpA[\[Alpha]]=Transpose[OpAdag[\[Alpha]]];
OpN[\[Alpha]]=OpAdag[\[Alpha]].OpA[\[Alpha]];

\[Alpha]++];

]

(*OpA[\[Alpha]_]=OpAtemp[\[Alpha]];
OpAdag[\[Alpha]_]=OpAdagtemp[\[Alpha]];*)


(* ::Subsection:: *)
(*Spin operators*)


(* ::Text:: *)
(*Sswap`op[s,\[Sigma],\[Tau]] implements the operator |\[Tau]\[RightAngleBracket]\[LeftAngleBracket]\[Sigma]| on the s^th spin, i.e. it is either a projector onto state \[Sigma] (for \[Sigma]  = \[Tau]) or it implements a transition from state \[Sigma] to state \[Tau] (\[Sigma] != \[Tau]).  All spin operators can be composed from these building blocks.*)


SswapGetMatrixElement[j_,s_,\[Sigma]_,\[Tau]_]:=Module[{vec0,vec1},

vec0=GetVecFast[j];
If[Abs[vec0[[s]]-\[Sigma]]>0,Return[0]];

vec1=vec0;
vec1[[s]]=\[Tau];

Return[{GetPosFast[vec1],j}->1.];

]

Options[MakeSpinOps]={PackedArray->False};
MakeSpinOps[SpinStates_,opts:OptionsPattern[]]:=Module[{s,\[Sigma],\[Tau]},
s=1;While[s<=NumSpins,
\[Sigma]=0;While[\[Sigma]<=SpinStates[[s]]-1,
\[Tau]=0;While[\[Tau]<=SpinStates[[s]]-1,

Sswapmes[s,\[Sigma],\[Tau]]=DeleteCases[(SswapGetMatrixElement[#,s,\[Sigma],\[Tau]]&)/@Range[HSdim],0];

Sswapop[s,\[Sigma],\[Tau]]=SparseArray[Sswapmes[s,\[Sigma],\[Tau]],{HSdim,HSdim}];

If[OptionValue[PackedArray]==True,Sswapop[s,\[Sigma],\[Tau]]=Developer`ToPackedArray[Normal[Sswapop[s,\[Sigma],\[Tau]]]//N]];

\[Tau]++];
\[Sigma]++];
s++];

]

OpSwap[s_,\[Sigma]_,\[Tau]_]=Sswapop[s,\[Sigma],\[Tau]];


(* ::Text:: *)
(*Here are the Pauli operators for each spin about an arbitrary axis in the xy plane (specified by angle \[Phi])*)


(* ::Subsection:: *)
(*Function to build all operators simultaneously*)


Options[MakeAllOps]={PackedArray->False};
MakeAllOps[SpinStates_,ModeCutoffs_,opts:OptionsPattern[]]:=Module[{},MakeSpinOps[SpinStates,opts];MakeBosonOps[opts];OpId=IdentityMatrix[HSdim,SparseArray];];


(* ::Section:: *)
(*Build basis and make operators*)


Clear[GetOperators]
Options[GetOperators]={Display->False,PackedArray->False};
GetOperators[SpinStates_,ModeCutoffs_,opts:OptionsPattern[]]:=Module[{},

ConstructBasis[SpinStates,ModeCutoffs];
MakeAllOps[SpinStates,ModeCutoffs,FilterRules[{opts},Options[MakeAllOps]]];


If[OptionValue[Display]==True,

oplist={OpA,OpAdag,OpN,OpSwap};
descriptions=Transpose[{(ToString[#]&)/@oplist,(#::usage &)/@oplist}];

list=Join[{{"OpId",OpId::usage}},descriptions,{{"Hilbert space dimension","HSdim="<>ToString[HSdim]}}];

Print[TableForm[list,TableHeadings->{{},{"Operator","Description"}}]]];


]


(* ::Subsection:: *)
(*Truncated matrix exponentials*)


(* ::Text:: *)
(*This function takes an operator "op" and returns a Taylor expansion of exp(op) to order "order".  When expanding exp(I k\[CenterDot]r), "order"=1 will give the usual Lamb-Dicke approximation.  "order" >= 5 will cause the function to just return a converged matrix exponential.*)


ME[op_,order_]:=If[order<5,OpId+Sum[MatrixPower[op,n]/n!,{n,1,order}],MatrixExp[op]];


(* ::Subsection:: *)
(*Position operators*)


(* ::Text:: *)
(*Function notes. This function ingests:*)
(**)
(*mlist: a list of the mass associated with each degree of freedom*)
(*num: The number of ions in the crystal*)
(*\[Omega]list: A list of the mode angular frequencies*)
(*bmat: A matrix specifying the normal modes*)


OpR[mlist_,\[Omega]list_,bmat_]:=Module[{Id,pos0,X`ops,\[Alpha],s},

X`ops=Table[Sum[Sqrt[\[HBar]/(mlist[[s]]*\[Omega]list[[\[Alpha]]])]bmat[[s,\[Alpha]]]((OpAdag[\[Alpha]]+OpA[\[Alpha]])/Sqrt[2]),{\[Alpha],Length[mlist]}],{s,Length[mlist]}];
Return[Partition[X`ops,3]];

]


(* ::Subsection:: *)
(*Operator averages*)


(* ::Text:: *)
(*Ev[op,\[Tau]] computes the expectation value of the operator "op" using the wavefunction computed above at time "\[Tau]".*)
(**)
(*MakeFunc[op,range,mesh] returns a table of the expectation value of operator "op" at times t sampled over the range "range" in units of "range"/"mesh".*)
(**)
(*The "ExplicitTD" version of these functions allows the input of operators defined as explicitly time dependent functions.  You just input the operator symbol though, for example if you define operator[t_]:=...[t], then you enter just the function name "operator".*)


Clear[Global`t]
EV[op_, \[Tau]_, nds_] := Module[{vec, vecstar}, vec = nds /. {Global`t -> \[Tau]}; 
    vecstar = Conjugate[vec]; Return[Chop[Dot[vecstar,op,vec]]]; ]
MakeFunc[op_, nds_, range_, mesh_] := Module[{t, func}, 
   func = Table[{t, EV[op, t, nds]}, {t, range[[1]], range[[2]], 
       (range[[2]] - range[[1]])/mesh}]; Return[func]; ]
EVExplicitTD[op_, \[Tau]_, nds_] := Module[{vec, vecstar}, 
   vec = nds /. {Global`t -> \[Tau]}; vecstar = Conjugate[vec]; 
    Return[Chop[Dot[vecstar,op[\[Tau]],vec]]]; ]
MakeFuncExplicitTD[op_, nds_, range_, mesh_] := 
  Module[{t, func}, func = Table[{t, EVExplicitTD[op, t, nds]}, 
      {t, range[[1]], range[[2]], (range[[2]] - range[[1]])/mesh}]; Return[func]; ]


(* ::Subsection:: *)
(*Reduced spin density matrices*)


TrMotion[\[Rho]_] := Module[{ step1, step2, dim`spin, dim`motion}, 
   dim`spin = Times @@ SpinStates; 
    dim`motion = Times @@ (Global`ModeCutoffs + 1); 
    step1 = Transpose[Partition[(Partition[#1, dim`motion] & ) /@ \[Rho], dim`motion], 
      {1,3,2,4}]; step2 = (Tr /@ #1 & ) /@ step1; Return[step2]]


(* ::Section:: *)
(*Schrodinger equation solver*)


Clear[SEQSolve]
Options[SEQSolve]=Join[{Progress->False,FinalState->False},Options[NDSolve]];
SEQSolve[H_, v0_,{tstart_,tfin_},opts:OptionsPattern[]]:=Module[{dims,dimic,hsdim,vec,vars,solvars,LHS,RHS,SEQ,BCS,tlist,\[Psi],nds,ndslist,ndsdata,vals},

Clear[Global`t,j];

dims=Dimensions[N[v0]];
dimic=Depth[N[v0]]-1;

If[Dimensions[H/.Global`t->tstart]!={Last[dims],Last[dims]},Print[Style["Error: Hamiltonian and initial conditions don't have the same dimensions",Red,Bold]];Return[]];

hsdim=Last[dims];

vars=Table[\[Psi][j][Global`t],{j,1,hsdim}];
If[OptionValue[FinalState]==False,solvars=vars,solvars={}];
LHS=Table[\[Psi][j]'[Global`t],{j,1,hsdim}];
RHS=-I H.vars;
SEQ=Thread[LHS==RHS];

If[dimic==1,

If[OptionValue[Progress]==True,Print["Progress (time through single solution):\n",ProgressIndicator[Dynamic[tmonitor/(tfin-tstart)]]]];
BCS=Thread[(vars/.Global`t->tstart)==v0];
ndsdata=First[NDSolve`ProcessEquations[Join[SEQ,BCS,If[OptionValue[FinalState]==False,{},{WhenEvent[Global`t==tfin-$MachineEpsilon(tfin-tstart),Sow[vars]]}]],solvars,Global`t,Join[FilterRules[{opts},Options[NDSolve]],If[OptionValue[Progress]==True,{StepMonitor:>(tmonitor=Global`t)},{}]]]];

If[OptionValue[FinalState]==False,NDSolve`Iterate[ndsdata,tfin];nds=NDSolve`ProcessSolutions[ndsdata];Return[nds[[;;,2]]],vals=Reap[NDSolve`Iterate[ndsdata,tfin]][[2,1,1]];Return[vals]];

];

If[dimic>1,

If[OptionValue[Progress]==True,Print["Progress (looping through initial conditions):\n",ProgressIndicator[Dynamic[jmonitor/Length[v0]]]]];
jmonitor=1;
BCS=Thread[(vars/.Global`t->tstart)==v0[[1]]];

ndsdata=First[NDSolve`ProcessEquations[Join[SEQ,BCS,If[OptionValue[FinalState]==False,{},{WhenEvent[Global`t==tfin-$MachineEpsilon(tfin-tstart),Sow[vars]]}]],solvars,Global`t,FilterRules[{opts},Options[NDSolve]]]];

If[OptionValue[FinalState]==False,NDSolve`Iterate[ndsdata,tfin];nds=NDSolve`ProcessSolutions[ndsdata];ndslist={nds[[;;,2]]},vals=Reap[NDSolve`Iterate[ndsdata,tfin]][[2,1,1]];ndslist={vals}];

Do[jmonitor=j;

BCS=Thread[(vars/.Global`t->tstart)==v0[[j]]];
ndsdata=First[NDSolve`Reinitialize[ndsdata,BCS]];

If[OptionValue[FinalState]==False,NDSolve`Iterate[ndsdata,tfin];nds=NDSolve`ProcessSolutions[ndsdata];AppendTo[ndslist,nds[[;;,2]]],vals=Reap[NDSolve`Iterate[ndsdata,tfin]][[2,1,1]];AppendTo[ndslist,vals]],

{j,2,First[dims]}];

Return[ndslist];

];

]






(* ::Section:: *)
(*Schrodinger equation expectation value solver*)


Clear[SEQSolveEV]
Options[SEQSolveEV]=Join[{Progress->False},Options[NDSolveValue]];
SEQSolveEV[H_, v0_, {op_,times_}, {tstart_,tfin_},opts:OptionsPattern[]]:=Module[{dims,dimic,vec,vars,func,solvars,LHS,RHS,SEQ,BCS,tlist,\[Psi],nds,ndslist,ndsv,ndsdata,vals},

Clear[Global`t,j];

dims=Dimensions[N[v0]];
dimic=Depth[N[v0]]-1;

If[Dimensions[H/.Global`t->tstart]!={Last[dims],Last[dims]},Print[Style["Error: Hamiltonian and initial conditions don't have the same dimensions",Red,Bold]];Return[]];

vars=Table[\[Psi][j][Global`t],{j,1,HSdim}];
func=Conjugate[vars].op.vars/.{Global`t->times};
LHS=Table[\[Psi][j]'[Global`t],{j,1,HSdim}];
RHS=-I H.vars;
SEQ=Thread[LHS==RHS];

If[dimic==1,

If[OptionValue[Progress]==True,Print["Progress (time through single solution):\n",ProgressIndicator[Dynamic[tmonitor/(tfin-tstart)]]]];
BCS=Thread[(vars/.Global`t->tstart)==v0];
ndsv=NDSolveValue[Join[SEQ,BCS],func,{Global`t,tstart,tfin},Join[FilterRules[{opts},Options[NDSolve]],If[OptionValue[Progress]==True,{StepMonitor:>(tmonitor=Global`t)},{}]]];
Return[Transpose[{times,ndsv}]];

];

If[dimic>1,

jmonitor=1;
If[OptionValue[Progress]==True,Print["Progress (looping through initial conditions):\n",ProgressIndicator[Dynamic[jmonitor/Length[v0]]]]];
ndslist={};

Do[jmonitor=j;

BCS=Thread[(vars/.Global`t->tstart)==v0[[j]]];
ndsv=NDSolveValue[Join[SEQ,BCS],func,{Global`t,tstart,tfin},Join[FilterRules[{opts},Options[NDSolveValue]],If[OptionValue[Progress]==True,{StepMonitor:>(tmonitor=Global`t)},{}]]];
AppendTo[ndslist,Transpose[{times,ndsv}]],

{j,1,First[dims]}];

Return[ndslist];

];

]






(* ::Section:: *)
(*Master equation solver*)


Clear[MEQSolve]
Options[MEQSolve]=Join[{Progress->False,FinalState->False},Options[NDSolve]];
MEQSolve[H_, jops_, \[Rho]0_,{tstart_,tfin_},opts:OptionsPattern[]]:=Module[{\[Rho],dims,dimic,hsdim,vec,vars,solvars,LHS,RHS,SEQ,BCS,tlist,\[Psi],nds,ndslist,ndsdata,vals},

Clear[Global`t,j];

dims=Dimensions[N[\[Rho]0]];
dimic=Depth[N[\[Rho]0]]-1;

If[Dimensions[H/.Global`t->tstart]!={Last[dims],Last[dims]},Print[Style["Error: Hamiltonian and initial conditions don't have the same dimensions",Red,Bold]];Return[]];

hsdim=Last[dims];

vars=Table[\[Rho][j,k][Global`t],{j,1,hsdim},{k,1,hsdim}];
If[OptionValue[FinalState]==False,solvars=vars,solvars={}];
LHS=Table[\[Rho][j,k]'[Global`t],{j,1,hsdim},{k,1,hsdim}];
RHS=-I (H.vars-vars.H)+Total[(#.vars.ConjugateTranspose[#]-1/2 (ConjugateTranspose[#].#.vars + vars.ConjugateTranspose[#].#)&)/@jops];
SEQ=Thread[Flatten[LHS]==Flatten[RHS]];

If[dimic==2,

If[OptionValue[Progress]==True,Print["Progress (time through single solution):\n",ProgressIndicator[Dynamic[tmonitor/(tfin-tstart)]]]];
BCS=Thread[Flatten[(vars/.Global`t->tstart)]==Flatten[\[Rho]0]];
ndsdata=First[NDSolve`ProcessEquations[Join[SEQ,BCS,If[OptionValue[FinalState]==False,{},{WhenEvent[Global`t==tfin-$MachineEpsilon(tfin-tstart),Sow[vars]]}]],solvars,Global`t,Join[FilterRules[{opts},Options[NDSolve]],If[OptionValue[Progress]==True,{StepMonitor:>(tmonitor=Global`t)},{}]]]];

If[OptionValue[FinalState]==False,NDSolve`Iterate[ndsdata,tfin];nds=NDSolve`ProcessSolutions[ndsdata];Return[nds[[;;,2]]],vals=Reap[NDSolve`Iterate[ndsdata,tfin]][[2,1,1]];Return[vals]];

];

If[dimic>2,

If[OptionValue[Progress]==True,Print["Progress (looping through initial conditions):\n",ProgressIndicator[Dynamic[jmonitor/Length[\[Rho]0]]]]];
jmonitor=1;
BCS=Thread[Flatten[(vars/.Global`t->tstart)]==Flatten[\[Rho]0[[1]]]];

ndsdata=First[NDSolve`ProcessEquations[Join[SEQ,BCS,If[OptionValue[FinalState]==False,{},{WhenEvent[Global`t==tfin-$MachineEpsilon(tfin-tstart),Sow[vars]]}]],solvars,Global`t,FilterRules[{opts},Options[NDSolve]]]];

If[OptionValue[FinalState]==False,NDSolve`Iterate[ndsdata,tfin];nds=NDSolve`ProcessSolutions[ndsdata];ndslist={nds[[;;,2]]},vals=Reap[NDSolve`Iterate[ndsdata,tfin]][[2,1,1]];ndslist={vals}];

Do[jmonitor=j;

BCS=Thread[Flatten[(vars/.Global`t->tstart)]==Flatten[\[Rho]0[[j]]]];
ndsdata=First[NDSolve`Reinitialize[ndsdata,BCS]];

If[OptionValue[FinalState]==False,NDSolve`Iterate[ndsdata,tfin];nds=NDSolve`ProcessSolutions[ndsdata];AppendTo[ndslist,nds[[;;,2]]],vals=Reap[NDSolve`Iterate[ndsdata,tfin]][[2,1,1]];AppendTo[ndslist,vals]],

{j,2,First[dims]}];

Return[ndslist];

];

]



(* ::Section:: *)
(*Utilities to extract quantum channels / fidelity*)


Clear[ComputationalBasis]
Options[ComputationalBasis]={MotionalOp:>OpId};
ComputationalBasis[opts:OptionsPattern[]]:=Module[{poss,vecs,qlist,vacuum},

vacuum=ConstantArray[0,NumModes];
qlist=IntegerDigits[Range[0,Times@@SpinStates-1],MixedRadix[SpinStates],Length[SpinStates]];
poss=Table[GetPosFast[Join[qlist[[j]],vacuum]],{j,1,Length[qlist]}];
vecs=Normalize[Dot[OptionValue[MotionalOp],#]]&/@Table[UnitVector[HSdim,poss[[j]]],{j,1,Length[poss]}];
Return[vecs//N];
];



Clear[MutuallyUnbiasedBases]
Options[MutuallyUnbiasedBases]={MotionalOp:>OpId};
MutuallyUnbiasedBases[num_,opts:OptionsPattern[]]:=Module[{poss,vecs,vacuum,MakeVec,B1,B2,B3,B4,B5,mub},

If[MemberQ[{1,2},num]==False,Print["Haven't added this case yet"];Return[$Failed]];
vacuum=ConstantArray[0,NumModes];



If[num==1,
poss={GetPosFast[Join[{0},vacuum]],GetPosFast[Join[{1},vacuum]]};
vecs=Normalize[Dot[OptionValue[MotionalOp],#]]&/@Table[UnitVector[HSdim,poss[[j]]],{j,1,Length[poss]}];
MakeVec[vec_]:=vec.vecs;
B1={MakeVec[{1,0}],MakeVec[{0,1}]};
B2=1/Sqrt[2] {MakeVec[{1,1}],MakeVec[{1,-1}]};
B3=1/Sqrt[2] {MakeVec[{1,I}],MakeVec[{1,-I}]};
mub=Join[B1,B2,B3];
Return[mub];
];



If[num==2,
poss={GetPosFast[Join[{0,0},vacuum]],GetPosFast[Join[{0,1},vacuum]],GetPosFast[Join[{1,0},vacuum]],GetPosFast[Join[{1,1},vacuum]]};
vecs=Normalize[Dot[OptionValue[MotionalOp],#]]&/@Table[UnitVector[HSdim,poss[[j]]],{j,1,Length[poss]}];
MakeVec[vec_]:=vec.vecs;
B1={MakeVec[{1,0,0,0}],MakeVec[{0,1,0,0}],MakeVec[{0,0,1,0}],MakeVec[{0,0,0,1}]};
B2=1/2 {MakeVec[{1,1,1,1}],MakeVec[{1,1,-1,-1}],MakeVec[{1,-1,-1,1}],MakeVec[{1,-1,1,-1}]};
B3=1/2 {MakeVec[{1,-1,-I,-I}],MakeVec[{1,-1,I,I}],MakeVec[{1,1,I,-I}],MakeVec[{1,1,-I,I}]};
B4=1/2 {MakeVec[{1,-I,-I,-1}],MakeVec[{1,-I,I,1}],MakeVec[{1,I,I,-1}],MakeVec[{1,I,-I,1}]};
B5=1/2 {MakeVec[{1,-I,-1,-I}],MakeVec[{1,-I,1,I}],MakeVec[{1,I,-1,I}],MakeVec[{1,I,1,-I}]};
mub=Join[B1,B2,B3,B4,B5];
Return[mub];
];

]


From\[Psi]GetL[\[Psi]list_]:=Module[{spindim=Times@@SpinStates, LsupT,qr,\[Psi]out,\[Rho]out,\[Rho]spinout,\[Rho]spinoutvec,Lsup},
LsupT={};
Do[
qr=Reverse[QuotientRemainder[j-1,spindim]+1];
\[Psi]out=\[Psi]list[[qr]];
\[Rho]out=KroneckerProduct[\[Psi]out[[1]],Conjugate[\[Psi]out[[2]]]];
\[Rho]spinout=TrMotion[\[Rho]out];
\[Rho]spinoutvec=Flatten[Transpose[\[Rho]spinout]]//Chop;
AppendTo[LsupT,\[Rho]spinoutvec],
{j,1,spindim^2}];
Lsup=Transpose[LsupT];
Return[Lsup];
]

From\[Rho]GetL[\[Rho]list_]:=Module[{spindim=Times@@SpinStates, LsupT,qr,\[Psi]out,\[Rho]out,\[Rho]spinout,\[Rho]spinoutvec,Lsup},
LsupT={};
Do[
\[Rho]spinout=TrMotion[\[Rho]list[[j]]];
\[Rho]spinoutvec=Flatten[Transpose[\[Rho]spinout]]//Chop;
AppendTo[LsupT,\[Rho]spinoutvec],
{j,1,Length[\[Rho]list]}];
Lsup=Transpose[LsupT];
Return[Lsup];
]


LtoP[mat_]:=Module[{spindim=Times@@SpinStates},

Return[ArrayReshape[Transpose[ArrayReshape[mat,{spindim,spindim,spindim,spindim}],{4,2,3,1}],{spindim^2,spindim^2}]];

]


Options[KrausOperators]={Truncation->10^-10};
KrausOperators[ProcessMatrix_,opts:OptionsPattern[]]:=Module[{egs,KrausOps,KrausOpsPhase,egsfilter,spindim=Times@@SpinStates},

egs=Transpose[Eigensystem[ProcessMatrix]]//Chop;
egsfilter=Select[egs,#[[1]]>OptionValue[Truncation]&];
KrausOps=ArrayReshape[(Sqrt[#[[1]]]*#[[2]]),{spindim,spindim}]&/@egsfilter;
KrausOpsPhase=Table[KrausOps[[j]]Exp[-I Arg[KrausOps[[j,1,1]]]],{j,1,Length[KrausOps]}];
Return[KrausOpsPhase];

]


Clear[GetChannel]
Options[GetChannel]=Join[{ChannelForm->"TransferMatrix"},Options[SEQSolve],Options[MutuallyUnbiasedBases],Options[ComputationalBasis],Options[KrausOperators]];

GetChannel[H_,{tmin_,tmax_},opts:OptionsPattern[]]:=Module[{spindim=Times@@SpinStates,veclist,\[Psi]outlist,Lmat,Pmat},

(*veclist=MutuallyUnbiasedBases[NumSpins,FilterRules[{opts},Options[MutuallyUnbiasedBases]]][[1;;2^NumSpins]];*)
veclist=ComputationalBasis[FilterRules[{opts},Options[ComputationalBasis]]];


\[Psi]outlist=SEQSolve[H,veclist,{tmin,tmax},Progress->False,FinalState->True,FilterRules[{opts},Options[NDSolve]]];
Lmat=From\[Psi]GetL[\[Psi]outlist];

If[OptionValue[ChannelForm]=="TransferMatrix",Return[Lmat]];
If[OptionValue[ChannelForm]=="ProcessMatrix",Return[LtoP[Lmat]]];
If[OptionValue[ChannelForm]=="KrausOperators",Return[KrausOperators[LtoP[Lmat],FilterRules[{opts},KrausOperators]]]];

]


(*Options[GetChannel]=Join[{ChannelForm->"TransferMatrix"},Options[SEQSolve],Options[MutuallyUnbiasedBases],Options[ComputationalBasis],Options[KrausOperators]];

GetChannel[H_, jops_, {tmin_,tmax_},opts:OptionsPattern[]]:=Module[{spindim=Times@@SpinStates,veclist,\[Rho]list,\[Rho]outlist,Lmat,Pmat},

veclist=ComputationalBasis[FilterRules[{opts},Options[ComputationalBasis]]];
\[Rho]list=Flatten[Table[KroneckerProduct[veclist[[k]],Conjugate[veclist[[j]]]],{j,1,spindim},{k,1,spindim}],1];

\[Rho]outlist=MEQSolve[H, jops, \[Rho]list, {tmin,tmax}, Progress->False,FinalState->True, FilterRules[{opts}, Options[NDSolve]]];

Lmat=From\[Rho]GetL[\[Rho]outlist];

If[OptionValue[ChannelForm]=="TransferMatrix",Return[Lmat]];
If[OptionValue[ChannelForm]=="ProcessMatrix",Return[LtoP[Lmat]]];
If[OptionValue[ChannelForm]=="KrausOperators",Return[KrausOperators[LtoP[Lmat],FilterRules[{opts},KrausOperators]]]];

]*)


Options[AverageFidelity]=Join[Options[SEQSolve],Options[GetChannel],{Display->False}]

AverageFidelity[H1_,{t1min_,t1max_},H2_,{t2min_,t2max_},opts:OptionsPattern[]]:=Module[{L1,L2,GC1,GC2,d,prcfid,avgfid},

L1=GetChannel[H1,{t1min,t1max},FilterRules[{opts},Options[GetChannel]]];
L2=GetChannel[H2,{t2min,t2max},FilterRules[{opts},Options[GetChannel]]];

d=2^NumSpins;
prcfid=Tr[ConjugateTranspose[L1].L2]/d^2;
avgfid=(d*prcfid+1)/(d+1);

Return[avgfid//Chop];

]

ProcessFidelity[H1_,{t1min_,t1max_},H2_,{t2min_,t2max_},opts:OptionsPattern[]]:=Module[{L1,L2,GC1,GC2,d,prcfid,avgfid},

L1=GetChannel[H1,{t1min,t1max},FilterRules[{opts},Options[GetChannel]]];
L2=GetChannel[H2,{t2min,t2max},FilterRules[{opts},Options[GetChannel]]];

d=2^NumSpins;
prcfid=Tr[ConjugateTranspose[L1].L2]/d^2;

Return[prcfid//Chop];

]


(* ::Section:: *)
(*Average fidelity*)


(* ::Text:: *)
(*Function to compute average fidelity for time evolution under H2, with target Hamiltonian H1*)


Clear[AverageInfidelity]
Options[AverageInfidelity]=Join[Options[SEQSolve],Options[MutuallyUnbiasedBases]];
AverageInfidelity[H1_,{t1min_,t1max_},H2_,{t2min_,t2max_},opts:OptionsPattern[]]:=Module[{mub,inFid,vec1,vec2},

If[MemberQ[{{2},{2,2}},SpinStates]==False,Print["This code is only designed to compute average fidelity for 1 or 2 qubits"];Return[$Failed]];

mub=MutuallyUnbiasedBases[NumSpins,FilterRules[{opts},Options[MutuallyUnbiasedBases]]];
inFid[list1_,list2_]:=Module[{j=1,\[Rho]noise,\[Rho]nom,fidelitylist={}},
While[j<=Length[list1],
\[Rho]nom=KroneckerProduct[list1[[j]],Conjugate[list1[[j]]]];\[Rho]noise=KroneckerProduct[list2[[j]],Conjugate[list2[[j]]]];
AppendTo[fidelitylist,Tr[TrMotion[\[Rho]noise].TrMotion[\[Rho]nom]]];
j++];
Return[1-Mean[fidelitylist]];
];

vec1=SEQSolve[H1,mub,{t1min,t1max},FilterRules[{opts},Options[SEQSolve]],FinalState->True];
vec2=SEQSolve[H2,mub,{t2min,t2max},FilterRules[{opts},Options[SEQSolve]],FinalState->True];

Return[inFid[vec1,vec2]//Chop];

]


(* ::Section:: *)
(*Epilogue*)


End[]


EndPackage[]
