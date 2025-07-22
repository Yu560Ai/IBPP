(* ::Package:: *)

BeginPackage["IBPP`"]


Print["*******************************************************\n*********** \!\(\*
StyleBox[\"I\",\nFontWeight->\"Bold\"]\)(ntegration)\!\(\*
StyleBox[\"B\",\nFontWeight->\"Bold\"]\)(y)\!\(\*
StyleBox[\"P\",\nFontWeight->\"Bold\"]\)(art)\!\(\*
StyleBox[\"P\",\nFontWeight->\"Bold\"]\)(artial) ************\n*******************************************************"];


initialize::usage = "Initialize the intermediate variables to be used in INTSECA";


(*For IBPP basis*)


verticesList::usage = "Find the set of all \[LeftAngleBracket]J\[RightAngleBracket]";


Sol::usage = "Sol";
BdyBasis::usage = "{Bdy,Basis}";
funcTree::usage = "Plot the directed graph for basis";


AMatrix::usage = "A-matrix for each kinematic variable";
ATotal::usage = "total derivative A-matrix (for single twist): entries are the Log functions";


(*To given basis*)


CiCoeff::usage = "Gives the linear coefficient for projecting Feynman integral into basis integrals";


DEQ::usage = "Gives the coefficient 
	of each order of derivatives in the differential equation for the Feynman integral.";


(*Tools*)
t[{a__}] := \[LeftAngleBracket]a\[RightAngleBracket]; (* Transform list to \[LeftAngleBracket]...\[RightAngleBracket] symbol *)
tp[f_]:=f/.\[LeftAngleBracket]a__\[RightAngleBracket]:>{a} (*transform \[LeftAngleBracket]...\[RightAngleBracket] symbol to list*)
sort={\[LeftAngleBracket]a__\[RightAngleBracket]:>Signature[{a}]*t[Sort[{a}]]};


Begin["`Private`"];


(*Input*)
dim = Global`dim;
nkin = Global`nkin;
kin = Global`kin;
nBplane = Global`nBplane;
nTplane = Global`nTplane;
powers = Global`powers;
B = Global`B;
T = Global`T;
psi = Global`psi;


(*initialize the intermediate variables*)
initialize[] := (
nplane = nBplane+nTplane;
X = Append[Table[z[i] = Symbol["z" <> ToString[i]], {i, 1, dim}],1];
Lplanes = Join[Table[Global`B[i] . X, {i, nBplane}], Table[Global`T[i] . X, {i, nTplane}]];
jacT =JacT[Lplanes];
permT =PermT[dim,nkin];
Jac =Table[D[Lplanes[[i]],z[j]],{j,1,dim},{i,1,Length[Lplanes]}];
replaceTplane=Table[i->(i+nBplane),{i,1,nTplane}];
power=Join[ConstantArray[0,{nBplane}],powers];
dkin = Map[Symbol["d" <> ToString[#]] &, kin];);


(*Wedge product*)
rules={Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]a__\[RightAngleBracket]]:>0,Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>If[OrderedQ[{{a},{b}}],Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],-Wedge[\[LeftAngleBracket]b\[RightAngleBracket],\[LeftAngleBracket]a\[RightAngleBracket]]],
Wedge[c_*\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>c*Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],d_*\[LeftAngleBracket]b__\[RightAngleBracket]]:>d*Wedge[\[LeftAngleBracket]a\[RightAngleBracket],\[LeftAngleBracket]b\[RightAngleBracket]],Wedge[(c1_*term1_+rest_),(term2_)]:>Wedge[c1*term1,term2]+Wedge[rest,term2],
Wedge[c_,d_*\[LeftAngleBracket]b__\[RightAngleBracket]]:>c*d*\[LeftAngleBracket]b\[RightAngleBracket],Wedge[c_*\[LeftAngleBracket]a__\[RightAngleBracket],d_]:>c*d*\[LeftAngleBracket]a\[RightAngleBracket]};
wedgeToBracketRule={
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket],rest_]:>Wedge[\[LeftAngleBracket]a,b\[RightAngleBracket],rest],
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket],\[LeftAngleBracket]b__\[RightAngleBracket]]:>Wedge[\[LeftAngleBracket]a,b\[RightAngleBracket]],
Wedge[\[LeftAngleBracket]a__\[RightAngleBracket]]:>\[LeftAngleBracket]a\[RightAngleBracket]};
parallel:=\[LeftAngleBracket]a__\[RightAngleBracket]/;Det[Jac[[All,{a}]]]===0->0;
parallelRemove[v_List]:=DeleteCases[v//.parallel,0];


(*Find IBPP basis*)


(1)do IBP explicitly
phiJList[n_] :=t /@ Sort[Sort/@Flatten[With[{limits =Table[{Subscript[i, k], If[k == 1, 1, Subscript[i, k - 1] + 1], nplane}, {k, 1, n}]},Table[Array[Subscript[i, #] &, n], Evaluate[Sequence @@ limits]]], n - 1]];
verticesList:=phiJList[dim]//parallelRemove;
Omega:=powers . (t/@Array[{#+nBplane}&,nTplane]);
OmegaV[xi_List]:=Table[Wedge[Omega,xi[[i]]]//.rules//.wedgeToBracketRule//.sort,{i,1,Length[xi]}]//parallelRemove;
coordinate[Vertex_]:=First@(Solve[Map[Lplanes[[#]]==0&,tp[Vertex]],X[[1;;dim]]]//Simplify);
Relations[vertices_List] :=#==0&/@(OmegaV[phiJList[dim-1]])
Sol[]:=With[{vertices=verticesList},Solve[Relations[vertices],vertices]//First//Cancel//Simplify//Quiet]


(2)generate basis on cuts


boundary[vertex_List]:=Complement[vertex,Range[nBplane+1,nplane]]


BdyphiJList[n_]:=(t/@Sort[Sort/@(Flatten[With[{limits=Table[{Subscript[i,k],If[k==1,1,Subscript[i,k-1]+1],nTplane},{k,1,n}]},Table[Array[Subscript[i,#]&,n],Evaluate[Sequence@@limits]]],n-1])])/.replaceTplane;


BdyBasis[]:=(
vertices=verticesList;
sol=Sol[];
Basis=Complement[vertices,sol[[All,1]]];
bdyGrp=GroupBy[tp/@Basis,boundary];
Bdy=bdyGrp//Keys;
BdyVertices=Map[t,(bdyGrp//Values),{2}];
BdyVertices=BdyVertices[[Ordering[Bdy]]];
Bdy=Bdy//Sort;
Return[{Bdy,BdyVertices}]
)


(*Plot the boundary structure*)
funcTree[list_]:=Block[{graph,funcs,Nsite},
Nsite=Length@list[[-1]];
graph=ResourceFunction["HasseDiagram"][SubsetQ[#2,#1]&,list,VertexShapeFunction->"Name",GraphLayout->"LayeredDigraphEmbedding"];
funcs=Length@Cases[list,#]&/@Table[_,{i,0,Nsite},{j,i}];
Print[graph];
Print[Grid[{Prepend[Table[i,{i,0,Nsite}],"# codimension"],
Prepend[funcs,"# boundaries"]},Frame->All]]
]


(3)organize the differentiation


JacT[Lplanes_List]:=Table[Join[Table[D[Lplanes[[i]],kin[[j]]],{j,1,nkin}],Table[D[Lplanes[[i]],z[j]],{j,1,dim}]],{i,1,Length[Lplanes]}];
PermT[dim_,nkin_]:=Table[Permutations[Join[{n},Range[nkin+1,nkin+dim]]],{n,1,nkin}];


DKinVertex[Vertex_List(*,nkin_:nkin,dim_:dim*)]:=
Table[
Sum[
(
Signature[permT[[nkin,i]]]
(power[[Ad]]/( Subscript[l, Ad] Product[Subscript[l, Vertex[[j]]],{j,1,dim}])) 
jacT[[Ad,permT[[n,i,1]]]] 
Product[jacT[[Vertex[[k]],permT[[n,i,1+k]]]],{k,1,dim}]
)
,{i,1,Length[permT[[1]]]},{Ad,1,nplane}]
,{n,1,nkin}];

DKinCollect[Basis_List]:=(
nu=Basis//Length;
vertex={Basis//tp}//Transpose;
orient=ConstantArray[{1},nu];
DkinCollect=Table[Sum[orient[[i,j]] DKinVertex[vertex[[i,j]]],{j,1,Length[vertex[[i]]]}],{i,1,nu}];
Lindex=Table[{},{nkin},{nu}];Lcoeff=Table[{},{nkin},{nu}];
subL=Subsets[Range[nplane],{dim+1}];
Do[coeff=Coefficient[DkinCollect[[j,nKin]],1/Product[Subscript[l, subL[[i,k]]],{k,1,1+dim}]]//Simplify;If[Simplify[coeff]===0, None ,
(
Lindex[[nKin,j]]=Append[Lindex[[nKin,j]],i];
Lcoeff[[nKin,j]]=Append[Lcoeff[[nKin,j]],coeff];
)
]
,{i,1,Length[subL]},{j,1,nu},{nKin,1,nkin}];
Return[{Lindex,Lcoeff}]
)

Cin[VertexP_List,nume_]:=(
nume0=Sum[Subscript[c, VertexP[[i]]] Lplanes[[VertexP[[i]]]],{i,1,dim+1}]-nume//Simplify;sol0=Solve[Append[Table[Coefficient[nume0,z[i]]==0,{i,1,dim+1}],(nume0/.Table[z[i]->0,{i,1,dim}])==0],Table[Subscript[c,VertexP[[i]]],{i,1,dim+1}]]//Quiet;
Return[First@sol0]);

DKinComp[nKin_,DKinCollect_List,sol_List]:=(
Lindex=DKinCollect[[1]];
Lcoeff=DKinCollect[[2]];
subL=Subsets[Range[nplane],{dim+1}];
cin=Table[Cin[subL[[Lindex[[nKin,i,j]]]],Lcoeff[[nKin,i,j]]],{i,1,nu},{j,1,Length[Lindex[[nKin,i,All]]]}];
DkinComp=Table[
Sum[vertexListT=subL[[Lindex[[nKin,i,j]]]];
Sum[vertexList=vertexListT[[Complement[Range[1+dim],{n}]]];
(
(Subscript[c, vertexListT[[n]]]/.cin[[i,j]]//Simplify)*(vertexList//t)
)
,{n,1,1+dim}]
,{j,1,Length[Lindex[[nKin,i,All]]]}]
,{i,1,nu}];

DkinComp=DkinComp/.Table[Subscript[c, i]->0,{i,1,nplane}];
rule:=\[LeftAngleBracket]a__\[RightAngleBracket]:>(1/Det[jacT[[{a},nkin+1;;nkin+dim]]])\[LeftAngleBracket]a\[RightAngleBracket];
DkinComp=DkinComp/.rule;
DkinComp=DkinComp/.sol//Simplify//Apart;
Return[DkinComp]
)


APRT=expr_:>(Module[{terms},terms=If[Head[expr]===Plus,List@@expr,{expr}];terms=Apart/@terms;Total[terms]  (*Sum the processed terms*)]);


AMatrix[]:=(
sol=Sol[];
bdyBasis=BdyBasis[];
basis=bdyBasis[[2]]//Flatten;
nu=Length[basis];
dKinCollect=DKinCollect[basis];
Amatrix=Table[
dKinComp=DKinComp[nKin=i,dKinCollect,sol];
Table[Coefficient[dKinComp[[i]],basis[[j]]]//Apart/.APRT,{i,1,nu},{j,1,nu}](*//Apart*)
,{i,1,nkin}];
Return[Amatrix]
)


(*Total derivative A-matrix*)
toPositive=x_:>-x/;(First[x]//Length)==2;
toLogForm[expr_,i_]:=Module[
{terms},terms=If[Head[expr]===Plus,List@@expr,{expr}];(*Check if the input is a sum or a single term*)
terms//Simplify;
Table[Numerator[term]*Log[Denominator[term]/.toPositive]/Coefficient[Denominator[term],kin[[i]]]/. {ComplexInfinity->0,Indeterminate->0}//Quiet,{term,terms}](*Process each term individually and return the results as a list*)
]
ATotal[A_List,twists_List:Union[powers]]:=Sum[twist*Map[Total[Union[Flatten[#//MapIndexed[toLogForm[#,First[#2]]&]]]]&,MapThread[List,Coefficient[A,twist],2],{2} ],{twist,twists}]//Quiet;


(*ATotal[A_List, twists_:Automatic] := Module[{tw},
  tw = If[twists === Automatic, Union[powers], twists];
  Sum[twist*Map[Total[Union[Flatten[#//MapIndexed[toLogForm[#,First[#2]]&]]]]&,MapThread[List,Coefficient[A,twist],2],{2} ],{twist,twists}]//Quiet
]*)


End[];


EndPackage[];
