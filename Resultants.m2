--######################################################################
-- PROGRAMMER : Nicolás Botbol, Laurent Busé, Manuel Dubinsky
-- UPDATE HISTORY : 3 March 2011 -> 16 June 2011 -> 7 July 2011 -> 6 September 2011 -> 17 October 2011 -> 24 October 2011 -> 2 November 2011 -> 12 January 2012.
---------------------------------------------------------------------------
newPackage("Resultants",
   Version => "1.4",
   Date => "12 January 2012",
   Authors => {
         {Name => "Nicolás Botbol", Email => "nbotbol@dm.uba.ar", HomePage => "http://mate.dm.uba.ar/~nbotbol/"},
	     {Name => "Laurent Busé", Email => "Laurent.Buse@inria.fr", HomePage => "http://www-sop.inria.fr/members/Laurent.Buse/"},
	     {Name => "Manuel Dubinsky"}
	     },
   Headline => "Package for computing resultants",
   DebuggingMode => true
   )

export {
--    matrixToListByColumns,
--    matrixToListByRows,
    rankNum,
    maxCol,
    maxColNum,
    maxMinor,
    maxMinorNum,
-- MAIN FUNCTIONS
	degHomPolMap,
	listDetComplex,
	listDetComplexNum,
	detComplex,
	detComplexNum,
	mapsComplex,
	minorsComplex,
	minorsComplexNum,
	degMap,
	macRes,
	macaulayFormula,
	bezoutianMatrix,
	ciRes,
	ciResDeg,
	ciResDegGH,
	cm2Res,
	detRes,
	detResDeg
}

--######################################################################
--## Basic functions ###################################################
--######################################################################

-- Functions that end with 'num' (rankNum, maxColNum, maxMinorNum, listDetComplexNum, minorsComplexNum and detComplexNum) are numerical functions, meaning that it does the same computation than the non-num function but after a random evaluation.
-- It is perhaps recommendable to run them at least twice.

---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- PURPOSE : Methods that converts a matrices into lists and vice-versa (by rows and columns)

matrixToListByColumns = method();

--   INPUT : 'm' a matrix
--  OUTPUT : 'l' a list which has the elements of 'm' listed from the up-left corner to the down-right corner
matrixToListByColumns(Matrix) := (m) -> (
	l := {};
	for i from 0 to (rank source m) - 1 do (
		col := {};
		for j from 0 to (rank target m) - 1 do (
			col = col | {m_i_j};
		);
		l = l | {col};
	);
	return l;
)

matrixToListByRows = method();

matrixToListByRows(Matrix) := (m) -> (
	return matrixToListByColumns transpose m;
)


---------------------------------------------------------------
---------------------------------------------------------------
-- PURPOSE : returns the degree of a 'RingElement' in the variables 'var'

pdeg = method ();

pdeg(RingElement, List) := (f, var) -> (
	return max((degrees (coefficients(f,Variables=>var))_0)_1)_0;
);

--   INPUT : m is a line matrix |f1,..,fn| of polynomials
--  OUTPUT : var is a list of variables of the ring of f
pdeg(Matrix, List) := (m,var) -> (
     return apply((matrixToListByRows m)_0,i -> if i == 0 then 0 else pdeg(i, var))
);

---------------------------------------------------------------
---------------------------------------------------------------
-- PURPOSE : returns the coefficients of the RingElement/Matrix of RingElements in the monomials 'base'. It is a shortcut to the built-in function 'coefficients'

coeffs = method ();

coeffs(RingElement, List, List) := (f,var,base) -> (
	return coefficients(f, Variables=>var, Monomials=>base);
);

coeffs(Matrix, List, List) := (m,var,base) -> (
	return coefficients(m, Variables=>var, Monomials=>base);
);

coeffs(Matrix, List, Matrix) := (m,var,base) -> (
	return coefficients(m, Variables=>var, Monomials=>base);
);

---------------------------------------------------------------
---------------------------------------------------------------
-- PURPOSE : This function calculates the sourceShifts of the morphism R(d1)+...+R(dn)->R(e1)+...+R(ek) based on the target shifts

sourceShifts = method ();

sourceShifts(Matrix,List,List) := (m, targetShifts, var) -> (	
	nonZero := apply(matrixToListByColumns(m), i -> position(i, j -> j != 0));
	sourceShiftsList := {};
	for i from 0 to (length nonZero)-1 do (
		sourceShiftsList = sourceShiftsList | { pdeg(m_(nonZero_i,i),var) + targetShifts_(nonZero_i) };
	);

	return sourceShiftsList;
);

---------------------------------------------------------------
---------------------------------------------------------------
-- PURPOSE : it returns the complement of 2 lists

listComplement = method ();
listComplement(List, List) := (l1, l2) -> (
	return (sort toList(set l1 - set l2))
);

---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- PURPOSE : it returns the rank of a matrix obtained after specialization 
-- of the variables. With high probability, this is the rank of the input matrix.

rankNum = method();
rankNum(Matrix) := (M) -> (
     Aring:=ring M;
     l:={};
     i:=0;
     
     while i<numgens(Aring) do (l=l|{random({0},Aring)}; i=i+1;);
     
     s:=map(Aring,Aring,l);
     N:=s(M); 
     rm:=rank(N);
     return(rm)
 );    


---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- PURPOSE : Auxiliary method that takes from a given m x n - Matrix of rank r, a new full rank m x r - Matrix
-- It returns a list of which has in the first position a maximal matrix of linearly independent columns of M and in the
-- second the indices of those columns
--   INPUT : 'M' an m x n - Matrix of rank r
--  OUTPUT : 'N' an m x r - Matrix of rank r

maxCol = method();
maxCol(Matrix) := (M) -> (
        rm:=rank(M);
        i:=0;
        c:={};
        
        while #c<rm do (
                if rank M_(c|{i}) == #(c|{i}) then c=c|{i};
                i=i+1;
        );
        
        return {M_c,c}
);

-- alternative with a specialization of the variables -- to gain in time computation

maxColNum = method();
maxColNum(Matrix) := (M) -> (
     Aring:=ring M;
     l:={};
     i:=0;
     
     while i<numgens(Aring) do (l=l|{random({0},Aring)}; i=i+1;);
     
     s:=map(Aring,Aring,l);
     N:=s(M); 
     rm:=rank(N);
     i=0;
     d:=1;
     c:={};
     while #c<rm do ( if rank N_(c|{i}) == #(c|{i}) then c=c|{i};
                      i=i+1;); 
     return(M_c,c)
);
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- PURPOSE : Method that takes from a given m x n - Matrix of rank r, a new r x r full rank Matrix"
--   INPUT : 'M' an m x n - Matrix of rank r
--  OUTPUT : 'N' an r x r - Matrix of rank r

maxMinor = method();
maxMinor (Matrix) := (M) -> (
        --Apply two times maxCol to obtain a maximal minor
        --This is not very efficient...      
        return (transpose (maxCol(transpose (maxCol(M))_0 ))_0 )
);

-- alternative with a specialization of the variables -- to gain in time computation

maxMinorNum = method();
maxMinorNum (Matrix) := (M) -> (
        return (transpose (maxCol(transpose (maxCol(M))_0 ))_0 )
);

---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- PURPOSE : Method that takes a list of variables in a polynomial ring R and returns the corresponding list of integer for vars(R)
varpos = method();
--   INPUT : a list of variables
--  OUTPUT : a list of integers

varpos(List) := (l) -> (
     --l is a list (non empty) of variables of the same ring.
     --It returns the corresponding list of number of these var.
     i:=0;ln:={};lvar:={};mvars:=vars(ring l#0);
     for i from 0 to (rank source mvars)-1 do lvar=lvar|{mvars_(0,i)}; 
     for i from 0 to #l-1 do ln=ln|{position(lvar, j -> j == l#i)};
     return(ln)
);

--######################################################################
--######################################################################
--## Main functions ####################################################
--######################################################################
--######################################################################

---------------------------------------------------------------
---------------------------------------------------------------
-- PURPOSE : Let R be a polynomial ring in two groups of variables R=S[X1,...,Xr] and S=k[a1,...,as]. Here, X1,...,Xr ar called 'var' and a1,...,as are called 'coefficients'. Let m be a line matrix [f1,...,fn], where fi is an element of R which is homogeneous as a polynomial in the variables 'var', of degree di for all i in 'var'. The matrix 'm' defines a graded map of R-modules (of degree 0 in 'var') from R(-d1)+...+R(-dn) to R. In particular, looking on each strand d, we have a map of free S-modules of finite rank f_d: R_{d-d1}+...+R_{d-dn} -> R_d, where R_d is the homogeneous part of degree d in 'var' of R.
--This function returns a sequence with two elements: first the list of monomials of degree d in 'var'; Second, the matrix f_d with entries in S in the base of monomials.
--For computing the base of monomials, it needs as a second argument the list (d1,...,dn) of the degrees of the fi's in 'var'. There is an auxiliary function computing this automatically from the list of elements fi's and the list of variables 'var' called 'sourceShifts'.
-- INPUT: (m, sourceShifts, var, d): 'm' a row matrix of homogeneous polynomials in the variables 'var',  a list 'sourceShifts' of integers representing the degrees of 'm', a list 'var' with ring variables to be eliminated, a positive integer number 'd' which represents the strand of the map.
-- OUTPUT: a sequence with two elements: the list of monomials of degree d in 'var' and, the matrix f_d with entries in S in the base of monomials. (Same arity as 'coeffs')

degHomPolMap = method ();

degHomPolMap(Matrix,List,List,ZZ) := (m, sourceShifts, var,d) -> (
	i := position((matrixToListByRows m)_0, i -> i != 0);
	targetShift := sourceShifts_i - pdeg(m_(0,i), var);

	mat := matrix{{}};
	for i from 0 to (rank source m)-1 do (
		mat = mat | (m_i_0 * gens((ideal var)^(d-sourceShifts#i)));
	);

	return coeffs(mat, var, gens((ideal var)^(d-targetShift)));
);

-- default method with no source shifts...
degHomPolMap(Matrix,List,ZZ) := (m, var,d) -> (
	degHomPolMap(m, apply((matrixToListByRows m)_0, i -> ((degrees(monomials(i, Variables=>var)))_1)_0_0), var, d)
);

---------------------------------------------------------------
---------------------------------------------------------------
-- PURPOSE : this functions must be thought in the context of Elimination Theory as an intermediate step in processing the morphisms of a chain complex. Given a morphism of a chain complex of free modules f: R^n->R^m (R a polynomial ring), one may be interested in computing the strand of the complex of a certain degree 'd' in a subset ('var') of the variables of R. The new expression of the morphism has two parts: a set of monomials in the variables 'var' and a set of coefficients. This function returns the matrix of coefficients of the morphism in the variables 'var'. (see degHomPolMap)
-- INPUT: (m, targetShifts, var, d): 'm' a row matrix of polynomials representing an element of the free module R^n (the source of the morphism), 'targetShifts' is a list integers (d1,...,dm) corresponding to the shifts of the summands in the target in the case R^m is written as R(-d1)+...+R(-dm), 'var' is the list of variables of the polynomial ring R to take into account to 'eliminate or hide', for constructing the base, 'd' the degree of the strand of the complex or map.
-- OUTPUT: the matrix representing the morphism f.

degMap = method ();
degMap(Matrix,List,List,ZZ) := (m, targetShifts, var, d) -> (
	M := matrix{{}};
	rows := rank target m;
	sourceShiftsList := sourceShifts(m,targetShifts,var);
	for i from 0 to rows - 1 do (
		row := transpose(matrix((transpose m)_i));
		MM:=degHomPolMap(row,sourceShiftsList,var,d);
		if M == 0 then (
			M = MM_1;
		) else (
			M = transpose(transpose(M) | transpose(MM_1));
		);		
	);
	return M
);

---------------------------------------------------------------
---------------------------------------------------------------

--#######################################################################
--## Determinant of a complex ###########################################
--#######################################################################

-- PURPOSE : this function calculates the morphisms of a ChainComplex with respect to a subset of the variables of the polynomial ring.
-- INPUT: (complex, var, d): 'complex' is a ChainComplex, 'var' is the list of ring variables to take into account in the morphism, 'd' integer corresponding to the degree of the strand of the chain complex.
-- OUTPUT: a list of matrices representing the morphisms of the chain complex


mapsComplex = method ();
mapsComplex(ChainComplex, List, ZZ) := (complex, var, d) -> (
	targetShifts := {0,0,0};
	mapList := {};
	columnList := {};
	complList := {};
	for i from 1 to length complex do (
		m := degMap(complex.dd_i, targetShifts, var, d);
		mapList = mapList | {m};
		targetShifts = sourceShifts(complex.dd_i,targetShifts,var);
	);
	return mapList
);

-- PURPOSE : this function calculates the sub-morphisms of a ChainComplex with respect to a subset of the variables of the polynomial ring.
-- INPUT: (complex, var, d): 'complex' is a ChainComplex, 'var' is the list of ring variables to take into account in the morphism, 'd' integer corresponding to the degree of the strand of the chain complex.
-- OUTPUT: a list of matrices representing a restriction and correstriction of the morphisms of the chain complex (the choice of the rows and columns is done according to the computation of a determinant of a complex).

minorsComplex = method ();
minorsComplex(ChainComplex, List, ZZ) := (complex, var, d) -> (
	minList := {};
	columnList := {};
	complList := {};
	mapComp := mapsComplex (complex, var, d);
	for i from 0 to (length mapComp) -1 do (
		m := mapComp_i;
		complList = listComplement(toList(0..(rank target m) - 1),  columnList);
		m = (transpose(m))_complList;
		m = transpose(m);
		columnList = (maxCol m)_1;
		minList = minList | {(m_columnList)};
	);
	return minList
);

-- PURPOSE : same as 'minorsComplex' but using numerical rank computation.

minorsComplexNum = method ();
minorsComplexNum(ChainComplex, List, ZZ) := (complex, var, d) -> (
	minList := {};
	columnList := {};
	complList := {};
	mapComp := mapsComplex (complex, var, d);
	for i from 0 to (length mapComp) -1 do (
		m := mapComp_i;
		complList = listComplement(toList(0..(rank target m) - 1),  columnList);
		m = (transpose(m))_complList;
		m = transpose(m);
		columnList = (maxColNum m)_1;
		minList = minList | {(m_columnList)};
	);
	return minList
);

-- PURPOSE : this function calculates the determinants of the submatrices of a ChainComplex with respect to a subset of the variables of the polynomial ring.
-- INPUT: (complex, var, d): 'complex' is a ChainComplex, 'var' is the list of ring variables to take into account in the morphism, 'd' integer corresponding to the degree of the strand of the chain complex.
-- OUTPUT: a list of polynomials corresponding to the determinants of the maps given by 'minorsComplex'.

listDetComplex = method ();
listDetComplex(ChainComplex, List, ZZ) := (complex, var, d) -> (
	targetShifts := {0,0,0};
	detList := {};
	columnList := {};
	complList := {};
	for i from 1 to length complex do (
		m := degMap(complex.dd_i, targetShifts, var, d);
		complList = listComplement(toList(0..(rank target m) - 1),  columnList);
		m = (transpose(m))_complList;
		m = transpose(m);
		columnList = (maxCol m)_1;
		detList = detList | {determinant(m_columnList)};
		targetShifts = sourceShifts(complex.dd_i,targetShifts,var);
	);
	return detList
);

-- PURPOSE : same as 'listDetComplex' but using numerical rank computation.

listDetComplexNum = method ();
listDetComplexNum(ChainComplex, List, ZZ) := (complex, var, d) -> (
	targetShifts := {0,0,0};
	detList := {};
	columnList := {};
	complList := {};
	for i from 1 to length complex do (
		m := degMap(complex.dd_i, targetShifts, var, d);
		complList = listComplement(toList(0..(rank target m) - 1),  columnList);
		m = (transpose(m))_complList;
		m = transpose(m);
		columnList = (maxColNum m)_1;
		detList = detList | {determinant(m_columnList)};
		targetShifts = sourceShifts(complex.dd_i,targetShifts,var);
	);
	return detList
);

-- PURPOSE : this function calculates the determinant of a ChainComplex with respect to a subset of the variables of the polynomial ring.
-- INPUT: (complex, var, d): 'complex' is a ChainComplex, 'var' is the list of ring variables to take into account in the morphism, 'd' integer corresponding to the degree of the strand of the chain complex.
-- OUTPUT: a polynomial corresponding to the determinant of the given complex. This is obtained by taking alternate product of the elements in the list 'listDetComplex'.

detComplex = method ();
detComplex(ChainComplex, List, ZZ) := (complex, var, d) -> (
	listDetCmp := listDetComplex(complex, var, d);
	detC := 1_(ring var_0);
	for i from 0 to length(listDetCmp)-1 do (
		if even(i) then (detC = detC* (listDetCmp_i)) else (
		detC = detC / (listDetCmp_i);
		);
	);
	return detC;
);

-- PURPOSE : same as 'detComplex' but using numerical rank computation.

detComplexNum = method ();
detComplexNum(ChainComplex, List, ZZ) := (complex, var, d) -> (
	listDetCmp := listDetComplexNum(complex, var, d);
	detC := 1_(ring var_0);
	for i from 0 to length(listDetCmp)-1 do (
		if even(i) then (detC = detC* (listDetCmp_i)) else (
		detC = detC / (listDetCmp_i);
		);
	);
	return detC;
);
---------------------------------------------------------------
---------------------------------------------------------------

--#######################################################################
--## Macaulay resultant #################################################
--#######################################################################

-- PURPOSE : this function calculates the Macaulay resultants 
-- INPUT: (p,var): 'p' is a one line matrix of homogeneous polynomial in variables 'var'
-- OUTPUT: It returns a list. The first argument is the matrix of the first Koszul map in degree the well-known critical degree. The second and third are basis of source and target (see degHomPolMap)

macRes = method ();

macRes(Matrix,List) := (p,var) -> (  
  return((degHomPolMap(p,var,sum(pdeg(p,var))-#var+1))_1)
  --remove the _1 at the end of the line above if the monomial basis indexing the rows are wanted	
);

---------------------------------------------------------------
---------------------------------------------------------------

--#######################################################################
--## Macaulay Formula ###################################################
--#######################################################################

-- PURPOSE : this function calculates the Macaulay formula 
-- INPUT: (p,var): 'p' is a one line matrix of homogeneous polynomial in variables 'var'
-- OUTPUT: It returns a list of two matrices such that the ratio of these two matrices is equal, if it is defined, to the Macaulay resultant of p w.r.t. the variables var.

macaulayFormula = method ();

macaulayFormula(Matrix,List) := (p,var) -> (  
     ld:=pdeg(p,var); 
     nu:=sum(ld)-#var+1;
     listmon:=gens((ideal var)^nu);
     sizelistmon:=numgens source listmon;
     f:=matrix{{}};
     dodu:={};
     for i to (sizelistmon-1) do (
     	  m:=listmon_(0,i);
     	  indexm:={};
     	  for j to #var-1 do (
	       if pdeg(m,{var_j})>=ld_j then indexm=append(indexm,j);
	       if #indexm>=2 then (dodu=append(dodu,i);  break;);
	  );
     ind:=indexm_0;
     f=f | matrix{{sub( m/(var_ind)^(ld_ind)*p_(0,ind),ring(p))}};
     );
     (M,C):=coefficients(f,Variables=>var,Monomials=>listmon);
     D:=submatrix(C,dodu,dodu);
     return((C,D));       
);

---------------------------------------------------------------
---------------------------------------------------------------

--#######################################################################
--## Bezoutian Matrix ###################################################
--#######################################################################

-- PURPOSE : this function calculates the bezoutian matrix associated to a system of n+1 (affine) polynomials in n variables  
-- INPUT: (p,var): 'p' is a one line matrix of (affine) polynomials in the n variables 'var'
-- OUTPUT: It returns the bezoutian matrix.

bezoutianMatrix = method ();

bezoutianMatrix(Matrix,List) := (p,var) -> (  
     --p is a matrix of m (affine) polynomials in R
     --It returns the Bezoutian matrix w.r.t. var
     R:=ring p;
     n:=#var;
     np:=varpos(var);--position of the n var in the list vars(R)
     m:=rank source p; --need m-1 == n
     tt:=getSymbol "tt"; 
     zz:=getSymbol "zz";
     Rb:=R(monoid[tt_1 ..  tt_n,  zz_1 ..  zz_n]); --ring for Bezoutian
     i:=0;  k:=0;
     --first column:
     lv:=gens R; nlv:=#lv; --list of generators of R
     for i from 0 to n-1 do lv=lv_{0..np#(i)-1}|{Rb_i}|lv_{np#(i)+1..nlv-1};
     rb0:=map(Rb,R,lv);--Send var on tt_
     rbp:=rb0 p;--p in Rb
     --rb1:=map(Rb,R); --initialization of rb1
     Theta:=transpose rbp; l:={};
     --second columns:
     pp1:=rbp; --introduced for late use
     pp2:=substitute(pp1,{Rb_0 => Rb_n}); -- tt_1=>zz_1
     Theta=Theta | transpose matrix { for k from 0 to m-1 list
          (pp1_(0,k) - pp2_(0,k))//(Rb_0 - Rb_n) };
     --the other columns:
     for i from 2 to n do ( 
          pp1=pp2;
	  pp2=substitute(pp2,{Rb_(i-1) => Rb_(n+i-1)}); -- tt_i => zz_i
          Theta=Theta | transpose matrix { for k from 0 to m-1 list
                (pp1_(0,k) - pp2_(0,k)) // (Rb_(i-1) - Rb_(n+i-1)) };
     );
     --The Bezoutian of p is the determinant of Theta:
     bez:=det Theta; 
     --Construction of the Bezoutian matrix:
     lvar:=gens Rb;
     ttvar:=lvar_{0..(n-1)};
     zzvar:=lvar_{n..(2*n-1)};
     zzmon:=(coefficients(bez,Variables=>zzvar))#0; --target basis
     mct:=(coefficients(bez,Variables=>ttvar))#1; -- idem#0 = source basis
     mbez:=(coefficients(mct_(0,0),Variables=>zzvar,Monomials=>zzmon))#1;
     for i from 1 to rank target mct - 1 do
     	  mbez=mbez|(coefficients(mct_(i,0),Variables=>zzvar,Monomials=>zzmon))#1;
     return(substitute(mbez,R))
);

---------------------------------------------------------------
---------------------------------------------------------------

--#######################################################################
--## Residual resultant of a complete intersection ######################
--#######################################################################

-- PURPOSE : this function calculates the residual resultant over a complete intersection 
-- INPUT: (g,H,var): 'g' is a one line matrix of homogeneous polynomial in variables 'var' 
-- forming a complete intersection. H is a matrix such that F=gH and F is the system of 
-- polynomials for which the residual resultant is computed
-- OUTPUT: It returns a matrix.

ciRes= (g, H, var) -> (
  --g is a one line matrix in R
  --H is a matrix in R
  --it returns the residual resultants of g*H over g w.r.t to var
  ng:=rank source g; m:=rank source H; --we must have rank target M == ng
  dg:=pdeg(g,var);
  --dg:={}; i:=0; for i from 0 to ng-1 do (dg=dg|{(degree(g_(0,i)))_0});
  f:=g*H; --polynomials f1,..,fm
  df:=pdeg(f,var);
  --df:={}; for i from 0 to m-1 do (df=df|{pdeg(var,f_(0,i))_0});
  bm:=subsets(0..m-1,ng); nbm:=#bm; --base of minors
  for i from 0 to nbm-1 do (f=f|det(H_(bm_i)));--add minors to f
  return((degHomPolMap(f,var,(sum df) - m + 1 - (m - ng + 1)*(min dg)))_1)
);

-- PURPOSE: similar than ciRes but return the critical degree in which the resultant is computed

ciResDegGH= (g, H, var) -> (
  --g is a one line matrix in R
  --H is a matrix in R
  --it returns the critical degree of the residual resultant of g*H over g w.r.t to var
  ng:=rank source g; m:=rank source H; --we must have rank target M == ng
  dg:=pdeg(g,var);
  f:=g*H; --polynomials f1,..,fm
  df:=pdeg(f,var);
  return((sum df) - m + 1 - (m - ng + 1)*(min dg))
);

-- PURPOSE: compute the partial degrees of the residual resultant over a complete intersection
-- INPUT: two lists of integers: the first one is the list of degrees of the polynomials for 
-- which one wants to compute the residual resultant, the second one is the list of degrees 
-- of the complete intersection associated to this residual resultant.
-- OUTPUT: the list of partial degrees

ciResDeg = (ld,lk) -> (
  --ld is a list of integers {d_0..d_m}
  --lk is a list of integers {k_1..k_n}
  --It returns the regularity and the degrees of the CiRes associated to these degrees
  i:=0; nd:=#ld; nk:=#lk;
  s:=reverse subsets(0..nd-1,nd-1);
  {(sum ld) - nd + 1 - (nd - nk + 1)*(min lk),
    for i from 0 to nd-1 list cideg(ld_(s_i),lk)
    }
);

cideg = (ld,lk) -> (
  --ld and lk are lists of integer.
  --Calling with ld:=[d1,...,dm] and lk:=[k1,...,kn], it returns the degree
  --of CiRes in the coefficient of the polynomial f_0.
  m:=#ld; n:=#lk;i:=0;j:=0;u:={};v:={};w:={};
  if m >= 2*n+1 then (
       H:=for i from 0 to n list (
          u=for j from 0 to i list sympol(lk,i-j);
          v=for j from i+1 to m-n list 0;
         (u|v));
       H=H|for i from n+1 to m-n list (
          u=for j from 0 to i-n-1 list 0;
          v=u|for j from i-n to i list sympol(lk,i-j);
          w=v|for j from i+1 to m-n list 0))
  else (H=for i from 0 to m-n list (
          u=for j from 0 to i list sympol(lk,i-j);
          v=u|for j from i+1 to m-n list 0)
       );
  c:=for i from 1 to m-n list i;
  H=(matrix(H))^c;
  N:=sympol(ld,m);s:=subsets(0..m-n,m-n);
  if m==n then N=sympol(ld,m)-sympol(lk,n)
         else for i from 0 to m-n do
  N=N+sympol(ld,i)*(-1)^(m-n-i+1)*sympol(lk,n)*det(H_(s_i))*(-1)^(n*(m-n+ 1));
  return(N);
);

sympol = (l,n) -> (
  --l is a list of integer with #l>=n
  --n is an integer
  --it returns the symmetric polynomial (-1)^(n-l)sum l_i1..l_in
  (-1)^(#l-n)*sum(apply(subsets(l,n),product))
);  

--########################################################################
--## Residual resultant of a Cohen-Macaulay codim 2 ideal ################
--########################################################################

-- PURPOSE : this function calculates the residual resultant over a Cohen-Macaulay codim 2 base locus 
-- INPUT: (g,H,var): 'g' is a one line matrix of homogeneous polynomial in variables 'var' 
-- forming a CM codim 2 ideal. H is a matrix such that F=gH and F is the system of 
-- polynomials for which the residual resultant is computed
-- OUTPUT: It returns a matrix.

cm2Res= (g, H, var) -> (
  --g is a one line matrix in R
  --H is a matrix in R such that f=gH, 
  --It returns the residual resultants of f over g
  n:=rank source g; --rank source H=m, and we must have rank target M==n
  dg:=pdeg(g,var);
  f:=g*H; --the polynomials f1,..,fm
  df:=pdeg(f,var);
  S:= syz  g; --first syzygy of G with Hilbert-Burch theorem
  return((degHomPolMap(gens minors(n,S|H),var,(sum df) - 2*(min dg + 1)))_1)
);
 
--######################################################################
--## Determinantal resultant ###########################################
--######################################################################

-- PURPOSE : this function calculates the determinantal resultant a matrix
-- INPUT: (p,r,var): 'p' is a matrix of homogeneous polynomial in variables 'var'
-- and r is an integer 
-- OUTPUT: the determinantal resultant of p associated to the condition that 
-- the rank of p is lower or equal to r.

detRes=(p,r,var) -> (
   --p is a matrix of homogeneous polynomials in var
   --r is an integer
   m:=rank source p; n:=rank target p;
   dp:=pdeg(p^{n-1},var);--degrees of last row
   dc:=pdeg(transpose(p_{0}),var); --degree of first column
   dk:=sort(apply(dc, i->dp#0-i));
   return((degHomPolMap(gens(minors(r+1,p)),var,
   (n-r)*(sum dp - sum dk)-(m-n)*(sum dk_{0..n-r-1})-(m-r)*(n-r)+1)))_1
);

-- PURPOSE : this function calculates the critical degree and that partial degrees of 
-- the determinantal resultant
-- INPUT: 
-- dp and dk are list of integers corresponding to DetRes with r.
-- dp=d1,..,dm and dk=k1,..,kn
-- r is an integer
-- R is the ring where computations take place
-- OUTPUT: a list of integers containing the critical degree and then the partial degrees


detResDeg=(dp,dk,r,R) -> (

   m:=#dp;n:=#dk;
   h:=getSymbol "h";
   t:=getSymbol "t";
   nR:=R(monoid[h,t]); 
   sdp:=0_nR;sdk:=0_nR;
   for i from 1 to m do sdp=sdp+dp#(i-1)_nR;
   for i from 1 to n do sdk=sdk+dk#(i-1)_nR;
   subsdk:=0_nR;dk=sort(dk);
   for i from 1 to n-r do subsdk=subsdk+dk#(i-1)_nR;
   reg:=(n-r)*(sdp - sdk)-(m-n)*subsdk-(m-r)*(n-r)+1;
   vmax:=m+n-2*r-1;
   vmin:=m-n+1;
   F:={};i:=0;j:=0;
   for i from 1 to n do 
       F=F|{sum for j from 0 to vmax list ((nR_1)*(dk#(i-1)_nR))^j};
   F=product(F);
   degs:={};E:=0;S:=0;coefS:=0;nc:=0;mTP:=0;
   for j from 0 to m-1 do (
   	 E=(1-((dp#j)_nR+(nR_0))*(nR_1))*product(0..j-1,i->1-((dp#i)_nR)*(nR_1))*product(j+1..m-1,i->1-((dp#i)_nR)*(nR_1)); 
    	S=coefficients(matrix{{E*F}},Variables=>{nR_1});--coeff en t
		coefS=transpose(S#1);nc=rank source coefS;--decreasing --All monomials in t appears 1,t,t^2,....
		mTP=coefS_{(nc-1-m+r)..(nc-1-m+n-1)};
		for i from 1 to n-r-1 do (
	    	mTP=mTP||coefS_{(nc-1-m+r-i)..(nc-1-m+n-1-i)};
		);
		degs=degs|{substitute(((coefficients(det(mTP),Variables=>{nR_0},Monomials=>{matrix{{nR_0}}}))_1)_(0,0),R)};
   );
   return({substitute(reg,R),degs})
);

---------------------------------------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
--------------------- DOCUMENTATION ---------------------------
---------------------------------------------------------------
beginDocumentation()
---------------------------------------------------------------
---------------------------------------------------------------
-- Simple Doc information
---------------------------------------------------------------
---------------------------------------------------------------
document {
	Key => {Resultants},
	Headline => "A package for computing resultants.",
	
	TT "Resultants", " is a package for elimination theory, emphasizing universal formulas, in particular, resultant computations.",
	
	PARA {}, "The package contains an implementation for computing determinant of free graded complexes, called ", TO2((detComplex), "detComplex"), ", with several derived methods:  ", TO2((listDetComplex), "listDetComplex"),", ", TO2((mapsComplex), "mapsComplex"),", and  ", TO2((minorsComplex), "minorsComplex"), ". This provides a method for producing universal formulas for any family of schemes, just by combining the ", TO2 {(resolution,Ideal),"resolution(Ideal)"}, " method with  ", TO2((detComplex), "detComplex"), ". In Section 2 determinants of free resolutions are treated, as well as a few examples. We recommend to see [Dem84, Jou95, GKZ94, Bus06] for more details on determinants of complexes in elimination theory.",

	PARA {}, "The package also provides methods for computing matrices and formulas for different resultants applicable on different families of polynomials, such as the Macaulay resultant (", TO2((macRes), "macRes"),") for generic homogeneous polynomials; residual resultant (", TO2((ciRes), "ciRes"),", ", TO2((cm2Res), "cm2Res"),") for generic polynomials having a non empty base locus scheme; determinantal resultant (", TO2((detRes), "detRes"),") for generic polynomial matrices of a given generic rank. Those resultants and their implementation are reviewed in Section 3 and for the theory behind the author can refer to [Jou91, Cha93, GKZ94, Jou95, Jou97, CLO98, BEM01, Bus01b, Bus06, Bus04].",

	PARA {}, "The goal of this package is to provide universal formulas for elimination. The main advantage of this approach consists in the fact that we can provide formulas for any family of polynomials just by taking determinant to a free resolution. A direct consequence of a universal formula is that it is preserved by base change, this is, in particular, it commutes with specialization. A deep study of universal formulas for the image of a map of schemes can be seen in [EH00].",

	PARA {}, BOLD "Bibliography:", 

	PARA {}, "[BBD12] ", ITALIC "Nicolás Botbol, Laurent Busé and Manuel Dubinsky. ", HREF("http://mate.dm.uba.ar/~nbotbol/pdfs/JSAG-elimination.pdf", " PDF"), ". Package for elimination theory in Macaulay2 (2012).",

    PARA {}, "[BEM00] ", ITALIC "Laurent Busé, Mohamed Elkadi and Bernard Mourrain",", Generalized resultants over unirational algebraic varieties, J. Symbolic Comput. 29 (2000), no. 4-5, 515–526.", 

    PARA {}, "[BEM01] ", ITALIC "Laurent Busé, Mohamed Elkadi and Bernard Mourrain",", Resultant over the residual of a complete intersection, Journal of Pure and Applied Algebra 164 (2001), no. 1-2, 35–57.",

    PARA {}, "[Bus01a] ", ITALIC "Laurent Busé",", Residual resultant over the projective plane and the implicitization problem, Internation Symposium on Symbolic and Algebraic Computing (ISSAC), ACM, (2001). Please, see the errata.pdf attached file., pp. 48–55.", 

    PARA {}, "[Bus01b] ", ITALIC "Laurent Busé",", Étude du resultant sur une variété algébrique. phd thesis. (2001) ", 

    PARA {}, "[Bus04] ", ITALIC "Laurent Busé",", Resultants of determinantal varieties, J.Pure Appl. Algebra193 (2004), no.1-3, 71–97.", 

    PARA {}, "[Bus06] ", ITALIC "Laurent Busé",", Elimination theory in codimension one and applications, (2006).", 

    PARA {}, "[Cha93] ", ITALIC "Marc Chardin",", The resultant via a Koszul complex, Computational algebraic geometry (1992), Progr. Math, vol. 109, Birkhäuser Boston, Boston, MA, pp. 29–39. ", 

    PARA {}, "[CLO98] ", ITALIC "David Cox, John Little and Donal O’Shea",", Using algebraic geometry, Graduate Texts in Mathematics, vol. 185, Springer-Verlag, New York, (1998).", 

    PARA {}, "[Dem94] ", ITALIC "Michel Demazure",", Une définition constructive du resultant, Centre de Mathématiques de l’Ecole Polytechnique 2 (1984), no. Notes informelles du calcul formel 1984-1994, 0–23. ", 

    PARA {}, "[EH00] ", ITALIC "David Eisenbud and Joe Harris",", The geometry of schemes., Graduate Texts in Mathematics. 197. New York, NY: Springer. x, 294 p., (2000). ", 

    PARA {}, "[Eis95] ", ITALIC "David Eisenbud",", Commutative algebra, With a view toward algebraic geometry. Graduate Texts in Mathematics, vol. 150, Springer-Verlag, New York, (1995).",
    
    PARA {}, "[GKZ94] ", ITALIC "Israel M. Gel′fand, Mikhail M. Kapranov and Andrei V. Zelevinsky",", Discriminants, resultants, and multidimensional determinants, (1994). Mathematics: Theory & Applications, Birkh ̈auser Boston Inc, Boston, MA. ", 

    PARA {}, "[Jou91] ", ITALIC "Jean-Pierre Jouanolou",", Le formalisme du résultant, Adv. Math 90 (1991), no. 2, 117–263.", 

    PARA {}, "[Jou95] ", ITALIC "Jean-Pierre Jouanolou",", Aspects invariants de l’élimination, vol. 114, 1995, pp. 1–174. ", 

    PARA {}, "[Jou97] ", ITALIC "Jean-Pierre Jouanolou",", Formes d’inertie et résultant: un formulaire, Adv. Math. 126 (1997), no. 2, 119–250.", 

    PARA {}, "[Mac02] ", ITALIC "Francis S. Macaulay",", Some formulae in elimination, Proc. London Math. Soc. 33 (1902), no. 1, 3–27.", 
    
    PARA {}, "[Mou02] ", ITALIC "Bernard Mourrain",", Enumeration problems in Geometry, Robotics and Vision, Prog. in Math. 143 (1996), 285–306.",
}

------------------------ \ degHomPolMap / ------------------------
document {
     	Key => {degHomPolMap},
	Headline => "given a subset of variables 'var' of the polynomial ring R, it returns the base of monomials on these variables, and the matrix of coefficients of a morphism of free modules f:R(d1)+...+R(dn)->R_d with respect to these variables",
	Usage => " coefAndMonomials = degHomPolMap(aSingleRowMatrix, sourceShiftList, varList, targetDegree)",

	Inputs => {
		"aSingleRowMatrix" => Matrix => {"single row matrix with polynomials {f1,...,fn}"},
		"sourceShiftList" => List => {"list {d1,...,dn} of degrees corresponding to the degrees of {f1,...,fn}"},
		"varList" => List => {"list 'var' of variables of the polynomial ring R with respect to which the polynomials fi's are homogeneous of degree 'di' (to take into account for elimination)"},
		"targetDegree" => ZZ => {"the degree in 'var' of the homogeneous strand of the map f (i.e.: R_d)"}
	},
	Outputs => {
		"List" => List => {"a list {monomials, coefficients} of the coefficients and monomials of the morphism f (same arity of 'coeffs')"}
	},

	PARA {}, "Let R be a polynomial ring in two groups of variables R=S[X1,...,Xr] and S=k[a1,...,as]. Here, X1,...,Xr ar called 'var' and a1,...,as are called 'coefficients'. Let m be a line matrix [f1,...,fn], where fi is an element of R which is homogeneous as a polynomial in the variables 'var', of degree di for all i in 'var'. The matrix 'm' defines a graded map of R-modules (of degree 0 in 'var') from R(-d1)+...+R(-dn) to R. In particular, looking on each strand d, we have a map of free S-modules of finite rank f_d: R_{d-d1}+...+R_{d-dn} -> R_d, where R_d is the homogeneous part of degree d in 'var' of R.",

	PARA {}, "This function returns a sequence with two elements: first the list of monomials of degree d in 'var'; Second, the matrix f_d with intries in S in the base of monomials.",

	PARA {}, "For computing the base of monomials, it needs as a second argument the list (d1,...,dn) of the degrees of the fi's in 'var'. There is an auxiliar function computing this automatically from the list of elements fi's and the list of variables 'var' called 'sourceShifts'.",

	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = degHomPolMap (M,l,2)",
		" dHPM = degHomPolMap (M,{2,1},l,2)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = degHomPolMap (M,l,1)",
		" dHPM = degHomPolMap (M,{1,1,1},l,1)"
		},
     
	SeeAlso => {degMap, macRes, detComplex, listDetComplex, minorsComplex, mapsComplex, coeffs}
     
}

------------------------ \ degMap / ------------------------

document {
     	Key => {degMap},
	Headline => "This function returns the matrix of coefficients of the morphism of free modules 'm' in the variables 'var'",
	Usage => " morphimsMatrix = degMap(aPolynomialMatrix, targetShiftsList, varList, complexDegree)",

	Inputs => {
		"aPolynomialMatrix" => Matrix => {"a row matrix of polynomials representing an element of the free module R^n (the source of the morphism)"},
		"targetShiftsList" => List => {"is a list integers (d1,...,dm) corresponding to the shifts of the summands in the target in the case R^b is written as R(-d1)+...+R(-dm)"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account to 'eliminate or hide', for constructing the base"},
		"complexDegree" => ZZ => {"the degree of the strand of the complex or map"}
	},
	Outputs => {
		"aCoefficientsMatrix" => Matrix => {"the matrix of the coefficients of the morphism with respect to the variables 'var'"}
	},

	PARA {}, "This functions must be thought in the context of Elimination Theory as an intermediate step in processing the morphisms of a chain complex. Given a morphism of a chain complex of free modules f: R^n->R^m (R a polynomial ring), one may be interested in computing the strand of the complex of a certain degree 'd' in a subset ('var') of the variables of R. The new expression of the morphism has two parts: a set of monomials in the variables 'var' and a set of coefficients. This function returns the matrix of coefficients of the morphism in the variables 'var'. (See 'degHomPolMap')",

	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = degMap (M,{2,1},l,2)",
		" dHPM = degMap (M,{2,1},l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = degMap (M,{1,1,1},l,1)",
		" dHPM = degMap (M,{1,1,1},l,2)"
		},
     
	SeeAlso => {degHomPolMap, macRes, detComplex, listDetComplex, minorsComplex, mapsComplex }
}

------------------------ \ mapsComplex / ------------------------

document {
     	Key => {mapsComplex},
	Headline => "This function calculates the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	Usage => " mapsOfTheComplex = mapsComplex(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"a list of matrices"}
	},

	PARA {}, "This function calculates the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",

	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = mapsComplex (koszul M,l,2)",
		" dHPM = mapsComplex (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = mapsComplex (koszul M,l,1)",
		" dHPM = mapsComplex (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, listDetComplex, minorsComplex, mapsComplex }
}

------------------------ \ minorsComplex / ------------------------

document {
     	Key => {minorsComplex},
	Headline => "This function calculates some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree. The choice of the minors is according to the construction of the determinant of a complex",
	Usage => " minorsOfTheComplex = minorsComplex(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"a list of square (full-rank) matrices"}
	},

	PARA {}, "This function calculates some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",
	
	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = minorsComplex (koszul M,l,2)",
		" dHPM = minorsComplex (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = minorsComplex (koszul M,l,1)",
		" dHPM = minorsComplex (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, listDetComplex, detComplex, mapsComplex }
}

------------------------ \ minorsComplexNum / ------------------------

document {
     	Key => {minorsComplexNum},
	Headline => "This function calculates some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	Usage => " minorsOfTheComplex = minorsComplexNum(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"a list of square (full-rank) matrices"}
	},

	PARA {}, "This function calculates some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	PARA {}, " The choice of the minors is according to the construction of the determinant of a complex.",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",
	PARA {},"This function uses the same algorithm to uses to 'listDetComplex' but uses  numerical rank computation instead of exact rank computation.",

	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = minorsComplexNum (koszul M,l,2)",
		" dHPM = minorsComplexNum (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = minorsComplexNum (koszul M,l,1)",
		" dHPM = minorsComplexNum (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, listDetComplex, detComplex, mapsComplex }
}


------------------------ \ listDetComplex / ------------------------

document {
     	Key => {listDetComplex},
	Headline => "This function calculates the list with the determinants of some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	Usage => "listOfTheDetOfTheComplex = listDetComplex(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"a list with the determinant polynomials of the maps computed by 'minorsComplex'"}
	},

	PARA {}, "This function calculates the list with the determinants of some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree. Precisely, this list corresponds to the list with the determinant polynomials of the maps computed by 'minorsComplex'.",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",
	
	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = listDetComplex (koszul M,l,2)",
		" dHPM = listDetComplex (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = detComplex (koszul M,l,1)",
		" dHPM = detComplex (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, detComplex, minorsComplex, mapsComplex }
}
------------------------ \ listDetComplexNum / ------------------------

document {
     	Key => {listDetComplexNum},
	Headline => "This function calculates the list with the determinants of some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	Usage => "listOfTheDetOfTheComplex = listDetComplexNum(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"a list with the determinant polynomials of the maps computed by 'minorsComplex'"}
	},

	PARA {}, "This function calculates the list with the determinants of some minors of the maps of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree. Precisely, this list corresponds to the list with the determinant polynomials of the maps computed by 'minorsComplex'.",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",
	PARA {}, "It uses the same algorithm to uses to 'listDetComplex' but uses  numerical rank computation instead of exact rank computation.",

	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = listDetComplexNum (koszul M,l,2)",
		" dHPM = listDetComplexNum (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = detComplexNum (koszul M,l,1)",
		" dHPM = detComplexNum (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, detComplex, minorsComplex, mapsComplex }
}

------------------------ \ detComplex / ------------------------

document {
     	Key => {detComplex},
	Headline => "This function calculates the determinant of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	Usage => " deteriminantComplex = detComplex(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"an element in frac(R) that is the alternate product of the elements in the list 'listDetComplex'"}
	},

	PARA {}, "This function calculates the determinant of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree. It corresponds to the alternate product of the elements in the list 'listDetComplex'",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",
	
	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = detComplex (koszul M,l,2)",
		" dHPM = detComplex (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = detComplex (koszul M,l,1)",
		" dHPM = detComplex (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, listDetComplex, minorsComplex, mapsComplex }
}


------------------------ \ detComplexNum / ------------------------

document {
     	Key => {detComplexNum},
	Headline => "This function calculates the determinant of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree.",
	Usage => " deteriminantComplex = detComplex(aChainComplex, varList, complexDegree)",

	Inputs => {
		"aChainComplex" => ChainComplex => {"a chain complex of free modules over a polynomial ring"},
		"varList" => List => {"list of variables of the polynomial ring R to take into account for elimination"},
		"complexDegree" => ZZ => {"integer corresponding to the degree of the strand of the chain complex."}
	},
	Outputs => {
		"aPolynomialList" => List => {"an element in frac(R) that is the alternate product of the elements in the list 'listDetComplex'"}
	},

	PARA {}, "This function calculates the determinant of a graded ChainComplex with respect to a subset of the variables of the polynomial ring in a fixed degree. It corresponds to the alternate product of the elements in the list 'listDetComplexNum'.",
	PARA {}, "The input ChainComplex needs to be an exact complex of free modules over a polynomial ring. The polynomial ring must contain the list 'varList' as variables.",
	PARA {}, "It is recommended not to defines rings as R=QQ[x,y][a,b,c] when the variables to eliminate are '{x,y}'. In this case, see 'flattenRing' for passing from R=QQ[x,y][a,b,c] to QQ[x,y,a,b,c].",
	PARA {}, "It uses the same algorithm to uses to 'listDetComplex' but uses  numerical rank computation instead of exact rank computation.",
	EXAMPLE {" R=QQ[a,b,c,x,y] ",
		" f1 = a*x^2+b*x*y+c*y^2 ",
		" f2 = 2*a*x+b*y ",
		" M = matrix{{f1,f2}} ",
		" l = {x,y} ",
		" dHPM = detComplexNum (koszul M,l,2)",
		" dHPM = detComplexNum (koszul M,l,3)"
		},
		
	EXAMPLE {" R=QQ[a,b,c,d,e,f,g,h,i,x,y,z] ",
		" f1 = a*x+b*y+c*z ",
		" f2 = d*x+e*y+f*z ",
		" f3 = g*x+h*y+i*z ",
		" M = matrix{{f1,f2,f3}} ",
		" l = {x,y,z} ",
		" dHPM = detComplexNum (koszul M,l,1)",
		" dHPM = detComplexNum (koszul M,l,2)"
		},
     
	SeeAlso => {degHomPolMap, listDetComplex, minorsComplex, mapsComplex }
}

------------------------ \ macRes / ------------------------
document {
     	Key => {macRes},
	Headline => "returns a matrix associated to the Macaulay resultant",
	Usage => " macRes(aSingleRowMatrix, varList)",

	Inputs => {
		"aSingleRowMatrix" => Matrix => {" a single row matrix with polynomials f1,...,fn"},
		"varList" => List => {" a list of n variables such that the polynomials f1,...,fn are homogeneous with respect to these variables"},
	},
	Outputs => {
		"Matrix" => Matrix => {"a generically surjective matrix such that the gcd of its maximal minors if the Macaulay resultant of f1,...,fn with respect to the variables 'varList'"}
	},

	PARA {}, "Let f1,...,fn be a polynomials two groups of variables X1,...,Xn and a1,...,as and such that f1,...,fn are homogeneous polynomials with respect to the variables X1,...,Xn. This function returns a matrix which is generically (in terms of the parameters a1,...,as) surjective such that the gcd of its maximal minors is the Macaulay resultant of f1,...,fn.",


	EXAMPLE {" R=QQ[a..i,x,y,z]",
	"f1 = a*x+b*y+c*z",
	"f2 = d*x+e*y+f*z",
	"f3 = g*x+h*y+i*z",
	"M = matrix{{f1,f2,f3}}",
	"l = {x,y,z}",
	"MR = macRes (M,l)"
		},		
     
	SeeAlso => {degMap, macaulayFormula, detComplex, listDetComplex, minorsComplex, mapsComplex }
     
}



------------------------ \ macaulayFormula / ------------------------
document {
     	Key => {macaulayFormula},
	Headline => "returns two matrices such that the ratio of their determinants is the Macaulay resultant",
	Usage => " macaulayFormula(aSingleRowMatrix, varList)",

	Inputs => {
		"aSingleRowMatrix" => Matrix => {"a single row matrix with polynomials f1,...,fn"},
		"varList" => List => {"a list of n variables such that the polynomials f1,...,fn are homogeneous with respect to these variables"},
	},
	Outputs => {
		"aList" => List => {"a list of two matrices such that the ratio of their determinants is the Macaulay resultant of f1,...,fn with respect to the variables 'varList'"}
	},

	PARA {}, "Let f1,...,fn be a polynomials two groups of variables X1,...,Xn and a1,...,as and such that f1,...,fn are homogeneous polynomials with respect to the variables X1,...,Xn. This function returns two matrices M1 and M2 such that det(D1)/det(D2) is the Macaulay resultant of f1,...,fn providing det(D2) is nonzero.",
	
	PARA {}, "Remark: if D2 is the empty matrix, its determinant has to be understood as 1 (and not zero, which is the case in Macaulay2 since the empty matrix is identified to the zero.",


	EXAMPLE {" R=QQ[a..i,x,y,z]",
	"f1 = a*x+b*y+c*z",
	"f2 = d*x+e*y+f*z",
	"f3 = g*x+h*y+i*z",
	"M = matrix{{f1,f2,f3}}",
	"l = {x,y,z}",
	"MR = macaulayFormula (M,l)"
		},
     
	SeeAlso => {degMap, macRes, detComplex, listDetComplex, minorsComplex, mapsComplex }
     
}


------------------------ \ bezoutianMatrix / ------------------------
document {
     	Key => {bezoutianMatrix},
	Headline => "returns a matrix associated to generalized resultants",
	Usage => " bezoutianMatrix(aSingleRowMatrix, varList)",

	Inputs => {
		"aSingleRowMatrix" => Matrix => {" a single row matrix with (affine) polynomials f1,...,fn"},
		"varList" => List => {" a list of n-1 variables to be eliminated form the fi's"},
	},
	Outputs => {
		"aMatrix" => Matrix => {"an elimination matrix"}
	},

	PARA {}, "Let R be a polynomial ring in two groups of variables X1,...,Xn-1 and a1,...,as. The variables a_1,..,as are seen as parameters and the variables X1,...,Xn-1 are to be eliminated. Being given a row matrix [f1,...,fn] where each fi is a polynomial in X1,...,Xn-1 and a1,...,ar, this function returns an elimination matrix that only depends on the parameters a1,...,as and whose maximal nonzero minor yields a multiple of the generalized resultant associated to f1,...,fn.",


	EXAMPLE {" R=QQ[a..i,x,y]",
	"f1 = a*x+b*y+c",
	"f2 = d*x+e*y+f",
	"f3 = g*x+h*y+i",
	"M = matrix{{f1,f2,f3}}",
	"l = {x,y}",
	"MR = bezoutianMatrix (M,l)"
		},		
     
	SeeAlso => {macRes, macaulayFormula, ciRes, cm2Res}
     
}


------------------------ \ ciRes / ------------------------
document {
     	Key => {ciRes},
	Headline => "returns a matrix corresponding to the residual resultant over a complete intersection",
	Usage => " ciRes(aSingleRowMatrix, Matrix, varList)",

	Inputs => {
		"aSingleRowMatrix" => Matrix => {"a single row matrix describing the base locus"},
		"Matrix" => Matrix => {"a matrix corresponding to the decomposition of a polynomial system over the base locus"},
		"varList" => List => {"list 'var' of variables with respect to which the polynomials are homogeneous and from which one wants to remove these variables"},
	},
	Outputs => {
		"aMatrix" => Matrix => {"a matrix corresponding to the residual resultant"}
	},

	PARA {}, " This function basically computes the matrix of the first application in the resolution of (I:J) given in the article of Bruns, Kustin and Miller: 'The resolution of the generic residual intersection of a complete intersection', Journal of Algebra 128.",
	
	PARA {}, "The first argument is a list of homogeneous polynomials J=(g1,..,gm) forming a complete intersection with respect to the variables 'varList'. Given a system of homogeneous I=(f1,..,fn), such that I is included in J and (I:J) is a residual intersection, one wants to to compute a sort of resultant of (I:J). The second argument is the matrix M such that I=J.M. The output is a generically (with respect to the other variables than 'varList') surjective matrix such that the 
determinant of a maximal minor is a multiple of the resultant of I on the closure of the complementary of V(J) in V(I). Such a minor can be obtain with ", TO2((maxMinor),"maxMinor"), " and ", TO2((maxMinorNum),"maxMinorNum"),".",


	EXAMPLE {" R=QQ[a_0,a_1,a_2,a_3,a_4,b_0,b_1,b_2,b_3,b_4,c_0,c_1,c_2,c_3,c_4,x,y,z]", 
	"G=matrix{{z,x^2+y^2}}", 
	"H=matrix{{a_0*z+a_1*x+a_2*y,b_0*z+b_1*x+b_2*y,c_0*z+c_1*x+c_2*y},{a_3,b_3,c_3}}",
	"L=ciRes(G,H,{x,y,z})",
	"maxCol L"
		},
     
	SeeAlso => {macaulayFormula, macRes,cm2Res, bezoutianMatrix}
     
}


------------------------ \ ciResDeg / ------------------------
document {
     	Key => {ciResDeg},
	Headline => "compute a regularity index and partial degrees of the residual resultant over a complete intersection",
	Usage => " ciRes(List, List)",

	Inputs => {
		"List" => List => {"a list of element in the ambient ring corresponding to the degrees of a system of polynomials d1,...,dn"},
		"List" => List => {"a list of element in the ambient ring corresponding to the degrees of a complete intersection k1,...,km, where m<n"},
	},
	Outputs => {
		"List" => List => {"a list of element consisting of a regularity index and partial degree of homogeneity"}
	},

	PARA {}, " Given a system of polynomials f0,...,fn of degree d0,...,dn that are contained in a complete intersection g1,...,gm of degree k1,...,km, this function returns the regularity index used to form the matrix associated to the residual resultant over a complete intersection and then all the partial degree of this resultant with respect to the coefficients of f0,f1,..,fn.",


	EXAMPLE {" R=ZZ[d_0..d_3,k_1,k_2]",
	"L=ciResDeg({d_0,d_1,d_2,d_3},{k_1,k_2})", 
		},
     
	SeeAlso => {ciRes,ciResDegGH}
     
}

------------------------ \ ciResDegGH / ------------------------
document {
     	Key => {ciResDegGH},
	Headline => "compute a regularity index used for the residual resultant over a complete intersection",
	Usage => " ciResDegGH(aSingleRowMatrix, Matrix, varList)",

	Inputs => {
		"aSingleRowMatrix" => Matrix => {"a single row matrix describing the base locus"},
		"Matrix" => Matrix => {"a matrix corresponding to the decomposition of a polynomial system over the base locus"},
		"varList" => List => {"list 'var' of variables with respect to which the polynomials are homogeneous and from which one wants to remove these variables"},
	},
	Outputs => {
		"Integer" => ZZ => {"a regularity index to form the residual resultant-"}
	},

	PARA {}, " This function is similar to the first element in the list returned by the function ", TO2(ciResDeg,"ciResDeg")," but with arguments that are identical to the ones used with the function ", TO2(ciRes,"ciRes"), ".",

	EXAMPLE {" R=QQ[a_0,a_1,a_2,a_3,a_4,b_0,b_1,b_2,b_3,b_4,c_0,c_1,c_2,c_3,c_4,x,y,z]", 
	"G=matrix{{z,x^2+y^2}}", 
	"H=matrix{{a_0*z+a_1*x+a_2*y,b_0*z+b_1*x+b_2*y,c_0*z+c_1*x+c_2*y},{a_3,b_3,c_3}}",
	"ciResDegGH(G,H,{x,y,z})",
		},
     
	SeeAlso => {ciRes,ciResDeg}
     
}


------------------------ \ cm2Res / ------------------------
document {
     	Key => {cm2Res},
	Headline => "returns a matrix corresponding to the residual resultant over a Cohen-Macaulay codimension 2 base locus",
	Usage => " ciRes(aSingleRowMatrix, Matrix, varList)",

	Inputs => {
		"Matrix" => Matrix => {"a single row matrix describing the base locus"},
		"Matrix" => Matrix => {"a matrix corresponding to the decomposition of a polynomial system over the base locus"},
		"varList" => List => {"list 'var' of variables with respect to which the polynomials are homogeneous and from which one wants to remove these variables"},
	},
	Outputs => {
		"aMatrix" => Matrix => {"a matrix corresponding to the residual resultant"}
	},

	PARA {}, " Suppose given a homogeneous ideal l.c.i. CM codim 2 J=(g1,..,gn), such that I=(f1,..,fm) is included in J and (I:J) is a residual intersection. Let H be the matrix that I=J.H. Let R be the matrixof the first syzygies of J. This function computes an elimination matrix corresponding to the residual resultant over V(I) over V(J).",


	EXAMPLE {"R = QQ[X,Y,Z,x,y,z]",
	"F = matrix{{x*y^2,y^3,x*z^2,y^3+z^3}}",
	"G = matrix{{y^2,z^2}}",
	"M = matrix{{1,0,0},{0,1,0},{0,0,1},{-X,-Y,-Z}}",
	"H = (F//G)*M",
	"l = {x,y,z}",
	"L=cm2Res (G,H,l)",
	"maxCol L",
		},
     
	SeeAlso => {macaulayFormula, macRes,ciRes, bezoutianMatrix}
     
}


------------------------ \ detRes / ------------------------
document {
     	Key => {detRes},
	Headline => "returns a matrix corresponding to the residual resultant over a Cohen-Macaulay codimension 2 base locus",
	Usage => " detRes(aSingleRowMatrix, Matrix, varList)",

	Inputs => {
		"Matrix" => Matrix => {"a polynomial matrix M"},
		"Integer" => ZZ => {"an integer r corresponding to the regularity index used to form the determinantal resultant"},
		"varList" => List => {" a list of homogeneous variables that are to be eliminated"},
	},
	Outputs => {
		"aMatrix" => Matrix => {"a matrix corresponding to the determinantal resultant"}
	},

	PARA {}, " Compute the determinantal resultant of an (n,m)-matrix (n<m) of homogeneous polynomials over the projective space of dimension m-n, i.e. a condition on the parameters of these polynomials to have rank(M)<n. The integer r is used to form the matrix detRes",


	EXAMPLE {"R=QQ[a_0..a_5,b_0..b_5,x,y]",
	"M:=matrix{{a_0*x+a_1*y,a_2*x+a_3*y,a_4*x+a_5*y},{b_0*x+b_1*y,b_2*x+b_3*y,b_4*x+b_5*y}}",
	"detRes(M,1,{x,y})"
		},
     
	SeeAlso => {macaulayFormula, macRes,ciRes, cm2Res, bezoutianMatrix}
     
}


------------------------ \ detResDeg / ------------------------
document {
     	Key => {detResDeg},
	Headline => "compute a regularity index and partial degrees of the determinantal resultant",
	Usage => " detResDeg(List, List, integer, Ring)",

	Inputs => {
		"List" => List => {"a list of degrees indexing the columns of a polynomial matrix "},
		"List" => List => {"a list of degrees indexing the rows of the same polynomial matrix M"},
		"Integer" => ZZ => {"an integer r corresponding to the drop of rank used to form the determinantal resultant"},
		"Ring" => Ring => {" an ambient ring where the computations take place"},
	},
	Outputs => {
		"aList" => List => {"a list of element consisting of a regularity index and partial degree of homogeneity of the  determinantal resultant"}
	},

	PARA {}, " Compute the regularity index and the multi-degree of the determinantal resultant associated to the matrix M",


	EXAMPLE {"R = ZZ[d1,d2,d3,k1,k2]",
	"detResDeg({d1,d2,d3},{k1,k2},1,R)",
		},
     
	SeeAlso => {macaulayFormula, macRes,ciRes, ciResDeg, cm2Res, bezoutianMatrix}
     
}



------------------------ \ documentation maxCol / ------------------------

document {
	Key => "maxCol",
	Headline => "Returns a submatrix form by a maximal set of linear independent columns.",
	Usage => " MM = maxCol(Mat)",
	Inputs => {
		"Mat" => Matrix
	},
	Outputs => {
		"MM" => Matrix,
		"cols" => List
	},
	PARA {}, " From a given m x n - Matrix of rank r, ", TO maxCol, " returns a submatrix 'MM' form by a maximal set of linear independent columns, and the list of columns 'cols' chosen.",

	EXAMPLE { 
		" M = matrix {{1,2,3},{1,2,3},{4,5,6},{4,5,6}}",
		" maxCol M;"},

	PARA {}, "NOTE: because of the necessity of ", TO rank," the base field need to be QQ for doing generic evaluation. If not, one gets the message: expected an affine ring (consider Generic=>true to work over QQ).",

	EXAMPLE {
		" R=QQ[a..g]",
		" M = matrix {{a,a,b},{c,c,d},{e,e,f},{g,g,g}}",
		" maxCol M"},

	SeeAlso => {maxMinor, rank, maxColNum, rankNum, maxMinorNum}

}

------------------------ \ documentation maxMinor / ------------------------

document {
	Key => "maxMinor",
	Headline => "Returns a maximal minor of the matrix of full rank.",
	Usage => " MM = maxMinor(Mat)",
	Inputs => {
		"Mat" => Matrix
	},
	Outputs => {
		"MM" => Matrix
	},
	PARA {}, " From a given m x n - Matrix of rank r, ", TO maxMinor, " returns an r x r full rank Matrix. This method uses twice the method ", TO maxCol," by transposing twice.",
	
	EXAMPLE { 
		" M = matrix {{1,2,3},{1,2,3},{4,5,6},{4,5,6}}",
		" maxMinor M"},

	PARA {}, "NOTE: because of the necessity of ", TO rank," the base field need to be QQ for doing generic evaluation. If not, one gets the message: expected an affine ring (consider Generic=>true to work over QQ).",

	EXAMPLE {
		" R=QQ[a..g]",
		" M = matrix {{a,a,b},{c,c,d},{e,e,f},{g,g,g}}",
		" maxMinor M"},

	SeeAlso => {maxCol, rank, maxColNum, rankNum, maxMinorNum}
}

------------------------ \ documentation maxColNum / ------------------------

document {
	Key => "maxColNum",
	Headline => "Returns a submatrix form by a maximal set of linear independent columns by random evaluation.",
	Usage => " MM = maxColNum(Mat)",
	Inputs => {
		"Mat" => Matrix
	},
	Outputs => {
		"MM" => Matrix,
		"cols" => List
	},
	PARA {}, " Same as ", TO maxCol, ", but uses ", TO rankNum, " for numerical rank computation",

	EXAMPLE { 
		" M = matrix {{1,2,3},{1,2,3},{4,5,6},{4,5,6}}",
		" maxColNum M"},
	
	PARA {}, "NOTE: because of the necessity of ", TO rank," the base field need to be QQ for doing generic evaluation. If not, one gets the message: expected an affine ring (consider Generic=>true to work over QQ).",
	
	EXAMPLE {
		" R=QQ[a..g]",
		" M = matrix {{a,a,b},{c,c,d},{e,e,f},{g,g,g}}",
		" maxColNum M"},

	SeeAlso => {maxCol, maxMinor, rank, rankNum, maxMinorNum}

}

------------------------ \ documentation maxMinorNum / ------------------------

document {
	Key => "maxMinorNum",
	Headline => "Returns a maximal minor of the matrix of full rank by random evaluation.",
	Usage => " MM = maxMinorNum(Mat)",
	Inputs => {
		"Mat" => Matrix
	},
	Outputs => {
		"MM" => Matrix
	},
	PARA {}, " Same as ", TO maxMinor, ", but uses ", TO rankNum, " for numerical rank computation",
	
	EXAMPLE { 
		" M = matrix {{1,2,3},{1,2,3},{4,5,6},{4,5,6}}",
		" maxMinorNum M"},

	PARA {}, "NOTE: because of the necessity of ", TO rank," the base field need to be QQ for doing generic evaluation. If not, one gets the message: expected an affine ring (consider Generic=>true to work over QQ).",
	
	EXAMPLE {
		" R=QQ[a..g]",
		" M = matrix {{a,a,b},{c,c,d},{e,e,f},{g,g,g}}",
		" maxMinorNum M"},

	SeeAlso => {maxMinor, maxCol, rank, maxColNum, rankNum}
}

------------------------ \ documentation rankNum / ------------------------

document {
	Key => "rankNum",
	Headline => "computes the rank of a matrix by random evaluation.",
	Usage => " MM = rankNum(Mat)",
	Inputs => {
		"Mat" => Matrix
	},
	Outputs => {
		"MM" => Matrix
	},
	PARA {}, " Same as ", TO rank, ", but uses ", TO random, " for numerical rank computation",
	
	PARA {}, "NOTE: because of the necessity of ", TO rank," the base field need to be QQ for doing generic evaluation. If not, one gets the message: expected an affine ring (consider Generic=>true to work over QQ).",

	EXAMPLE {
		" R=QQ[a..g]",
		" M = matrix {{a,a,b},{c,c,d},{e,e,f},{g,g,g}}",
		" rankNum M"},

	SeeAlso => {rank, random, maxColNum, maxMinorNum}
}



---------------------------------------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
------------------------- TESTS -------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
---------------------------------------------------------------
--	degMap,
--	macRes	

-- Test 0
-- Checking the function degHomPolMap
TEST ///
R=QQ[a,b,c,x,y];
f1 = a*x^2+b*x*y+c*y^2;
f2 = 2*a*x+b*y;
M = matrix{{f1,f2}};
l = {x,y};

dHPM = degHomPolMap (M,l,2)
MR = macRes (M,l)
Syl = matrix {{a, 2*a, 0}, {b, b, 2*a}, {c, 0, b}}

assert(dHPM == MR)
assert(dHPM_0 == gens ((ideal {x,y})^2))
assert(toString dHPM_1 == toString Syl)

mapC = mapsComplex (koszul M,l,2)

assert(dHPM_1 == mapC_0)

///

-- Test 1
-- Checking the function degHomPolMap and macRes
TEST ///
R=QQ[a..i,x,y,z];
f1 = a*x+b*y+c*z;
f2 = d*x+e*y+f*z;
f3 = g*x+h*y+i*z;
M = matrix{{f1,f2,f3}};
l = {x,y,z}
dHPM = degHomPolMap (M,l,1)
MR = macRes (M,l)
Jac = transpose matrix{{a,b,c},{d,e,f},{g,h,i}};

assert(dHPM == MR)
assert(dHPM_0 == gens (ideal {x,y,z}))
assert(toString dHPM_1 == toString Jac)

mapC = mapsComplex (koszul M,l,1)

assert(dHPM_1 == mapC_0)

///

-- Test 2
-- Checking the function mapsComplex and minorsComplex

TEST ///

R=QQ[a,b,c,x,y];
f1 = a*x^2+b*x*y+c*y^2;
f2 = 2*a*x+b*y;
M = matrix{{f1,f2}};
l = {x,y};

mapC2 = mapsComplex (koszul M,l,2)
minC2 = minorsComplex (koszul M,l,2)

assert(mapC2_0 == minC2_0)

mapC3 = mapsComplex (koszul M,l,3)
minC3 = minorsComplex (koszul M,l,3)

assert(mapC3_0_{0,1,2,3} == minC3_0)

assert((degHomPolMap (M,l,3))_1 == mapC3_0)

///

-- Test 3
-- Checking the function mapsComplex and minorsComplex

TEST ///

R=QQ[a..i,x,y,z];
f1 = a*x+b*y+c*z;
f2 = d*x+e*y+f*z;
f3 = g*x+h*y+i*z;
M = matrix{{f1,f2,f3}};
l = {x,y,z}
mapC1 = mapsComplex (koszul M,l,1)
minC1 = minorsComplex (koszul M,l,1)

assert(mapC1_0 == minC1_0)

mapC2 = mapsComplex (koszul M,l,2)
minC2 = minorsComplex (koszul M,l,2)

assert(mapC2_0_{0,1,2,3,4,6} == minC2_0)

assert((degHomPolMap (M,l,2))_1 == mapC2_0)

///


-- Test 4
-- Checking the function detComplex

TEST ///

R=QQ[a,b,c,x,y];
f1 = a*x^2+b*x*y+c*y^2;
f2 = 2*a*x+b*y;
M = matrix{{f1,f2}};
l = {x,y};

detC2 = detComplex (koszul M,l,2)
detC3 = detComplex (koszul M,l,3)
detC4 = detComplex (koszul M,l,4)

assert(detC2 == detC3)
assert(detC2 == detC4)

///


-- Test 5
-- Checking the function detComplex

TEST ///

R=QQ[a..i,x,y,z];
f1 = a*x+b*y+c*z;
f2 = d*x+e*y+f*z;
f3 = g*x+h*y+i*z;
M = matrix{{f1,f2,f3}};
l = {x,y,z}

detC1 = detComplex (koszul M,l,1)
detC2 = detComplex (koszul M,l,2)
detC3 = detComplex (koszul M,l,3)
detC4 = detComplex (koszul M,l,4)

assert(detC1 == detC2)
assert(detC3 == detC4)
assert(detC1 == -detC3)

///

-- Test 10
-- Checking the function ciRes
TEST ///

R=QQ[a_0,a_1,a_2,a_3,a_4,b_0,b_1,b_2,b_3,b_4,c_0,c_1,c_2,c_3,c_4,x,y,z]; 
G=matrix{{z,x^2+y^2}}; 
H=matrix{{a_0*z+a_1*x+a_2*y,b_0*z+b_1*x+b_2*y,c_0*z+c_1*x+c_2*y},{a_3,b_3,c_3}}; 
L=ciRes(G,H,{x,y,z})
maxCol L


assert(toString L == "matrix {{a_3, b_3, c_3, -a_3*b_1+a_1*b_3, 0, 0, -a_3*c_1+a_1*c_3, 0, 0, -b_3*c_1+b_1*c_3, 0, 0}, {0, 0, 0, -a_3*b_2+a_2*b_3, -a_3*b_1+a_1*b_3, 0, -a_3*c_2+a_2*c_3, -a_3*c_1+a_1*c_3, 0, -b_3*c_2+b_2*c_3, -b_3*c_1+b_1*c_3, 0}, {a_1, b_1, c_1, -a_3*b_0+a_0*b_3, 0, -a_3*b_1+a_1*b_3, -a_3*c_0+a_0*c_3, 0, -a_3*c_1+a_1*c_3, -b_3*c_0+b_0*c_3, 0, -b_3*c_1+b_1*c_3}, {a_3, b_3, c_3, 0, -a_3*b_2+a_2*b_3, 0, 0, -a_3*c_2+a_2*c_3, 0, 0, -b_3*c_2+b_2*c_3, 0}, {a_2, b_2, c_2, 0, -a_3*b_0+a_0*b_3, -a_3*b_2+a_2*b_3, 0, -a_3*c_0+a_0*c_3, -a_3*c_2+a_2*c_3, 0, -b_3*c_0+b_0*c_3, -b_3*c_2+b_2*c_3}, {a_0, b_0, c_0, 0, 0, -a_3*b_0+a_0*b_3, 0, 0, -a_3*c_0+a_0*c_3, 0, 0, -b_3*c_0+b_0*c_3}}")
///


-- Test 8
-- Checking the function ciResDeg
TEST ///

R=ZZ[d_0..d_3,k_1,k_2]
L=ciResDeg({d_0,d_1,d_2,d_3},{k_1,k_2})

assert(toString L == "{d_0+d_1+d_2+d_3-3*k_2-3, {d_1*d_2*d_3-d_1*k_1*k_2-d_2*k_1*k_2-d_3*k_1*k_2+k_1^2*k_2+k_1*k_2^2, d_0*d_2*d_3-d_0*k_1*k_2-d_2*k_1*k_2-d_3*k_1*k_2+k_1^2*k_2+k_1*k_2^2, d_0*d_1*d_3-d_0*k_1*k_2-d_1*k_1*k_2-d_3*k_1*k_2+k_1^2*k_2+k_1*k_2^2, d_0*d_1*d_2-d_0*k_1*k_2-d_1*k_1*k_2-d_2*k_1*k_2+k_1^2*k_2+k_1*k_2^2}}")

///

-- Test 9
-- Checking the function cm2Res
TEST ///

R = QQ[X,Y,Z,x,y,z];
F = matrix{{x*y^2,y^3,x*z^2,y^3+z^3}}
G = matrix{{y^2,z^2}};
M = matrix{{1,0,0},{0,1,0},{0,0,1},{-X,-Y,-Z}};
H = (F//G)*M;
l = {x,y,z};
CmR = (cm2Res (G,H,l))

assert(toString CmR_0 == "matrix {{x^3, x^2*y, x^2*z, x*y^2, x*y*z, x*z^2, y^3, y^2*z, y*z^2, z^3}}")

listCmR = matrixToListByColumns CmR_1;

assert(toString listCmR_0 == "{0, 0, 0, -1, 0, 0, X, 0, 0, X}")
assert(toString listCmR_1 == "{0, 0, 0, 0, 0, 0, Y-1, 0, 0, Y}")
assert(toString listCmR_2 == "{0, 0, -Y, 0, X, 0, 0, 0, 0, 0}")
assert(toString listCmR_3 == "{0, 0, 0, 0, -Y, 0, 0, X, 0, 0}")
assert(toString listCmR_4 == "{0, 0, 0, 0, 0, -Y, 0, 0, X, 0}")
assert(toString listCmR_5 == "{0, 0, 0, 0, 0, -1, Z, 0, 0, Z}")
assert(toString listCmR_6 == "{1, -X, -Z, 0, 0, 0, 0, 0, 0, 0}")
assert(toString listCmR_7 == "{0, 1, 0, -X, -Z, 0, 0, 0, 0, 0}")
assert(toString listCmR_8 == "{0, 0, 1, 0, -X, -Z, 0, 0, 0, 0}")
assert(toString listCmR_9 == "{0, -Y+1, 0, 0, -Z, 0, 0, 0, 0, 0}")
assert(toString listCmR_10== "{0, 0, 0, -Y+1, 0, 0, 0, -Z, 0, 0}")
assert(toString listCmR_11 == "{0, 0, 0, 0, -Y+1, 0, 0, 0, -Z, 0}")

///

-- Test 10
-- Checking the function detResDeg
TEST ///

R = ZZ[d1,d2,d3,k1,k2]
DRD = detResDeg({d1,d2,d3},{k1,k2},1,R)

assert(toString DRD == "{d1+d2+d3-k1-2*k2-1, {d2+d3-k1-k2, d1+d3-k1-k2, d1+d2-k1-k2}}")
///



-- Test 11
-- Checking the function detRes
TEST ///

R=QQ[a_0..a_5,b_0..b_5,x,y]
M:=matrix{{a_0*x+a_1*y,a_2*x+a_3*y,a_4*x+a_5*y},{b_0*x+b_1*y,b_2*x+b_3*y,b_4*x+b_5*y}}
detRes(M,1,{x,y})

assert(toString detRes(M,1,{x,y}) == "(matrix {{x^2, x*y, y^2}},matrix {{-a_2*b_0+a_0*b_2, -a_4*b_0+a_0*b_4, -a_4*b_2+a_2*b_4}, {-a_3*b_0-a_2*b_1+a_1*b_2+a_0*b_3, -a_5*b_0-a_4*b_1+a_1*b_4+a_0*b_5, -a_5*b_2-a_4*b_3+a_3*b_4+a_2*b_5}, {-a_3*b_1+a_1*b_3, -a_5*b_1+a_1*b_5, -a_5*b_3+a_3*b_5}})")

///
