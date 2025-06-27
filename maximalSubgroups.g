BindGlobal( "MyConvertToMagmaInputString",
    function( g,str,n )
    local s, i, nf;
    s:=ShallowCopy(str);
    Append(s,":=PermutationGroup<");
    Append( s, String(n) );
    Add( s, '|' );
    nf := false;
    for i in GeneratorsOfGroup(g) do
        if nf then
            Append( s, ",\n" );
        fi;
        nf:=true;
        Append( s, String(i) );
    od;
    Append( s, ">;\n" );
    return s;
end );


BindGlobal("OrderMagma", function(G)
    local path, magma, input, resString, output,str,n;
    path := DirectoriesSystemPrograms();
    magma := Filename( path, "magma" );
    str:=ReplacedString(ReplacedString(ConvertToMagmaInputString(G, "G"), "()", ""), ",\n,", "");
    input := InputTextString(Concatenation([str,"print(Order(G));"]));
    resString := "";
    output := OutputTextString(resString, true);
    Process(path[1], magma, input, output, ["-b"]);
    return EvalString(resString);
end);  
    
BindGlobal("MyOrder", function(G)
    local g;
    if SymSurf_Magma=true then
        return OrderMagma(G);
    else
        return Order(G);
    fi;
end);

BindGlobal("MaximalSubgroupsMagma", function(G,n)
    local path, magma, input, res, output;
    path := DirectoriesSystemPrograms();
    magma := Filename( path, "magma" );
    input := InputTextString(Concatenation([
            ReplacedString(ReplacedString(MyConvertToMagmaInputString(G, "G",n), "()", ""), ",\n,", ""),
            "M := MaximalSubgroups(G);\n",
            "print([\"Group(\"*Sprint([x : x in Generators(m`subgroup)])*\")\" : m in M]);"
        ]));
    res := "";
    output := OutputTextString(res, true);
    SetPrintFormattingStatus(output,false);
    Process(path[1], magma, input, output, ["-b"]);
    # edge case: trivial group constructor
    res := ReplacedString(res, "[]", "()");
    return EvalString(res);
end);

BindGlobal("MyMaximalSubgroups", function(G,n)
    local g;
    if SymSurf_Magma=true then 
        return MaximalSubgroupsMagma(G,n);
    else
        return List(ConjugacyClassesMaximalSubgroups(G),g->Representative(g));
    fi;
end);

BindGlobal("MyIsConjugate", function(G,H,K,n)
    local path, magma, input, resString, output,str1,str2,str3;
    
    path := DirectoriesSystemPrograms();
    magma := Filename( path, "magma" );
    str1:=ReplacedString(ReplacedString(MyConvertToMagmaInputString(G, "G",n), "()", ""), ",\n,", "");
    str2:=ReplacedString(ReplacedString(MyConvertToMagmaInputString(H, "H",n), "()", ""), ",\n,", "");
    str3:=ReplacedString(ReplacedString(MyConvertToMagmaInputString(K, "K",n), "()", ""), ",\n,", "");
    input := InputTextString(Concatenation([str1,str2,str3,
            "print(IsConjugate(G, H, K));"]));
    resString := "";
    output := OutputTextString(resString, true);
    Process(path[1], magma, input, output, ["-b"]);
    return EvalString(resString);
    
end);

BindGlobal("MyMaximalSubgroupsUpToConjugacy", function(G,classes,n)
    local res,i,j,k,group,len,bool,temp,tempOrders,ord,orders;
    res:=ShallowCopy(classes[1]);
    orders:=List(res,g->MyOrder(g));
    for i in [2..Length(classes)] do
        temp:=[];
        tempOrders:=[];
        for j in [1..Length(classes[i])] do 
            bool:=true;
            k:=1;
            group:=classes[i][j];
            len:=Length(res);
	    ord:=MyOrder(group);
            while bool and k<=len do
		if orders[k]=ord then 
	            if MyIsConjugate(G,res[k],group,n) then
        	        bool:=false;
                    fi;
		fi;
                k:=k+1;
            od;
            if bool then
		Add(tempOrders,ord); 
                Add(temp,group);
            fi;
        od;
        Append(res,temp);
        Append(orders,tempOrders);
    od;
    return res;
end);


MyConjugateFreeList:=function(G,L)  
    local g,res,i,j,len,bool,n;
    res:=[L[1]];
    n:=NrMovedPoints(G);
    for i in [2..Length(L)] do 
        j:=1;len:=Length(res);
        bool:=true;
        while j<=len and bool do;      
            if MyIsConjugate(G,res[j],L[i],n) then 
                bool:=false;
            fi;
            j:=j+1;
        od;
        if bool then 
            Add(res,L[i]);
        fi;
    od;
    return res;
end;



AllCandidatesOfAutomorphismGroupsOfEdgeTransitiveSurfaces_GAP:=function(G,edge)
  local g,n,nE,res,classes,temp,i,sub,class,t,maxsubgroups,conj,subgroups,subgroup,candidate;
  n:=NrMovedPoints(G);
  nE:=3/2*n;
  res:=[];
  if Order(G) in [nE,2*nE] then
    Add(res,G);
  fi;
  subgroups:=[G];
  while subgroups <> [] do
    Print("found ", Length(subgroups)," maximal subgroups\n");
    temp:=[];
    for subgroup in subgroups do
      Print(Position(subgroups,subgroup)," \n");
      maxsubgroups:=ConjugacyClassesMaximalSubgroups(subgroup);
      maxsubgroups:=List(maxsubgroups,Representative);
      for candidate in maxsubgroups do
        if Length(Orbits(candidate,edge,OnSets))=nE then
          Add(temp,candidate);
          if  Size(candidate) in [nE,2*nE]  then
                  Add(res,candidate);
          fi;
        fi;
      od;
    od;
    subgroups:=temp;
    Print("subgroups ",Length(subgroups)," and  res ",Length(res));
  od;
  return res;
end;



BindGlobal("SymSurf_AllCandidatesE", function(G,edge)
    local path, magma, input, res, output; 
    if SymSurf_Magma=true then 
        path := DirectoriesSystemPrograms();
        magma := Filename( path, "magma" );
        input := InputTextString(Concatenation(
                ["load \"/home/data/akpanya/Edgetransitivesurfaces/implementationMagma.m\";\n",
                ReplacedString(ReplacedString(ConvertToMagmaInputString(G, "G"), "()", ""), ",\n,", ""),
                "M := AllCandidatesOfAutomorphismGroupsOfEdgeTransitiveSurfaces_MagmaCT(G,",String(edge),");\n",
                "print([\"Group(\"*Sprint([x : x in Generators(m)])*\")\" : m in M]);"
            ]));
        res := "";
#        magma:=Concatenation(magma," implementationMagma.m");
        output := OutputTextString(res, true);
        SetPrintFormattingStatus(output,false);
        Process(path[1], magma, input, output, ["-b"]);
        res:=SplitString(res,"\n");
        res:=Concatenation(res{[2..Length(res)]});
        # edge case: trivial group constructor
        res := ReplacedString(res, "[]", "()");
        res:=EvalString(res);
        if res=() then res:=[]; fi;
        return res;
    else 
        return AllCandidatesOfAutomorphismGroupsOfEdgeTransitiveSurfaces_GAPCT(G,edge);
    fi;
end);

BindGlobal("SymSurf_AllCandidatesFilteredE", function(G,edge,order)
    local g, temp;
    temp:=SymSurf_AllCandidatesE(G,edge);
    return Filtered(temp,g->Order(g)=order);
end);
