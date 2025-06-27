##testing
randomList:=function(n)
    local g,temp,res,i,k;
    temp:=[1..n];
    res:=[];
    for i in [1..n] do 
        k:=PseudoRandom(temp);
        temp:=Difference(temp,[k]);
        Add(res,k);
    od;
    return res;
end;


RandomCopyOfSimplicialSurface:=function(surface)
    local g,nV,nF,f,randomV,randomF,vof,newvof,i;
    nV:=NumberOfVertices(surface);
    nF:=NumberOfFaces(surface);
    randomV:=randomList(nV);
    randomF:=randomList(nF);
    vof:=VerticesOfFaces(surface);
    newvof:=[];
    for i in [1..nF] do
       f:=vof[i];
       newvof[randomF[i]]:=randomV{f};
    od;
    return SimplicialSurfaceByVerticesInFacesNC(newvof);
end;


RandomCopyOfCubicGraph:=function(digraph)
    local g,nV,nE,randomE,randomV,edges,newedges,i,e;
    nV:=DigraphNrVertices(digraph);
    nE:=DigraphNrEdges(digraph);
    randomV:=randomList(nV);
    randomE:=randomList(nE);
    newedges:=[];
    edges:=DigraphEdges(digraph);
    for i in [1..nE] do
       e:=edges[i];
       newedges[randomE[i]]:=randomV{e};
    od;
    return DigraphByEdges(newedges);
end;


SymSurfTestingSurfaces:=function(verticesoffaces)
    local g,func,files,vfType,file,surf,surf2,faces,vf,s,surfaces,sigs,digraph,i,l;
    func:=[#ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4,
           #ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_2,
           ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2,           
           ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1_Type_1,
           ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1_Type_2];
    vfType:=[[2,2],[2,1,1],[2,1,2]];
        for faces in verticesoffaces do
            Print(Position(verticesoffaces,faces)," ",Length(verticesoffaces),"new test #############################\n");
            surf:=SimplicialSurfaceByVerticesInFaces(faces);
            surf2:=SCFromFacets(faces);
            vf:=FaceEdgeType(surf);
            sigs:=SCExportIsoSig(surf2);
            s:=RandomCopyOfSimplicialSurface(surf);
            digraph:=RandomCopyOfCubicGraph(FaceDigraphsGraph(s)); Print("Order ",Order(AutomorphismGroup(digraph)),"\n");
            if not vf in vfType then return Error(); fi;
            for i in [1..13] do
                if vf=vfType[i] then 
                    l:=func[i](digraph);
                    l:=List(l,g->VerticesOfFaces(s));
                    l:=List(l,g->SCFromFacets(g));
                    l:=List(l,g->SCExportIsoSig(g));
                    if not(sigs in l) then
                        Print(i,"\n");
                        Error();
                    fi;
                fi;
            od;;
        od;
    return true;
end;

SymSurfTestingCandidates2:=function()
    local g,files,file,i,l,surf1,surf2,d1,d2,can1,can2,can3,n,aut1,aut2,j,len,bool,faces;

    for i in [2..5000] do 
        l:=AllCubicVTGraphs(2*i);
        l:=Filtered(l,g->Order(AutomorphismGroup(g))<=4000);
        for d1 in l do
            Print(i," ",Position(l,d1),"new test #############################\n");            
            aut1:=AutomorphismGroup(d1);
            d2:=RandomCopyOfCubicGraph(d1);
            aut2:=AutomorphismGroup(d2);
            if Set(DigraphEdges(d1))=Set(DigraphEdges(d2)) then 
		Print("warning d1=d2\n");
            fi;
            if not IsIsomorphicDigraph(d1,d2) then 
                Error("Digraphs are not isomorphic");
            fi; 
            can1:=SymSurf_AllCandidates(aut1);
            can2:=SymSurf_AllCandidates(aut2);
            n:=DigraphNrVertices(d1);
            Print("found ",Length(can1)," candidates\n");
            if Length(can1)<>Length(can2) then
                Error("random copy has different number of candidates");
            fi;
            can3:=ConjugacyClassesSubgroups(aut1);
            can3:=List(can3,g->Representative(g));
            can3:=Filtered(can3,g->Length(Orbit(g,1))=n);
            can3:=Filtered(can3,g->Order(g) in [n,2*n,3*n,6*n]);
            if Length(can1)<>Length(can3) then
                Error("algroithm computes wrong number of candidates");
            fi;
            len:=Length(can1);
            for g in can3 do
                bool:=false;
                j:=1;
                while not bool and j<=len do
                    if IsConjugate(aut1,g,can1[j]) then
                        bool:=true;
                    fi;
                    j:=j+1;
                od;
                if not bool then
                    Error("subgroups missing");
                fi;

            od;
        od;
    od;
end;


SymSurfTestingCandidates:=function(verticesoffaces)
    local g,files,file,surf1,surf2,d1,d2,can1,can2,can3,n,aut1,aut2,j,len,bool,faces;

        for faces in verticesoffaces do
            Print(Position(verticesoffaces,faces),"new test #############################\n");
            surf1:=SimplicialSurfaceByVerticesInFaces(faces); 
            d1:=FaceDigraphsGraph(surf1);
            aut1:=AutomorphismGroup(d1);
            surf2:=RandomCopyOfSimplicialSurface(surf1);
            d2:=RandomCopyOfCubicGraph(d1);
       	    aut2:=AutomorphismGroup(d2);
            can1:=SymSurf_AllCandidates(aut1);
       	    can2:=SymSurf_AllCandidates(aut2);
            n:=NumberOfFaces(surf1);
            Print("found ",Length(can1)," candidates\n");
            if Length(can1)<>Length(can2) then 
                Error("random copy has different number of candidates");
            fi;
 
            can3:=ConjugacyClassesSubgroups(aut1);
            can3:=List(can3,g->Representative(g));
            can3:=Filtered(can3,g->Length(Orbit(g,1))=n);
            can3:=Filtered(can3,g->Order(g) in [n,2*n,3*n,6*n]);
            if Length(can1)<>Length(can3) then
                Error("algroithm computes wrong number of candidates");
            fi;
            len:=Length(can1);
            for g in can3 do 
                bool:=false;
                j:=1;
                while not bool and j<=len do 
                    if IsConjugate(aut1,g,can1[j]) then
                        bool:=true;
                    fi;
                    j:=j+1;
                od;
                if not bool then 
                    Error("subgroups missing");
                fi;

            od;
        od;
#    od;
    return true;
end;

### SymSurf
SymSurfTestingAllEdgeTransitiveSurfaces:=function()
    local g,i,j,k,res1,res2,d1,d2,temp,l;
    for k in [2..400] do 
        Print(k,"new test #############################\n");
        l:=AllCubicVTGraphs(2*k);
        for d1 in l do
            d2:=RandomCopyOfCubicGraph(d1);
            if Set(DigraphEdges(d1))=Set(DigraphEdges(d2)) then
                Print("warning d1=d2\n");
                Error();
            fi;
            res1:=AllEdgeTransitiveSurfacesOfGraph(d1);
       	    res2:=AllEdgeTransitiveSurfacesOfGraph(d2);
            if List(res1,Length)<>List(res2,Length) then 
                Error("not the same number of surfaces");
            fi;
            for i in [1..13] do
                if res1[i]<>[] then 
                    temp:=ShallowCopy(res1[i]);
                    Append(temp,res2[i]);
                    temp:=IsomorphismRepresentatives(temp);
                    if Length(temp)<>Length(res1[i]) then
                        Error("different surfaces constructed");
                    fi; 
                fi;
            od;
        od;
    od;
    return true;
end;

SymSurfTestingAllEdgeTransitiveSurfaces2:=function()
    local g,i,j,k,res1,res2,d1,d2,temp,l,vfTypes,d;
    vfTypes:=[[3,1],[2,2],[2,1,1],[2,1,2],[2,1,3],[1,1,1],[1,1,2],[1,1,3],[1,1,4],[1,2,],[1,3,1],[1,3,2],[1,6]];
    for k in [2..24] do
        Print(k,"new test #############################\n");
        l:=AllCubicVTGraphs(2*k);
        l:=Filtered(l,g->Order(AutomorphismGroup(g))<2000000);
        for d in l do
            res1:=AllEdgeTransitiveSurfacesOfGraph(d);
            Print("this might take a while\n");
            temp:=AllSimplicialSurfacesOfDigraph(d,true);
            res2:=List([1..13],i->Filtered(temp,g->VertexFaceType(g)=vfTypes[i]));
            Print("done\n");
            Print(List(res2,Length),"\n");
            if List(res1,Length)<>List(res2,Length) then
                Error("not the same number of surfaces");
            fi;
            for i in [1..13] do
                if res1[i]<>[] then
                    temp:=ShallowCopy(res1[i]);
                    Append(temp,res2[i]);
                    temp:=IsomorphismRepresentatives(temp);
                    if Length(temp)<>Length(res1[i]) then
                        Error("different surfaces constructed");
                    fi;
                fi;
            od;
        od;
    od;
    return true;
end;


