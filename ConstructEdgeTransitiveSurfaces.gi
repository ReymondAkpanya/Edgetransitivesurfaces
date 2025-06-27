LoadPackage("simpl");
LoadPackage("graphsym");
BindGlobal("SymSurf_Magma",true);
MakeReadWriteGlobal("SymSurf_Magma");
Read("implementationGAP.g");
Read("maximalSubgroups.g");
Read("helper.g");
Read("ConstructEdgeTransitiveSurfaces.gd");



##################################################################################################
#####
#####
#####



BindGlobal(
    "__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4",function(digraph,edges,group,n)
        local g,edge,ee,orbit_lengths,small_orbit,big_orbit,paths,path,umbrellas,res,res2,k,j,neighbour_edges,
        temp_umbrellas,i,temp_umbrellas2,v,neigh,aut,automorphisms,ord,cycles,temp,cyc,transpositions,v1,v2,t;
        edge:=edges[1];
        if Length(Orbits(group))<>1 then
            return [];
        fi;
        res:=[];
        neighbour_edges:=Filtered(edges,g->1 in g);
        automorphisms:=Filtered(group,g->edge[1]^g=edge[2] and Order(g)<>2);
        for g in automorphisms do
            temp:=List([1..Order(g)],i->edge[1]^(g^i));        
            if Length(temp)=Length(Set(temp)) then
                cyc:=CycleFromList(temp);
                temp:=ConjugacyClass(group,cyc);
                temp:=Elements(temp);
                temp:=Set(List(temp,g->Set([g,g^(-1)])));
                temp:=List(temp,g->g[1]);
                if IsCycleDoubleCover(neighbour_edges,temp) then
                   Add(res,temp);
                fi;
            fi;
        od;
        res:=List(res,umb->__SimplicialSurfaceByUmbrellaDescriptor(umb,n));
        return Filtered(res,g->g<>fail);
end
);

InstallMethod(
    ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4,"for a digraph",[IsDigraph],function(digraph)
        local n,edges,g,G,groups,group,res;
        n:=DigraphNrVertices(digraph);
        edges:=DigraphEdges(digraph);
        edges:=Set(List(edges,g->Set(g)));
        res:=[];
        G:=AutomorphismGroup(digraph);
        groups:=SymSurf_AllCandidatesFilteredE(G,edges[1], 6*n);
        for group in groups do  
            Append(res,__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4(digraph,edges,group,n));
        od;
        return res;
    end
);
####
####   End of Functions for face-transitive surfaces with vf(X)=(1,6)
####
##############################################################

##############################################################
####
####   Begin Functions for far face-transitive surfaces with vf(X)=(1,3)
####


############
############ vf(X)=(1,3) type 1
############


InstallMethod(
    ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_2_Type_1,"for a digraph", [IsDigraph],function(digraph)
        local n,edges,g,G,groups,group,orbits,res;
        n:=DigraphNrVertices(digraph);
        edges:=DigraphEdges(digraph);
        edges:=Set(List(edges,g->Set(g)));
        res:=[];
        G:=AutomorphismGroup(digraph);
        groups:=SymSurf_AllCandidatesFilteredE(G,edges[1],3*n);
        for group in groups do  
            Append(res,__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4(digraph,edges,group,n));
        od;
        return IsomorphismRepresentatives(res);
    end
);

############
############ end of vf(X)=(1,3) type 1
############

############
############ vf(X)=(1,3) type 2
############

BindGlobal(
    "__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_2_Type_2",function(digraph,edges,group,n) 
        local g,edge,ee,orbit_lengths,small_orbit,big_orbit,paths,path,umbrellas,res,res2,k,j,neighbour_edges,
        temp_umbrellas,i,temp_umbrellas2,v,neigh,aut,automorphisms,ord,cycles,temp,cyc,transpositions,v1,v2,t;
        res:=[];
        if Length(Orbits(group))<>1 then
            return [];
        fi;
        neighbour_edges:=Filtered(edges,g->1 in g);
        temp:=Difference(Union(neighbour_edges[1],neighbour_edges[2]),[1]);
        path:=[temp[1],1,temp[2]];
        edge:=[temp[1],1];
        automorphisms:=Filtered(group,g->path[1]^g=path[3] and Order(g)<>2);
        for g in automorphisms do
            temp:=[];
            for i in [1..Order(g)] do
                Append(temp,[edge[1]^(g^i),edge[2]^(g^i)]); 
            od;
            if Length(temp)=Length(Set(temp)) then
                cyc:=CycleFromList(temp);    
                temp:=ConjugacyClass(group,cyc);
                temp:=Elements(temp);
                temp:=Set(List(temp,g->Set([g,g^(-1)])));
                temp:=List(temp,g->g[1]);
                if IsCycleDoubleCover(neighbour_edges,temp) then
                    Add(res,temp);
                fi;
            fi;
        od;
        res:=List(res,umb->__SimplicialSurfaceByUmbrellaDescriptor(umb,n));
        return Filtered(res,g->g<>fail);
    end
);

InstallMethod(
    ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_2_Type_2,"for a digraph",[IsDigraph],function(digraph)
        local n,edges,g,G,groups,group,orbits,res;
        n:=DigraphNrVertices(digraph);
        edges:=DigraphEdges(digraph);
        edges:=Set(List(edges,g->Set(g)));
        res:=[];
        G:=AutomorphismGroup(digraph);
        groups:=SymSurf_AllCandidatesFilteredE(G,edges[1],3*n);
        for group in groups do  
            Append(res,__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_2_Type_2(digraph,edges,group,n));
        od;
        return IsomorphismRepresentatives(res);
    end
);











BindGlobal(
    "__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2",function(digraph,edges,group,n)
        local g,edge,edge2,orbit_lengths,small_orbit,big_orbit,paths,path,umbrellas,res,res2,neighbour_edges,
        temp_umbrellas,edgesOfV1,i,temp_umbrellas2,v,neigh,aut,automorphisms,ord,cycles,temp,cyc,transpositions;
        res:=[];
        Print("start\n");
        edgesOfV1:=Filtered(edges,g->1 in g);
        edge:=Set(edgesOfV1[1]);
        edge2:=Filtered(edges,g->edge[2] in g and g<> edge)[1];
        v:=Difference(edge2,edge)[1];
        path:=[edge[1],edge[2],v];
        neigh:=path[2];
        automorphisms:=Filtered(Elements(group),g->1^g=v);
        for aut in automorphisms do
            temp:=ShallowCopy(path);
            Add(temp,neigh^(aut));
            ord:=Order(aut);
            for i in [2..ord-1] do
                g:=aut^i;
                 Append(temp,[1^g,neigh^g]);
            od;
Print("temp construction\n");
            if Length(Set(temp))=Length(temp)  then 
                cyc:=CycleFromList(temp);
                temp:=ConjugacyClass(group,cyc);
                temp:=Elements(temp);
                temp:=Set(List(temp,g->Set([g,g^(-1)])));
                temp:=List(temp,g->g[1]);
                Print("check cycle double cover\n");
                if IsCycleDoubleCover(edgesOfV1,temp) then
                    Add(res,temp);
                fi;         
            fi;
        od;
        res:=List(res,umb->__SimplicialSurfaceByUmbrellaDescriptor(umb,n));
        return Filtered(res,g->g<>fail);
    end
); 


InstallMethod(
    ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2,"for a digraph",[IsDigraph],function(digraph)
        local g,nrE,aut,umb,bool,orbits,res,inv1,inv2,edges,i,group,
        cyc1,cyc2,inv3,class,n,nE,t1,t2,t3,bool2,groups,G,involutions;
        n:=DigraphNrVertices(digraph);
        nE:=3/2*n;
        edges:=DigraphEdges(digraph);
        edges:=Set(List(edges,g->Set(g)));
        res:=[];
        G:=AutomorphismGroup(digraph);
        groups:=SymSurf_AllCandidatesFilteredE(G,edges[1],2*nE);
        for group in groups do
            Append(res,__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2(digraph,edges,group,n));
        od;
        return res;
    end
);

InstallMethod(
    ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1,"for a digraph",[IsDigraph],function(digraph)
        local g,nrE,aut,umb,bool,orbits,res,inv1,inv2,edges,i,group,
        cyc1,cyc2,inv3,class,n,nE,t1,t2,t3,bool2,groups,G,involutions;
        n:=DigraphNrVertices(digraph);
        nE:=3/2*n;
        edges:=DigraphEdges(digraph);
        edges:=Set(List(edges,g->Set(g)));
        res:=[];
        G:=AutomorphismGroup(digraph);
        groups:=SymSurf_AllCandidatesFilteredE(G,edges[1],1*nE);
        for group in groups do
            Append(res,__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2(digraph,edges,group,n));
        od;
        return res;
    end
);
#####
#####
#####
##################################################################################################




##################################################################################################
#####
#####
#####


#BindGlobal(
#    "__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1_Type_2",function(digraph,edges,group,n)
#        local g,edge,orbit_lengths,small_orbit,big_orbit,paths,path,umbrellas,res,res2,neighbour_edges,
#        temp_umbrellas,edgesOfV1,i,temp_umbrellas2,v,neigh,aut,automorphisms,ord,cycles,temp,cyc,transpositions,h,t;
#        edgesOfV1:=Filtered(edges,g->1 in g);
#        res:=[];
#        edge:=Filtered(edges,g->1 in g)[1];
#        paths:=findPath(digraph,edge,5,edges);
#        for path in paths do 
#            v:=Last(path);
#            automorphisms:=Filtered(Elements(group),g->1^g=v);
#            for aut in automorphisms do
#                temp:=ShallowCopy(path);
#                temp:=temp{[1,2,3,4]};
#                t:=ShallowCopy(path);
#                t:=t{[1,2,3,4]};
#                ord:=Order(aut);
#                for i in [1..ord-1] do
#                    g:=aut^i;
#                    Append(temp,List(t,h->h^g));
#                od;
#                if Length(Set(temp))=Length(temp)  then 
#                    cyc:=CycleFromList(temp);
#                    temp:=ConjugacyClass(group,cyc);
#                    temp:=Elements(temp);
#                    temp:=Set(List(temp,g->Set([g,g^(-1)])));
#                    temp:=Set(List(temp,g->g[1]));
#                    if IsCycleDoubleCover(edgesOfV1,temp) then
#                        AddSet(res,temp);
#                    fi;         
#                fi;
#            od;
#        od;
#        res:=List(res,umb->__SimplicialSurfaceByUmbrellaDescriptor(umb,n));
#        return Filtered(res,g->g<>fail);
#    end
#);
#####
#####
#####
##################################################################################################
__help_IsIsomorphic:=function(l,surface)
  local g,temp,nrV,counter,orientable;
  nrV:=NumberOfVertices(surface);
  counter:=ListCounter(CounterOfVertices(surface));
  orientable:=IsOrientableSurface(surface);
  temp:=Filtered(l,g->NumberOfVertices(g)=nrV);
  temp:=Filtered(temp,g->ListCounter(CounterOfVertices(g))=counter);
  temp:=Filtered(temp,g->IsOrientableSurface(g)=orientable);
  for g in temp do
    if IsIsomorphic(surface,g) then 
      return true;
    fi;
  od;
  return false;
end;



AllEdgeTransitiveSurfacesOfGraph:=function(digraph)
    local group,aut,edges,n,allgroups,order,res,FaceEdgeType_2_2,FaceEdgeType_2_1,
    orbits,autE,temp,t,autV,cand,candidates,candidate,bool_database,nE,FaceEdgeType_1_4,FaceEdgeType_1_2_Type_1,FaceEdgeType_1_2_Type_2;
    
    bool_database:=true;
    aut:=AutomorphismGroup(digraph);
    edges:=DigraphEdges(digraph);
    edges:=Set(List(edges,g->Set(g)));
    n:=NrMovedPoints(aut);
    nE:=3/2*n;
    candidates:=SymSurf_AllCandidatesE(aut,edges[1]);
    FaceEdgeType_1_4:=[];
    FaceEdgeType_2_2:=[];
    FaceEdgeType_2_1:=[];
#    FaceEdgeType_2_1_Type_2:=[];
    FaceEdgeType_1_2_Type_1:=[];
    FaceEdgeType_1_2_Type_2:=[];
    Print("candiates ", Length(candidates)," ",List(candidates,Order),"\n" );
    ### construct edge-transitive surfaces 
    for group in candidates do
        order:=Order(group); 
        Print("candidates\n");
        ########## construct surfaces and face edge types   
        if order=nE then  
            #################check vf(X)=(2,1) type 1
            Print("check (2,1) type 1\n");
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2(digraph,edges,group,n);
            if temp <> [] then
                temp:=Filtered(temp,g->FaceEdgeType(g)=[2,1]);
                Append(FaceEdgeType_2_1,temp);
            fi;
            Print("check (2,1) type 1 done\n");

#            #################check vf(X)=(2,1) type 2
#            Print("check (2,1) type 2\n");
#            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1_Type_2(digraph,edges,group,n);
#            if temp <> [] then
#                temp:=Filtered(temp,g->FaceEdgeType(g)=[2,1,2]);
#                Append(FaceEdgeType_2_1_Type_2,temp); 
#            fi;
#            Print("check (2,1) type 2  done\n");

        elif order=2*nE then        
            #################check vf(X)=(2,2) 
            Print("check (2,2)\n");
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2(digraph,edges,group,n);
            if temp <> [] then
                temp:=Filtered(temp,g->FaceEdgeType(g)=[2,2]);
                Append(FaceEdgeType_2_2,temp); 
            fi;
            Print("check (2,2) type 2  done\n");


            #################check vf(X)=(1,2) type 1
            Print("check (1,2) type 1\n");
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4(digraph,edges,group,n);
            if temp <> [] then
                temp:=Filtered(temp,g->FaceEdgeType(g)=[1,2,1]);
                Append(FaceEdgeType_1_2_Type_1,temp);
            fi;
            Print("check (1,2) type 1  done\n");

            #################check vf(X)=(1,2) type 2
            Print("check (1,2) type 2\n");
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_2_Type_2(digraph,edges,group,n);
            if temp <> [] then
                temp:=Filtered(temp,g->FaceEdgeType(g)=[1,2,2]);
                Append(FaceEdgeType_1_2_Type_2,temp);
            fi;
            Print("check (1,2) type 1  done\n");        
        elif order=4*nE then 
            #################check vf(X)=(1,4)
            Print("check (1,4)\n");
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_1_4(digraph,edges,group,n);
            if temp <> [] then
                temp:=Filtered(temp,g->FaceEdgeType(g)=[1,4]);
                Append(FaceEdgeType_1_4,temp);
            fi;
            Print("check (1,4) done\n");
        fi;
    od;

    res:=[FaceEdgeType_1_4,FaceEdgeType_1_2_Type_1,FaceEdgeType_1_2_Type_2,
          FaceEdgeType_2_2,FaceEdgeType_2_1];
    return List(res,g->IsomorphismRepresentatives(g));
end;


writeIntoFiles:=function(n1,n2)
    local t,g,n,numbers,str1,str2,resO,resNO,str,str3,filestream,orien,surf,surfaces,l,i2,digraph,i,j,file,k,k2,vof,len;
    filestream:=["/Surfaces_With_Face_Edge_Type_1_4",
                 "/Surfaces_With_Face_Edge_Type_1_2_Type_1",
                 "/Surfaces_With_Face_Edge_Type_1_2_Type_2",
                 "/Surfaces_With_Face_Edge_Type_2_2",
                 "/Surfaces_With_Face_Edge_Type_2_1"];
    filestream:=List(filestream,g->Concatenation("RES5000-10000/",String(n1),"_",String(n2),g));
    numbers:=List([1..5],i->0);
    resO:=List([1..5],i->[]);
    resNO:=List([1..5],i->[]);
    for n in List([n1/2..n2/2],i->2*i) do
        l:=[];
        t:=AllCubicATGraphs(n);
        if t<> fail then 
            Append(l,t);
        fi;
        t:=AllCubicSSGraphs(n);
       	if t<> fail then 
       	    Append(l,t);
       	fi;
        Print("##########\n##########\n##########\n##########\n##########\n##########\n##########\n Number of vertices",n);
        if l<> [] then 
            for digraph in l do
                surfaces:=AllEdgeTransitiveSurfacesOfGraph(digraph);
                if Set(surfaces)<>[[false]] then 
                    for i in [1..5] do
                        if surfaces[i]<>[] then
                            for i2 in [1..Length(surfaces[i])] do
                                surf:=surfaces[i][i2];
                                orien:=IsOrientableSurface(surf);
                                k:=(numbers[i]-(numbers[i] mod 10))/10;
                                k2:=(numbers[i] mod 10)+1;
                                file:=Concatenation(filestream[i],"_File",String(k+1));
                                str:=Concatenation("#SurfaceInfo: ",String(NumberOfVertices(surf))," Vertices, ",
                                              String(NumberOfEdges(surf))," Edges, ",    
                                              String(NumberOfFaces(surf))," Faces, IsOrientable=",String(orien),
                                              "\n #Vertices of faces:\n",
                                              "vof",String(k2),":=[");
                                Print("printing\n");
                                vof:=VerticesOfFaces(surf);
                                len:=Length(vof);
                                for j in [1..Length(vof)] do
                                    str:=Concatenation(str,"[",String(vof[j][1]),",",String(vof[j][2]),",",String(vof[j][3]),"]");    
                                    if j<> len then
                                        str:=Concatenation(str,",");  
                                    else
                                        str:=Concatenation(str,"];");
                                    fi;
                                    if j mod 10=0 and j<>len then
                                        str:=Concatenation(str,"\n");
                                    fi;
                                od;
                                Print("printing done\n");
                                str:=Concatenation(str,"\n###############################################################\n\n");
                                AppendTo(file,str);
                                numbers[i]:=numbers[i]+1;
                                if orien then 
                                    Add(resO[i],EulerCharacteristic(surf));
                                else
       	       	          	    Add(resNO[i],EulerCharacteristic(surf));
                                fi;  
                            od;
                        fi;
                    od;
                fi;
            od;
        fi;
        n:=n+2;
    od;
    
    str1:=Concatenation("numbers_",String(n1),"_",String(n2),":=",String(numbers),";\n");
    str2:=Concatenation("EulerO_",String(n1),"_",String(n2),":=",String(List(resO,g->Collected(g))),";\n");
    str3:=Concatenation("EulerNO_",String(n1),"_",String(n2),":=",String(List(resNO,g->Collected(g))),";\n");
    AppendTo("numbers.g",str1);
    AppendTo("EulerO.g",str2);
    AppendTo("EulerNO.g",str3);
    return [numbers,List(resO,g->Collected(g)),List(resNO,g->Collected(g))];
end;




