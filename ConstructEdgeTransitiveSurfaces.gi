LoadPackage("simpl");
LoadPackage("graphsym");
BindGlobal("SymSurf_Magma",false);
MakeReadWriteGlobal("SymSurf_Magma");
Read("implementationGAP.g");
Read("maximalSubgroups.g");
Read("helper.g");
#Read("ConstructFaceTransitiveSurfaces.gd");


##################################################################################################
#####
#####
#####

BindGlobal("__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2",function(digraph,edges,group,n)
        local g,edge,edge2,orbit_lengths,small_orbit,big_orbit,paths,path,umbrellas,res,res2,neighbour_edges,
        temp_umbrellas,edgesOfV1,i,temp_umbrellas2,v,neigh,aut,automorphisms,ord,cycles,temp,cyc,transpositions;
        res:=[];
        edgesOfV1:=Filtered(edges,g->1 in g);
        edge:=edgesOfV1[1];
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
            if Length(Set(temp))=Length(temp)  then 
                cyc:=CycleFromList(temp);
                temp:=ConjugacyClass(group,cyc);
                temp:=Elements(temp);
                temp:=Set(List(temp,g->Set([g,g^(-1)])));
                temp:=List(temp,g->g[1]);
                if IsCycleDoubleCover(edgesOfV1,temp) then
                    Add(res,temp);
                fi;         
            fi;
        od;
        return List(res,umb->__SimplicialSurfaceByUmbrellaDescriptor(umb,n));
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
        groups:=SymSurf_AllCandidatesFiltered(G,2*nE);
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


BindGlobal(
    "__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1_Type_2",function(digraph,edges,group,n)
        local g,edge,orbit_lengths,small_orbit,big_orbit,paths,path,umbrellas,res,res2,neighbour_edges,
        temp_umbrellas,edgesOfV1,i,temp_umbrellas2,v,neigh,aut,automorphisms,ord,cycles,temp,cyc,transpositions,h,t;
        edgesOfV1:=Filtered(edges,g->1 in g);
        res:=[];
        edge:=Filtered(edges,g->1 in g)[1];
        paths:=findPath(digraph,edge,5,edges);
        for path in paths do 
            v:=Last(path);
            automorphisms:=Filtered(Elements(group),g->1^g=v);
            for aut in automorphisms do
                temp:=ShallowCopy(path);
                temp:=temp{[1,2,3,4]};
                t:=ShallowCopy(path);
                t:=t{[1,2,3,4]};
                ord:=Order(aut);
                for i in [1..ord-1] do
                    g:=aut^i;
                    Append(temp,List(t,h->h^g));
                od;
                if Length(Set(temp))=Length(temp)  then 
                    cyc:=CycleFromList(temp);
                    temp:=ConjugacyClass(group,cyc);
                    temp:=Elements(temp);
                    temp:=Set(List(temp,g->Set([g,g^(-1)])));
                    temp:=List(temp,g->g[1]);
                    if IsCycleDoubleCover(edgesOfV1,temp) then
                        Add(res,temp);
                    fi;         
                fi;
            od;
        od;
        return List(res,umb->__SimplicialSurfaceByUmbrellaDescriptor(umb,n));
    end
);
#####
#####
#####
##################################################################################################
__help_IsIsomorphic:=function(l,surface)
  local g,temp,nrV,counter,orientable;
  nrV:=NumberOfVertices(surface);
  counter:=ListCounter(CounterOfVertices(surface));
  orientable:=IsOrientable(surface);
  temp:=Filtered(l,g->NumberOfVertices(g)=nrV);
  temp:=Filtered(temp,g->ListCounter(CounterOfVertices(g))=counter);
  temp:=Filtered(temp,g->IsOrientable(g)=orientable);
  for g in temp do
    if IsIsomorphic(surface,g) then 
      return true;
    fi;
  od;
  return false;
end;

AllEdgeTransitiveSurfacesOfGraph:=function(digraph)
    local group,aut,edges,n,allgroups,order,res,FaceEdgeType_2_2,FaceEdgeType_2_1_Type_1,FaceEdgeType_2_1_Type_2,
    orbits,autE,temp,t,autV,cand,candidates,candidate,bool_database,nE;
    
    bool_database:=true;
    aut:=AutomorphismGroup(digraph);
    edges:=DigraphEdges(digraph);
    edges:=Set(List(edges,g->Set(g)));
    n:=NrMovedPoints(aut);
    nE:=3/2*n;
    candidates:=SymSurf_AllCandidates(aut);

    #### fe(X)=(2,2)
    FaceEdgeType_2_2:=[];

    #### fe(X)=(2,1)
    FaceEdgeType_2_1_Type_1:=[];
    FaceEdgeType_2_1_Type_2:=[];
 
    ### construct edge-transitive surfaces 
    for group in candidates do
        order:=Order(group); 
        Print("candidates\n");
        
        if order=2*nE then  
        ########### check whether we constructed fe(X)=(2,2)
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2(digraph,edges,group,nE);
            if temp <> [] then
                Append(FaceEdgeType_2_2,selectSurfaces(temp,nE,2,2));
            fi; 
        elif order=nE then 
        ########### check whether we constructed fe(X)=(2,1) type 1
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_2(digraph,edges,group,nE);
            if temp <> [] then
                Append(FaceEdgeType_2_1_Type_1,selectSurfaces(temp,nE,2,1)); 
            fi;
        ########### check whether we constructed fe(X)=(2,1) type 2
            temp:=__help_ConstructEdgeTransitiveSurfacesWithFaceEdgeType_2_1_Type_2(digraph,edges,group,orbits,n);
            if temp <> [] then
                Append(FaceEdgeType_2_1_Type_2,selectSurfaces(temp,nE,2,1)); #######TODO check not type 1
            fi;
        fi;
    od;
    ###########


    ###### see whether fe(X)=(2,1) type 2 is in type 1
    FaceEdgeType_2_1_Type_2:=Filtered(FaceEdgeType_2_1_Type_2,g->not __help_IsIsomorphic(FaceEdgeType_2_1_Type_1,g));
    res:=[FaceEdgeType_2_2,FaceEdgeType_2_1_Type_1,FaceEdgeType_2_1_Type_2];
    if bool_database then 
        return res;
    else 
        return [res,List(res,g->Length(g))];
    fi;
end;

####
####   End of Functions for transitive subgroups
####
##############################################################

