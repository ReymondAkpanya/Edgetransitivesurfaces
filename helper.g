AllCandidatesOfAutomorphismGroups:=function(G)  
  local g,n,res,classes,temp,i,sub,class,t,maxsubgroups,conj;
  n:=NrMovedPoints(G);
  res:=[];
  conj:=ConjugacyClassSubgroups(G,G);
  if Order(G) in [n,2*n,3*n,6*n] then
    Add(res,conj);
  fi;
  classes:=[conj];
  while classes <> [] do
    Print("classes ", Length(classes),"\n");
    temp:=[];
    for class in classes do 
      Print(Position(classes,class)," \n");
      g:=Representative(class);
      maxsubgroups:=List(ConjugacyClassesMaximalSubgroups(g),i->Representative(i));
      for sub in maxsubgroups do
        if Length(Orbits(sub,[1..n]))=1 then
          t:=[ConjugacyClassSubgroups(G,sub)]; 
          temp:=Union(temp,t);
          if (Size(sub)=n and IsRegular(sub)) or (Size(sub) in [2*n,3*n,6*n])  then
	    res:=Union(res,t);
	    Print("found ",Length(res),"\n");
          fi;
        fi;
      od;
    od;
    classes:=temp;
  od;
  return List(res,g->Representative(g));
end;



AllCandidatesOfAutomorphismGroups_MagmaCT:=function(G)  
    local g,n,res,classes,temp,i,sub,class,t,maxsubgroups,maximalsubgroups,maxClasses;
    n:=NrMovedPoints(G);
    res:=[];
    if MyOrder(G) in [n,2*n,3*n,6*n] then
        Add(res,G);
    fi;
    classes:=[G];
    while classes <> [] do
        Print("classes ", Length(classes),"\n");
        temp:=[];
        maxClasses:=List(classes,sub->MyMaximalSubgroups(sub,n));
        maxClasses:=List(maxClasses,class->Filtered(class,sub->Length(Orbits(sub,[1..n]))=1));
        maxClasses:=Filtered(maxClasses,g->g<>[]);
        if maxClasses<>[] then 
            temp:=MyMaximalSubgroupsUpToConjugacy(G,maxClasses,n);
        fi;
        for sub in temp do
            if MyOrder(sub) in [n,2*n,3*n,6*n]  then
                AddSet(res,sub);
            fi;
        od;
        classes:=temp;
    od;
    return res;
end;
AllCandidatesOfAutomorphismGroups_MagmaCTF:=function(G,n)
    local g;
    return Filtered(AllCandidatesOfAutomorphismGroups_MagmaCT(G),g->Order(g)=n);
end;

ApproximateOrderOfGroup:=function(group,nrV)
  local gen,n,k,i;
  k:=8;
  gen:=GeneratorsOfGroup(group);
  n:=Int(Length(gen)/k);
  for i in [1..Int(nrV/k)] do
  Print(n*i,"\n");
    if Order(Group(gen{[1..n*i]}))>=6*nrV then 
      return true;
    fi;
  od;
  if Order(group)<=6*nrV then 
    return true;
  fi;
  return false;
end;

findPath:=function(digraph,edge,len,edges)
    local g,paths,tempP,path,j,v,i,temp,remaining_neigh;
    paths:=[edge];
    for i in [3..len] do
        tempP:=[];
        for path in paths do 
            v:=Last(path);
            temp:=Filtered(edges,g->v in g);
            
            remaining_neigh:=Difference(Union(temp),[path[Length(path)-1], v]);
            for j in remaining_neigh do
                temp:=ShallowCopy(path);
                Add(temp,j);
                Add(tempP,temp);
            od;
        od;
        paths:=tempP;
    od;
    return Filtered(paths,g->Length(g{[1..Length(g)-1]})=Length(g)-1);
end;

IsCycleDoubleCover:=function(edgesof_v1, cycles)
  local g,e,bool,tempcycles;
  bool:=true;
  tempcycles:=Filtered(cycles,g->1^g<>1);
  Print(edgesof_v1,"\n");
  for e in edgesof_v1 do 
  Print("check", e,"\n");
    if Length(Filtered(tempcycles,g->Set(e) in  [Set([e[1],e[1]^g]) , Set([e[1],e[1]^(g^(-1))])]))<>2 then
      return false;
    fi;
  od;
  return bool;
end;


BindGlobal("__SimplicialSurfaceByUmbrellaDescriptor",function(umbdesc,n)
    local g,bool,v,umb,vof,f,voe,facesOfV;
    vof:=List([1..n],i->[]);
    for v in [1..Length(umbdesc)] do
        umb:=umbdesc[v];
        bool:=true;
        f:=1;
        while bool do
            if f^umb <> f then
                bool:=false;
            else  
                f:=f+1;
            fi;
        od;## MovedPointsPerm(umb)[1];
        facesOfV:=List([1..Order(umb)],j->f^(umb^j));
        for f in facesOfV do
            AddSet(vof[f],v);
        od;
    od;
    voe:=Union(List(vof,g->[Set(g{[1,2]}),Set(g{[1,3]}),Set(g{[2,3]})])); ###Combinations 
    if Length(voe)=3/2*n then
        Print("construction\n"); 
        return SimplicialSurfaceByVerticesInFacesNC(vof);
        Print("construction stop\n"); 
    else
        return fail; 
    fi;
end);


BindGlobal("__SimplicialSurfaceByUmbrellaDescriptor2",function(umbdesc,n,order)
    local g,bool,v,umb,vof,f,voe,facesOfV;
    vof:=List([1..n],i->[]);
    for v in [1..Length(umbdesc)] do
        umb:=umbdesc[v];
        bool:=true;
        f:=1;
        while bool do
            if f^umb <> f then
                bool:=false;
            else  
                f:=f+1;
            fi;
        od;## MovedPointsPerm(umb)[1];
        facesOfV:=List([1..Order(umb)],j->f^(umb^j));
        for f in facesOfV do
            AddSet(vof[f],v);
        od;
    od;
    voe:=Union(List(vof,g->[Set(g{[1,2]}),Set(g{[1,3]}),Set(g{[2,3]})])); ###Combinations 
    if Length(voe)=3/2*n then
        voe:=Append(voe,List(voe,g->[g[2],g[1]]));
        d:=DigraphByEdges(voe);
        aut:=AutomorphismGroup(d);
        if MyOrder(aut)=order then
            return [vof,aut];
        else
            return fail; 
        fi;
    else
        return fail;
    fi;
end);



FaceEdgeType:=function(surface)
    local g,vof,umb,sigma,temp,v,autV,lu,orbitsV,t1,t2,t3,autF,ordS,t,ordStab,i,deg,autE,orbitsE,orbitsF;
    if not IsVertexFaithful(surface) then
        return fail;
    fi;
    Print("autE\n"); 
    autE:=AutomorphismGroupOnEdges(surface);
   # autE:=AutE(surface);
    Print("autE stop\n");  
    orbitsE:=Orbits(autE);
    Print("autF\n"); 
    autF:=AutomorphismGroupOnFaces(surface);
   # autF:=AutF(surface);
    Print("autF stop\n"); 
    orbitsF:=Orbits(autF);
    ordS:=Order(autF)/NumberOfEdges(surface);
    t:=[Length(orbitsF),ordS];
    if Length(Orbits(autE))<>1 then
        return fail;
    fi; 
    if t in [[2,2],[1,4],[2,1]] then 
        return t;
    fi;
    umb:=UmbrellaPathOfVertex(surface,1);
        umb:=ShallowCopy(FacesAsList(umb));
    if t=[1,2] then
        Append(umb, [umb[1]]); 
        lu:=Length(umb);
        temp:=Filtered(autF,g->List([1..lu-1],i->umb[i]^g)=umb{[2..lu]});
        if temp<>[] then 
       	    return [1,2,1];
       	elif temp=[] then
       	    return [1,2,2];
        else 
            Error("vertex face type [1,2]");
       	fi;
    fi;
    return fail;
end;

IsomorphismRepresentativesDigraph:=function(surfaces)
    local g,res,len,digraphs,i,j,d1,d2,bool;
    res:=[1];
    len:=Length(surfaces);
    digraphs:=List(surfaces,g->EdgeDigraphsGraph(g));
    for i in [2..len] do
        bool:=true;
        for j in res do
            d1:=digraphs[i];
            d2:=digraphs[j];
            if DigraphNrVertices(d1)=DigraphNrVertices(d2) then  
                if MyOrder(AutomorphismGroup(d1))=MyOrder(AutomorphismGroup(d2)) then
                    if IsIsomorphicDigraph(digraphs[j],digraphs[i]) then 
                        bool:=false;
                    fi;
                fi;
            fi;
        od;
        if bool then 
            Add(res,j);
        fi;
    od;
    return surfaces{res};
end;

AutE:=function(s)
    local g,vof,voe,n,aut,gen,new_gen,i,temp;
    if not IsVertexFaithful(s) then
        return fail;
    fi;

    vof:=Set(VerticesOfFaces(s));
    voe:=VerticesOfEdges(s);
    n:=Length(voe);
    l:=[1..n];
    d:=EdgeDigraphsGraph(s);
    aut:=AutomorphismGroup(d);
    aut:=Stabiliser(aut,Set(vof),OnSetsSets);
    gen:=GeneratorsOfGroup(aut);
    new_gen:=[];
    for g in gen do
        temp:=List(voe,e->Set([e[1]^g,e[2]^g]));
        temp:=List(temp,e->Position(voe,e));        
        Add(new_gen,PermList(temp));
    od;
    if Length(new_gen)>0 then 
        return Group(new_gen);
    else
        return Group(());
    fi;
end;

AutF:=function(s)
    local g,vof,lvof,n,aut,gen,new_gen,i,temp,f;
    if not IsVertexFaithful(s) then
        return fail;
    fi;
    vof:=Set(VerticesOfFaces(s));
    lvof:=VerticesOfFaces(s);
    n:=Length(vof);
    l:=[1..n];
    d:=EdgeDigraphsGraph(s);
    aut:=AutomorphismGroup(d);
    aut:=Stabiliser(aut,Set(vof),OnSetsSets);
    gen:=GeneratorsOfGroup(aut);
    new_gen:=[];
    for g in gen do
        temp:=List(lvof,f->Set([f[1]^g,f[2]^g,f[3]^g]));
        temp:=List(temp,f->Position(lvof,f));        
        Add(new_gen,PermList(temp));
    od;
    if Length(new_gen)>0 then 
        return Group(new_gen);
    else
        return Group(());
    fi;
end;


test:=function()
    local i,s,G1,G2,G12,G22,l;
    for i in [2..14] do
        l:=AllSimplicialSpheres(2*i);
        Print(i,"\n");
        for s in l do 
            G1:=AutomorphismGroupOnFaces(s);
            G2:=AutomorphismGroupOnEdges(s);
            G12:=AutF(s);
            G22:=AutE(s);
            if G1 <> G12 or G2<> G22 then 
                Error();                
            fi;
        od;
    od;
    return true;
end;






