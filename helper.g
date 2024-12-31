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
      remaining_neigh:=Difference(Union(temp),path);
      for j in remaining_neigh do
        temp:=ShallowCopy(path);
        Add(temp,j);
        Add(tempP,temp);
      od;
    od;
    paths:=tempP;
  od;
  return paths;
end;


IsCycleDoubleCover:=function(edgesof_v1, cycles)
  local g,e,bool;
  bool:=true;
  for e in edgesof_v1 do 
    if Length(Filtered(cycles,g->Set(e) in  [Set([e[1],e[1]^g]) , Set([e[1],e[1]^(g^(-1))])]))<>2 then
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
        return SimplicialSurfaceByVerticesInFacesNC(vof);
    else
        return fail; 
    fi;
end);



writeEdgeTransitiveSurfacesIntoFiles2:=function(n1,n2)
  local g,n,numbers,str,filestream,surf,surfaces,l,digraph,i,j,file,k,k2,vof,len;
  
  filestream:=["/Surfaces_With_Vertex_Face_Type_2_2",
               "/Surfaces_With_Vertex_Face_Type_2_1_Type_1",
               "/Surfaces_With_Vertex_Face_Type_2_1_Type_2"];
  filestream:=List(filestream,g->Concatenation("results",String(n1),"-",String(n2),g));
  numbers:=List([1..3],i->0);
  for n in List([n1/2..n2/2],i->2*i) do
    l:=AllCubicATGraphs(n);
    if l<>fail then 
      for digraph in l do
        surfaces:=AllEdgeTransitiveSurfacesOfGraph(digraph);
        if surfaces<>fail then
          for i in [1..3] do
            if surfaces[i]<> [] then
              k:=(numbers[i]-(numbers[i] mod 10))/10;
              k2:=(numbers[i] mod 10)+1;
              file:=Concatenation(filestream[i],"_File",String(k+1));
              for surf in surfaces[i] do
                str:=Concatenation("#SurfaceInfo: ",String(NumberOfVertices(surf))," Vertices, ",
                                              String(NumberOfEdges(surf))," Edges, ",
                                              String(NumberOfFaces(surf))," Faces, IsOrientable=",String(IsOrientable(surf)),
                                              "\nVertices of faces:\n vof",String(k2),":=[");
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
                str:=Concatenation(str,"\n #---------------------------------------------------\n\n");
                AppendTo(file,str);
              od;
              numbers[i]:=numbers[i]+Length(surfaces[i]);
            fi;
          od;
        fi;
      od;
    fi;
    n:=n+2;
  od;
  return numbers;
end;








selectSurfaces:=function(surfaces,nG,nE,nV)
    local temp,t,autE,autV,i,g;
    temp:=Filtered(surfaces,g->g<>fail);
    t:=[1..Length(temp)];
    if [nE,nV]<>[1,1] then 
        autE:=List(temp,g->AutomorphismGroupOnEdges(g));
        autV:=List(temp,g->AutomorphismGroupOnVertices(g));   
        t:=Filtered(t,i->Order(autE[i])=nG);
        t:=Filtered(t,i->Length(Orbits(autE[i],Edges(temp[i])))=nE);
        t:=Filtered(t,i->Length(Orbits(autV[i],Vertices(temp[i])))=nV);
    else
        t:=Filtered(t,i->Order(AutomorphismGroup(temp[i]))=3*nG);
    fi;
    if temp<>[] then
        return IsomorphismRepresentatives(temp{t});
    else
        return [];
    fi;
end;
