MaximalSubgroupsUpToConjugacyGAP:=function(G,classes)
    local res,i,j,k,group,len,bool,temp,tempOrders,orders,ord;
    res:=classes[1];
    orders:=List(res,g->Order(g));
    for i in [2..Length(classes)] do
        temp:=[];
        tempOrders:=[];
        for j in [1..Length(classes[i])] do
            bool:=true;
            k:=1;
            group:=classes[i][j];
            len:=Length(res);
            ord:=Order(group);
            while bool and k <= len do
                if orders[k] = ord then
                    if IsConjugate(G,res[k],group) then
                        bool:=false;
                    fi;
                fi;
                k:=k+1;
            od;
            if bool then
                tempOrders:=Add(tempOrders,ord);
                temp:=Add(temp,group);
            fi;
        od;
	res:=Append(res,temp);
        orders:=Append(orders,tempOrders);
    od;
    return res;
end;



AllCandidatesOfAutomorphismGroupsOfEdgeTransitiveSurfaces_GAPCT:=function(G,edge)
    local g,n,res,classes,maxClasses,temp,i,sub,class,t,maxsubgroups,maximalsubgroups,nE;
    n:=NrMovedPoints(G);
    nE:=3/2*n;
    res:=[];
    if Order(G) in [nE,2*nE] then
        res:=Add(res,G);
    fi;
    classes:=[G];
    while classes <> [] do
        temp:=[];
        maxClasses:=List(classes,sub->MaximalSubgroupClasses(sub));
       ## maxClasses:=List(maxXlasses,class->Representative(class));
        maxClasses:=List(maxClasses,Filtered(class,sub->Length(Orbit(sub,edge,OnSets))=nE));
        maxClasses:=Filtered(maxClasses,g->g<>[]);
        if maxClasses <> [] then
            temp:=MaximalSubgroupsUpToConjugacyGAP(G,maxClasses);
        fi;
        for sub in temp do
            if Order(sub) in [nE,2*nE]  then
                res:=Add(res,sub);
            fi;
        od; 
        classes:=temp;
    od;
    return res;
end;
