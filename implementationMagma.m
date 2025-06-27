ConjugateFreeListFromClasses:=function(G,classes)
    local res,i,j,k,group,len,bool,temp,tempOrders;
    res:=classes[1];
    orders:=[Order(g): g in res];
    for i in [2..#classes] do
        temp:=[];
        tempOrders:=[];
        for j in [1..#classes[i]] do
            bool:=true;
            k:=1;
            group:=classes[i][j];
            len:=#res;
            ord:=Order(group);
            while bool and k le len do
                if orders[k] eq ord then
                    if IsConjugate(G,res[k],group) then
                        bool:=false;
                    end if;
                end if;
                k:=k+1;
            end while;
            if bool then
                tempOrders:=Append(tempOrders,ord);
                temp:=Append(temp,group);
            end if;
        end for;
	res:=res cat temp;
        orders:=orders cat tempOrders;
    end for;
    return res;
end function;


SubgroupsConjugacyList:=function(G,l)
    local res,i,j,k,H,len,bool,temp,tempOrders;
    orders:=[Order(g): g in l];
    res:=[1];
    for i in [2..#l] do
        H:=l[i];
        bool:=true;
        j:=1;
        t:=[k: k in res | Order(H) eq orders[k] ];
        len:=#t;
        if len eq 0 then 
            res:=Append(res,i);
        else
            while bool and j le len do
                if IsConjugate(G,l[t[j]],H) then
                    bool:=false;
                end if;
                j:=j+1;
            end while;
            if bool then
                res:=Append(res,i);
            end if;
        end if;
    end for;
    return [l[k]: k in res];
end function;


AllCandidatesOfAutomorphismGroupsOfEdgeTransitiveSurfaces_MagmaCT:=function(G,ed)
    local g,n,nE,res,lenO,edge,e,orbit,classes,temp,i,sub,class,t,maxsubgroups,maximalsubgroups;
    edge:=Seqset(ed);
    orbit:=Orbit(G,edge);
    lenO:=#orbit;
    sup:=Support(G);
    n:=#sup;
    res:=[];
    if sup ne { 1 .. n} then
        return false;
    end if;
    nE:=3/2*n;
    if nE ne lenO then
        return false;
    end if;
    if Order(G) in [1*nE,2*nE,4*nE] then
        res:=Append(res,G);
    end if;
    classes:=[G];
    while classes ne [] do
        temp:=[];
        maxClasses:=[MaximalSubgroups(sub): sub in classes];
        maxClasses:=[[sub`subgroup: sub in class ] : class in maxClasses];
        maxClasses:=[[sub : sub in class | #Orbit(sub,edge) eq nE]: class in maxClasses]; 
        maxClasses:=[class: class in maxClasses|class ne []];
        if maxClasses ne [] then
            temp:=ConjugateFreeListFromClasses(G,maxClasses);
        end if;
        for sub in temp do
            if Order(sub) in [1*nE,2*nE,4*nE]  then
                res:=Append(res,sub);
            end if;
        end for; 
        classes:=temp;
    end while;
    
    if res ne [] then
        return SubgroupsConjugacyList(G,res);
    else
        return [];
    end if;
end function;
