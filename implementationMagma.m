MaximalSubgroupsUpToConjugacyMagma:=function(G,classes)
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
            while bool and k lt len do
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



AllCandidatesOfAutomorphismGroupsOfEdgeTransitiveSurfaces_MagmaCT:=function(G,edge)
    local g,n,res,classes,temp,i,sub,class,t,maxsubgroups,maximalsubgroups,nE;
    n:=#Support(G);
    nE:=3/2*n;
    res:=[];
    if Order(G) in [nE,2*nE] then
        res:=Append(res,G);
    end if;
    classes:=[G];
    while classes ne [] do
        temp:=[];
        maxClasses:=[MaximalSubgroups(sub): sub in classes];
        maxClasses:=[[sub`subgroup: sub in class ] : class in maxClasses];
        maxClasses:=[[sub : sub in class | #Orbit(sub,{edge[1],edge[2]}) eq nE]: class in maxClasses];
        maxClasses:=[class: class in maxClasses|class ne []];
        if maxClasses ne [] then
            temp:=MaximalSubgroupsUpToConjugacy(G,maxClasses);
        end if;
        for sub in temp do
            if Order(sub) in [nE,2*nE]  then
                res:=Append(res,sub);
            end if;
        end for; 
        classes:=temp;
    end while;
    return res;
end function;
