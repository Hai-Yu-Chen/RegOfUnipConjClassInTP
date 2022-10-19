#!/usr/bin/env python
# coding: utf-8

# In[167]:


# Pattern algorithm for type ADE
# Conventions are the same as Bourbaki, for example,
# Type E convention 1 3 4 5 6 7 8
#                       2

# Input under above convention if type E
J1=[1,2,3,4];
J2=[5,6,7,8];
Type="E";n=8;
D=DynkinDiagram([Type, n]);

# main program.
from sage.combinat.root_system.dynkin_diagram import DynkinDiagram_class











def weight(globalType, globaln, D): # return the weigtht of a chunk(type of original dynkin diagram, rank of original dynkin diagram, current chunk)
    n=D.rank();
    Type=D.cartan_matrix().cartan_type().type(); # the intrisic type of current dynkin subdiagram.
    if globalType=="A":
        return (n,0,"A");
    if globalType=="D":
        if Type=="A": # type A chunk.
            if Set(D.index_set())==Set([globaln-2,globaln-1,globaln]): # type D3 case. Note that here we rely on the index set.
                return (2*n-2,0,"D");
            return (n,0,"A");
        else: # type D chunk.
            return (2*n-2,0,"D"); 
    if globalType=="E":
        if Type=="A": # type A chunk.
            if Set([2,4]).issubset(Set(D.index_set())): # Note that here we rely on the index set.
                if n>=3:
                    return (n,1,"A")  # A^# case;
                elif n==2:
                    return (n,-1,"A"); # A^b case;
            return (n,0,"A");
        if Type=="D": 
            return (2*n-2,0,"D")
        if Type=="E":
            return (100,0,"E") # weight is infinity for type E chunks.

def disjointChunks(dynkin,E,i,C,P,maxLen,D): # return all maximal selection P of disjoint chunks P(current selection, the union of all chunk-index of D,current position in C, all dominant chunks, maximal selections,length of maximal selections) 
    if i>=len(C):
        if len(dynkin)>=maxLen:
            if len(dynkin)>maxLen:
                maxLen=len(dynkin);
                P=[];
            P.append(copy(dynkin));
        return P,maxLen;
    x=C[i];
    if Set(x[0]).intersection(E).is_empty()==True:
        f=True;
        for j in dynkin:
            if D.subtype(Set(j[0]).union(Set(x[0]))).is_connected()==True: # the new connected chunk is not disjoint to dynkin.
                f=False;
                break;
        if f: # if disjoint, we can add the new chunk x.
            dynkin.append(x);
            P,maxLen=disjointChunks(dynkin,E.union(Set(x[0])),i+1,C,P,maxLen,D); 
            dynkin.pop();
    P,maxLen=disjointChunks(dynkin,E,i+1,C,P,maxLen,D); # we ignore the new chunk x.
    return P,maxLen;
    
def weightAlg(Type, D,n , J1, J2,J): # the weight algorithm on labeled dynkin diagram D,J1,J2(type of dynkin diagram, dynkin diagram, rank, label J1, label J2, union of all labels/support)
    if Set(J)==Set(J1) or Set(J)==Set(J2):  # the whole diagram is uniformly labeled.
        return [];
    L1=D.subtype(J1);
    L2=D.subtype(J2);
    index1=DynkinDiagram_class(L1).strongly_connected_components();
    index2=DynkinDiagram_class(L2).strongly_connected_components();
    
    if len(index1)==1:
        index1=[J1];
    if len(index2)==1:
        index2=[J2];
    weight1=[];
    weight2=[];
    maxWeight=0;
    for i in index1:
        w=weight(Type,n, D.subtype(i))
        weight1.append(w);
        if w[0]>maxWeight:
            maxWeight=w[0];
    for i in index2:
        w=weight(Type,n, D.subtype(i))
        weight2.append(w);
        if w[0]>maxWeight:
            maxWeight=w[0];
    
    # Step 1: finding all dominant chunks.
    C=[];# format: (root_index, label, (weight, type))
    for i in range(len(weight1)):
        if weight1[i][0]==maxWeight:
            C.append((index1[i],1,weight1[i]));
    for i in range(len(weight2)):
        if weight2[i][0]==maxWeight:
            C.append((index2[i],2,weight2[i]));
    # Step 2: finding all selections P of dominant chunks.
    P,temp=disjointChunks([],Set([]),0,C,[],0,D); # get the list of maximal selections.
    dominant_collection=[];
    if len(P)==1:
        dominant_collection=P[0];
    else: # Step 3: tie breaking.
        # 1. choose as many type A as possible.
        P1=copy(P);
        for d in P:
            for l in d:
                if l[2][2]!="A": # the type of chunks
                    P1.remove(d);
        if len(P1)>0:
            P=P1;
        if len(P)==1:
            dominant_collection=P[0];
        else:
            # 2. choose those not adjacent to extra root.
            extraRoots=[];
            if Type=="D":
                extraRoots=[n,n-1];
            if Type=="E":
                extraRoots=[2];
            if extraRoots!=[]:
                P1=copy(P);
                for j in extraRoots:
                    for d in P:
                        f=False;
                        for l in d:
                            if (j in l[0])==True:
                                break;
                            if D.subtype(Set(l[0]).union(Set([j]))).is_connected()==True: # this selection of chunks is adjacent to extra root.
                                f=True;
                        if f:
                            if d in P1:
                                P1.remove(d);
                
                if len(P1)>0:
                    P=P1;
                if len(P)==1:
                    dominant_collection=P[0];
                else:
                    # 3. A^# and A^b cases.
                    if Type=="E":
                        f=False;
                        for d in P:
                            for l in d:
                                if l[2][1]==1:    # A^# case.
                                    f=True;
                                    dominant_collection=d;
                                    break;
                        if not f:
                            P1=copy(P);
                            for d in P:
                                for l in d:
                                    if l[2][1]==-1:       # A^b case  
                                        P1.remove(d);
                            if len(P1)>0:
                                P=P1;
        
    if dominant_collection==[]:    # 4. the rest choices are all ok.
        dominant_collection=P[0];
    dominants=Set({});
    for d in dominant_collection:
        dominants=dominants.union(Set(d[0]));
    dominants=list(dominants)
    
    # kill the roots adjacents to the dominant selection.
    kill_list=[];
    for i in D.index_set():
        if not (i in dominants):
            f=False;
            for j in dominants:
                if D.subtype(Set([i]).union(Set([j]))).is_connected():
                    f=True;
            if f:
                kill_list.append(i);
                if i in J1:
                    J1.remove(i);
                if i in J2:
                    J2.remove(i);
                if i in J:
                    J.remove(i);
                    
    # induction with the subdiagram.
    D=D.subtype(J);
    for c in DynkinDiagram_class(D).strongly_connected_components():
        if len(c)==1:
            continue;
        D1=D.subtype(c);
        I1=list(Set(J1).intersection(Set(c)));
        I2=list(Set(J2).intersection(Set(c)));
        I=c;
        if "type_relabel" in D1.cartan_matrix().cartan_type().__module__: # need relabeling
            label_inv=D1.cartan_matrix().cartan_type()._relabelling;
        else:
            label_inv={v:v for v in range(1,len(c)+1)}; # trivial relabeling
        label = {v: w for w, v in label_inv.items()}
        D1_relabel=D1.relabel(label)
        I1_relabel=[label[w] for w in I1];
        I2_relabel=[label[w] for w in I2];
        I=list(Set(I1_relabel).union(Set(I2_relabel)));
        temp=weightAlg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,I);
        if temp!=[]:
            temp_1=[label_inv[w] for w in temp]
            kill_list=list(Set(kill_list).union(Set(temp_1)));
    return copy(kill_list);












































def branch(x,last_root,I1,I2,J,D,m,result):
    # Find m number of I1 vertices starting from x protected by I2(starting point, last step, main branch label, protection label, all labeled roots, dynkin diagram, steps to remain, record history root): return successful or not. 
    nbhd=[]; # the neighbour roots of x except x itself and last root.
    next_root=[];
    for k in J:
        if k!=x and (not(k in last_root)) and D.subtype(Set([k,x])).is_connected()==True: # k is the neighbour of x.
            if k in I1:
                next_root.append(k);
            nbhd.append(k);
#     print("x=",x,"lastroot=",last_root,"nbhd=",nbhd,"next root=",next_root,"I1=",I1,"I2=",I2,"J=",J,"m=",m);
    if m<=1: # final step.
        flag=True;
        for k in nbhd:
            if (not(k in I2)): # protection check.
                flag=False;
        if flag:
            return True,result;
        else:
            return False,[];
    
    # not final step.
    for y in next_root:
        flag=True;
#         print(y,nbhd)
        for k in nbhd:
            if (not(k in I2)) and (k!=y): # protection check except next root.
#                 print("k=",k)
                flag=False;
#                 print(k,I2,y,flag,"###############")
        if flag:
            result.append(y);
            temp,temp1=branch(y,[x],I1,I2,J,D,m-1,result);
            if temp:
                return True,temp1;
            result.pop();
    return False,[]; # return false if no next roots are successful.
def pattern1(x,y,J1,J2,J,D,m): # root x has label J1 and y has J2, we want to find m number of J1 dominant m number of J2 pattern with J1 protection.
    flag1,negative_branch=branch(y,[x],J2,J1,J,D,m,[y])
    flag2,positive_branch=branch(x,[y],J1,J1,J,D,m,[x]);
    if flag1 and flag2:
        for i in positive_branch:
            for j in negative_branch:
                if D.subtype(Set([i,j])).is_connected()==True:
                    return True,[j];
    return False,[];

def pattern2(x,y,J1,J2,J,D): # root x has label J1 and y has J2, we want to find m number of J1 dominant m number of J2 pattern with J1 protection.
    flag1,negative_branch=branch(y,[x],J2,J1,J,D,2,[2,y])
#     print(flag1,negative_branch);
#     print("!!!!!!!!!",x,y,J1,J1,J,[x])
    flag2,positive_branch=branch(x,[2,y],J1,J1,J,D,3,[x]);
#     print(flag2,positive_branch);
    if flag1 and flag2:
        for i in positive_branch:
            for j in negative_branch:
                if D.subtype(Set([i,j])).is_connected()==True and j!=2:
                    return True,[2,j];
    return False,[];

def pattern_alg(Type, D, n,J1,J2,J):
    if Set(J)==Set(J1) or Set(J)==Set(J2):  # the whole diagram is uniformly labeled.
        return [];
    kill_list=[];
    if Type=="E" and n==8: # pattern 4 for type E8.
#         print(Set(J1),Set([1,2,3,4]))
        if Set(J1)==Set([1,2,3,4]) and Set(J2)==Set([5,6,7,8]):
            kill_list.append(5);
            return kill_list;
        if Set(J2)==Set([1,2,3,4]) and Set(J1)==Set([5,6,7,8]):
            kill_list.append(5);
            return kill_list;
    quit=False;
    for i in J:
        if quit: break;
        count1=0;
        count2=0;
        nbhd=[]
        for j in J:
            if j!=i and D.subtype(Set([i,j])).is_connected()==True: # j is the neighbour of i.
                nbhd.append(j);
#         print(i,nbhd,count2)
        for j in nbhd:
            if quit: break;
            if (i in J1) and (j in J2): # j is the neighbour of i with opposite sign.
                for m in [1,2,3]:
                    flag,result=pattern1(i,j,J1,J2,J,D,m); # use J1 dominant J2 pattern 1-3.
                    if flag: 
                        kill_list=kill_list+copy(result);
                        quit=True;
                if (Type=="E") and (4 in J1) and (2 in J2): # pattern 4.
                    flag,result=pattern2(i,j,J1,J2,J,D);
                    if flag: 
                        kill_list=kill_list+copy(result);
                        quit=True;
            if (i in J2) and (j in J1): 
                for m in [1,2,3]:
                    flag,result=pattern1(i,j,J2,J1,J,D,m); # use J2 dominant J1 pattern.
                    if flag: 
                        kill_list=kill_list+copy(result);
                        quit=True;
                if (Type=="E") and (4 in J2) and (2 in J1): # pattern 4.
                    flag,result=pattern2(i,j,J2,J1,J,D);
                    if flag: 
                        kill_list=kill_list+copy(result);
                        quit=True;
            
#     print(kill_list)     
    J1=list(Set(J1).difference(Set(kill_list)));
    J2=list(Set(J2).difference(Set(kill_list)));
    J=list(Set(J).difference(Set(kill_list)));
    # induction with the subdiagram.
    D=D.subtype(J);
    for c in DynkinDiagram_class(D).strongly_connected_components():
        if len(c)==1:
            continue;
        D1=D.subtype(c);
        I1=list(Set(J1).intersection(Set(c)));
        I2=list(Set(J2).intersection(Set(c)));
        I=c;
        if "type_relabel" in D1.cartan_matrix().cartan_type().__module__: # need relabeling
            label_inv=D1.cartan_matrix().cartan_type()._relabelling;
        else:
            label_inv={v:v for v in range(1,len(c)+1)}; # trivial relabeling
        label = {v: w for w, v in label_inv.items()}
        D1_relabel=D1.relabel(label)
        I1_relabel=[label[w] for w in I1];
        I2_relabel=[label[w] for w in I2];
        I=list(Set(I1_relabel).union(Set(I2_relabel)));
        if D1_relabel.cartan_matrix().cartan_type().type()=="E":
            temp=pattern_alg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,I);
        else:
            temp=weightAlg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,I);
        if temp!=[]:
            temp_1=[label_inv[w] for w in temp];
#             print(temp_1);
            kill_list=list(Set(kill_list).union(Set(temp_1)));
    return copy(kill_list);
    
J=list(Set(J1).union(Set(J2)));
# print("One possible J is",sorted(list(Set(list(Set(J1).union(Set(J2)))).difference(Set(pattern_alg(Type,D,n,copy(J1),copy(J2),copy(J)))))));


# below are testing code.
def testing(J1,J2,i,Type,D,n):
    if i>n:
#         print(Type,D,n,copy(J1),copy(J2),copy(J))
        result=pattern_alg(Type,D,n,copy(J1),copy(J2),copy(list(Set(J1).union(Set(J2)))));
        print(J1,J2,"J=",sorted(list(Set(list(Set(J1).union(Set(J2)))).difference(Set(result)))));
        return;
    J1.append(i);
    testing(J1,J2,i+1,Type,D,n)
    J1.pop();
    J2.append(i);
    testing(J1,J2,i+1,Type,D,n)
    J2.pop();
#     testing(J1,J2,i+1,Type,D,n)
for Type in ['E']:
    for n in [6,7,8]:
        print("\n\n testing type",Type, n)
        testing([1],[],2,Type,DynkinDiagram([Type, n]),n)

