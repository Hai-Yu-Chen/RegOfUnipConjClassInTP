#!/usr/bin/env python
# coding: utf-8

# In[7]:


# Weight algorithm for type ADE
# Conventions are the same as Bourbaki, for example,
# Type E convention 1 3 4 5 6 7 8
#                       2

# Input under above convention if type E
J1=[1,2,3,4];
J2=[5,6,7,8];
Type="E";n=8;
D=DynkinDiagram([Type, n]);

# Main program

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
J=list(Set(J1).union(Set(J2)));
kill_list=weightAlg(Type,D,n,copy(J1),copy(J2),copy(J))
print("One possible J is",sorted(list(Set(J).difference(Set(kill_list)))))




# below are testing code.
# def testing(J1,J2,i,Type,D,n):
#     if i>n:
#         result=sorted(list(Set(list(Set(J1).union(Set(J2)))).difference(Set(weightAlg(Type,D,n,copy(J1),copy(J2),list(Set(J1).union(Set(J2))))))));
#         print(J1,J2,"J=",result);
#         return;
#     J1.append(i);
#     testing(J1,J2,i+1,Type,D,n)
#     J1.pop();
#     J2.append(i);
#     testing(J1,J2,i+1,Type,D,n)
#     J2.pop();
#     testing(J1,J2,i+1,Type,D,n)
# for Type in ['A','D','E']:
#     for n in [8]:
#         print("\n\n testing type",Type, n)
#         testing([1],[],2,Type,DynkinDiagram([Type, n]),n)

# to print dynkin diagran use print(D.cartan_matrix().cartan_type().ascii_art())

