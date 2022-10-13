#!/usr/bin/env python
# coding: utf-8

# In[57]:


# Weight algorithm for type ADE
# Conventions are the same as Bourbaki, for example,
# Type E convention 1 3 4 5 6 7 8
#                       2

# Input under above convention if type E
J1=[1,3,5,7];
J2=[2,4,6,8];
Type="E";n=8;
D=DynkinDiagram([Type, n]);
# Main program

from sage.combinat.root_system.dynkin_diagram import DynkinDiagram_class

def weight(Type, globaln, D):
    #return the weight of chunks.
    n=D.rank();
    intrinsicType=D.cartan_matrix().cartan_type().type();
#     print(D,intrinsicType)
    if Type=="A":
        return (n,0,"A");
    if Type=="D":
        if intrinsicType=="A":
            if Set(D.index_set())==Set([globaln-2,globaln-1,globaln]): # type D3 case.
                return (2*n-2,0,"D");
            return (n,0,"A");
        else:
            return (2*n-2,0,"D");
    if Type=="E":
        if intrinsicType=="A":
            if Set([2,4]).issubset(Set(D.index_set())):
                if n>=3:
                    return (n,1,"A")  # A^# case;
                elif n==2:
                    return (n,-1,"A"); # A^b case;
            return (n,0,"A");
        if intrinsicType=="D":
            return (2*n-2,0,"D")
        if intrinsicType=="E":
            return (100,0,"E") # weight is infinity for type E chunks.

def disjointChunks(dynkin,E,i,C,P,maxLen): # E is the union of all chunk-index of D.
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
            if D.subtype(Set(j[0]).union(Set(x[0]))).is_connected()==True: # the new connected chunk is not disjoint.
                f=False;
                break;
        if f:
            dynkin.append(x);
            P,maxLen=disjointChunks(dynkin,E.union(Set(x[0])),i+1,C,P,maxLen); # add the new chunk.
            dynkin.pop();
    P,maxLen=disjointChunks(dynkin,E,i+1,C,P,maxLen); # do not add the new chunk.
    return P,maxLen;
    
def weightAlg(Type, D,n , J1, J2,J):
    if Set(J)==Set(J1) or Set(J)==Set(J2):
#         print("jump!!")
        return [];
    L1=D.subtype(J1);
    L2=D.subtype(J2);
    index1=DynkinDiagram_class(L1).strongly_connected_components();
    index2=DynkinDiagram_class(L2).strongly_connected_components();
#     print(L1.index_set())
    weight1=[];
    weight2=[];
    maxWeight=0;
    for i in index1:
        w=weight(Type,n, L1.subtype(i))
        weight1.append(w);
        if w[0]>maxWeight:
            maxWeight=w[0];
    for i in index2:
        w=weight(Type,n, L2.subtype(i))
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
            
    # Step 2: finding all disjoint dominant chunks.
    P,temp=disjointChunks([],Set([]),0,C,[],0);
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
            extraRoot=[];
            if Type=="D":
                extraRoots=[n,n-1];
            if Type=="E":
                extraRoots=[2];
            if extraRoot!=[]:
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
#                                     print("A^# case");
                                    f=True;
                                    dominant_collection=d;
                                    break;
                        if not f:
                            P1=copy(P);
                            for d in P:
                                for l in d:
                                    if l[2][1]==-1:       # A^b case  
#                                         print("A^b case")
                                        P1.remove(d);
                            if len(P1)>0:
                                P=P1;
        
    if dominant_collection==[]:    # 4. the rest choices are all ok.
        dominant_collection=P[0];
    dominants=Set({});
    for d in dominant_collection:
        dominants=dominants.union(Set(d[0]));
    dominants=list(dominants)
    kill_list=[];
    for i in D.index_set():
        if not (i in dominants):
            f=False;
            for j in dominants:
                if D.subtype(Set([i]).union(Set([j]))).is_connected():
#                     print(i,j)
                    f=True;
            if f:
                kill_list.append(i);
                if i in J1:
                    J1.remove(i);
                if i in J2:
                    J2.remove(i);
                J.remove(i);
    D=D.subtype(J);
#     print(kill_list)
#     print("dominant:",dominants,"remains=",J)
    for c in DynkinDiagram_class(D).strongly_connected_components():
        if len(c)==1:
            continue;
        D1=D.subtype(c);
        I1=list(Set(J1).intersection(Set(c)));
        I2=list(Set(J2).intersection(Set(c)));
        I=c;
#         print("before relabel=",D1,I1,I2,I,D1.cartan_matrix().cartan_type().__module__)
        if "type_relabel" in D1.cartan_matrix().cartan_type().__module__:
            label_inv=D1.cartan_matrix().cartan_type()._relabelling;
        else:
            label_inv={v:v for v in range(1,len(c)+1)};
        label = {v: w for w, v in label_inv.items()}
#         print(label)
        D1_relabel=D1.relabel(label)
        I1_relabel=[label[w] for w in I1];
        I2_relabel=[label[w] for w in I2];
#         print("after relabel=",D1_relabel.cartan_matrix().cartan_type().type(),'\n',D1_relabel.cartan_matrix().cartan_type().ascii_art(),D1_relabel.rank(),I1_relabel,I2_relabel,list(D1_relabel.index_set()))
        temp=weightAlg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,list(D1_relabel.index_set()));
        if temp!=[]:
            temp_1=[label_inv[w] for w in temp]
#             print("temp_1=",temp_1)
            kill_list=list(Set(kill_list).union(Set(temp_1)));
    return copy(kill_list);
#     print(index1,weight1)
kill_list=weightAlg(Type,D,n,J1,J2,list(D.index_set()))
print("One possible J is",sorted(list(Set(D.index_set()).difference(Set(kill_list)))))

