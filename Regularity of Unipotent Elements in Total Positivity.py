#!/usr/bin/env python
# coding: utf-8

# In[5]:


# Conventions are the same as Bourbaki, for example,
# Type E convention 1 3 4 5 6 7 8
#                       2

# Input under above convention if type E
J1=[1,2,3,4];
J2=[5,6,7,8];
Type="E";n=6;
D=DynkinDiagram([Type, n]);

# main program.
from sage.combinat.root_system.dynkin_diagram import DynkinDiagram_class







# weight algorithm

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
        return [[]];
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
        dominant_collection.append(P[0]);
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
            dominant_collection.append(P[0]);
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
                    dominant_collection.append(P[0]);
                else:
                    # 3. A^# and A^b cases.
                    if Type=="E":
                        f=False;
                        for d in P:
                            for l in d:
                                if l[2][1]==1:    # A^# case.
                                    f=True;
                                    dominant_collection.append(d);
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
        dominant_collection+=P;
        
    totalKillList=[];
    D_copy=copy(D);
    J1_copy=copy(J1);
    J2_copy=copy(J2);
    J_copy=copy(J);
    for dominant_selection in dominant_collection:
        D=copy(D_copy);
        J1=copy(J1_copy);
        J2=copy(J2_copy);
        J=copy(J_copy);
        dominants=Set({});
        for d in dominant_selection:
            dominants=dominants.union(Set(d[0]));
        dominants=list(dominants);
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
        kill_list=list(Set(kill_list));
        D=D.subtype(J);
        subdiagram=False;
        kill_list=[kill_list];
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
            totalTemp=weightAlg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,I);
            newKillList=[];
            for temp in totalTemp:
                if temp!=[]:
                    temp_1=[label_inv[w] for w in temp];
                    subdiagram=True;
                    for j in kill_list:
                        newKillList.append(copy(list(Set(j).union(Set(temp_1)))));
            if newKillList!=[]:
                kill_list=newKillList;
                
        for j in kill_list:
            if not(j in totalKillList): 
                totalKillList.append(j);
    return copy(totalKillList);









































# pattern algorithm

def branch(x,last_root,I1,I2,J,D,m,result):
    # Find m number of I1 vertices starting from x protected by I2(starting point, last step, main branch label, protection label, all labeled roots, dynkin diagram, steps to remain, record history root): return successful or not. 
    nbhd=[]; # the neighbour roots of x except x itself and last root.
    next_root=[];
    for k in J:
        if k!=x and (not(k in last_root)) and D.subtype(Set([k,x])).is_connected()==True: # k is the neighbour of x.
            if k in I1:
                next_root.append(k);
            nbhd.append(k);
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
        for k in nbhd:
            if (not(k in I2)) and (k!=y): # protection check except next root.
                flag=False;
        if flag:
            result.append(y);
            temp,temp1=branch(y,[x],I1,I2,J,D,m-1,result);
            if temp:
                return True,temp1;
            result.pop();
    return False,[]; # return false if no next roots are successful.
def pattern1(x,y,J1,J2,J,D,m): # root x has label J1 and y has J2, we want to find m number of J1 dominant m number of J2 pattern with J1 protection: return vertices to be killed.
    flag1,negative_branch=branch(y,[x],J2,J1,J,D,m,[y])
    flag2,positive_branch=branch(x,[y],J1,J1,J,D,m,[x]);
    if flag1 and flag2:
        for i in positive_branch:
            for j in negative_branch:
                if D.subtype(Set([i,j])).is_connected()==True:
                    return True,[j];
    return False,[];

def pattern2(x,y,J1,J2,J,D): # root x has label J1 and y has J2, we want to find m number of J1 dominant m number of J2 pattern with J1 protection: return vertices to be killed.
    flag1,negative_branch=branch(y,[x],J2,J1,J,D,2,[2,y]);
    flag2,positive_branch=branch(x,[2,y],J1,J1,J,D,3,[x]);
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
    if Type=="E" and n==8: # pattern 5 for type E8.
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
            if (i in J2) and (j in J1): # switching labels J1 and J2.
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
        if D1_relabel.cartan_matrix().cartan_type().type()=="E": # if the remaining subdiagram is of Type E, we do pattern algorithm again.
            temp=pattern_alg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,I);
        else: # if of classical types, we do weight algorithm.
            temp=weightAlg(D1_relabel.cartan_matrix().cartan_type().type(),D1_relabel,D1_relabel.rank(),I1_relabel,I2_relabel,I);
            temp=temp[0];
        if temp!=[]:
            temp_1=[label_inv[w] for w in temp];
            kill_list=list(Set(kill_list).union(Set(temp_1)));
    return copy(kill_list);
    
# # test pattern algorithm individually.
# J=list(Set(J1).union(Set(J2)));
# print("One possible J is",sorted(list(Set(list(Set(J1).union(Set(J2)))).difference(Set(pattern_alg(Type,D,n,copy(J1),copy(J2),copy(J)))))));








# Lusztig_Spaltenstein algorithm

def Lusztig_Spaltenstein(i,conjugate,W,I,X,M,J,K):  
    # return J and K are conjugated or not (current position in I, conjugated or not, weyl group, I:I_i with I_0=J  I_n=K satisfying given conditions, record element used for conjugation, collection of all conjugates of J, # The elements used for conjugation, J,K): boolean whether J and K are conjugated.
    if Set(J)==Set(K):
        return True;
    for j in range(n):
        if (not ((j+1) in I[i])):

            L=copy(I[i]);
            L.append(j+1);
            x=W.long_element(index_set=I[i])*W.long_element(index_set=L); #longest coset representative.
            X.append(x);
            L.pop();

            # calculate x^-1*L*x and see if it is again standard parabolic.
            flag=False;
            for k in range(len(L)):
                y=x^-1*W.simple_reflection(L[k])*x;
                if y.length()!=1: #x^-1*L*x is not simple reflection
                    flag=True;
                    break;
                L[k]=int(str(y)[1:]);
            if flag:
                continue;
            if Set(L)==Set(K):
                conjugate=True;
                I.append(L);
#                 Uncomment following code if want detailed conjugation procedure.
#                 print("The two parabolic subgroups are conjugate, with conjugation sequence as follows:");
#                 for l in range(len(I)-1):
#                     print(Set(I[l]),"--", X[l],"-> ",end="");
#                 print(Set(I[len(I)-1]));
                return conjugate;

            # detect if L is already inside the conjuation class of J, cutting redundant search.
            selfloop=False;
            for l in range(len(M)):
                if (Set(L)==Set(M[l])):
                    selfloop=True;
            if selfloop:
                continue;
            I.append(L);
            M.append(L); # memorize all conjugates of J.
            conjugate=Lusztig_Spaltenstein(i+1,conjugate,W,I,X,M,J,K);
            if conjugate:
                return conjugate;
            I.pop();
            X.pop();
    return conjugate;   
    
    
    




# below are testing code for all cases in type=A/D/E,n=6-8.
def testing(J1,J2,i,Type,D,n):
    if i>n:
        print("J1=",J1,"J2=",J2)
        result_pattern=sorted(list(Set(list(Set(J1).union(Set(J2)))).difference(Set(pattern_alg(Type,D,n,copy(J1),copy(J2),copy(list(Set(J1).union(Set(J2)))))))));
        totalKillList=weightAlg(Type,D,n,copy(J1),copy(J2),list(Set(J1).union(Set(J2))));
        for kill_list in totalKillList:
            result_weight=sorted(list(Set(list(Set(J1).union(Set(J2)))).difference(Set(kill_list))));
            temp=Lusztig_Spaltenstein(0,False,WeylGroup(D.cartan_matrix().cartan_type(),prefix="s",implementation="permutation"),[result_weight],[],[result_weight],result_weight,result_pattern);
            if temp: 
                result_LS="conjugated";
            else:
                result_LS="not conjugated";
#                 print(J1,J2,"weight:",result_weight,"pattern:",result_pattern) #uncomment if only want not conjugated output.
            print("weight:",result_weight,"pattern:",result_pattern,"\n\t\t\t\t\t\t\t\t\t\t\t They are",result_LS);
        return;
    J1.append(i);
    testing(J1,J2,i+1,Type,D,n)
    J1.pop();
    J2.append(i);
    testing(J1,J2,i+1,Type,D,n)
    J2.pop();
#     testing(J1,J2,i+1,Type,D,n) # uncomment if want cases where J1 union J2 is not all vertices.
for Type in ['A','D','E']: # input all test types you want in the list here.
    for n in [6,7,8]: # input all test ranks you want in the list here.
        print("\n\n testing type",Type, n)
        testing([1],[],2,Type,DynkinDiagram([Type, n]),n)

