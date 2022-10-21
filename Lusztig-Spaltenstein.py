#!/usr/bin/env python
# coding: utf-8

# In[15]:


# Lusztig-Spaltenstein Algorithm
# Type E convention 1 3 4 5 6 7 8 same as Bourbaki
#                       2

# Input under above convention if type E
J=[1,2,3,4];
K=[1,2,3,5];
Type='E';n=8;

# Main program


# Lusztig_Spaltenstein algorithm

def Lusztig_Spaltenstein(i,conjugate,W,I,X,M,J,K):  
    # return J and K are conjugated or not (current position in I, conjugated or not, weyl group, I:I_i with I_0=J  I_n=K satisfying given conditions, record element used for conjugation, collection of all conjugates of J, # The elements used for conjugation, J,K): boolean whether J and K are conjugated.
    if Set(J)==Set(K):
        return True,M;
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
                print("The two parabolic subgroups are conjugate, with conjugation sequence as follows:");
                for l in range(len(I)-1):
                    print(Set(I[l]),"--", X[l],"-> ",end="");
                print(Set(I[len(I)-1]));
                return conjugate,M;

            # detect if L is already inside the conjuation class of J, cutting redundant search.
            selfloop=False;
            for l in range(len(M)):
                if (Set(L)==Set(M[l])):
                    selfloop=True;
            if selfloop:
                continue;
            I.append(L);
            M.append(L); # memorize all conjugates of J.
            conjugate,M=Lusztig_Spaltenstein(i+1,conjugate,W,I,X,M,J,K);
            if conjugate:
                return conjugate,M;
            I.pop();
            X.pop();
    return conjugate,M;   

W=WeylGroup([Type,n],prefix="s",implementation="permutation");
flag,M=Lusztig_Spaltenstein(0,False,W,[J],[],[J],J,K);
if not(flag):
    print("The two parabolic subgroups are not conjugate.");
    print("All conjugates of ",J," are", M);

