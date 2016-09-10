from sys import argv
from decimal import Decimal
import re
import collections
import itertools
import copy

class Variable:
    def __init__(self,name='',truth_val=''):
        self.name=name
        self.truth_val=truth_val

class BN:
    def __init__(self):
        # Dictionary of Node objects
        self.nodes=collections.OrderedDict()
        self.variables=[]

    def addNode(self,name,node):
        self.nodes[name]=node

    def addVars(self,var):
        self.variables.append(var)

class Node:
    def __init__(self):
        self.name = ''
        self.num_parents=0
        self.parent = []
        self.cpt = {}
        self.decision='F'

    def setName(self,name):
        self.name=name

    def setProb(self,pro):
        # 'pro' is a dictionary for storing probability values
        self.cpt=pro

    def getProb(self,comb):
        return self.cpt[comb]

    def setParent(self,par):
        self.parent=par
        if par is not None:
            self.num_parents=len(par)

def enumeration_helper(X,e,bn):
    Q={}
    #original query
    ecopy=copy.deepcopy(e)
    orig_len=len(X)
    #eg: X is [Demoralize, Infiltration] , e={Infiltration=+, LeakIdea=+}
    dct_indices=collections.OrderedDict()
    for count,sam in enumerate(X):
        if sam in e and bn.nodes[sam].decision=='T':
            dct_indices[count]=e[sam]
            X.remove(sam)
    numofqueryvars = len(X)
    lst = map(list, itertools.product(['+', '-'], repeat=numofqueryvars))
    comb = [('').join(l) for l in lst]
    for foo in comb:
        #extending e
        for i in range(numofqueryvars):
            ecopy[X[i]]=foo[i]   #extend e with xi
        Q[foo]=enumerate_all(bn,bn.variables,ecopy) #needs a normalized value * bn.nodes['utility'].cpt[foo[i]]
        #normalization
    addtn=sum(Q.values())
    for k in Q:
        new_val= Q[k]/addtn
        Q[k]=new_val
    for foo in comb:
        if dct_indices:
            for sam in dct_indices:
                comb2=foo[:sam]+dct_indices[sam]+foo[sam+1:]
            Q[foo]=Q[foo]*bn.nodes['utility'].cpt[comb2]
            # print 'Checking utility for combination: ',comb2
        else:
            # print 'Checking utility for combination: ',foo
            Q[foo]=Q[foo]*bn.nodes['utility'].cpt[foo]
    return Q


def enumeration_ask(X,e,bn):
    Q={}
    numofqueryvars=len(X)
    lst = map(list, itertools.product(['+','-'], repeat=numofqueryvars))
    comb=[('').join(l) for l in lst]
    ecopy=copy.deepcopy(e)
    for foo in comb:
        #extending e
        for i in range(numofqueryvars):
            ecopy[X.keys()[i]]=foo[i]   #extend e with xi
        Q[foo]=enumerate_all(bn,bn.variables,ecopy)
    sum=0
    q_str=''
    for val in Q:
        sum +=Q[val]
    for k in X:
        q_str+=X[k]
    return Decimal(str((Q[q_str]/sum)+1e-8)).quantize(Decimal('.01'))

def enumerate_all(bn,vars,e):
    if not vars:
        return 1.0
    y,rest=vars[0],vars[1:]
    if y in e:
        return prob(bn,y,e)*enumerate_all(bn,rest,e)
    else:
        sum_end=0.0
        another_copy=copy.deepcopy(e)
        for sym in ['+','-']:
            another_copy = extend(y,another_copy,sym)
            sum_end += prob(bn,y,another_copy)*enumerate_all(bn,rest, another_copy)
        return sum_end

def extend(y,e,sym):
    e[y]=sym
    return e

def prob(bn,y,e):
    parent_y=bn.nodes[y].parent
    comb=''
    comb+=e[y]
    if parent_y is not None:
        for par_y in parent_y:
            if par_y in e:
                comb+=e[par_y]
    if len(comb) is 1:
        if comb=='+':
            return bn.nodes[y].cpt[comb]
        else:
            if bn.nodes[y].decision=='T':
                return 1.0
            return 1-bn.nodes[y].cpt['+']
    if comb[0] is '+':
        return bn.nodes[y].cpt[comb[1:]]
    else:
        return 1-bn.nodes[y].cpt[comb[1:]]

def main():
    script,opt,path=argv
    inputfile=open(path,'r')
    output=open('output.txt','w')
    strng=inputfile.read()
    parts=re.split('\*{6}|\*{3}',strng)
    vars={}
    answer=''
    bn=BN()
    for count,part in enumerate(parts):
        part=part.strip('\r\n')
        # queries
        if count is 0:
            #Extracting and storing queries
            queries=part.split('\n')

        # Probability Tables
        else:
            node = Node()
            info=part.split('\n')
            prob_table_for_part={}
            for index,line in enumerate(info):
                line=line.strip()
                if index == 0:
                    if '|' in line:
                        numerator,denominator=line.split(' | ')
                        node.setName(numerator)
                        bn.addVars(numerator)
                        if ' ' in denominator:
                            parents=denominator.split(' ')
                            node.setParent(parents)
                        else:
                            parent=[]
                            parent.append(denominator)
                            node.setParent(parent)
                    else:
                        node.setName(line)
                        node.setParent(None)
                        bn.addVars(line)
                elif 'decision' in line:
                    node.num_parents=0
                    prob_table_for_part['+']=1.0
                    node.decision='T'
                    break

                else:  #2nd,3rd..lines
                    v,eq,k=line.partition(' ')

                    if node.num_parents is not 0:
                        prob_table_for_part[k.replace(' ','')]=float(v)
                    else:
                        prob_table_for_part['+']=float(v)

            if node.num_parents != 0:
                node.setProb(prob_table_for_part)

            else:
                node.setProb(prob_table_for_part)
            bn.addNode(node.name,node)
            if 'utility' in bn.variables:
                bn.variables.remove('utility')

    for query in queries:
        X = {}
        X_MEU=[]
        O={}
        e={}
        query_type,q_rest=query.split('(')
        q_rest=q_rest.rstrip(')')

        if '|' in q_rest:  # conditional
            numerator, denominator = q_rest.split(' | ')
            if ', ' in numerator:
                terms = numerator.split(', ')
                if query_type=='MEU':
                    X_MEU=terms
                else:
                    for term in terms:
                        var, sym = term.split(' = ')
                        X[var] = sym
            else:
                if query_type=='MEU':
                    X_MEU.append(numerator)
                else:
                    var, sym = numerator.split(' = ')
                    X[var] = sym
            # evidence
            if ', ' in denominator:
                terms = denominator.split(', ')
                for term in terms:
                    var, sym = term.split(' = ')
                    e[var] = sym
            else:
                var, sym = denominator.split(' = ')
                e[var] = sym
        elif ', ' in q_rest:  # joint
            terms = q_rest.split(', ')
            if query_type == 'MEU':
                X_MEU=terms
            else:
                for term in terms:
                    var, sym = term.split(' = ')
                    X[var] = sym
        else:  # marginalized
            if query_type == 'MEU':
                X_MEU.append(q_rest)
            else:
                var, truth_val = q_rest.split(' = ')
                X[var] = truth_val
        if query_type=='P':#Case P
            getval=enumeration_ask(X,e,bn)
            answer+= str(getval)+'\n'
        elif query_type=='EU': #EU
            new_E=copy.deepcopy(X)
            O=copy.deepcopy(bn.nodes['utility'].parent)
            new_E.update(e)
            Q=enumeration_helper(O,new_E,bn)
            answer+= str(int(round(sum(Q.values()))))+'\n'
        elif query_type=='MEU':
            max_eu=float('-inf')
            max_eu_comb=''
            numofQuVars=len(X_MEU)
            lst = map(list, itertools.product(['+', '-'], repeat=numofQuVars))
            combs = [('').join(l) for l in lst]
            for comb in combs:
                dct_x={}
                i=0
                for var in X_MEU:
                    # print var
                    dct_x[var]=comb[i]
                    i+=1
                newer_E=copy.deepcopy(dct_x)
                newer_E.update(e)
                O=copy.deepcopy(bn.nodes['utility'].parent)
                Q=enumeration_helper(O,newer_E,bn)
                eu_for_this_comb=sum(Q.values())
                if max_eu<eu_for_this_comb:
                    max_eu=eu_for_this_comb
                    max_eu_comb=(" ").join(comb)
            answer+= max_eu_comb+" "+str(int(round(max_eu)))+'\n'
    output.write(answer[:-1])

if __name__=='__main__':
    main()
