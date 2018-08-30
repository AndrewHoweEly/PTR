import minisolvers
import re
from itertools import chain, combinations, product

############################

class RankedModel:
    def __init__(self):
        self.layers = []

    def copy(self):
        rm = RankedModel()
        rm.layers=self.layers
        return rm

    def insert_vals(self, vals, levels=-1):
        if levels==-1:
            levels="0"*len(vals)
        for x in range(len(set(levels))):
            self.layers.append([])
        for i in range(len(levels)):
            self.layers[int(levels[i])].append(vals[i])

    def get_lowest_layer(self, atom_index):
        i = 0
        mini=1000
        for layer in self.layers:
            for val in layer:
                if val[atom_index] == "1":
                    if mini > i:
                        mini = i
            i += 1
        if mini==1000:
            return -1
        return mini

    #def get_layer(self, val):
        #height
     #   i=0
      #  for layer in self.layers:
       #     for v in layer:
        #        if v == val:
         #           return i
          #  i+=1
        #return -1

    def height(self, v):
        #return the height of a valuation in the ranked intepretation
        for i in range(len(self.layers)):
            for val in self.layers[i]:
                if val==v:
                    return i
        return "inf"

    def preferred(self, rm_2, vals):
        # return true if current RM is =< RM2
        for val in vals:
            h1 = self.height(val)
            h2 = rm_2.height(val)
            if h1 == "inf" or h2 == "inf":
                if h1 =="inf" and h2 != "inf":
                    return False
            else:
                if h1 > h2:
                    return False
        return True
            
    def __str__(self):
        string = ""
        for i in reversed(range(len(self.layers))):
            string += "L"+str(i)+" "+str(self.layers[i]) + "\n"
        return string

class Node():
    # Tree representation of propositional formula
    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def insert_left(self, left):
        self.left = left

    def insert_right(self, right):
        self.right = right

    def __str__(self, lvl=0):
        ret = " "*lvl + self.value + "\n"
        if self.left:
            ret += self.left.__str__(lvl+1)
        if self.right:
            ret+= self.right.__str__(lvl+1)
        return ret

    def inorder(self):
        if self.left == None and self.right == None:
            return self.value
        elif self.right == None:
            return self.value + self.left.inorder()
        else:
            return self.left.inorder()+ self.value + self.right.inorder()

############################
        # Pre-processing
def add_brackets(s):
    s = s.replace(" ","")
    atoms = re.split(">|&|\|",s)
    ops = re.split("\*|-*[a-z]",s)
    ops = [o for o in ops if o!=""]
    s = ""
    if len(atoms)>=2:
        s = atoms.pop() + ")" + s
        s = ops.pop() + s
        s = "(" + atoms.pop() + s

    while len(atoms) > 0:
        s = "("+atoms.pop()+ops.pop()+s+")"
    return s

        
def get_vars(kb):
    # Return a listing of variables for SAT solver format
    var_list = []
    for s in kb:
        for ch in s:
            if ch in "abcdefghijklmnopqrstuvwxyz" and ch not in var_list:
                var_list.append(ch)
    return var_list

def sat_format(kb,var_list):
    # return a list of SAT clauses
    s = "&".join(kb)
    clauses = []
    ors = s.split("&")
    for sent in ors:
        new_clause = []
        atoms = sent.split("|")
        for var in atoms:
            if "-" in var:
                new_clause.append(-(var_list.index(var.strip()[1:])+1))
            else:
                new_clause.append(var_list.index(var.strip())+1)
        clauses.append(new_clause)
    return clauses
############################
  

############################
    #tree operations
def negate(node):
    # Return the negation of a statement
    if node.value=="&":
        node.value= "|"
        node.left = negate(node.left)
        node.right = negate(node.right)
    elif node.value=="|":
        node.value="&"
        node.left = negate(node.left)
        node.right = negate(node.right)
    elif node.value=="-":
        node.value=node.left.value
        node.left=None
    else:
        node.left = Node(node.value)
        node.value="-"
    return node

def conv_impl(node):
    # Return a tree using | instead of >
    if node == None:
        return None
    if node.value == ">":    
        node.value = "|"
        if node.left.value==">":
            conv_impl(node.left)
        node.left = negate(node.left)
    conv_impl(node.left)
    conv_impl(node.right)
    return node



def fits_orOfAnd(node):
    # Check if a tree fits the situation of an Or of And
    if node.value == "|":
        if node.left.value == "&":
            return True
        if node.right.value =="&":
            return True
        else:
            return False
    return False


def conv_orOfAnd(node):
    #If a formula tree matches that of (A and B) or C convert to
    # (A or C) and (B or C) to be in CNF
    if fits_orOfAnd(node):
        node.value="&"
        if node.left.value=="&":
            temp_A=node.left.left
            temp_B=node.left.right
            temp_C=node.right
            node.left = Node("|")
            node.right= Node("|")
            node.left.left=temp_A
            node.left.right=temp_C
            node.right.left=temp_B
            node.right.right=temp_C
        elif node.right.value=="&":
            temp_C=node.left
            temp_B=node.right.right
            temp_A=node.right.left
            node.left = Node("|")
            node.right= Node("|")
            node.left.left=temp_C
            node.left.right=temp_A
            node.right.left=temp_C
            node.right.right=temp_B
    if node.left:
        conv_orOfAnd(node.left)
    if node.right:
        conv_orOfAnd(node.right)
    return node

def create_tree(s):
    if "(" not in s:
        if ">" in s:
            s = s.split(">")
            new_node = Node(">")
            new_node.left = create_tree(s[0])
            new_node.right = create_tree(s[1])
        elif "|" in s:
            s = s.split("|")
            new_node = Node("|")
            new_node.left = create_tree(s[0])
            new_node.right = create_tree(s[1])
        elif "&" in s:
            s = s.split("&")
            new_node = Node("&")
            new_node.left = create_tree(s[0])
            new_node.right = create_tree(s[1])
        elif "-" in s:
            s = s.split("-")
            new_node = Node("-")
            new_node.left = create_tree(s[1])
        else:
            new_node = Node(s)

    elif s[0] == "-":
        new_node = Node("-")
        new_node.left = create_tree(s[1:])

    else:
        if not ("-" in s or ">" in s or "|" in s or "&" in s):
            s = s.replace("(","")
            s = s.replace(")","")
            new_node = Node(s)
        else:
            counter = 0
            i=0
            for ch in s:
                if ch=="(":
                    counter+=1
                if ch==")":
                    counter-=1
                if counter == 0:
                    if len(s) <= i+1:
                        new_node = create_tree(s[1:len(s)-1])
                    else:
                        new_node = Node(s[i+1])
                        new_node.left = create_tree(s[:i+1])
                        new_node.right =create_tree(s[i+2:])
                    break
                i+=1

    return new_node

#############################
  # satisfaction
def sat_kb(kb, val,var_list):
    # Check a valuation satisfies a classical KB
    # return true if val satisfies KB
    solver = minisolvers.MinisatSolver()
    new_kb = kb.copy()
    for i in range(len(kb)):
        tree = create_tree(kb[i])
        tree = conv_impl(tree)
        tree = conv_orOfAnd(tree)
        new_kb[i]=tree.inorder()
    
    val_s = []
    for i in range(len(val)):
        if val[i] =="0":
            val_s.append("-"+var_list[i])
        else:
            val_s.append(var_list[i])
    val="&".join(val_s)
    new_kb.append(val)
    clauses = sat_format(new_kb,var_list)
    #print('clauses',clauses)
    for i in range(len(var_list)):
        solver.new_var()
    for clause in clauses:
        solver.add_clause(clause)
    return solver.solve()

def sat_rm_val(kb, val, ranked_model,var_list):
    # Check a valuation satisfies a KB with typicality statements wrt a ranked model
    # return true if val satisfies 
    new_kb=[]
    for s in kb:
        if "*" in s:
            typ_instances = [j for j, ch in enumerate(s) if ch=="*"]
            while typ_instances !=[]:
                j=typ_instances.pop()
                atom = s[j+1]
                
                #find most typical layer of atom
                lowest_layer = ranked_model.get_lowest_layer(var_list.index(atom))
                cur_layer = ranked_model.height(val)
                if cur_layer =="inf":
                    cur_layer=-1
                if lowest_layer < cur_layer: # not the most typical world
                    s=s.replace("*"+atom,"("+atom+"&-"+atom+")")# replace typ instance with false
                else: #most typical world, now evaluate on classical
                    s=s.replace("*"+atom,atom)
                typ_instances = [j for j, ch in enumerate(s) if ch=="*"]
            new_kb.append(s)
        else:
            new_kb.append(s)
    return sat_kb(new_kb,val,var_list)

def sat_kb_rm(kb, rm,var_list):
    # Check a ranked interpretation satisfies a KB
    for level in rm.layers:
        for val in level:
            if not sat_rm_val(kb, val, rm,var_list):
                return False
    return True 

#algorithm helper functions
def powerset(s):
    # return a list of subsets as set type
    result = []
    for length in range(len(s)+1):
        for subset in combinations(s,length):
            result.append(set(subset))
    return result
            
def valid_intr(ranking):
    # check if string ranking is a valid interpretation,
    # no valuation should be >1 level above the others
    # valuations should not be all on same level if lvl >1
    if len(ranking)==1:
        if ranking=="0":
            return True
        else:
            return False
    rnk = [int(x) for x in list(ranking)]
    rnk.sort()
    if rnk[0]!=0:
        return False
    pairwise = list(zip(rnk,rnk[1:]))
    for pair in pairwise:
        if pair[1]-pair[0]>1:
            return False
    return True

def incr_arrange(rankings):
    # return a list of ranking arrangements but all incremented by 1 level
    temp = set()
    for a in rankings:
        for i in range(len(a)):
            temp_rank = list(a)
            temp_rank[i] = str(int(temp_rank[i])+1)
            temp.add("".join(temp_rank))
        #print(temp)
    return [rank for rank in list(temp) if valid_intr(rank)]


# main algorithm
def pt_ranked(kb):
    var_list = get_vars(kb)
    print(var_list)
    U = ["".join(seq) for seq in product("01", repeat=len(var_list))] #every possible valuation
    # remove valuations that break classical statements
    classical_kb = [sentence for sentence in kb if not "*" in sentence]
    U = [val for val in U if sat_kb(classical_kb, val, var_list)]
    print('u',U)
    G = powerset(U)
    G.reverse()
    G.remove(set())
    pt_min = [] # all minimal r anked models
    while G != []:
        X = []
        for subset in G:
            if len(subset) == len(G[0]):
                X.append(subset)
            else:
                break
        #print("x",X)
        for s in X:
            #print('s',s)
            rankings = ["0"*len(s)]
            pt_min_s=[]
            while pt_min_s == []:
                for arr in rankings:
                    #try model
                    rm = RankedModel()
                    rm.insert_vals(list(s),arr)
                    #print('arr',arr)
                    if sat_kb_rm(kb,rm,var_list):
                        #print(rm)
                        pt_min_s.append(rm)
                if rankings == incr_arrange(rankings):
                    break
                rankings = incr_arrange(rankings)
                #print("len rankings",len(rankings))
            if pt_min_s==[]:
                G.remove(s)#[x for x in G if not x==s]
            else:
                G = [subset for subset in G if not s.issuperset(subset)]
            pt_min += pt_min_s
            #print('g',G)
    return pt_min

def pt_entail(s, kb):
    # check if a statement is entailed by a ptl kb
    ranked_model = pt_ranked(kb)
    var_list = get_vars(kb)
    # get most typical layer of atoms in s
    
    #layer = ranked_model.get_lowest_layer()

#x=["*t>(-p&-r)","t>(x|-x)","(x|-x)>t"]
#y=["*p>*y","y>-f","-f>y","*r>*f"]
for rm in pt_ranked(["p>b","*b>f"]):#"p>b","*b>f","*p>-f"]):
    print('Ranked Model\n',rm)



#a = RankedModel()
#b = RankedModel()

#v = ['000','001','010','100','111']
#x = [val for val in v if val != '111']
#a.insert_vals(x,'100')
#b.insert_vals(x,'110')
#print('a\n',a)
#print('b\n',b)
#print(a.preferred(b,v))


















