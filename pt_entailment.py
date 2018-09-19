"""A Python Module to compute PT Minimal Models and PT Entailment

Classes:
    RankedModel
     Represent a ranked interpretation holding valuations on different levels
    Node
     Binary formula tree for propositional sentences
"""

import minisolvers
import re
from itertools import chain, combinations, product

############################

class RankedModel:
    """The RankedModel class represents a ranked interpretation or model
    holding valuations.
    It provides methods to find information on typicality of sentences and
    preferred models.
    """
    
    def __init__(self):
        self.layers = []

    def copy(self):
        rm = RankedModel()
        rm.layers=self.layers
        return rm

    def insert_vals(self, vals, levels=-1):
        """ Insert a list of valuations into RankedModel using the arrangement levels
        """
        if levels==-1:
            levels="0"*len(vals)
        for x in range(len(set(levels))):
            self.layers.append([])
        for i in range(len(levels)):
            self.layers[int(levels[i])].append(vals[i])


    def get_typical_layer_s(self, sentence, var_list):
        """ Return lowest layer that satisfies a sentence
        """
        for i in range(len(self.layers)):
            for val in self.layers[i]:
                if sat_kb([sentence], val, var_list):
                    return i
        return "inf"

                
    def get_typical_layer_atom(self, atom_index, false_flag = False):
        """ Return lowest layer 1 atom is satisfied on
        or if false flag lowest level not atom is satisfied on
        """
        if false_flag:
            for i in range(len(self.layers)):
                for val in self.layers[i]:
                    if val[atom_index] == "0":
                        return i
        else:
            for i in range(len(self.layers)):
                for val in self.layers[i]:
                    if val[atom_index] == "1":
                        return i
        return "inf"

    def height(self, v):
        """ Return the height of a valuation in the ranked intepretation
        """
        for i in range(len(self.layers)):
            for val in self.layers[i]:
                if val==v:
                    return i
        return "inf"

    def preferred(self, rm_2, vals):
        """Return true if current RM is =<PT RM2
        """
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
    """ Tree representation of propositional formula
    """
    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def copy(self):
        new_node = Node(self.value)
        if self.left:
            new_node.left = self.left.copy()
        if self.right:
            new_node.right = self.right.copy()
        return new_node
    
    def insert_left(self, left):
        self.left = left

    def insert_right(self, right):
        self.right = right

    def find_typicality(self):
        """Return nodes with typicality children
        """
        typ = []
        if self.left:
            if self.left.value == "*":
                typ.append(self)
            typ+= self.left.find_typicality()

        if self.right:
            if self.right.value == "*":
                typ.append(self)
            typ+= self.right.find_typicality()
            
        return typ

    def inorder_bra(self):
        """ Return inorder string with brackets
        """
        if self.left == None and self.right == None:
            return self.value
        elif self.right == None:
            return self.value + self.left.inorder()
        else:
            return "("+self.left.inorder_bra()+ self.value + self.right.inorder_bra()+")"

    def inorder(self):
        """ Return inorder string of nodes
        """
        if self.left == None and self.right == None:
            return self.value
        elif self.right == None:
            return self.value + self.left.inorder()
        else:
            return self.left.inorder()+ self.value + self.right.inorder()
        
    def __str__(self, lvl=0):
        ret = " "*lvl + self.value + "\n"
        if self.left:
            ret += self.left.__str__(lvl+1)
        if self.right:
            ret+= self.right.__str__(lvl+1)
        return ret

############################
        # Pre-processing
def add_brackets(s):
    """ Return string with brackets associatively right to left
    """
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
    """ Return a list of atoms used in KB
    """
    var_list = []
    for s in kb:
        atoms = re.split(">|&|\||-|\*|\(|\)",s)
        for atom in atoms:
            if atom not in var_list and atom!="":
                var_list.append(atom)
    return var_list

def sat_format(kb,var_list):
    """ Return a list of SAT clauses
    """
    s = "&".join(kb)
    clauses = []
    ors = s.split("&")
    for sent in ors:
        new_clause = []
        atoms = sent.split("|")
        for var in atoms:
            if "-" in var:
                try:
                    new_clause.append(-(var_list.index(var.strip()[1:])+1))
                except ValueError:
                    print(sent)
                    print("ValueError",var.strip()[1:])
            else:
                new_clause.append(var_list.index(var.strip())+1)
        clauses.append(new_clause)
    return clauses
############################

############################
    #tree operations
def negate(node):
    """ Return the negation of a statement
    """
    if node.value=="&":
        node.value= "|"
        node.left = negate(node.left)
        node.right = negate(node.right)
    elif node.value=="|":
        node.value="&"
        node.left = negate(node.left)
        node.right = negate(node.right)
    elif node.value=="-":
        node=node.left.copy()
    else:
        node.left = Node(node.value)
        node.value="-"
    return node

def conv_impl(node):
    """ Return a tree using | instead of >
    """
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

def prop_neg(node):
    """ Return formula tree with propagation of negations
    """
    if node==None:
        return None
    if node.value =="-" and node.left.value in "&|-":
        node = negate(node.left)
    node.left=prop_neg(node.left)
    node.right=prop_neg(node.right)
    return node
        
def fits_orOfAnd(node):
    """ Return true if a formula tree fits the situation of an Or of And
    """
    if node.value == "|":
        if node.left.value == "&":
            return True
        if node.right.value =="&":
            return True
        else:
            return False
    return False


def conv_orOfAnd(node):
    """ Return a formula tree. Find nodes that match that of "(A and B) or C"
    convert to "(A or C) and (B or C)" to be in CNF
    """
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
    """ Return a formula tree from a sentence
    """
    s = s.replace(" ","")
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
        elif "*" in s:
            s = s.split("*")
            new_node = Node("*")
            new_node.left = create_tree(s[1])
        elif "-" in s:
            s = s.split("-")
            new_node = Node("-")
            new_node.left = create_tree(s[1])            
        else:
            new_node = Node(s)

    elif s[0] == "-":
        new_node = Node("-")
        new_node.left = create_tree(s[1:])

    elif s[0] == "*":
        new_node = Node("*")
        new_node.left = create_tree(s[1:])

    else:
        if not ("-" in s or ">" in s or "|" in s or "&" in s or "*" in s):
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
                        break
                    elif s[i+1] in ">&|":
                        new_node = Node(s[i+1])
                        new_node.left = create_tree(s[:i+1])
                        new_node.right =create_tree(s[i+2:])
                        break
                i+=1

    return new_node


#############################
  # satisfaction
def sat_kb(kb, val, var_list):
    """ Check a valuation satisfies a classical KB
     return true if val satisfies KB
    """
    solver = minisolvers.MinisatSolver()
    new_kb = kb.copy()
    for i in range(len(kb)):
        tree = create_tree(kb[i])
        tree = conv_impl(tree)
        tree = prop_neg(tree)
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

    for i in range(len(var_list)):
        solver.new_var()
    for clause in clauses:
        solver.add_clause(clause)
    return solver.solve()

def sat_rm_val(kb, val, ranked_model, var_list):
    """Check a valuation satisfies a KB with typicality statements wrt a ranked model
     return true if val satisfies
    """
    new_kb=[]
    
    for s in kb:
        s_tree=create_tree(s)
        typ_roots = s_tree.find_typicality()
        if typ_roots:
            for node in typ_roots:
                if node.left.value=="*":
                    #if typ is left child
                    # Find lowest level node.left.left is satisfied on
                    typ_sent = node.left.left.inorder_bra()
                    if not (">" in typ_sent or "&" in typ_sent or "|" in typ_sent):
                        if "-" in typ_sent:
                            atom = node.left.left.left.inorder()
                            lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom),True)
                        else:
                            atom=node.left.left.inorder()
                            lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom))
                    else:
                        lowest_layer = ranked_model.get_typical_layer_s(typ_sent, var_list)
                    cur_layer = ranked_model.height(val)

                    if lowest_layer == "inf":
                        lowest_layer = len(ranked_model.layers)

                    if lowest_layer < cur_layer:
                        # val is not most typical world, replace with false
                        node.left = create_tree("("+var_list[0]+"&"+"-"+var_list[0]+")")
                    else:
                        #typical world, evaluate classically
                        node.left = node.left.left
                else:
                    #else typ must be right child
                    # Find lowest level node.right.left is satisfied on
                    typ_sent = node.right.left.inorder_bra()
                    
                    if not (">" in typ_sent or "&" in typ_sent or "|" in typ_sent):
                        if "-" in typ_sent:
                            atom=node.right.left.left.inorder()
                            lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom),True)
                        else:
                            atom=node.right.left.inorder()
                            lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom))                              
                    else:
                        lowest_layer = ranked_model.get_typical_layer_s(typ_sent, var_list)
                    cur_layer = ranked_model.height(val)
                    
                    if lowest_layer == "inf":
                        lowest_layer = len(ranked_model.layers)

                    if lowest_layer < cur_layer:
                        # val is not most typical world, replace with false
                        node.right = create_tree("("+var_list[0]+"&"+"-"+var_list[0]+")")
                    else:
                        #typical world, evaluate classically
                        node.right = node.right.left
            new_kb.append(s_tree.inorder_bra())
        else:
            new_kb.append(s)
    return sat_kb(new_kb, val, var_list)



def sat_kb_rm(kb, rm, var_list):
    """ Return true if a ranked interpretation satisfies a KB
    """
    for level in rm.layers:
        for val in level:
            if not sat_rm_val(kb, val, rm, var_list):
                return False
    return True 

#algorithm helper functions

def powerset(s):
    """ Return a list of subsets as set type
    """
    result = []
    for length in range(len(s)+1):
        for subset in combinations(s,length):
            result.append(set(subset))
    return result
            
def valid_intr(ranking):
    """ Method to check if string ranking is a valid interpretation,
    no valuation should be >1 level above the others
    valuations should not be all on same level if lvl >1
    """
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
    """ Returns a list of unique arrangements all incremented by 1 level
    """
    temp = set()
    for a in rankings:
        for i in range(len(a)):
            temp_rank = list(a)
            temp_rank[i] = str(int(temp_rank[i])+1)
            temp.add("".join(temp_rank))
    return [rank for rank in list(temp) if valid_intr(rank)]


def pt_ranked(kb):
    """ Returns the set of minimal ranked models for typicality KB
        This is the main algorithm the project is concerned with
    """
    var_list = get_vars(kb)
    print(var_list)
    U = ["".join(seq) for seq in product("01", repeat=len(var_list))] #every possible valuation
    # remove valuations that dn satisfy classical statements
    classical_kb = [sentence for sentence in kb if not "*" in sentence]
    U = [val for val in U if sat_kb(classical_kb, val, var_list)]
    print('U',U)

    G = powerset(U)
    G.reverse()
    G = [list(subset) for subset in G if subset != set()]
    pt_min = [] # all minimal ranked models
    for subset in G:
        #i+=1
        rankings = ["0"*len(subset)]
        pt_min_s=[]
        while pt_min_s == []:
            for arr in rankings:
                #try model
                rm = RankedModel()
                rm.insert_vals(subset, arr)
                #i+=1
                if sat_kb_rm(kb, rm, var_list):
                    #if ranked model with current arrangement satisfies KB
                    pt_min_s.append(rm)

            rankings = incr_arrange(rankings)
            
            if rankings == []:
                break
            # cheap optimisation trick to skip arrangements
            #if len(rankings)>1000:
            #    break
        for model in pt_min:
            for i in range(len(pt_min_s)):
                model2 = pt_min_s[i]
                if model.preferred(model2,U):
                    pt_min_s.remove(model2)
        pt_min += pt_min_s
    return pt_min


def entail(s, val, var_list):
    """ Returns true if a statement is entailed by a valuation
    """
    solver = minisolvers.MinisatSolver()
    s = create_tree(s)
    s = conv_impl(s)
    s = negate(s)
    s = conv_orOfAnd(s)
    s = s.inorder()
    val_s = []
    for i in range(len(val)):
        if val[i] =="0":
            val_s.append("-"+var_list[i])
        else:
            val_s.append(var_list[i])
    val="&".join(val_s)
    kb= [s] + [val]
    clauses = sat_format(kb,var_list)
    for i in range(len(var_list)):
        solver.new_var()
    for clause in clauses:
        solver.add_clause(clause)
    return not solver.solve()

def pt_entail(s, kb, ranked_models):
    """ Returns true if a statement is entailed by a PTL KB
        input statement, knowledge base, and the minimal models from pt_ranked
    """
    #ranked_models = pt_ranked(kb)
    var_list = get_vars(kb)
    for ranked_model in ranked_models:
        # check if classical statement
        if "*" not in s:
            for layer in ranked_model.layers:
                for val in layer:
                    if not (entail(s,val,var_list)):
                        return False
        else:
        #statement contains typicality
            for layer in ranked_model.layers:
                for val in layer:
                    s_tree=create_tree(s)
                    typ_roots = s_tree.find_typicality()
                    for node in typ_roots:
                        if node.left.value=="*":
                            #if typ is left child
                            # Find lowest level node.left.left is satisfied on
                            typ_sent = node.left.left.inorder_bra()
                            if not (">" in typ_sent or "&" in typ_sent or "|" in typ_sent):
                                if "-" in typ_sent:
                                    atom=node.left.left.left.inorder()
                                    lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom),True)
                                else:
                                    atom=node.left.left.inorder()
                                    lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom))
                            else:
                                lowest_layer = ranked_model.get_typical_layer_s(typ_sent, var_list)
                            cur_layer = ranked_model.height(val)

                            if lowest_layer == "inf":
                                lowest_layer = len(ranked_model.layers)

                            if lowest_layer < cur_layer:
                                # val is not most typical world, replace with false
                                node.left = create_tree("("+var_list[0]+"&"+"-"+var_list[0]+")")
                            else:
                                #typical world, evaluate classically
                                node.left = node.left.left
                        else:
                            #else typ must be right child
                            # Find lowest level node.right.left is satisfied on
                            typ_sent = node.right.left.inorder_bra()
                            if not (">" in typ_sent or "&" in typ_sent or "|" in typ_sent):
                                if "-" in typ_sent:
                                    atom=node.right.left.left.inorder()
                                    lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom),True)
                                else:
                                    atom=node.right.left.inorder()
                                    lowest_layer = ranked_model.get_typical_layer_atom(var_list.index(atom))

                            else:
                                lowest_layer = ranked_model.get_typical_layer_s(typ_sent, var_list)
                            cur_layer = ranked_model.height(val)
                            
                            if lowest_layer == "inf":
                                lowest_layer = len(ranked_model.layers)

                            if lowest_layer < cur_layer:
                                # val is not most typical world, replace with false
                                node.right = create_tree("("+var_list[0]+"&"+"-"+var_list[0]+")")
                            else:
                                #typical world, evaluate classically
                                node.right = node.right.left
                    new_s = s_tree.inorder_bra()
                    if not sat_kb([new_s],val,var_list):
                        return False
                    
    return True
                

