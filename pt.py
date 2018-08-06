import minisolvers
# *p > -f

class RankedInterpretation:
    def __init__(self):
        self.layers = {}

    def insert(self,vals,layer):
        self.layers[layer]=vals

    def inc_layer(self,vals,layer,inc):
        start_layer = self.layers[layer]
        if inc == "inf":
            self.layers[inc]=[]
            for val in start_layer:
                if val in vals:
                    start_layer.remove(val)
                    self.layers[inc].append(val)
        else:
            self.layers[layer+inc]=[]
            for val in start_layer:
                if val in vals:
                    start_layer.remove(val)
                    self.layers[layer+inc].append(val)

    def find_layer(self, atom):
        minm = 0
        for layer in self.layers:
            for val in layer:
                if atom in layer:
                    
        
    def __str__(self):
        lines=[]
        for layer in self.layers:
            line=[]
            for val in self.layers[layer]:
                line.append(val)
            lines.append(str(layer)+": "+", ".join(line))
        return "\n".join(lines)

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

    def inorder_bra(self):
        if self.left == None and self.right == None:
            return self.value
        elif self.right == None:
            return self.value + self.left.inorder()
        else:
            return "("+self.left.inorder()+ self.value + self.right.inorder()+")"

    def inorder(self):
        if self.left == None and self.right == None:
            return self.value
        elif self.right == None:
            return self.value + self.left.inorder()
        else:
            return self.left.inorder()+ self.value + self.right.inorder()

    def get_vars(self):
        var_list = []
        if not self.value in var_list and self.value in "abcdefghijklmnopqrstuvwxyz":
            var_list.append(self.value)
        left_var_list = []
        right_var_list = []
        
        if self.left:
            left_var_list = self.left.get_vars()

        if self.right:
            right_var_list = self.right.get_vars()

        for var in left_var_list + right_var_list:
            if var not in var_list:
                var_list.append(var)
                
        return var_list
    
    def __str__(self):
        return self.value


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
                        new_node.right = create_tree(s[i+2:])
                    break
                i+=1
                
    return new_node


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
    conv_impl(node.left)
    return node


def conv_to_or(sentence):
    # Return a representation containing | instead of >
    s = sentence.split(">")
    ant = s[0].strip()
    cons = s[1].strip()
    new_sentence = "-" + ant + "|" + cons
    return new_sentence


def create_clauses(node):
    cur = []
    if node.value=="&":
        cur.append(create_clauses(node.left))
        cur.append(create_clauses(node.right))
    elif node.value=="|":
        for child in node.left, node.right:
            if child.value=="-":
                cur.append("-"+child.left.value)
            elif child.value in "abcdefghijklmnopqrstuvwxyz":
                cur.append(child.value)
            else:
                cur += create_clauses(child)
    elif node.value=="-":
        cur.append("-"+node.left.value)
    elif node.value in "abcdefghijklmnopqrstuvwxyz":
        cur.append(node.value)
    return cur


def conv_CNF_tree(node):
    #
    var_list = node.get_vars()
    new_CNF = []
    node = conv_impl(node)
    
    
    
def conv_CNF(s):
    # Return a tuple containing array of clauses in CNF and the number of variables
    var_list = []
    for ch in s:
        if ch in "abcdefghijklmnopqrstuvwxyz":
            if not ch in var_list:
                var_list.append(ch)
    new_CNF = []
    ors = s.split("&")
    for sent in ors:
        new_clause = []
        if ">" in sent:
            sent = conv_to_or(sent)
        vars = sent.split("|")
        for var in vars:
            if "-" in var:
                new_clause.append(-(var_list.index(var.strip()[1:])+1))
            else:
                new_clause.append(var_list.index(var.strip())+1)
        new_CNF.append(new_clause)
    return new_CNF, len(var_list)

def get_model(kb):
    # Return a model if a knowledge base is satisfiable
    S = minisolvers.MinisatSolver()
    cnf_tup = conv_CNF(kb)
    clauses= cnf_tup[0]
    no_var= cnf_tup[1]

    for i in range(no_var):
        S.new_var()
        pass
    for clause in clauses:
        S.add_clause(clause)
        pass
    if S.solve():
        return list(S.get_model())

def check_satisfies(kb, val=""):
    # Return true if a knowledge base is satisfiable, option for valuation to check if satisfiable
    S = minisolvers.MinisatSolver()
    if val != "":
        kb = kb + "&" + val
    cnf_tup = conv_CNF(kb)
    clauses= cnf_tup[0]
    no_var= cnf_tup[1]

    for i in range(no_var):
        S.new_var()
        pass
    for clause in clauses:
        S.add_clause(clause)
        pass
    return S.solve()


def check_satisfies_ranked(kb, val, rm):
    # Return true if a valuation satisfies a KB wrt a ranked model
    # kb an array of strings
    for s in kb:
        if not "*" in s:
            if not check_satisfies(s, val):
                return False
        else:
            typ_instances = [i for i, ch in enumerate(s) if ch=="*"]
            for i in typ_instances:
                print(i)
                atom = s[i+1]
                #find most typical layer of atom
                lyr = rm.find_layer(atom)

check_satisfies_ranked(["*a>b"],"1",1)

def check_entail(kb, s):
    # Return true if a sentence is entailed by a knowledge base
    if ">" in s:
        s = conv_to_or(s)
    s = negate(create_tree(s)).inorder()
    kb = kb + "&" + s
    return not check_satisfies(kb)


def get_atoms(kb):
    # Return the list of atoms in a knowledge base
    var_list = []
    for ch in kb:
        if ch in "abcdefghijklmnopqrstuvwxyz":
            if not ch in var_list:
                var_list.append(ch)
    return var_list


def get_valuations(atoms):
    # Return all the unique valuations of a set of atoms
    U = []
    n = len(atoms)
    combs = []
    for i in range(2**n):
        combs.append(format(i,'0'+str(n)+'b'))
    for comb in combs:
        val = []
        for i in range(n):
            if int(comb[i]) == 0:
                val.append("-"+ atoms[i])
            else:
                val.append(atoms[i])
        U.append('&'.join(val))
    return U


def pt_minimal(kb):
    U = get_valuations(get_atoms(kb))
    S = U
    mod_order = []
    ranked_0 = (U,mod_order)
    r_k = []
    T = U#ranked_0 #contains the interpretations the procedure is going to consider
    i=0
    while i<2:
        i+=1
        for r_i in T:
            kb_ri = []
            for val in U:
                if check_satisfies(kb,val):
                    kb_ri.append(val)
            print(kb_ri)
            S_i = kb_ri
            #if S_i = S
#pt_minimal("p>q")

