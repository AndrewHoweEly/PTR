import minisolvers
import re

############################

class RankedModel:
    def __init__(self):
        self.layers = []

    def insert(self, vals):
        self.layers.append(vals)

    def inc_layer(self, vals):
        for i in range(len(self.layers)):
            layer = self.layers[i]
            for val in layer:
                if not val in vals:
                    layer.remove(val)
                    try:
                        self.layers[i+1].append(val)
                    except IndexError:
                        self.layers.append([val])

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

    def get_layer(self, val):
        i=0
        for layer in self.layers:
            for v in layer:
                if v == val:
                    return i
            i+=1
        return -1
    
    def __str__(self):
        string = ""
        for layer in self.layers:
            string += str(layer) + "\n"
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

def check_satifies_typ(kb, val, ranked_model):
    # Check a valuation satisfies a KB wrt a ranked model
    var_list = []#get_vars(kb)
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
                lowest_layer = ranked_model.get_lowest_layer(var_list.index(atom))
                cur_layer = ranked_model.get_layer(val)
                if lowest_layer < cur_layer: # not the most typical world
                    s.replace("*"+atom,atom+"&-"+atom)# replace typ instance with false


        

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
            
def get_vars(kb):
    # Return a listing of variables for SAT solver format
    var_list = []
    for s in kb:
        for ch in s:
            if ch in "abcdefghijklmnopqrstuvwxyz" and ch not in var_list:
                var_list.append(ch)
    return var_list


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


def add_brackets(s):
    s = s.replace(" ","")
    atoms = re.split(">|&|\|",s)
    ops = re.split("\*|-*[a-z]",s)
    ops = [o for o in ops if o!=""]
    s = ""
    if len(atoms)>2:
        s = atoms.pop() + ")" + s
        s = ops.pop() + s
        s = "(" + atoms.pop() + s

    while len(atoms) > 0:
        s = "("+atoms.pop()+ops.pop()+s+")"
    return s


s="c|a&b"
s=add_brackets(s)
print(s)
x = create_tree(s)
print(x)
x=conv_orOfAnd(x)
print(x)















