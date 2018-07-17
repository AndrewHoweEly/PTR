import minisolvers
# *p > -f

        
def conv_to_or(sentence):
    s = sentence.split(">")
    ant = s[0].strip()
    cons = s[1].strip()
    newSentence = "-" + ant + "|" + cons 
    return newSentence

def conv_CNF(s):
    varList = []
    for ch in s:
        if ch in "abcdefghijklmnopqrstuvwxyz":
            if not ch in varList:
                varList.append(ch)
    newCNF = []
    ors = s.split("&")
    for sent in ors:
        newClause = []
        if ">" in sent:
            sent = conv_to_or(sent)
        vars = sent.split("|")
        for var in vars:
            if "-" in var:
                newClause.append(-(varList.index(var.strip()[1:])+1))
            else:
                newClause.append(varList.index(var.strip())+1)
        newCNF.append(newClause)
    return newCNF, len(varList)
    
def check_entail(kb, s):
    S = minisolvers.MinisatSolver()
    kb = kb + "&" + s
    cnfTup = conv_CNF(kb)
    clauses = cnfTup[0]
    noVar = cnfTup[1]
    for i in range(noVar):
        S.new_var()
    for clause in clauses:
        S.add_clause(clause)
    try:
        return S.solve()
    except:
        return False

def get_atoms(kb):
    var_list = []
    for ch in kb:
        if ch in "abcdefghijklmnopqrstuvwxyz":
            if not ch in var_list:
                var_list.append(ch)
    return var_list

def get_valuations(atoms):
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
                if check_entail(kb,val):
                    kb_ri.append(val)
            print(kb_ri)
            S_i = kb_ri   
            if S_i = S
pt_minimal("p>q")

















egKb = "b>f & p > b & p>-f"
#print(check_entail(egKb,"p"))
