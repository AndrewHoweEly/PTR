import pt
import sys

def main():
    # Run with first argument as text file containing lines of kb
    # second argument instruction to satisfy or check entailment or get model
    # entail 3rd argument sentence to check
    filename = sys.argv[1]
    f=open(filename,'r')
    lines=f.readlines()
    f.close()

    if sys.argv[2]=="sat":
        kb = []
        for line in lines:
            kb.append(line.rstrip())
        kb = "&".join(kb)
        print(kb)
        print(pt.check_satisfies(kb))
    elif sys.argv[2]=="ent":
        s=""
        kb=[]
        for line in lines:
            if line.startswith("s:"):
                s=line[2:]
                break
            kb.append(line.rstrip())
        kb= "&".join(kb)
        print(kb)
        print(pt.check_entail(kb,s))
    elif sys.argv[2]=="mod":
        kb=[]
        for line in lines:
            kb.append(line.rstrip())
        kb= "&".join(kb)
        print(kb)
        print(pt.get_model(kb))

        
    #print("Minisat wrapper, enter propositional statements as follows: \n >: implies, &: and, |: or, -: not")
    #print("Enter your knowledge base, each statement on a new line:")
    #kb_in = []
    #line = input()
    #while line != "":
    #    kb_in.append(line)
    #    line=input()
    #kb = "&".join(kb_in)
    #print(kb)
    #statement = input("Enter a statement to check entailment:\n")
    #if pt.check_entail(kb,statement):
    #    print("Statement is entailed by the knowledge base")
    #else:
    #    print("Statement is not entailed by the knowledge base")

if __name__ == "__main__":
    main()
