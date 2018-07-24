import pt

def main():
    print("Minisat wrapper, enter propositional statements as follows: \n >: implies, &: and, |: or, -: not")
    print("Enter your knowledge base, each statement on a new line:")
    kb_in = []
    line = input()
    while line != "":
        kb_in.append(line)
        line=input()
    kb = "&".join(kb_in)
    print(kb)
    statement = input("Enter a statement to check entailment:\n")
    if pt.check_entail(kb,statement):
        print("Statement is entailed by the knowledge base")
    else:
        print("Statement is not entailed by the knowledge base")

if __name__ == "__main__":
    main()
