import pt_entailment as pt
import sys

print("Enter a knowledge base:")
kb = []
line = input()
while line != "":
    kb.append(line)
    line=input()
print("The atoms are:", pt.get_vars(kb))
print("The minimal models are:")
min_models = pt.pt_ranked(kb,1000)
for model in min_models:
    print(model)

line = input("Enter a statement to be entailed or quit (q):\n")
while line!="q":
    print(pt.pt_entail(line,kb,min_models))
    line=input("Enter a statement to be entailed or quit (q):\n")
