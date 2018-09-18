# PTR-PT-Entail
Implementation of PT Entailment for PTL

To use PT-Entail:

First compile the PyMiniSolvers Library:

1. Clone/Download https://github.com/liffiton/PyMiniSolvers 

2. Build the shared libraries with $ make

Now place pt_entailment.py and demo.py in the same folder 

Run demo.py

An example PTL Knowledge base to use is:

"(\*(p|\-p))\>(\-p&\-r)", "\*p\>\*\-f", "\*r\>\*f"




