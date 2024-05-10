# Group Identification

 - Kun Fang, 105623, kun.fang@tecnico.ulisboa.pt
 - Nicolás Castro, 1105833, nicolas.castro@tecnico.ulisboa.pt
 - Guilherme Chalupa, 90264, guilhermechalupa@tecnico.ulisboa.pt


# Implemented Features

Task 1: - We extended the datatype com in the file Imp.v with the constructs:
		. NDChoice (c1 c2 : com)
		. Guard (b : bexp) (c : com)
	- Defined a new notation for each construct.
	- Defined examples p1 and p2 as specified.

Task 2: - We fully defined the step-indexed evaluator ceval_step in the file Interpreter.v.
	  It gets every example correct.
	- We prooved p1_equals_p2.
	- We sadly couldn't proove ceval_step_more.

Task 3: - Definition of the Evaluation Relationship: The ceval relationship is defined to represent the evaluation of commands in a state. Various rules are provided for different types of commands.
	- Sample Evaluation Evidence: Sample evaluation evidence for different programs, showing how the ceval evaluation relationship works in action.
	- Definition of Behavioral Equivalence and Proof of Properties: 
		. Defining the notions of behavioral equivalence (cequiv) between programs and testing tactics.
		. Prove some important properties about non-deterministic choice.

# Extras
TODO: Identify and describe additional work that you have done,
      so that it can be considered for extra credits.
