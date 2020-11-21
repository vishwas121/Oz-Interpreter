# Homework 2 CS350A
Vishwas choudhary 180876

## Code inspired from previous year assignments
All parts done and merged.


## Directions
To run the code, please use the Mozart interpreter in emacs (using ozc does not work). The state of the environment and store are outputted in the emulator buffer. 'Browse' is used to print environment and the SAS.

Assign the variable `Prog` with the AST (in line 12). Now run the file.

## Description

 Environment is printed as a nested list with first element representing the identifier and second element representing the corresponding SAS variable. SAS variables are represented by Natural numbers. The values in SAS are records represented as `value(w)` where `w` is any value or `t` for true and `f` for false. Procedure values are represented as tuples with first being the procedure definition and second value being the list of free variables and the corresponding SAS variables.

 ### Note: Since `proc` is a keyword in Oz, `proc1` is used.

 The state of the SAS and environment are printed after instruction is executed, i.e., after the statement is popped from the semantic stack. 

 For `add` and `product`, two statements are added to the operational semantics.

- Add is done by `[add ident(x) ident(y) ident(z)]`. This denotes the statement `Z = X+Y`. 
- Product is done by `[mul ident(x) ident(y) ident(z)]`. This denotes the statement `Z = X*Y`. 
