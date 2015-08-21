# Linearizability

UpLin is a prototype which verifies linearizabilitis of concurrent algorithms implemented by singly-linked lists. 
UpLin is implemented by Ocalm and currently, it supports both fixed and non-fixed linearization points of algorithms. 

Target programs are list-based concurrent algothims such as stacks, queues, ordered sets, unordered sets and CCAS.

Installation
************

The prototype can be compiled and installed on Window, MAC, UNIX-like systems. The only requirement is to install OCAML on your 
computer.  You can follow the instruction from the OCAML webpage https://ocaml.org/docs/install.html#Windows  

Getting Prototype
===============

   Git users can clone UpLin as follows:

   $ git clone https://github.com/quytc/Linearizability.git

   Non git users may find it easier to download the latest revision as
   a zip archive:

   https://github.com/quytc/Linearizability/archive/master.zip

Running Command
==================

   The following assumes that you are in a shell in the main directory
   of UpLin.

   1. Build as usual. You only need to type make command as follow:
      
     $ make

   2. Then you can run the prototype to verify the algorithm by the command 
   
      $/run -p property_name -e algorithm_name

      where property_name can be "shape" or "linearizability" and algorithm_name is the name of the verified algorithm.

Algorithm Structure
==================   
 Structure 
-----------
  Global: < var >
                
// Structure of each method

Local:   < var >

 < initial_data_structure > < para > 

< initial_thread > < pc-1 > < pc-2 >  [ < local var >]

  < statement_name > pc-3 pc-4 < para >
  
  < statement_name > pc-4 pc-5 < para >
  
  < statement_name > pc-5 pc-6 < para >
  
  .....
  
  < statement_name > pc-(n-1) pc-n < para >

 < kill_thread > <pc-n> <pc-1>

| Prototype Statement                             | 	      Description		    |
|--------------------------|--------------------------------|
| assign x y               |          x := y          	    |
| data_assign x d          |         x.data := d     	    |
| data_less_than x y       |         x.data < y.data         |
| data_equal x d           |         x.data = d      	    |
| data_variable_equal x y  |         x.data = y.data 	    |
| data_inequal x d          |         x.data <> d		|
| data_variable_inequal x y   | 			      x.data <> y.data|
|equal x y		|			      x = y|
|inequal x y		|	    x <> y|
|cas x y z 		|	   if x = y then x := z|
|cas x d1 d2 		|	  if x.data = d1 then x.data := d2|
|cas x d y z 		 |          if x.data = d && x.next = y then x.next := z|
|next_equal		|	    x.next = y|
|next_inequal		|	 x.next <> y|
|dot_next_assign x y 	|	    x.next := y|
|assign_dot_next x y	|	 x := y.next|
|linearize m a b	|	 obs (m, a, b): m: method,	a: observer value b: return value  |
|linearize m1 a1 b1 m2 [pc-1,..,pc-n]  a2 b2 ord   |  if ord = 1 then obs (m1, a1, b1); obs (m2, a2, b2) else obs (m2, a2, b2); obs (m1, a1, b1): pc-1,...,pc-n are program counters of the method m2|



