
# Linearizability
Contact: Cong Quy Trinh, Department of Information Technology, Uppsala University
Email: cong-quy.trinh@it.uu.se

This prototype is designed to verify lilearizability of concurrent algorithms implemented using singly-linked lists. 
The prototype is implemented in OCAML and supports algorithms with both fixed and non-fixed linearization points. 

Target algorithms are list-based concurrent algorithms such as stacks, queues, ordered sets, unordered sets and CCAS.

Installation
===============

You will need: 

* ocaml compiler (tested with version 4.01.1)
* make  

Getting Prototype
===============

   Git users can clone the prototype as follows:

   $ git clone https://github.com/quytc/Linearizability.git

   Non git users may find it easier to download the latest revision as
   a zip archive:

   https://github.com/quytc/Linearizability/archive/master.zip

Running Command
==================

   The following assumes that you are in a shell in the main directory
   of the prototype.

   1. Build as usual. You only need to type make commands as follow:

     $ make

   2. Then you can run the prototype to verify the algorithm by the command 
   
      2.1. Verifying shape properties:

         $./run -p shape -e algorithm_name

      2.2. Verifying linearizability:
      
         $./run -p linearizability -e algorithm_name
      
      Where algorithm_name is the name of the input algorithm.
      
   For example: You can verify linearizability of Treiber algorithm by the command: 
   
          $./run -p linearizability -e treiber. 
   
   Here is the list of algorithms that you can run:  
      + Stack: treiber, HSYstack
      + Queue: MS, TwolockMS; ElimMS; HWqueue; DGLM
      + Lock-based set: Pessimistic, Optimistic, Lazyset
      + Lock-free set: Vechev, Vechev_CAS, Vechev_DCAS, HMset, THarris, MMichael
      + Unordered set: Unordered
      + CAS algorithm: CCAS, RDCSS

The algorithm source codes can be found in the folder /src. For example, treiber.ml stores the source code of treiber algorithm

Input file format
==================   
This is just early prototype, we have not made C-like syntax inputs for users. The input now need to be modelled by OCAML. Each algorithm statement or controller rule is modeled by an OCAML function. Let us show an example of how the push method of treiber stack is modelled.

-------------------------------------------------------------------------------------------
  1:let s = Label.global (3,"S", 1)

  2:let null = Label.nil

  3:let x = Label.local (0,"x",1)

  4:let t = Label.local (1,"t",1)
  
  5:let initial_predicates  = C.create_stack s 
  
  6:let predicate_transformers =
  
   [
  
      7: (new R.init_thread 0 1 [|x;t|]);
  
      8: (new R.new_cell 1 4 x);
  
      9: (new R.assign 4 5 t s);
  
      10:(new R.dot_next_assign 5 6 x t);
   
      11:(new R.cas_fail 6 (7) s t x);
   
      12:(new R.atomic 6 8 [ (new R.cas_success 6 8 s t x); (new R.validate_push 8 7 x);]); 
   
      13:(new R.kill_thread 7 0);
  
  ]

end

 -------------------------------------------------------------------------------------------

Each modelled statement consists of two program counters and an OCAML function modelling the input statement. The first counter specifies the current program counter of the statement whereas the second program counter specified the next program counter of the statement.

In this method, the modelling is done as following:
   + Variable declaration is modelled by the top four statements. 
   + Stack initialisation is modelled by the statement at line 5. 
   + The statement at line 8 models the malloc statement(x = new Node) 
   + The statements at lines 9,10,11,12 model the assign statement(t = s), pointer assignment statement(x.next = t) and CAS statements respectively. 
   + Thread initialisation is modelled by the statement at line 7 while return statement is modeled by the statement at line 13. 
   + Finally the controller rule is modelled by statement (new R.validate_push 8 7 x). 
 


It might take some efforts to model algorithms by OCAML therefore if you have any problem with modelling you could contact me for help.


How to make a new algorithm
================== 

Assume that you want to make a new algorithm to verify named abc. You should follow the following steps:
- Create abc.ml and put it in the folder src
- Create abc.mli(same as .mli files of other algorithms) and put it in the folder src
- Add abc.ml to the files list in src/makefile
- Add this sentence | "abc" -> let module M = ForwardAnalysis.Algorithm(abc.Reset) in M.verify property "abc" to the run_example function in src/main.ml

