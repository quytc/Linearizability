
# Linearizability
Contact: Cong Quy Trinh, Department of Information Technology, Uppsala University
Email: cong-quy.trinh@it.uu.se

This prototype is designed to verify lilearizability of concurrent algorithms implemented by singly-linked lists. 
The prototype is implemented by OCAML and supports algorithms with both fixed and non-fixed linearization points. 

Target algorithms are list-based concurrent algothims such as stacks, queues, ordered sets, unordered sets and CCAS.

Installation
===============

The prototype can be compiled and installed on Window, MAC, UNIX-like systems. The only requirement is to install OCAML on your computer.  You can follow instructions from OCAML webpage https://ocaml.org/docs/install.html#Windows to install OCAML  

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

   1. Build as usual. You only need to type make command as follow:
      
     $ make

   2. Then you can run the prototype to verify the algorithm by the command 
   
      2.1. Verifying shape properties:

         $/run -p shape -e algorithm_name

      2.2. Verifying linearizability:
      
         $/run -p linearizability -e algorithm_name
      
      Where algorithm_name is the name of the verified algorithm.
      
   For example: You can verify linearizability of Treiber algorithm by the command: $/run -p linearizability -e Treiber. 
   
   The algorthm examples can be found in \src\examples including 
      + Stack: Treiber, HSYstack
      + Queue: MS, TwolockMS; ElimMS; HWqueue; DGLM
      + Lock-based set: Pessimistic, Optimistic, Lazyset
      + Lock-free set: Vechev, Vechev_CAS, Vechev_DCAS, HMset, THarris, MMichael
      + Unordered set: Unordered
      + CAS algorithm: CCAS, RDCSS


Input file format
==================   
This is just early prototype, we have not made C-like syntax inputs for users. The input now need to be modeled by OCAML. Each algorithm statement or controller rule is modeled by an OCAML function. Let us show an example of how the push method of treiber stack is modeled.

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
In this method, variable declaration is modeld by the top four statements. Stack initialisation is modeled by the statement at line 5. The statement at line 8 models a malloc statement(x = new Node) whereas the statements at lines 9,10,11,12 model assign statement(t = s), pointer assignment statement(x.next = t) and CAS statements respectively. Thread initialisation is modeled by the statement in line 7 while return statement is modeled by the statement at line 13. Finally the controller rule is modeld by statement (new R.validate_push 8 7 x). It takes some time to model algorithms by ocaml therefore if you have any problem with modeling you could contact me for help.

