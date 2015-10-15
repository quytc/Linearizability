
# Linearizability

This is a prototype which verifies linearizabilitis of concurrent algorithms implemented by singly-linked lists. 
The prototype is implemented by Ocalm and currently, it supports both fixed and non-fixed linearization points of algorithms. 

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

Input file format
==================   
This is just early prototype, we have not made C-like syntax inputs for users. The input need to be modeled in ocaml structure. Each algorithm statement or controller rule is modeled by an ocaml function. Let us show an example of how the ocaml input look like

module C = Constraint
  module R = Rule   
(*////////////////////////////////////////////////////////////////////TREIBER//////////////////////////////////////////////////////////////////////*)

module Reset : Example.E = struct
  let name = "Treibe33r"
  let s = Label.global (3,"S", 1)
  let null = Label.nil
  let free = Label.free
  let x = Label.local (0,"x",1)
  let t = Label.local (1,"t",1)
  let x' = Label.local (0,"x'",1)
  let t' = Label.local (1,"t'",1)
  let initial_predicates  =
  C.create_stack s 
  let predicate_transformers =
   [
    (* ============================ push ============================ *)
   (new R.atomic 0 1 [(new R.init_thread 0 1 [|x;t|]);]);
   (new R.new_cell 1 4 x);
   (new R.assign 4 5 t s);
   (new R.dot_next_assign_local 5 6 x t);
   (new R.atomic 6 (-1) [(new R.cas_fail 6 (-1) s t x);]);
   (new R.kill_variable (-1) 4 t);
   (new R.atomic 6 7 [ (new R.cas_success 6 77 s t x);
   (new R.validate_push 77 7 x);]); (*LINEARIZATION POINT*)
   (new R.kill_thread 7 0);
   (* ============================ pop =============================== *)
   (new R.atomic 0 12 [(new R.init_thread 0 12 [|x';t'|]);]);
   (new R.atomic 12 13 [(new R.assign 12 13 t' s);]);
   (new R.atomic 12 18 [(new R.assign 12 (-1) t' s);(new R.equality (-1) (-2) t' null);(new R.validate_pop_empty (-2) 18 t');]);
   (new R.atomic 13 18 [(new R.equality 13 (18) t' null);]);
   (new R.in_equality 13 15 t' null);
   (new R.assign_dot_next 15 17 x' t');
   (new R.atomic 17 12 [(new R.cas_fail 17 (-1) s t' x'); 
   (new R.kill_variable (-1) (-2) t');(new R.kill_variable (-2) 12 x');]);		
   (new R.atomic 17 (18) [(new R.cas_success 17 (21) s t' x');
   (new R.validate_pop (21) 18 t');]); (*LINEARIZATION POINT*)
   (new R.kill_thread 18 0);
  ]
end



