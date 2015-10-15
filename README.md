
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
This is just early prototype, we have not made C-like syntax inputs for users. The input now need to be modeled by ocaml. Each algorithm statement or controller rule is modeled by an ocaml function. Let us show an example of how the push method of treiber stack is modeled.

  let s = Label.global (3,"S", 1)

  let null = Label.nil

  let x = Label.local (0,"x",1)

  let t = Label.local (1,"t",1)
  
  let initial_predicates  = C.create_stack s 
  
  let predicate_transformers =
  
   [
  
   (new R.init_thread 0 1 [|x;t|]);
  
   (new R.new_cell 1 4 x);
  
   (new R.assign 4 5 t s);
  
   (new R.dot_next_assign 5 6 x t);
   
   (new R.cas_fail 6 (7) s t x);
   
   (new R.atomic 6 8 [ (new R.cas_success 6 8 s t x); (new R.validate_push 8 7 x);]); (*LINEARIZATION POINT*)
   
   (new R.kill_thread 7 0);
  
  ]

end

In this method, variable declaration is modeld by the top four statements. 

