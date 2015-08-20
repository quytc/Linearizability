# Linearizability

UpLin is a prototype which verifies linearizabilitis of concurrent algorithms implemented by singly-linked lists. 
UpLin is implemented by Ocalm and currently, it supports both fixed and non-fixed linearization points of algorithms. 

Target programs are list-based concurrent algothims such as stacks, queues, ordered sets, unordered sets and CCAS.

Installation
************

UpLin can be compiled and installed on Window, MAC, UNIX-like systems. The only requirement is to install OCAML on your 
computer.  You can follow the instruction from the OCAML webpage https://ocaml.org/docs/install.html#Windows  

Getting UpLin
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
      where property_name can be "shape" or "linearizability" and algorithm_name is the name of the verified    algorithm.
   
Input Structure
==================
   
   
Linearization Point
==================   
