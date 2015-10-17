open Printf 
type t = int
let example = ref ""
let property = ref "shape"

let usage = sprintf "usage: %s -e example  [-c]" Sys.argv.(0)

let myint = ref 0
 
let arglist = [
  ("-n",Arg.Unit (fun () -> Globals.nullpointer_dereferencing := true), ": checking Null Pointers dereferencing");
  ("-d",Arg.Unit (fun () -> Globals.danglingpointer := true), ": checking Dangling Pointers dereferencing");
  ("-f",Arg.Unit (fun () -> Globals.free_dereferencing := true),  ": checking Free cell dereferencing");
  ("-c",Arg.Unit (fun () -> Globals.cycle := true),  ": checking cycle creation");
  ("-r",Arg.Unit (fun () -> Globals.results := true),  ": prints the results");
  ("-rdir",Arg.String (fun dir -> Globals.results_dir := dir),  ": prints the results in [DIR]");
  ("-t",Arg.Unit (fun () -> Globals.trace := true),  ": including tracing of constraint generation");
  ("-progress",Arg.Unit (fun () -> Globals.progress := true),  ": printing the progress bar");
  ("-p", Arg.String (fun s -> property := s;), ": a specific property");
  ("-e", Arg.String (fun s -> example := s;), ": a specific example");
  			 
]
    
let run_example property = function      
  | "treiber" -> let module M = ForwardAnalysis.Algorithm(Treiber.Reset) in M.verify property  "treiber"
	| "HMset" -> let module M = ForwardAnalysis.Algorithm(HMset.Reset) in M.verify property "HMset"
  | "MS" -> let module M = ForwardAnalysis.Algorithm(MS.Reset) in M.verify property "MS"
	| "TwolockMS" -> let module M = ForwardAnalysis.Algorithm(TwolockMS.Reset) in M.verify property "twolockMS"
  | "HSYstack" -> let module M = ForwardAnalysis.Algorithm(HSYstack.Reset) in M.verify property "HSYstack"
	| "DGLM" -> let module M = ForwardAnalysis.Algorithm(DGLM.Reset) in M.verify property "DGLM"
  | "ElimMS" -> let module M = ForwardAnalysis.Algorithm(ElimMS.Reset) in M.verify property "ElimMS"
  | "HWqueue" -> let module M = ForwardAnalysis.Algorithm(HWqueue.Reset) in M.verify property "HWqueue"
  | "THarris" -> let module M = ForwardAnalysis.Algorithm(THarris.Reset) in M.verify property "THarris"
  | "MMichael" -> let module M = ForwardAnalysis.Algorithm(MMichael.Reset) in M.verify property "MMichael"
  | "OHearn" -> let module M = ForwardAnalysis.Algorithm(Vechev.Reset) in M.verify property "Vechev"
	| "Vechev_CAS" -> let module M = ForwardAnalysis.Algorithm(Vechev_CAS.Reset) in M.verify property "Vechev_CAS"
  | "Vechev_DCAS" -> let module M = ForwardAnalysis.Algorithm(Vechev_DCAS.Reset) in M.verify property "Vechev_DCAS"
  | "Optimistic" -> let module M = ForwardAnalysis.Algorithm(Optimistic.Reset) in M.verify property "Optimistic"
  | "Pessimistic" -> let module M = ForwardAnalysis.Algorithm(Pessimistic.Reset) in M.verify property "pessimistic"
  | "Lazyset" -> let module M = ForwardAnalysis.Algorithm(Lazyset.Reset) in M.verify property "LazySet"  
  | "Unordered" -> let module M = ForwardAnalysis.Algorithm(Unordered.Reset) in M.verify property "Unordered"    
  | "CCAS" -> let module M = ForwardAnalysis.Algorithm(CCAS.Reset) in M.verify property "CCAS"  
  | "RDCSS" -> let module M = ForwardAnalysis.Algorithm(RDCSS.Reset) in M.verify property "RDCSS"   
let _ = begin
  Arg.parse arglist (fun arg -> raise (Arg.Bad (sprintf "========================Bad argument========================: %s\n" arg))) usage;
	if not (List.mem !property ["shape"; "linearizability"]) then 
		begin 
			print_string "============================ Wrong property:==============================\n";
		()
		end
	else
  run_example !property !example
end;;
	
