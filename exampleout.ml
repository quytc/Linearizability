global: s;local: x, t, x’, t’;create_stack s;0: initial_thread (x,t): 					:22: [x’ := new;]							:33: [t := S;] 							:44: [x.next := t;]						:55: [cas_success (s,t,x); linearize (push, x, true); ]		:65: [cas_fail (s,t,x);]						:36: [kill_thread] 						:0 
