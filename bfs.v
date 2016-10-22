(*Authors: Syed Mohammed Arshad Zaidi, Anuj Sharma*)

Require Import Coq.Lists.List.

(* This is representation of single node of a graph *)
Inductive node :=
 Node : nat -> node.

(* This is representation of graph *)
Definition graph :=
 list (node * list node).

(* Raw function to check equality of nodes. *)
Definition are_nodes_equal :
  forall (x y:node),
    {x = y} + {x <> y}. repeat (decide equality). Defined.

(* Wrapper function on are_nodes_equal to verify equality of nodes. *)
Definition nodes_equal a b :=
  if are_nodes_equal a b then true else false.