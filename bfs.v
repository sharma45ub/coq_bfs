(*Authors: Syed Mohammed Arshad Zaidi, Anuj Sharma*)

Require Import Coq.Lists.List.

(*This is representation of single node of a graph*)
Inductive node :=
 Node : nat -> node.

(*This is representation of graph*)
Definition graph :=
 list (node * list node).
