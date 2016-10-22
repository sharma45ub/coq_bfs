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

 (* Raw function to search a given node in a given graph. *)
 Definition search_node {A:Type} (ps:list(node*A)) (x:node) :=
 match find (fun p => nodes_equal x (fst p)) ps with
 | Some p => Some (snd p)
 | None => None
 end.
 
 (* Wrapper function on search_node for searching node in a given graph. *)
 Definition is_node_present {A:Type} (ps:list(node*A)) (default:A) (x:node) :=
 match search_node ps x with
 | None => default
 | Some y => y
 end.
 
 (** Since pairs are used quite a bit, it is nice to be able to
 write them with the standard mathematical notation [(x,y)] instead
 of [pair x y].  We can tell Coq to allow this with a [Notation]
 declaration. *)
 
 Notation "( x , y )" := (pair x y).
 (** As with pairs, it is more convenient to write lists in
 familiar programming notation.  The following declarations
 allow us to use [::] as an infix [cons] operator and square
 brackets as an "outfix" notation for constructing lists. *)
 
 Notation "x :: l" := (cons x l)
 (at level 60, right associativity).
 Notation "[ ]" := nil.
 Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
 
 Definition customNode := Node 1.
 Definition noCustomNode := Node 404.
 Definition customGraph := [(Node 1, [Node 2; Node 3]);(Node 2, [Node 3;Node 4])].
 
 Check customGraph.
 
 Compute (search_node customGraph (Node 2)).
 
 Compute (nodes_equal (Node 2) (Node 4)).
 
 Compute (is_node_present customGraph [] customNode).
