(*Authors: Syed Mohammed Arshad Zaidi, Anuj Sharma*)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Notation "( x , y )" := (pair x y).
(* This is representation of single node of a graph *)
Inductive node :=
 Node : nat -> node.



(* Raw function to check equality of nodes. *)
Definition nodes_equal (x y:node): bool:=
    match x with |Node a => (match y with |Node b => beq_nat a b end) end. 

 (* Raw function to search a given node in a given graph. *)
 Definition search_node (ps : list (node * (list node)) ) (x:node): option (list node) :=
 match find (fun p => nodes_equal x (fst p)) ps with
 | Some p => Some (snd p)
 | None => None
 end.
 
 (* Wrapper function on search_node for searching node in a given graph. *)
 Definition is_node_present (ps:list(node* (list node))) (default:list node) (x:node) : list node :=
 match search_node ps x with
 | None => default
 | Some y => y
 end.
 
 (** Since pairs are used quite a bit, it is nice to be able to
 write them with the standard mathematical notation [(x,y)] instead
 of [pair x y].  We can tell Coq to allow this with a [Notation]
 declaration. *)
 

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
 Definition customGraph := [(Node 1, [Node 2; Node 3]);(Node 2, [Node 4;Node 5]); (Node 3, [Node 6; Node 7]);(Node 4, [Node 8; Node 9])].
 
 Check customGraph.
 
 Compute (search_node customGraph (Node 2)).

 Compute (is_node_present customGraph [] (Node 2)).
 
 Compute (nodes_equal (Node 2) (Node 4)).
 
 Compute (is_node_present customGraph [] customNode).

 (* This function will remove node from graph which is passed. *)
 Fixpoint remove_node (g: list(node*(list node))) (r: node) : list(node*(list node)) :=
   match g with
   | [] => []
   | h::t => match h with
             | (x,y) => match nodes_equal x r with
                        | true => t
                        | false => h::(remove_node t r)
                        end
             end
   end.

 Fixpoint remove_node_list (l: list node) (n: node) : list node :=
   match l with
   | [] => []
   | h::t => match nodes_equal n h with
             | true => remove_node_list t n
             | false => h::(remove_node_list t n)
             end
   end.

 (* Function for bfs traversal of custom graph. *)
 (* Fixpoint bfs (g:list(node*(list node))) (s:list node) : list node :=
   match s with
   | [] => []
   | h::t => h::(bfs g (t ++ (is_node_present g [] h)))
   end.
  *)

 Inductive id : Type :=
 | Id : nat -> id.

 Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

 Definition total_map (A:Type) := id -> A.

 Definition t_empty {A:Type} (v : A) : total_map A :=
   (fun _ => v).

 Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.
 
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

 
Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(* Function for bfs traversal of custom graph. *)
 (* Fixpoint bfs (g:list(node*(list node))) (s:list node) : list node :=
   match s with
   | [] => []
   | h::t => h::(bfs g (t ++ (is_node_present g [] h)))
   end.
  *)

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').


Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
    END.

Definition fact_in_coq' : com :=
  Y ::= ANum 1;;
  Z ::= ANum 3;;
 
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
    END.


Compute t_update (t_update (t_update empty_state X 2) Z 0) Y 2.
Compute t_update empty_state X 2.

(*
(X ::= ANum 2) / empty_state \\ t_update empty_state X 2
*)

Example test_fact: fact_in_coq'
   / empty_state
   \\ (t_update(t_update(t_update(t_update(t_update(t_update(t_update(t_update empty_state Y 1) Z 3) Y 3) Z 2) Y 6) Z 1) Y 6) Z 0).
Proof.
  unfold fact_in_coq'.
  apply E_Seq with (t_update empty_state Y 1).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state Y 1) Z 3).
    + apply E_Ass. reflexivity.
    + apply E_WhileLoop with (t_update(t_update(t_update(t_update empty_state Y 1) Z 3) Y 3) Z 2).
      * reflexivity.
      * apply E_Seq with (t_update(t_update (t_update empty_state Y 1) Z 3) Y 3).
        { apply E_Ass. reflexivity. }
        { apply E_Ass. reflexivity. }
      * apply E_WhileLoop with (t_update(t_update(t_update(t_update(t_update(t_update empty_state Y 1) Z 3) Y 3) Z 2) Y 6) Z 1).
        { reflexivity. }
        { apply E_Seq with (t_update(t_update(t_update(t_update(t_update empty_state Y 1) Z 3) Y 3) Z 2) Y 6).
          { apply E_Ass. reflexivity. }
          { apply E_Ass. reflexivity. }
        }
        { apply E_WhileLoop with (t_update(t_update(t_update(t_update(t_update(t_update(t_update(t_update empty_state Y 1) Z 3) Y 3) Z 2) Y 6) Z 1) Y 6) Z 0).
          { reflexivity. }
          { apply E_Seq with (t_update(t_update(t_update(t_update(t_update(t_update(t_update empty_state Y 1) Z 3) Y 3) Z 2) Y 6) Z 1) Y 6).
            { apply E_Ass. reflexivity. }
            { apply E_Ass. reflexivity. } }
          { apply E_WhileEnd. simpl. reflexivity. } }
Qed.

            
 Compute is_node_present customGraph [] (Node 4).

 (* Compute bfs customGraph [Node 1].*)

 (*Fixpoint graph_to_list (g: list(node*(list node))) : list node :=
   match g with
   | [] => []
   | h::t => match h with
             | (x,y) => [x] ++ y ++ (graph_to_list t)
             end
   end.

 Fixpoint node_in_list (l: list node) (n: node) : bool :=
   match l with
   | [] => false
   | h::t => match nodes_equal h n with
             | true => true
             | false => node_in_list t n
             end
   end.

 Compute remove_node_list (graph_to_list customGraph) (Node 3).
 Compute node_in_list (graph_to_list customGraph) (Node 21).
 Check [Node 1] ++ [(Node 2); (Node 3)].

 Fixpoint unique_list (r: list node) (l: list node) : list node :=
   match l with
   | [] => r
   | h::t => match node_in_list r h with
             | false => unique_list (r ++ [h]) t
             | true => unique_list r t
             end
   end.

 Compute graph_to_list customGraph.
 Compute unique_list [] (graph_to_list customGraph).
  
 
 Definition removed_one := remove are_nodes_equal (Node 1) (unique_list [] (graph_to_list customGraph)).
 Definition removed_two := remove are_nodes_equal (Node 2) removed_one.
 Compute removed_two.
 Definition removed_three := remove are_nodes_equal (Node 3) removed_two.
 Definition removed_four := remove are_nodes_equal (Node 4) removed_three.
 Compute removed_four.
*)

 (* Following lemma will state for removal of nodes in each iteration of bfs which results in termination of bfs traversal. *)
 (* Lemma bfs_iteration_custom : forall nd grph_nodes,
  length grph_nodes >= length (remove are_nodes_equal nd grph_nodes) /\
  (In nd grph_nodes -> length grph_nodes > length (remove are_nodes_equal nd grph_nodes)).
Proof.
  intros; induction grph_nodes; split; intros; simpl; try (omega).
  - inversion H.
  - simpl. destruct IHgrph_nodes as [H1 H2].
  remember (are_nodes_equal nd a) as visited_a. destruct visited_a; simpl; omega.
  - simpl. destruct IHgrph_nodes as [H1 H2].
    + destruct H as [H3 | H4]. remember (are_nodes_equal nd a) as visited_a. destruct visited_a; simpl.
      * omega.
      * subst. destruct n.
        { reflexivity. }
      * remember (are_nodes_equal nd a) as visited_a. destruct visited_a; simpl.
        { omega. }
        { remember (H2 H4) as H5. omega. }
Qed.

(* Defining notation for cons *)
Notation "x :: l" := (cons x l).


Inductive bfs_ind : graph -> list node -> Prop :=
| bfs_empty : bfs_ind [] []
| bfs_single : forall n, bfs_ind [(n,[])] [n]
| bfs_list_s: forall g n l l' n', bfs_ind [(n,l');g] l -> bfs_ind [(n',[n]);(n,l');g] (n':: l).

  *)
 
Definition inputGraph := [(Node 1, [Node 2; Node 3]);(Node 2, [Node 4;Node 5]); (Node 3, [Node 6; Node 7]);(Node 4, [Node 8; Node 9])].

Definition totalNodes := (ANum 4).

(* This will hold all vertices of current iteration. *)
(* Initializing it with starting vertex. *)
(*Definition current_stack := [Node 1].*)

(* Function to check if our node list is empty or not. 
Definition not_empty (l: list node) : bexp :=
  match l with
    |[] => BTrue
    | _ => BFalse
  end.

Definition get_next_node :=
  match current_stack with
  | [] => []
  | h::t => [h]
  end.
 *)

Fixpoint get_next_node_num_iter (n: nat) (l : list node): option (nat) :=
  match n with
   | O => match l with
            | [] => None
            | h::t => match h with | (Node x) => Some x end
          end
   | S m => match l with
            | [] => None
            | h::t => get_next_node_num_iter m t            
            end
  end.

Definition get (l:list node): option node :=
  match l with
  |[] => None
  |x::xs => Some x
  end.
                                
Definition pop (l:list node): option (list node) :=
  match l with
  |[] => None
  |x::xs => Some xs
  end.


Definition bfs_iteration  (graph : list (node * list node)) (current_stack : list node) : option (list node):=
  match get current_stack with 
 | None => None                                  
 | Some n => match search_node graph n with
               |None => None
               |Some l => Some ([n]++(tl current_stack) ++ l)
             end
 end.

Fixpoint bfs_aux (graph : list (node * (list node))) (current_stack:list node):
  option (list node) :=
   match graph with
   | [] => Some []
   | [x] => Some [fst x] 
   | x::xs  => match (bfs_iteration xs (snd x)) with
               |None => None
               |Some z =>
                match (pop z) with
                |None => None
                |Some p => match (bfs_aux xs p) with
                           |None => None
                           |Some r  =>  match get z with
                                        |None => None
                                        |Some w => Some ([w] ++ r)
                                                        end
                           end
                end
               end
   end.
   

Definition bfs (graph : list (node * (list node))) : option (list node) :=
  match graph with
   | [] => Some []
   | x::xs =>  match (bfs_aux xs (snd x)) with
               |None => None
               |Some r => Some ((fst x) :: r)
               end
end.

Definition g1 := [(Node 1, [Node 2; Node 3]);(Node 2, [Node 3;Node 4]); (Node 3, []);(Node 4, [])].
Compute (bfs g1).

Definition g2: list (node * list node) := [(Node 1, [])].
Compute (bfs g2).

Definition g3: list (node * list node) := [(Node 1, [Node 2]);(Node 2, []) ].
Compute (bfs g3).

Definition g4: list (node * list node) := [(Node 1, [Node 2; Node 3]);(Node 2, []) ;(Node 3,[])].
Compute (bfs g4).


Compute (bfs inputGraph).
  
