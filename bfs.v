(*Authors: Syed Mohammed Arshad Zaidi, Anuj Sharma*)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Notation "( x , y )" := (pair x y).
Notation "[ ]" := nil.

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
 | None => Some []
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

 Fixpoint node_in_list (l: list node) (n: node) : bool :=
   match l with
   | [] => false
   | h::t => match nodes_equal h n with
             | true => true
             | false => node_in_list t n
             end
   end.

 
 Fixpoint unique_list (r: list node) (l: list node) : list node :=
   match l with
   | [] => r
   | h::t => match node_in_list r h with
             | false => unique_list (r ++ [h]) t
             | true => unique_list r t
             end
   end.

 (*
Inductive bfs_ind : graph -> list node -> Prop :=
| bfs_empty : bfs_ind [] []
| bfs_single : forall n, bfs_ind [(n,[])] [n]
| bfs_list_s: forall g n l l' n', bfs_ind [(n,l');g] l -> bfs_ind [(n',[n]);(n,l');g] (n':: l).

  *)
 
Definition inputGraph := [(Node 1, [Node 2; Node 3]);(Node 2, [Node 3;Node 4]); (Node 3, [Node 4; Node 5]);(Node 4, [Node 5; Node 6]);(Node 5, [Node 6;Node 7]); (Node 6, [Node 7; Node 8]); (Node 7,[Node 8; Node 9]); (Node 8,[Node 9;Node 10]); (Node 9,[]); (Node 10,[])].

Definition totalNodes := (ANum 4).

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
               |Some l => Some (unique_list [] ([n]++(tl current_stack) ++ l))
             end
 end.

Fixpoint bfs_aux (graph : list (node * (list node))) (current_stack:list node):
  option (list node) :=
   match graph with
   | [] => Some []
   | [x] => Some [fst x] 
   | x::xs  => match (bfs_iteration xs (current_stack ++ (snd x))) with
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
   | [] => None
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

Definition g5: list (node * list node) := [(Node 1, [Node 2; Node 3]);(Node 2, [Node 3;Node 4]) ;(Node 3,[Node 4; Node 5]); (Node 4, []); (Node 5, [])].
Compute bfs g5.

Definition empty_graph: list (node * list node) := [].

Compute bfs inputGraph.

Theorem bfs_computation_graph1 :
  bfs inputGraph = Some [Node 1; Node 2; Node 3; Node 4; Node 5; Node 6; Node 7; Node 8; Node 9; Node 10].
Proof.
  simpl. reflexivity. Qed.


Theorem bfs_computation_graph2 :
  bfs g1 = Some [Node 1; Node 2; Node 3; Node 4].
Proof.
  simpl. reflexivity. Qed.


Theorem bfs_computation_graph3 :
  bfs g5 = Some [Node 1; Node 2; Node 3; Node 4; Node 5].
Proof.
  simpl. reflexivity. Qed.


Theorem bfs_computation_empty_graph :
  bfs empty_graph = None.
Proof.
  simpl. reflexivity. Qed.

(*Function to convert graph to list. *)
Fixpoint convert_graph_to_list(g: list (node * list node)) :=
  match g with
  | [] => []
  | h::t => match h with
            | (x,y) => x::convert_graph_to_list t
            end
  end.

Definition remove_option_graph (g: option(list node)) :=
  match g with
  | None => []
  | Some x => x
  end.


Theorem remove_option_graph_assoc (a: node*(list node))(g: list (node * (list node)))(n: nat):
  In (Node n) (remove_option_graph (bfs (a :: g))) = In (Node n) (remove_option_graph (bfs ([a]))) \/ In (Node n) (remove_option_graph (bfs (g))).
Proof.
Admitted.

Theorem convert_assoc (a: node*(list node))(g: list (node * (list node))) : convert_graph_to_list (a :: g) = (convert_graph_to_list [a]) ++ (convert_graph_to_list g).
Proof.
Admitted.

Theorem convert_single (a: node*(list node)) :
  convert_graph_to_list [a] = [fst a].
Proof.
  Admitted.

Theorem remove_assoc (a: node * (list node)) (g: list (node * (list node))) : remove_option_graph (bfs (a :: g)) = remove_option_graph(bfs [a]) ++ remove_option_graph(bfs g).
Proof.
  Admitted.

(* Theorem to prove bfs conversion of any graph g is equivalent to all its node traversed in order of bfs. *)
Theorem bfs_comprehensive (n: node) (g: list (node * list node)) :
  convert_graph_to_list g = remove_option_graph (bfs g).
Proof.
  induction g.
  - simpl. reflexivity.
  - rewrite convert_assoc. rewrite remove_assoc. rewrite <- IHg. 
    rewrite convert_single. simpl. reflexivity.
Qed.

(* Theorem to prove for every node n in graph it is also present in bfs of graph *)
Theorem bfs_node_present (n: node)(g: list (node * list node)) :
  In n (convert_graph_to_list g) -> In n (remove_option_graph (bfs g)).
Proof.
  intros. induction n.
  - induction g.
    + simpl in H. inversion H.
    + rewrite remove_assoc. simpl.  rewrite convert_assoc in H.
      rewrite convert_single in H. simpl in H. destruct H.
      * left. apply H.
      * right. apply IHg. apply H.
Qed.