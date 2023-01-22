From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
Require Import
  Schulze.Notations.

Import ListNotations.

Section MatrixDef.

  Context 
    {Node : Type}
    {finN : List Node}
    {Hndec : ∀ (c d : Node), {c = d} + {c <> d}}.


  Context 
    {R : Type}
    {zeroR oneR : R} (* 0 and 1 *)
    {plusR mulR : R -> R -> R}.


  Declare Scope Mat_scope.
  Delimit Scope Mat_scope with R.
  Bind Scope Mat_scope with R.
  Local Open Scope Mat_scope.


  Local Notation "0" := zeroR : Mat_scope.
  Local Notation "1" := oneR : Mat_scope.
  Local Infix "+" := plusR : Mat_scope.
  Local Infix "*" := mulR : Mat_scope.

  Definition Matrix := Node -> Node -> R.

  (* returns the cth row of m *)
  Definition get_row (m : Matrix) (c : Node) : Node -> R := 
    fun d => m c d.

  (* returns the cth column of m *)
  Definition get_col (m : Matrix) (c : Node) : Node -> R :=
    fun d => m d c.

  (* zero matrix, additive identity of plus *)
  Definition zero_matrix : Matrix := 
    fun _ _ => 0.
  


  (* identity matrix, mulitplicative identity of mul *)
  (* Idenitity Matrix *)
  Definition I : Matrix := 
    fun (c d : Node) =>
    match Hndec c d with 
    | left _ => 1
    | right _ => 0 
    end.
  
  
  (* transpose the matrix m *)
  Definition transpose (m : Matrix) : Matrix := 
    fun (c d : Node) => m d c.

  
  (* pointwise addition to two matrices *)
  Definition matrix_add (m₁ m₂ : Matrix) : Matrix :=
    fun c d => (m₁ c d + m₂ c d).



  Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
    match l with 
    | [] => 0
    | h :: t => f h + sum_fn f t
    end.


  (* generalised matrix multiplication *)
  Definition matrix_mul_gen (m₁ m₂ : Matrix) 
    (l : List Node) : Matrix :=
    λ (c d : Node),
      sum_fn (fun y => (m₁ c y * m₂ y d)) l.



  
  (* Specialised form of general multiplicaiton *)
  Definition matrix_mul (m₁ m₂ : Matrix) := 
    matrix_mul_gen m₁ m₂ finN.

  
  Fixpoint matrix_exp_unary (m : Matrix) (n : nat) : Matrix :=
    match n with 
    | 0%nat => I 
    | S n' => matrix_mul m (matrix_exp_unary m n')
    end.
  
  
    
  Fixpoint repeat_op_ntimes_rec 
    (e : Matrix) (n : positive) : Matrix :=
    match n with
    | xH => e
    | xO p => let ret := repeat_op_ntimes_rec e p in matrix_mul ret ret
    | xI p => let ret := repeat_op_ntimes_rec e p in 
      matrix_mul e (matrix_mul ret ret)
    end.

  
  Definition matrix_exp_binary (e : Matrix) (n : N) :=
    match n with
    | N0 => I
    | Npos p => repeat_op_ntimes_rec e p 
    end.



  Fixpoint exp_r (a : R) (n : nat) : R :=
    match n with 
    | O => 1
    | S n' => a * exp_r a n'
    end.


  Fixpoint sum_r (a : R) (n : nat) : R :=
    match n with
    | O => 1
    | S n' => (sum_r a n') + exp_r a n
    end.


  (* Print Grammar constr. *)
  Local Infix "+M" := matrix_add (at level 50) : Mat_scope.
  Local Infix "*M" := matrix_mul (at level 40) : Mat_scope.

  Fixpoint partial_sum_mat (m : Matrix) (n : nat) : Matrix:=
    match n with
    | O => I 
    | S n' => (partial_sum_mat m n') +M (matrix_exp_unary m n)
    end.


End MatrixDef.

(* This section contains proofs of various proof 
only assuming Semiring axioms. However, it
*)
Section MatProofSemiRing.

  (* Assumption on Node. Node 
    is finite type *)
  Context
    {Node : Type}
    {finN : List Node}
    {dupN : NoDup finN} (* finN is duplicate free *)
    {lenN : (2 <= List.length finN)}
    {memN : ∀ x : Node, In x finN}.


  Context
    {R : Type}
    {zeroR oneR : R} (* 0 and 1 *)
    {plusR mulR : R -> R -> R}.
  

  Declare Scope Mat_scope.
  Delimit Scope Mat_scope with R.
  Bind Scope Mat_scope with R.
  Local Open Scope Mat_scope.


  Local Notation "0" := zeroR : Mat_scope.
  Local Notation "1" := oneR : Mat_scope.
  Local Infix "+" := plusR : Mat_scope.
  Local Infix "*" := mulR : Mat_scope.


  Context
    (* Semiring Axiom on R *)
    {zero_left_identity_plus  : ∀ r : R, 0 + r = r}
    {zero_right_identity_plus : ∀ r : R, r + 0 = r}
    {plus_associative : ∀ a b c : R, a + (b + c) =
      (a + b) + c}
    {plus_commutative  : ∀ a b : R, a + b = b + a}
    {plus_idempotence : ∀ a : R, a + a = a}
    {zero_stable : ∀ a : R, 1 + a = 1}
    {one_left_identity_mul  : ∀ r : R, 1 * r = r}
    {one_right_identity_mul : ∀ r : R, r * 1 = r}
    {mul_associative : ∀ a b c : R, a * (b * c) =
      (a * b) * c}
    {left_distributive_mul_over_plus : ∀ a b c : R, 
      a * (b + c) = a * b + a * c}
    {right_distributive_mul_over_plus : ∀ a b c : R, 
      (a + b) * c = a * c + b * c}
    {zero_left_anhilator_mul  : ∀ a : R, 0 * a = 0}
    {zero_right_anhilator_mul : ∀ a : R, a * 0 = 0}.



  Lemma zero_add_left : 
  ∀ c d m,
    @matrix_add Node R plusR 
      (@zero_matrix Node R zeroR) m c d = m c d.
  Proof.
    intros c d m.
    unfold matrix_add, zero_matrix.
    rewrite zero_left_identity_plus.
    exact eq_refl.
  Qed.

  Lemma zero_add_right : 
    ∀ c d m, 
    @matrix_add Node R plusR m 
    (@zero_matrix Node R zeroR) c d = m c d.
  Proof.
    intros c d m.
    unfold matrix_add, zero_matrix.
    rewrite zero_right_identity_plus.
    exact eq_refl.
  Qed. 

  Lemma matrix_add_assoc : 
    ∀ m₁ m₂ m₃ c d, 
    @matrix_add _ _ plusR m₁ (@matrix_add _ _ plusR m₂ m₃) c d =
    @matrix_add _ _ plusR (@matrix_add Node R plusR m₁ m₂) m₃ c d.
  Proof using Node R plusR plus_associative.
    unfold matrix_add; intros.
    rewrite plus_associative;
    exact eq_refl.
  Qed.

  
  Lemma matrix_add_comm : 
    ∀ m₁ m₂ c d, 
    @matrix_add Node R plusR m₁ m₂ c d =
    @matrix_add Node R plusR m₂ m₁ c d.
  Proof using Node R plusR plus_commutative.
    intros; unfold matrix_add.
    rewrite plus_commutative.
    reflexivity.
  Qed.

  (* 
    1. Finish This proof.
    2. Write a function that computes 
      Schulze path as an inductive data type
  *)


End MatProofSemiRing.



