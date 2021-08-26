Require Import Coq.Program.Program.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Import List.ListNotations.
Require Import Coq.NArith.NArith.
Require Import MiniP4.Syntax.

Axiom hash: list bool -> list bool.

Fixpoint all_some {A: Type} (l: list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | x :: l =>
    match x, all_some l with
    | Some x, Some l' => Some (x :: l')
    | _, _ => None
    end
  end.

Definition both_some {A B: Type} (a: option A) (b: option B) : option (A * B) :=
  match a, b with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.

Instance bitstring_eq_dec: EqDec bitstring eq := ltac:(typeclasses eauto).
Program Fixpoint val_eqdec (x y: val) : {x = y} + {x <> y} :=
  match x, y with
  | VBits xs, VBits ys => if xs == ys then in_left else in_right
  | VBool x, VBool y => if x == y then in_left else in_right
  | VPair x1 x2, VPair y1 y2 => if val_eqdec x1 y1
                               then if val_eqdec x2 y2
                                    then in_left
                                    else in_right
                               else in_right
  | VUnit, VUnit => in_left
  | _, _ => in_right
  end.
Next Obligation.
  congruence.
Qed.
Next Obligation.
  congruence.
Qed.
Next Obligation.
  intro; subst.
  destruct y.
  - eapply H2; auto.
  - eapply H; auto.
  - eapply H1; auto.
  - eapply H0; auto.
Qed.
Solve All Obligations with (cbn; intros; intuition congruence).

Instance val_eq_dec: EqDec val eq := val_eqdec.

Definition interp_binop (o: binop) '((v1, v2): val * val) : val :=
  match o with
  | Eq => if v1 == v2 then VBits [true] else VBits [false]
  | Neq => if v1 == v2 then VBits [false] else VBits [true]
  end.

Fixpoint to_num (l: list bool) : N :=
  match l with
  | [] => 0
  | true :: l => 1 + 2 * to_num l
  | false :: l => 2 * to_num l
  end.

Fixpoint to_list_positive (n: positive) : list bool :=
  match n with
  | xH => [true]
  | xO n => false :: to_list_positive n
  | xI n => true :: to_list_positive n
  end.

Definition to_list (n: N) : list bool :=
  match n with 
  | N0 => [false]
  | Npos n => to_list_positive n
  end.

Program Definition interp_uop (o: uop) (v: val) : option val :=
  match o with
  | Hash =>
    match v with
    | VBits v => Some (VBits (hash v))
    | _ => None
    end
  | Sum =>
    match v with
    | VPair v1 v2 =>
      Some (VBits (match v1, v2 with
                   | VBits b1, VBits b2 => to_list (to_num b1 + to_num b2)%N
                   | _, _ => to_list 0%N
                   end))
    | _ => None
    end
  end.

Fixpoint interp_exp (s: state) (e: exp) : option val :=
  match e with
  | Var x => Env.find x s.(store)
  | EBool b => Some (VBool b)
  | Bits bs => Some (VBits bs)
  | Tuple exp1 exp2 =>
    match interp_exp s exp1, interp_exp s exp2 with
    | Some v1, Some v2 =>
      Some (VPair v1 v2)
    | _, _ => None
    end
  | Proj1 e =>
    match interp_exp s e with
    | Some (VPair v1 _) => Some v1
    | _ => None
    end
  | Proj2 e =>
    match interp_exp s e with
    | Some (VPair _ v2) => Some v2
    | _ => None
    end
  | Tt => Some VUnit
  | BinOp o e1 e2 =>
    option_map (interp_binop o) (both_some (interp_exp s e1) (interp_exp s e2))
  | UOp o e =>
    match interp_exp s e with
    | Some v => interp_uop o v
    | None => None
    end
  end.

Definition set_store (s: state) (e: Env.t name val) : state :=
  {| store := e;
     in_pkt := s.(in_pkt);
     out_pkt := s.(out_pkt) |}.

Definition set_in_pkt (s: state) (pk: list bool) : state :=
  {| store := s.(store);
     in_pkt := pk;
     out_pkt := s.(out_pkt) |}.

Definition grow_out_pkt (s: state) (pk: list bool) : state :=
  {| store := s.(store);
     in_pkt := s.(in_pkt);
     out_pkt := s.(out_pkt) ++ pk |}.

Definition set_type_env (s: def_state) (e: Env.t name typ) : def_state :=
  {| type_env := e;
     tables := s.(tables);
     rules := s.(rules) |}.

Definition set_tables (s: def_state) (e: Env.t name table) : def_state :=
  {| type_env := s.(type_env);
     tables := e;
     rules := s.(rules) |}.

Definition splitn {A} (n: nat) (l: list A) : list A * list A :=
  (firstn n l, skipn n l).

Fixpoint extr (pk: list bool) (t: typ) : option (val * list bool) :=
  match t with
  | Bit n => 
    let '(h, pk) := splitn n pk in
    Some (VBits h, pk)
  | Bool =>
    let '(h, pk) := splitn 1 pk in
    match h with
    | [b] => Some (VBool b, pk)
    | _ => None
    end
  | Prod t1 t2 =>
    match extr pk t1 with
    | Some (v1, pk) =>
      match extr pk t2 with
      | Some (v2, pk) =>
        Some (VPair v1 v2, pk)
      | None => None
      end
    | None => None
    end
  | Unit => Some (VUnit, pk)
  end.

Definition interp_extr (s: state) (x: name) (t: typ) : option state :=
  match extr s.(in_pkt) t with
  | Some (v, pk) =>
    Some {| store := Env.bind x v s.(store);
            in_pkt := pk;
            out_pkt := s.(out_pkt) |}
  | None => None
  end.

Fixpoint emit (v: val) : list bool :=
  match v with
  | VBits bs => bs
  | VBool b => [b]
  | VPair v1 v2 =>
    emit v1 ++ emit v2
  | VUnit => []
  end.

Definition interp_emit (s: state) (v: val) : option state :=
  let bs := emit v in
  Some (grow_out_pkt s bs).

Fixpoint find_rule (k: val) (rules: list rule) : option rule :=
  match rules with
  | r :: rules =>
    if k == r.(rule_match)
    then Some r
    else find_rule k rules
  | [] => None
  end.

Definition assign (s: state) (x: name) (v: val) : state :=
  set_store s (Env.bind x v s.(store)).

Definition bind_arg (s: state) : (name * typ) * val -> state :=
  fun '((x, _), v) => assign s x v.

Definition bind_args (ps: list (name * typ)) (args: list val) (s: state) : option state :=
  if List.length ps == List.length args
  then Some (List.fold_left bind_arg (List.combine ps args) s)
  else None.

Fixpoint interp_act (s: state) (a: action) : option state :=
  match a with
  | ActAssign x e =>
    option_map (assign s x) (interp_exp s e)
  | ActSeq a1 a2 =>
    match interp_act s a1 with
    | Some s => interp_act s a2
    | None => None
    end
  | ActNop =>
    Some s
  end.

Definition interp_table (s: state) (tbl: table) (rules: list rule) : option state :=
  match interp_exp s tbl.(table_key) with
  | Some key =>
    match find_rule key rules with
    | Some r =>
      interp_act s (List.nth r.(rule_action) tbl.(table_acts) ActNop)
    | None => None
    end
  | None => None
  end.

Fixpoint interp_cmd (fuel: nat) (d: def_state) (s: state) (c: cmd) : option state :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | Assign x e =>
      option_map (assign s x) (interp_exp s e)
    | Nop => Some s
    | Seq c1 c2 =>
      match interp_cmd fuel d s c1 with
      | Some s =>
        interp_cmd fuel d s c2
      | None => None
      end
    | If e c1 c2 =>
      match interp_exp s e with
      | Some (VBits [true]) =>
        interp_cmd fuel d s c1
      | Some _ =>
        interp_cmd fuel d s c2
      | None =>
        None
      end
    | Assume e
    | Assert e =>
      match interp_exp s e with
      | Some (VBits [true]) =>
        Some s
      | Some _ => None
      | None => None
      end
    | Extr x => 
      match Env.find x d.(type_env) with
      | Some t => interp_extr s x t
      | None => None
      end
    | Emit x =>
      match Env.find x s.(store) with
      | Some v => interp_emit s v
      | None => None
      end
    | Apply t =>
      match Env.find t d.(tables), Env.find t d.(rules) with
      | Some tbl, Some rules => interp_table s tbl rules
      | _, _ => None
      end
    end
  end.

Program Fixpoint interp_defn (fuel: nat) (ds: def_state) (s: state) (d: defn) : option (def_state * state) :=
  match d with
  | VarDecl t x e =>
    option_map (fun v => (set_type_env ds (Env.bind x t ds.(type_env)),
                       assign s x v))
               (interp_exp s e)
  | Table t keys acts =>
    Some (set_tables ds (Env.bind t {| table_key:=keys; table_acts := acts |} ds.(tables)), s)
  end.

Fixpoint interp_defns (fuel: nat) (ds: def_state) (s: state) (defs: list defn) : option (def_state * state) :=
  match defs with
  | [] => Some (ds, s)
  | d :: defs =>
    match interp_defn fuel ds s d with
    | Some (ds, s) => interp_defns fuel ds s defs
    | None => None
    end
  end.

Definition interp_prog (fuel: nat) (ds: def_state) (s: state) (p: prog) : option state :=
  let '(defs, c) := p in
  match interp_defns fuel ds s defs with
  | Some (ds, s) =>
    interp_cmd fuel ds s c
  | None =>
    None
  end.
