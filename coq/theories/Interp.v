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
  | VTuple xs, VTuple ys => if list_eq_dec val_eqdec xs ys then in_left else in_right
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
  - eapply H1; auto.
  - eapply H; auto.
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
    | VTuple vs =>
      Some (VBits (to_list (List.fold_right (fun v acc =>
                         match v with
                         | VBits l => (to_num l + acc)%N
                         | _ => acc
                         end)
                      0%N vs)))
    | _ => None
    end
  end.

Fixpoint interp_exp (s: state) (e: exp) : option val :=
  match e with
  | Var x => Env.find x s.(store)
  | Bits bs => Some (VBits bs)
  | Tuple exps =>
    option_map VTuple (all_some (List.map (interp_exp s) exps))
  | Proj e n =>
    match interp_exp s e with
    | Some (VTuple vs) => nth_error vs n
    | _ => None
    end
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
     type_env := s.(type_env);
     pkt := s.(pkt);
     acts := s.(acts);
     tables := s.(tables) |}.

Definition set_type_env (s: state) (e: Env.t name typ) : state :=
  {| store := s.(store);
     type_env := e;
     pkt := s.(pkt);
     acts := s.(acts);
     tables := s.(tables) |}.

Definition set_pkt (s: state) (pk: list bool) : state :=
  {| store := s.(store);
     type_env := s.(type_env);
     pkt := pk;
     acts := s.(acts);
     tables := s.(tables) |}.

Definition set_acts (s: state) (e: Env.t name action) : state :=
  {| store := s.(store);
     type_env := s.(type_env);
     pkt := s.(pkt);
     acts := e;
     tables := s.(tables) |}.

Definition set_tables (s: state) (e: Env.t name (table * list rule)) : state :=
  {| store := s.(store);
     type_env := s.(type_env);
     pkt := s.(pkt);
     acts := s.(acts);
     tables := e |}.

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
  | Prod ts =>
    match List.fold_left (fun acc t =>
                            match acc with
                            | Some (vs, pk) =>
                              match extr pk t with
                              | Some (v, pk) =>
                                Some (vs ++ [v], pk)
                              | None => None
                              end
                            | None => None
                            end) ts (Some ([], pk))
    with
    | Some (vs, pk) =>
      Some (VTuple vs, pk)
    | None =>
      None
    end
  end.

Definition interp_extr (s: state) (x: name) (t: typ) : option state :=
  match extr s.(pkt) t with
  | Some (v, pk) =>
    Some {| store := Env.bind x v s.(store);
            type_env := s.(type_env);
            pkt := pk;
            acts := s.(acts);
            tables := s.(tables) |}
  | None => None
  end.

Fixpoint emit (v: val) : list bool :=
  match v with
  | VBits bs => bs
  | VBool b => [b]
  | VTuple vs => List.fold_left (fun bs v => bs ++ emit v) vs []
  end.

Definition interp_emit (s: state) (v: val) : option state :=
  let bs := emit v in
  Some (set_pkt s bs).

Fixpoint find_rule (s: state) (k: val) (rules: list rule) : option name :=
  match rules with
  | r :: rules =>
    match interp_exp s r.(rule_match) with
    | Some v => if k == v then Some r.(rule_action) else find_rule s k rules
    | None => None
    end
  | [] => None
  end.

Fixpoint interp_cmd (fuel: nat) (s: state) (c: cmd) : option state :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | Assign x e =>
      option_map (fun v => set_store s (Env.bind x v s.(store)))
                 (interp_exp s e)
    | Block cs => List.fold_right
                   (fun c s => match s with
                            | Some s => interp_cmd fuel s c
                            | None => None
                            end)
                   (Some s)
                   cs
    | If e c1 c2 =>
      match interp_exp s e with
      | Some (VBits [true]) =>
        interp_cmd fuel s c1
      | Some _ =>
        interp_cmd fuel s c2
      | None =>
        None
      end
    | Extr x => 
      match Env.find x s.(type_env) with
      | Some t => interp_extr s x t
      | None => None
      end
    | Emit x =>
      match Env.find x s.(store) with
      | Some v => interp_emit s v
      | None => None
      end
    | Apply t =>
      match Env.find t s.(tables) with
      | Some (tbl, rules) => interp_table fuel s tbl rules
      | None => None
      end
    | Call a =>
      interp_call fuel s a
    end
  end
with interp_call (fuel: nat) (s: state) (a: name) : option state :=
       match fuel with
       | 0 => None
       | S fuel =>
         match Env.find a s.(acts) with
         | Some act => interp_cmd fuel s act.(body)
         | None => None
         end
       end
with interp_table (fuel: nat) (s: state) (tbl: table) (rules: list rule) : option state :=
       match fuel with
       | 0 => None
       | S fuel =>
         match interp_exp s tbl.(table_key) with
         | Some key =>
           match find_rule s key rules with
           | Some act => interp_call fuel s act
           | None => None
           end
         | None => None
         end
       end.

Program Fixpoint interp_defn (fuel: nat) (s: state) (d: defn) : option state :=
  match d with
  | VarDecl t x e =>
    option_map (fun v =>
                  set_type_env
                    (set_store s (Env.bind x v s.(store)))
                    (Env.bind x t s.(type_env)))
               (interp_exp s e)
  | Action a c =>
    Some (set_acts s (Env.bind a {| body := c |} s.(acts)))
  | Table t keys actions =>
    Some (set_tables s (Env.bind t ({| table_key:=keys; table_acts := actions |}, []) s.(tables)))
  end.

Fixpoint interp_defns (fuel: nat) (s: state) (defs: list defn) : option state :=
  match defs with
  | [] => Some s
  | d :: defs =>
    match interp_defn fuel s d with
    | Some s => interp_defns fuel s defs
    | None => None
    end
  end.

Definition interp_prog (fuel: nat) (s: state) (p: prog) : option state :=
  let '(defs, c) := p in
  match interp_defns fuel s defs with
  | Some s =>
    interp_cmd fuel s c
  | None =>
    None
  end.
