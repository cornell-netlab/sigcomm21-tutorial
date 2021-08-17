Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Import List.ListNotations.
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

Definition bitstring_eq_dec (b1 b2: bitstring) : {b1 = b2} + {b1 <> b2}.
Admitted.
Definition val_eq_dec (v1 v2: val) : {v1 = v2} + {v1 <> v2}.
Admitted.

Definition interp_binop (o: binop) '((v1, v2): val * val) : val :=
  match o with
  | Eq => if val_eq_dec v1 v2 then VBits [true] else VBits [false]
  | Neq => if val_eq_dec v1 v2 then VBits [false] else VBits [true]
  end.

Definition to_num (l: list bool) : nat.
Admitted.
Definition to_list (n: nat) : list bool.
Admitted.

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
                         | VBits l => to_num l + acc
                         | _ => acc
                         end)
                      0 vs)))
    | _ => None
    end
  end.

Fixpoint interp_expr (s: state) (e: exp) : option val :=
  match e with
  | Var x => Env.find x s.(store)
  | Bits bs => Some (VBits bs)
  | Tuple exps =>
    option_map VTuple (all_some (List.map (interp_expr s) exps))
  | Proj e n =>
    match interp_expr s e with
    | Some (VTuple vs) => nth_error vs n
    | _ => None
    end
  | BinOp o e1 e2 =>
    option_map (interp_binop o) (both_some (interp_expr s e1) (interp_expr s e2))
  | UOp o e =>
    match interp_expr s e with
    | Some v => interp_uop o v
    | None => None
    end
  end.

Definition set_store (s: state) (e: Env.t name val) : state :=
  {| store := e;
     pkt := s.(pkt);
     acts := s.(acts);
     tables := s.(tables) |}.

Definition interp_table (s: state) (tbl: table) (rules: list rule) : option state.
Admitted.

Program Fixpoint interp_cmd (fuel: nat) (s: state) (c: cmd) : option state :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | Assign x e =>
      option_map (fun v => set_store s (Env.bind x v s.(store)))
                 (interp_expr s e)
    | Block cs => List.fold_right
                   (fun c s => match s with
                            | Some s => interp_cmd fuel s c
                            | None => None
                            end)
                   (Some s)
                   cs
    | If e c1 c2 =>
      match interp_expr s e with
      | Some (VBits [true]) =>
        interp_cmd fuel s c1
      | Some _ =>
        interp_cmd fuel s c2
      | None =>
        None
      end
    | Extr x => _
    | Emit x => _
    | Apply t =>
      match Env.find t s.(tables) with
      | Some (tbl, rules) => interp_table s tbl rules
      | None => None
      end
    | Call a =>
      match Env.find a s.(acts) with
      | Some act => interp_cmd fuel s act.(body)
      | None => None
      end
    end
  end.
