(** ブーリアン型に関するモジュールです。 *)

Require Googology_In_Coq.Base.
Require Googology_In_Coq.Function.
Require Googology_In_Coq.Sum.
Require Googology_In_Coq.Unit.

(** ライブラリを要求します。 *)

Import Googology_In_Coq.Base.
Import Googology_In_Coq.Function (Function).
Import Googology_In_Coq.Sum (Sum).
Import Googology_In_Coq.Unit (Unit).

(** ライブラリを開きます。 *)

Inductive Bool@{i | } : Type@{i} := wrap : Sum@{i} Unit@{i} Unit@{i} -> Bool.
(* from: originally defined by Hexirp *)

(** ブーリアン型です。 *)

Definition
  unwrap@{i | } : Bool@{i} -> Sum@{i} Unit@{i} Unit@{i}
    := fun x : Bool@{i} => match x with wrap x_v => x_v end
.
(* from: originally defined by Hexirp *)

(** ブーリアン型です。 *)

Definition
  false@{i | } : Bool@{i} := wrap (Sum.left Unit@{i} Unit@{i} Unit.unit)
.
(* from: originally defined by Hexirp *)

(** ブーリアン型の第一構築子です。 *)

Definition
  true@{i | } : Bool@{i} := wrap (Sum.right Unit@{i} Unit@{i} Unit.unit)
.
(* from: originally defined by Hexirp *)

(** ブーリアン型の第二構築子です。 *)

Definition
  matching@{i | }
      (P : Bool@{i} -> Type@{i})
      (constructor_false : P false)
      (constructor_true : P true)
    : forall x : Bool@{i}, P x
    :=
      fun x : Bool@{i} =>
        match x as x_ return P x_ with
          wrap x_v
            =>
              Sum.matching
                Unit@{i}
                Unit@{i}
                (fun x_v_ : Sum@{i} Unit@{i} Unit@{i} => P (wrap x_v_))
                (
                  fun x_v_L : Unit@{i} =>
                    Unit.matching
                      (
                        fun x_v_L_ : Unit@{i} =>
                          P (wrap (Sum.left Unit@{i} Unit@{i} x_v_L_))
                      )
                      constructor_false
                      x_v_L
                )
                (
                  fun x_v_R : Unit@{i} =>
                    Unit.matching
                      (
                        fun x_v_R_ : Unit@{i} =>
                          P (wrap (Sum.right Unit@{i} Unit@{i} x_v_R_))
                      )
                      constructor_true
                      x_v_R
                )
                x_v
        end
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  matching_nodep@{i | }
      (P : Type@{i})
      (constructor_false : P)
      (constructor_true : P)
  : Bool@{i} -> P
  := matching (fun x_ : Bool@{i} => P) constructor_false constructor_true
.
(* from: originally defined by Hexirp *)

(** 場合分けです。 *)

Definition
  and@{i | } : Bool@{i} -> Bool@{i} -> Bool@{i}
    :=
      matching_nodep
        (Bool@{i} -> Bool@{i})
        (
          Function.apply
            Bool@{i}
            Bool@{i}
            (Function.const Bool@{i} Bool@{i} false)
        )
        (Function.apply Bool@{i} Bool@{i} (Function.id Bool@{i}))
.
(* from: originally defined by Hexirp *)

(** 論理積です。 *)

Definition
  or@{i | } : Bool@{i} -> Bool@{i} -> Bool@{i}
    :=
      matching_nodep
        (Bool@{i} -> Bool@{i})
        (Function.apply Bool@{i} Bool@{i} (Function.id Bool@{i}))
        (
          Function.apply
            Bool@{i}
            Bool@{i}
            (Function.const Bool@{i} Bool@{i} true)
        )
.
(* from: originally defined by Hexirp *)

(** 論理和です。 *)

Definition
  not@{i | } : Bool@{i} -> Bool@{i}
    := matching_nodep Bool@{i} true false
.
(* from: originally defined by Hexirp *)

(** 否定です。 *)
