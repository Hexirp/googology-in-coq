(* Run with -nois. *)

Require Import GiC.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)
Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** 宇宙 (universe) について表示するように設定します。 *)
Set Printing Universes.

(** conc_p_idpath です。 *)
Definition conc_p_1@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p idpath) p
  := fun p => match p with idpath => idpath end.

(** conc_idpath_p です。 *)
Definition conc_1_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc idpath p) p
  := fun p => match p with idpath => idpath end.

(** conc_p_conc_q_r です。 *)
Definition conc_p_cqr@{i} {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w), Path@{i} (conc p (conc q r)) (conc (conc p q) r)
  := fun p q r => match r with idpath => match q with idpath => match p with idpath => idpath end end end.

(** conc_conc_p_q_r です。 *)
Definition conc_cpq_r@{i} {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w), Path@{i} (conc (conc p q) r) (conc p (conc q r))
  := fun p q r => match r with idpath => match q with idpath => match p with idpath => idpath end end end.

(** conc_p_inv_p です。 *)
Definition conc_p_vp@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p (inv p)) idpath
  := fun p => match p with idpath => idpath end.

(** conc_inv_p_p です。 *)
Definition conc_vp_p@{i} {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc (inv p) p) idpath
  := fun p => match p with idpath => idpath end.

(** conc_inv_p_conc_p_q です。 *)
Definition conc_vp_cpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z), Path@{i} (conc (inv p) (conc p q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_p_conc_inv_p_q です。 *)
Definition conc_p_cvpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z), Path@{i} (conc p (conc (inv p) q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_conc_p_q_inv_q です。 *)
Definition conc_cpq_vq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z), Path@{i} (conc (conc p q) (inv q)) p
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** conc_conc_p_inv_q_q です。 *)
Definition conc_cpvq_q@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z), Path@{i} (conc (conc p (inv q)) q) p
  := fun p q => let
    t := match q
      as q'
      in Path _ z'
      return forall p' : Path@{i} x z', Path@{i} (conc (conc p' (inv q')) q') p'
      with idpath => fun p' => match p' with idpath => idpath end
    end
  in
    t p.

(** inv_conc_p_q です。 *)
Definition inv_cpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z), Path@{i} (inv (conc p q)) (conc (inv q) (inv p))
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** inv_conc_inv_p_q です。 *)
Definition inv_cvpq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z), Path@{i} (inv (conc (inv p) q)) (conc (inv q) p)
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** inv_conc_p_inv_q です。 *)
Definition inv_cpvq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z), Path@{i} (inv (conc p (inv q))) (conc q (inv p))
  := fun p q => let
    t := match q
      as q'
      in Path _ z'
      return forall p' : Path@{i} x z', Path@{i} (inv (conc p' (inv q'))) (conc q' (inv p'))
      with idpath => fun p' => match p' with idpath => idpath end
    end
  in
    t p.

(** inv_conc_inv_p_inv_q です。 *)
Definition inv_cvpvq@{i} {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} y x) (q : Path@{i} z y), Path@{i} (inv (conc (inv p) (inv q))) (conc q p)
  := fun p q => match p with idpath => match q with idpath => idpath end end.

(** inv_inv_p です。 *)
Definition inv_vp@{i} {A : Type@{i}} {x y z : A}
  : forall p : Path@{i} x y, Path@{i} (inv (inv p)) p
  := fun p => match p with idpath => idpath end.
