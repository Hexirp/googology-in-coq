(* Run with -nois. *)
(** [GiC.Path.OneDim] は、ある型とその上の道が一次元の亜群の構造として見做せることに関する定理を提供します。

    具体的には、任意の型 [A] と [Path A _ _] が [idpath] と [conc] と [inv] によって亜群になることに由来する様々な定理を示しています。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.

(** 必要なライブラリをインポートします。 *)

Import GiC.Base.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** ** [idpath] の [conc] においての単位元性 *)

(** [conc p idpath] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L70 *)
Definition conc_p_1@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p idpath) p
  := fun p => match p with idpath => idpath end.

(** [conc idpath p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L76 *)
Definition conc_1_p@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc idpath p) p
  := fun p => match p with idpath => idpath end.

(** ** [conc] の結合法則 *)

(** [conc p (conc q r)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L82 *)
Definition conc_p_cqr@{i | } {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w),
    Path@{i} (conc p (conc q r)) (conc (conc p q) r)
  := fun p q r => match r
    with idpath => match q
      with idpath => match p
        with idpath => idpath
      end
    end
  end.

(** [conc (conc p q) r] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L89 *)
Definition conc_cpq_r@{i | } {A : Type@{i}} {x y z w : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{i} z w),
    Path@{i} (conc (conc p q) r) (conc p (conc q r))
  := fun p q r => match r
    with idpath => match q
      with idpath => match p
        with idpath => idpath
      end
    end
  end.

(** ** [inv] の [conc] においての逆元性 *)

(** [conc p (inv p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L97 *)
Definition conc_p_vp@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc p (inv p)) idpath
  := fun p => match p with idpath => idpath end.

(** [conc (inv p) p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L103 *)
Definition conc_vp_p@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (conc (inv p) p) idpath
  := fun p => match p with idpath => idpath end.

(** ** 結合法則と逆元 *)

(** [conc (inv p) (conc p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L110 *)
Definition conc_vp_cpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (conc (inv p) (conc p q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** [conc p (conc (inv p) q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L117 *)
Definition conc_p_cvpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z),
    Path@{i} (conc p (conc (inv p) q)) q
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** [conc (conc p q) (inv q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L124 *)
Definition conc_cpq_vq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (conc (conc p q) (inv q)) p
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** [conc (conc p (inv q) q] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L131 *)
Definition conc_cpvq_q@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z),
    Path@{i} (conc (conc p (inv q)) q) p
  := fun p q => let
    t := match q
      as q'
      in Path _ z'
      return forall p' : Path@{i} x z',
        Path@{i} (conc (conc p' (inv q')) q') p'
      with idpath => fun p' => match p' with idpath => idpath end
    end
  in
    t p.

(** ** 逆元の分配法則 *)

(** [inv (conc p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L141 *)
Definition inv_cpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{i} (inv (conc p q)) (conc (inv q) (inv p))
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** [inv (conc (inv p) q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L148 *)
Definition inv_cvpq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} x z),
    Path@{i} (inv (conc (inv p) q)) (conc (inv q) p)
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** [inv (conc p (inv q))] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L155 *)
Definition inv_cpvq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} x z) (q : Path@{i} y z),
    Path@{i} (inv (conc p (inv q))) (conc q (inv p))
  := fun p q => let
    t := match q
      as q'
      in Path _ z'
      return forall p' : Path@{i} x z',
        Path@{i} (inv (conc p' (inv q'))) (conc q' (inv p'))
      with idpath => fun p' => match p' with idpath => idpath end
    end
  in
    t p.

(** [inv (conc (inv p) (inv q))] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L161 *)
Definition inv_cvpvq@{i | } {A : Type@{i}} {x y z : A}
  : forall (p : Path@{i} y x) (q : Path@{i} z y),
    Path@{i} (inv (conc (inv p) (inv q))) (conc q p)
  := fun p q => match p with idpath => match q with idpath => idpath end end.

(** ** 逆元の逆元 *)

(** [inv (inv p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L168 *)
Definition inv_vp@{i | } {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (inv (inv p)) p
  := fun p => match p with idpath => idpath end.

(** ** 関手 *)

(** [A] と [Path A _ _] による亜群から [B] と [Path B _ _] による亜群への関手は、 [f : A -> B] と [ap f : Path A _ _ -> Path B (f _) (f _)] により与えられます。 *)

(** [ap f idpath] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L367 *)
Definition ap_f_1@{i j | } {A : Type@{i}} {B : Type@{j}} (f : A -> B) (x : A)
  : Path@{j} (ap f (idpath x)) (idpath (f x))
  := idpath.

(** [ap f (conc p q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L378 *)
Definition ap_f_cpq@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y z : A}
  : forall (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{j} (ap f (conc p q)) (conc (ap f p) (ap f q))
  := fun p q => match q with idpath => match p with idpath => idpath end end.

(** [ap f (inv p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L406 *)
Definition ap_f_vp@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A}
  : forall p : Path@{i} x y, Path@{j} (ap f (inv p)) (inv (ap f p))
  := fun p => match p with idpath => idpath end.
