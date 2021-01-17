(* Run with -nois. *)
(** [GiC.Path.Functoriality] は、一次元の亜群の構造において関数が関手となることに関する定理を提供します。

    具体的には、 [(f, ap f)] が [(A, Path A x y)] から [(B, Path B x y)] への関手となることに関した定理などがあります。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Base.
Require GiC.Path.Base.
Require GiC.Path.OneDim.
Require GiC.Path.Transposition.

(** 必要なモジュールをインポートします。 *)

Import GiC.Base.
Import GiC.Path.Base.
Import GiC.Path.OneDim.
Import GiC.Path.Transposition.

(** 帰納原理 (induction principle) を生成しないように設定します。 *)

Unset Elimination Schemes.

(** 宇宙多相 (universe polymorphism) について設定します。 *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(** タクティックが使用できるように設定します。 *)

Set Default Proof Mode "Classic".

(** ビュレットを使用しないときにエラーになるように設定します。 *)

Set Default Goal Selector "!".

(** ** 関数の関手性 *)

(** [conc r (ap f (conc p q))] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L386 *)
Definition conc_r_ap_f_cpq@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {w : B} {x y z : A}
  : forall (r : Path@{j} w (f x)) (p : Path@{i} x y) (q : Path@{i} y z),
    Path@{j} (conc r (ap f (conc p q))) (conc (conc r (ap f p)) (ap f q)).
Proof.
  move=> r p q.
  refine (match q with idpath => _ end).
  refine (match p with idpath => _ end).
  change (Path@{j} (conc r (conc idpath idpath)) (conc (conc r idpath) idpath)).
  exact (conc_p_cqr r idpath idpath).
Defined.

(** [conc (ap f (conc p q)) r] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L393 *)
Definition conc_ap_f_cpq_r@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y z : A} {w : B}
  : forall (p : Path@{i} x y) (q : Path@{i} y z) (r : Path@{j} (f z) w),
    Path@{j} (conc (ap f (conc p q)) r) (conc (ap f p) (conc (ap f q) r)).
Proof.
  move=> p q r.

  refine (let t := _ in t r).
  refine
    (match q
      as q'
      in Path _ z'
      return
        forall r' : Path@{j} (f z') w,
          Path@{j}
            (conc (ap f (conc p q')) r')
            (conc (ap f p) (conc (ap f q') r'))
      with idpath => _
    end).
  refine
    (match p
      as p'
      in Path _ y'
      return
        forall r' : Path@{j} (f y') w,
          Path@{j}
            (conc (ap f (conc p' idpath)) r')
            (conc (ap f p') (conc (ap f idpath) r'))
      with idpath => _
    end).

  move=> r'.
  change
    (Path@{j} (conc (conc idpath idpath) r') (conc idpath (conc idpath r'))).
  exact (conc_cpq_r idpath idpath r').
Defined.

(** [inv (ap f p)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L401 *)
Definition inv_ap_f_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A}
  : forall p : Path@{i} x y, Path@{j} (inv (ap f p)) (ap f (inv p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** [ap] の関手性 *)

(** [ap idmap p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L413 *)
Definition ap_idmap_p@{i | }
  {A : Type@{i}} {x y : A}
  : forall p : Path@{i} x y, Path@{i} (ap idmap p) p.
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [ap (comp f g) p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L418 *)
Definition ap_cfg_p@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : B -> C) (g : A -> B) {x y : A}
  : forall p : Path@{i} x y, Path@{k} (ap (comp f g) p) (ap f (ap g p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [ap (fun x => f (g x)) p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L424 *)
Definition ap_lam_x_f_g_x_p@{i j k | }
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : B -> C) (g : A -> B) {x y : A}
  : forall p : Path@{i} x y,
    Path@{k} (ap (fun x : A => f (g x)) p) (ap f (ap g p)).
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [ap (const z) p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L430 *)
Definition ap_const_z_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} {x y : A} (z : B)
  : forall p : Path@{i} x y, Path@{j} (ap (const z) p) idpath.
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** [ap (fun x => z) p] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L430 *)
Definition ap_lam_a_z_p@{i j | }
  {A : Type@{i}} {B : Type@{j}} {x y : A} (z : B)
  : forall p : Path@{i} x y, Path@{j} (ap (fun x : A => z) p) idpath.
Proof.
  move=> p.
  refine (match p with idpath => _ end).
  cbv.
  exact idpath.
Defined.

(** ** [ap] の自然性 *)

(** [Path (conc (ap f q) (p y)) (conc (p x) (ap g q))] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L436 *)
Definition path_cAP_cPA@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (conc (ap f q) (p y)) (conc (p x) (ap g q)).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    exact (conc_1_p (p x)).
  -
    exact (inv (conc_p_1 (p x))).
Defined.

(** [Path (ap f q) (conc (conc (p x) (ap g q)) (inv (p y)))] です。 [Path (conc (ap f q) (p y)) (conc (p x) (ap g q))] を移項したものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L444 *)
Definition path_A_conc_cPA_vP@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (ap f q) (conc (conc (p x) (ap g q)) (inv (p y))).
Proof.
  move=> q.
  refine (fun_Path_cqp_r_Path_q_crvp (p y) (ap f q) (conc (p x) (ap g q)) _).
  exact (path_cAP_cPA p q).
Defined.

(** [Path (conc (p x) (ap f q)) (conc (ap g q) (p y))] です。 *)

(* from: originally defined by Hexirp *)
Definition path_cPA_cAP@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (g x) (f x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (conc (p x) (ap f q)) (conc (ap g q) (p y)).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    exact (conc_1_p (p x)).
  -
    exact (inv (conc_p_1 (p x))).
Defined.

(** [Path (ap f q) (conc (inv (p x)) (conc (ap g q) (p y)))] です。 [Path (conc (p x) (ap f q)) (conc (ap g q) (p y))] を移項したものと解釈できます。 *)

(* from: originally defined by Hexirp *)
Definition path_A_conc_vP_cAP@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (g x) (f x)) {x y : A}
  : forall q : Path@{i} x y,
    Path@{j} (ap f q) (conc (inv (p x)) (conc (ap g q) (p y))).
Proof.
  move=> q.
  refine (fun_Path_crq_p_Path_q_cvrp (conc (ap g q) (p y)) (ap f q) (p x) _).
  exact (path_cPA_cAP p q).
Defined.

(** [Path (conc (ap f q) (p y)) (conc (p x) q)] です。 [Path (conc (ap f q) (p y)) (conc (p x) (ap g q))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L452 *)
Definition path_cAP_cPq@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} (f x) x) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (conc (ap f q) (p y)) (conc (p x) q).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    exact (conc_1_p (p x)).
  -
    exact (inv (conc_p_1 (p x))).
Defined.

(** [Path (ap f q) (conc (conc (p x) q) (inv (p y)))] です。 [Path (ap f q) (conc (conc (p x) (ap g q)) (inv (p y)))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L460 *)
Definition path_A_conc_cPq_vP@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} (f x) x) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (ap f q) (conc (conc (p x) q) (inv (p y))).
Proof.
  move=> q.
  refine (fun_Path_cqp_r_Path_q_crvp (p y) (ap f q) (conc (p x) q) _).
  exact (path_cAP_cPq p q).
Defined.

(** [Path (conc (p x) (ap f q)) (conc q (p y))] です。 [Path (conc (p x) (ap f q)) (conc (ap g q) (p y))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L467 *)
Definition path_cPA_cqP@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} x (f x)) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (conc (p x) (ap f q)) (conc q (p y)).
Proof.
  move=> q.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    exact (conc_p_1 (p x)).
  -
    exact (inv (conc_1_p (p x))).
Defined.

(** [Path (ap f q) (conc (inv (p x)) (conc q (p y)))] です。 [Path (ap f q) (conc (inv (p x)) (conc (ap g q) (p y)))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: originally defined by Hexirp *)
Definition path_A_conc_vP_cqP@{i | }
  {A : Type@{i}} {f : A -> A} (p : forall x : A, Path@{i} x (f x)) {x y : A}
  : forall q : Path@{i} x y, Path@{i} (ap f q) (conc (inv (p x)) (conc q (p y))).
Proof.
  move=> q.
  refine (fun_Path_crq_p_Path_q_cvrp (conc q (p y)) (ap f q) (p x) _).
  exact (path_cPA_cqP p q).
Defined.

(** [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L475 *)
Definition path_conc_crA_cPs_conc_crP_cAs@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  (q : Path@{i} x y) {z w : B} (r : Path@{j} z (f x)) (s : Path@{j} (g y) w)
  : Path@{j}
    (conc (conc r (ap f q)) (conc (p y) s))
    (conc (conc r (p x)) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (conc r (p x)).
  -
    refine (ap2 conc _ _).
    +
      exact (conc_p_1 r).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{j} (conc r (p x)) (conc (conc r (p x)) idpath)).
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (ap g q))] です。 [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] の [s] を [idpath] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L486 *)
Definition path_conc_crA_P_conc_crP_A@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  (q : Path@{i} x y) {z : B} (r : Path@{j} z (f x))
  : Path@{j}
    (conc (conc r (ap f q)) (p y))
    (conc (conc r (p x)) (ap g q)).
Proof.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (conc r (p x)).
  -
    refine (ap (fun pzfx => conc pzfx (p x)) _).
    exact (conc_p_1 r).
  -
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** [Path (conc (ap f q) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] です。 [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] の [r] を [idpath] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L497 *)
Definition path_conc_A_cPs_conc_P_cAs@{i j | }
  {A : Type@{i}} {B : Type@{j}} {f g : A -> B}
  (p : forall x : A, Path@{j} (f x) (g x)) {x y : A}
  (q : Path@{i} x y) {w : B} (s : Path@{j} (g y) w)
  : Path@{j}
    (conc (ap f q) (conc (p y) s))
    (conc (p x) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    refine_conc (conc (p x) idpath).
    +
      exact (conc_1_p (conc (p x) idpath)).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{j} (p x) (conc (p x) idpath)).
    exact (inv (conc_p_1 (p x))).
Defined.

(** [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (conc q s))] です。 [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L508 *)
Definition path_conc_crA_cPs_conc_crP_cqs@{i | }
  {A : Type@{i}} {f : A -> A}
  (p : forall x : A, Path@{i} (f x) x) {x y : A}
  (q : Path@{i} x y) {z w : A} (r : Path@{i} z (f x)) (s : Path@{i} y w)
  : Path@{i}
    (conc (conc r (ap f q)) (conc (p y) s))
    (conc (conc r (p x)) (conc q s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (conc r (p x)).
  -
    refine (ap2 conc _ _).
    +
      exact (conc_p_1 r).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (conc r (p x)) (conc (conc r (p x)) idpath)).
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** [Path (conc (conc r q) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] です。 [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] の [f] を [idmap] としたものと解釈できます。 *)

(* from: invert https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L519 *)
Definition path_conc_crq_cPs_conc_crP_cAs@{i | }
  {A : Type@{i}} {g : A -> A}
  (p : forall x : A, Path@{i} x (g x)) {x y : A}
  (q : Path@{i} x y) {z w : A} (r : Path@{i} z x) (s : Path@{i} (g y) w)
  : Path@{i}
    (conc (conc r q) (conc (p y) s))
    (conc (conc r (p x)) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (conc r (p x)).
  -
    refine (ap2 conc _ _).
    +
      exact (conc_p_1 r).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (conc r (p x)) (conc (conc r (p x)) idpath)).
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) q)] です。 [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (ap g q))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L530 *)
Definition path_conc_crA_P_conc_crP_q@{i | }
  {A : Type@{i}} {f : A -> A}
  (p : forall x : A, Path@{i} (f x) x) {x y : A}
  (q : Path@{i} x y) {z : A} (r : Path@{i} z (f x))
  : Path@{i}
    (conc (conc r (ap f q)) (p y))
    (conc (conc r (p x)) q).
Proof.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (conc r (p x)).
  -
    refine (ap (fun pzfx => conc pzfx (p x)) _).
    exact (conc_p_1 r).
  -
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** [Path (conc (conc r q) (conc (p y) s)) (conc (conc r (p x)) (ap g q))] です。 [Path (conc (conc r (ap f q)) (conc (p y) s)) (conc (conc r (p x)) (ap g q))] の [f] を [idmap] としたものと解釈できます。 *)

(* from: invert https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L552 *)
Definition path_conc_crq_P_conc_crP_A@{i | }
  {A : Type@{i}} {g : A -> A}
  (p : forall x : A, Path@{i} x (g x)) {x y : A}
  (q : Path@{i} x y) {z : A} (r : Path@{i} z x)
  : Path@{i}
    (conc (conc r q) (p y))
    (conc (conc r (p x)) (ap g q)).
Proof.
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (conc r (p x)).
  -
    refine (ap (fun pzfx => conc pzfx (p x)) _).
    exact (conc_p_1 r).
  -
    exact (inv (conc_p_1 (conc r (p x)))).
Defined.

(** [Path (conc (ap f q) (conc (p y) s)) (conc (conc r (p x)) (conc q s))] です。 [Path (conc (ap f q) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] の [g] を [idmap] としたものと解釈できます。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L541 *)
Definition path_conc_A_cPs_conc_P_cqs@{i | }
  {A : Type@{i}} {f : A -> A}
  (p : forall x : A, Path@{i} (f x) x) {x y : A}
  (q : Path@{i} x y) {w : A} (s : Path@{i} y w)
  : Path@{i}
    (conc (ap f q) (conc (p y) s))
    (conc (p x) (conc q s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    refine_conc (conc (p x) idpath).
    +
      exact (conc_1_p (conc (p x) idpath)).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (p x) (conc (p x) idpath)).
    exact (inv (conc_p_1 (p x))).
Defined.

(** [Path (conc q (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] です。 [Path (conc (ap f q) (conc (p y) s)) (conc (conc r (p x)) (conc (ap g q) s))] の [f] を [idmap] としたものと解釈できます。 *)

(* from: invert https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L563 *)
Definition path_conc_q_cPs_conc_P_cAs@{i | }
  {A : Type@{i}} {g : A -> A}
  (p : forall x : A, Path@{i} x (g x)) {x y : A}
  (q : Path@{i} x y) {w : A} (s : Path@{i} (g y) w)
  : Path@{i}
    (conc q (conc (p y) s))
    (conc (p x) (conc (ap g q) s)).
Proof.
  refine (match s with idpath => _ end).
  refine (match q with idpath => _ end).
  simpl ap.
  refine_conc (p x).
  -
    refine_conc (conc (p x) idpath).
    +
      exact (conc_1_p (conc (p x) idpath)).
    +
      exact (conc_p_1 (p x)).
  -
    change (Path@{i} (p x) (conc (p x) idpath)).
    exact (inv (conc_p_1 (p x))).
Defined.

(** ** 関手性の一貫性 (coherence) についての補題 *)

(** [Path (conc (conc_1_p p) q) (ap (fun r => conc idpath r) q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L576 *)
Definition path_conc_'conc_1_p'_p_q_ap_lam_r_conc_1_r_q@{i | }
  {A : Type@{i}} {x : A} (p : Path@{i} x x) (q : Path@{i} p idpath)
  : Path@{i} (conc (conc_1_p p) q) (ap (fun r => conc idpath r) q).
Proof.
  refine
    (match inv_vp q
      as _
      in Path _ q'
      return Path@{i} (conc (conc_1_p p) q') (ap (fun r => conc idpath r) q')
      with idpath => _
    end).
  refine
    (match inv q
      as vq'
      in Path _ p'
      return
        Path@{i}
          (conc (conc_1_p p') (inv vq'))
          (ap (fun r => conc idpath r) (inv vq'))
      with idpath => _
    end).
  cbv.
  exact idpath.
Defined.

(** [Path (conc (conc_p_1 p) q) (ap (fun r => conc r idpath) q)] です。 *)

(* from: https://github.com/HoTT/HoTT/blob/756ff79da22d0804194145db775865c11c14aa48/theories/Basics/PathGroupoids.v#L584 *)
Definition path_conc_'conc_p_1'_p_q_ap_lam_r_conc_r_1_q@{i | }
  {A : Type@{i}} {x : A} (p : Path@{i} x x) (q : Path@{i} p idpath)
  : Path@{i} (conc (conc_p_1 p) q) (ap (fun r => conc r idpath) q).
Proof.
  refine
    (match inv_vp q
      as _
      in Path _ q'
      return Path@{i} (conc (conc_p_1 p) q') (ap (fun r => conc r idpath) q')
      with idpath => _
    end).
  refine
    (match inv q
      as vq'
      in Path _ p'
      return
      Path@{i}
        (conc (conc_p_1 p') (inv vq'))
        (ap (fun r => conc r idpath) (inv vq'))
      with idpath => _
    end).
  cbv.
  exact idpath.
Defined.
