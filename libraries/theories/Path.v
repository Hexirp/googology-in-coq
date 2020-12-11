(* Run with -nois. *)

(** * GiC.Path *)

(** [GiC.Path] は、道に関する定義や、道だけが主体となる定理を提供します。

    具体的には、このライブラリ以下にある道に関する様々なライブラリをエクスポートします。
 *)

(** ライブラリをエクスポートします。 *)
Require Export GiC.Path.Base.
Require Export GiC.Path.Function.
Require Export GiC.Path.OneDim.
Require Export GiC.Path.Transposition.
Require Export GiC.Path.Functoriality.
Require Export GiC.Path.Application_1_0.
Require Export GiC.Path.Application_1_1.
Require Export GiC.Path.Transport.
