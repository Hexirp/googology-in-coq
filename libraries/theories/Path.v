(* Run with -nois. *)
(** [GiC.Path] は、道に関する定義や、道だけが主体となる定理を提供します。

    具体的には、このライブラリ以下にある主要なライブラリをエクスポートします。
 *)

(** 必要なライブラリを要求します。 *)

Require GiC.Path.Base.
Require GiC.Path.Function.
Require GiC.Path.OneDim.
Require GiC.Path.Transposition.
Require GiC.Path.Functoriality.
Require GiC.Path.TwoDim.
Require GiC.Path.Application_1_0.
Require GiC.Path.Application_1_1.
Require GiC.Path.Transport.
Require GiC.Path.Fibration.
Require GiC.Path.Transport_2.
Require GiC.Path.Application_D.

(** ライブラリをエクスポートします。 *)

Export GiC.Path.Base.
Export GiC.Path.OneDim.
Export GiC.Path.Transposition.
Export GiC.Path.Functoriality.
Export GiC.Path.TwoDim.
