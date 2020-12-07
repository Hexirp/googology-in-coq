(*

Copyright 2020 Hexirp Prixeh

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

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
