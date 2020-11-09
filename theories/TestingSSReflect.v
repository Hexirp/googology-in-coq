Declare ML Module "ltac_plugin".
Declare ML Module "ssrmatching_plugin".
Declare ML Module "ssreflect_plugin".

Require Coq.Init.Prelude.
Import Coq.Init.Prelude.

Definition example_1 (A B C : Type) (f : B -> C) (g : A -> B) : A -> C.
Proof.
 move=> x.
 move: f.
 apply.
 move: g.
 apply.
 refine x.
Defined.

Print example_1.
