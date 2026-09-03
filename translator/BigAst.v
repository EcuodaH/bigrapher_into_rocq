From Stdlib Require Import String List.
Open Scope string_scope.


Inductive big_ast : Type :=
  | Ast_ion   : string -> list string -> big_ast
  | Ast_comp  : big_ast -> big_ast -> big_ast
  | Ast_par   : big_ast -> big_ast -> big_ast
  | Ast_ppar : big_ast -> big_ast -> big_ast
  | Ast_tensor : big_ast -> big_ast -> big_ast
  | Ast_nest : big_ast -> big_ast -> big_ast
  | Ast_id : nat -> list string -> big_ast
  | Ast_closure : string -> big_ast
  | Ast_close : string -> big_ast -> big_ast
  | Ast_sub : string -> list string -> big_ast -> big_ast.

Definition exemple_AxA : big_ast :=
  Ast_par (Ast_ion "A" ("x" :: nil)) (Ast_ion "A" ("x" :: nil)).