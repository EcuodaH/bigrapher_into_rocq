From Stdlib Require Import String.
Require Import BigParser Lexer PrintV.
Import MenhirLibParser.Inter.
Open Scope string_scope.

Definition big2v (s : string) : string :=
  match lex_string s with
  | None => "ERREUR: erreur lexer"
  | Some buf =>
    match main 50 buf with
    | Parsed_pr res _ => let '(ctrls, bigs) := res in print_file ctrls bigs
    | _ => "ERREUR: erreur de syntaxe (parser)"
    end
  end.