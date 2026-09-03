%{
From Stdlib Require Import String List.
Require Import BigAst.
Open Scope string_scope.
Import ListNotations.

Definition ctrl_info := (string * nat * bool)%type.
Definition big_info  := (string * big_ast)%type.

Inductive decl_t :=
  | Dctrl : ctrl_info -> decl_t
  | Dbig  : big_info  -> decl_t.

Definition split_decls (l : list decl_t) : (list ctrl_info * list big_info) :=
  fold_right
    (fun d acc =>
       let '(cs, bs) := acc in
       match d with
       | Dctrl c => (c :: cs, bs)
       | Dbig  b => (cs, b :: bs)
       end)
    ([], []) l.
%}

%token<string> IDENT
%token<nat> NUM
%token LBRACE RBRACE COMMA PIPE DPIPE STAR PLUS DOT LPAREN RPAREN
%token SEMI EQ CTRL ATOMIC BIG ID SLASH EOF

%start<(list (string * nat * bool)) * (list (string * big_ast))> main
%type<list decl_t> decls
%type<decl_t> decl
%type<big_ast> expr atom ion
%type<list string> names

%%

main:
| ds = decls EOF { split_decls ds }

decls:
| { [] }
| d = decl ds = decls { d :: ds }

decl:
| CTRL n = IDENT EQ a = NUM SEMI          { Dctrl (n, a, false) }
| ATOMIC CTRL n = IDENT EQ a = NUM SEMI   { Dctrl (n, a, true) }
| BIG n = IDENT EQ e = expr SEMI          { Dbig (n, e) }

expr:
| a = atom { a }
| e = expr PIPE  a = atom { Ast_par e a }
| e = expr DPIPE a = atom { Ast_ppar e a }
| e = expr STAR  a = atom { Ast_comp e a }
| e = expr PLUS  a = atom { Ast_tensor e a }
| e = expr DOT   a = atom { Ast_nest e a }

atom:
| i = ion { i }
| LPAREN e = expr RPAREN { e }
| ID { Ast_id 1 [] }
| ID LPAREN n = NUM RPAREN { Ast_id n [] }
| ID LPAREN n = NUM COMMA LBRACE ns = names RBRACE RPAREN { Ast_id n ns }
| ID LBRACE ns = names RBRACE { Ast_id 0 ns }
| SLASH n = IDENT { Ast_closure n }
| SLASH n = IDENT LPAREN e = expr RPAREN { Ast_close n e }
| out = IDENT SLASH LBRACE ns = names RBRACE LPAREN e = expr RPAREN { Ast_sub out ns e }

ion:
| c = IDENT                          { Ast_ion c [] }
| c = IDENT LBRACE RBRACE            { Ast_ion c [] }
| c = IDENT LBRACE ns = names RBRACE { Ast_ion c ns }

names:
| n = IDENT { [n] }
| n = IDENT COMMA rest = names { n :: rest }