From Coq Require Import BinNat Ascii String.
Require Import BigParser.
Import MenhirLibParser.Inter.
Open Scope char_scope.
Open Scope bool_scope.

CoFixpoint TheEnd : buffer := Buf_cons (EOF tt) TheEnd.

(** Comparaisons sur les caractère *)
Definition ascii_eqb c c' := (N_of_ascii c =? N_of_ascii c')%N.
Definition ascii_leb c c' := (N_of_ascii c <=? N_of_ascii c')%N.

Infix "=?" := ascii_eqb : char_scope.
Infix "<=?" := ascii_leb : char_scope.

Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

Definition is_alpha c :=
  ((("a" <=? c) && (c <=? "z")) ||
   (("A" <=? c) && (c <=? "Z")) ||
   (c =? "_"))%char.

Fixpoint identsize s :=
  match s with
  | EmptyString => 0
  | String c s =>
    if is_alpha c || is_digit c || (c =? "'") then S (identsize s)
    else 0
  end.

(** Avance de n caractères dans s *)
Fixpoint ntail n s :=
  match n, s with
  | 0, _ => s
  | _, EmptyString => s
  | S n, String _ s => ntail n s
  end.



Fixpoint drop_line s :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if (c =? "010") then s' else drop_line s'
  end.

Definition digit_val c : nat := N.to_nat (N_of_ascii c - N_of_ascii "0").

Fixpoint numsize s :=
  match s with
  | EmptyString => 0
  | String c s => if is_digit c then S (numsize s) else 0
  end.

Fixpoint readnum_aux s acc :=
  match s with
  | EmptyString => acc
  | String c s' => if is_digit c then readnum_aux s' (10 * acc + digit_val c) else acc
  end.

Fixpoint lex_string_cpt n s :=
  match n with
  | 0 => None
  | S n =>
    match s with
    | EmptyString => Some TheEnd
    | String c s' =>
      match c with
      | " "%char    => lex_string_cpt n s'
      | "009"%char  => lex_string_cpt n s' (* \t *)
      | "010"%char  => lex_string_cpt n s' (* \n *)
      | "013"%char  => lex_string_cpt n s' (* \r *)
      | "#"%char    => lex_string_cpt n (drop_line s') (*commentaires*)
      | "{"%char    => option_map (Buf_cons (LBRACE tt)) (lex_string_cpt n s')
      | "}"%char    => option_map (Buf_cons (RBRACE tt)) (lex_string_cpt n s')
      | "("%char    => option_map (Buf_cons (LPAREN tt)) (lex_string_cpt n s')
      | ")"%char    => option_map (Buf_cons (RPAREN tt)) (lex_string_cpt n s')
      | ","%char    => option_map (Buf_cons (COMMA tt))  (lex_string_cpt n s')
      | "*"%char    => option_map (Buf_cons (STAR tt))   (lex_string_cpt n s')
      | "+"%char    => option_map (Buf_cons (PLUS tt))   (lex_string_cpt n s')
      | "."%char    => option_map (Buf_cons (DOT tt))    (lex_string_cpt n s')
      | "/"%char    => option_map (Buf_cons (SLASH tt))  (lex_string_cpt n s')
      | ";"%char    => option_map (Buf_cons (SEMI tt))   (lex_string_cpt n s')
      | "="%char    => option_map (Buf_cons (EQ tt))     (lex_string_cpt n s')
      | "|"%char    =>
          match s' with
          | String "|"%char s'' => option_map (Buf_cons (DPIPE tt)) (lex_string_cpt n s'')
          | _                   => option_map (Buf_cons (PIPE tt))  (lex_string_cpt n s')
          end
      | _ =>
        if is_digit c then
          let k := numsize s in
          let v := readnum_aux s 0 in
          let s := ntail k s in
          option_map (Buf_cons (NUM v)) (lex_string_cpt n s)
        else if is_alpha c then
          let k  := identsize s in
          let id := substring 0 k s in
          let s  := ntail k s in
          (* mots-clés reserves *)
          if String.eqb id "ctrl" then
            option_map (Buf_cons (CTRL tt)) (lex_string_cpt n s)
          else if String.eqb id "atomic" then
            option_map (Buf_cons (ATOMIC tt)) (lex_string_cpt n s)
          else if String.eqb id "big" then
            option_map (Buf_cons (BIG tt)) (lex_string_cpt n s)
          else if String.eqb id "id" then
            option_map (Buf_cons (ID tt)) (lex_string_cpt n s)
          else
            option_map (Buf_cons (IDENT id)) (lex_string_cpt n s)
        else None
      end
    end
  end.


Definition lex_string s := lex_string_cpt (S (String.length s)) s.