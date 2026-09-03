From Coq Require Import String List Ascii PeanoNat.
Require Import BigAst.
Open Scope string_scope.
Import ListNotations.

(* saut de ligne *)
Definition nl : string := String (ascii_of_nat 10) EmptyString.

(* nat -> string (décimal), calqué sur prnat de minicalc *)
Definition digit (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

Fixpoint nat_str_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => ""
  | S f =>
    if Nat.ltb n 10 then digit n
    else nat_str_aux f (Nat.div n 10) ++ digit (Nat.modulo n 10)
  end.

Definition nat_str (n : nat) : string := nat_str_aux (S n) n.

(* construit "[:: a; b; c]", la syntaxe Rocq d'une liste litterale *)
Fixpoint join_semi (l : list string) : string :=
  match l with
  | [] => ""
  | [n] => n
  | n :: rest => n ++ "; " ++ join_semi rest
  end.

Definition print_namelist_ty (ty : string) (l : list string) : string :=
  match l with
  | [] => "(@nil " ++ ty ++ ")"
  | _ => "[:: " ++ join_semi l ++ "]"
  end.

Definition print_namelist (l : list string) : string := print_namelist_ty "name" l.

Fixpoint zip_positions (l : list string) (i : nat) : list (string * nat) :=
  match l with
  | [] => []
  | n :: rest => (n, i) :: zip_positions rest (S i)
  end.

Fixpoint lookup_pos (table : list (string * nat)) (nom : string) : nat :=
  match table with
  | [] => 0
  | (n, i) :: rest => if String.eqb n nom then i else lookup_pos rest nom
  end.

Fixpoint mem_str (x : string) (l : list string) : bool :=
  match l with
  | [] => false
  | y :: r => if String.eqb x y then true else mem_str x r
  end.

Definition add_name (acc : list string) (x : string) : list string :=
  if mem_str x acc then acc else acc ++ [x].

Fixpoint remove_str (n : string) (l : list string) : list string :=
  match l with
  | [] => []
  | x :: r => if String.eqb x n then remove_str n r else x :: remove_str n r
  end.

Fixpoint noms_ast (a : big_ast) (acc : list string) : list string :=
  match a with
  | Ast_ion _ names => fold_left add_name names acc
  | Ast_comp   b1 b2 => noms_ast b2 (noms_ast b1 acc)
  | Ast_par    b1 b2 => noms_ast b2 (noms_ast b1 acc)
  | Ast_ppar   b1 b2 => noms_ast b2 (noms_ast b1 acc)
  | Ast_tensor b1 b2 => noms_ast b2 (noms_ast b1 acc)
  | Ast_nest   b1 b2 => noms_ast b2 (noms_ast b1 acc)
  | Ast_id     _ names => fold_left add_name names acc
  | Ast_closure n => add_name acc n
  | Ast_close n b => add_name (noms_ast b acc) n
  | Ast_sub out ins b => add_name (fold_left add_name ins (noms_ast b acc)) out
  end.

(* noms internes (inner face) d'un big_ast, calculable sans passer par Rocq :
   un ion/atome n'a pas de noms internes (ses noms declares sont externes) ;
   composition et nest ne gardent que l'interne du membre de droite ;
   les autres operateurs symetriques (tensor/merge/parallel) unissent les deux *)
Fixpoint inner_names_ast (a : big_ast) (acc : list string) : list string :=
  match a with
  | Ast_ion _ _ => acc
  | Ast_id _ names => fold_left add_name names acc
  | Ast_closure n => add_name acc n
  | Ast_close _ b => inner_names_ast b acc
  | Ast_sub _ _ b => inner_names_ast b acc
  | Ast_comp _ b2 => inner_names_ast b2 acc
  | Ast_par b1 b2 => inner_names_ast b2 (inner_names_ast b1 acc)
  | Ast_ppar b1 b2 => inner_names_ast b2 (inner_names_ast b1 acc)
  | Ast_tensor b1 b2 => inner_names_ast b2 (inner_names_ast b1 acc)
  | Ast_nest _ b2 => inner_names_ast b2 acc
  end.

(* noms externes (outer face) d'un big_ast, calculable sans passer par Rocq :
   different de noms_ast, qui accumule TOUS les noms references (utile pour
   allouer le pool) mais reintegre a tort un nom deja ferme par un /n(..)
   englobe plus profondement (cas des fermetures imbriquees, ex /pts(/e1(P))).
   Ici un ion/id expose ses noms declares ; comp/nest ne gardent que le
   membre de gauche ; close/sub retirent le(s) nom(s) qu'ils consomment *)
Fixpoint outer_names_ast (a : big_ast) : list string :=
  match a with
  | Ast_ion _ names => names
  | Ast_id _ names => names
  | Ast_closure _ => []
  | Ast_close n b => remove_str n (outer_names_ast b)
  | Ast_sub out ins b => add_name (fold_left (fun acc m => remove_str m acc) ins (outer_names_ast b)) out
  | Ast_comp b1 _ => outer_names_ast b1
  | Ast_par b1 b2 => fold_left add_name (outer_names_ast b2) (outer_names_ast b1)
  | Ast_ppar b1 b2 => fold_left add_name (outer_names_ast b2) (outer_names_ast b1)
  | Ast_tensor b1 b2 => fold_left add_name (outer_names_ast b2) (outer_names_ast b1)
  | Ast_nest b1 b2 => fold_left add_name (outer_names_ast b2) (outer_names_ast b1)
  end.

(* nombre de racines d'un big_ast, calculable sans passer par Rocq *)
Fixpoint root_count (a : big_ast) : nat :=
  match a with
  | Ast_ion _ _ => 1
  | Ast_id n _ => n
  | Ast_closure _ => 0
  | Ast_close _ b => root_count b
  | Ast_sub _ _ b => root_count b
  | Ast_comp b1 _ => root_count b1
  | Ast_par _ _ => 1
  | Ast_ppar b1 b2 => root_count b1 + root_count b2
  | Ast_tensor b1 b2 => root_count b1 + root_count b2
  | Ast_nest b1 _ => root_count b1
  end.

(* collecte les noms de tous les bigraphes du fichier *)
Fixpoint noms_decls (l : list (string * big_ast)) (acc : list string) : list string :=
  match l with
  | [] => acc
  | (_, a) :: r => noms_decls r (noms_ast a acc)
  end.

(* cherche un controle dans la table : rend (indice, arite, atomique) *)
Fixpoint lookup_ctrl (table : list (string * nat * bool)) (nom : string) (i : nat)
    : option (nat * nat * bool) :=
  match table with
  | [] => None
  | (c, ar, atom) :: rest =>
      if String.eqb c nom then Some (i, ar, atom)
      else lookup_ctrl rest nom (S i)
  end.
(*Détection d'erreur*)
Fixpoint has_dup (l : list string) : bool :=
  match l with
  | [] => false
  | x :: r => if existsb (String.eqb x) r then true else has_dup r
  end.

Fixpoint check_ast (ct : list (string * nat * bool)) (a : big_ast) : option string :=
  match a with
  | Ast_ion ctrl names =>
      match lookup_ctrl ct ctrl 0 with
      | None => Some ("controle non declare : " ++ ctrl)
      | Some (_, ar, _) =>
          if has_dup names then
            Some ("noms dupliques dans " ++ ctrl ++ print_namelist names)
          else if negb (Nat.eqb ar (List.length names)) then
            Some ("arite incoherente pour " ++ ctrl ++ " : declaree " ++
                  nat_str ar ++ ", utilisee avec " ++ nat_str (List.length names) ++ " nom(s)")
          else None
      end
  | Ast_id _ _ | Ast_closure _ => None
  | Ast_close _ b => check_ast ct b
  | Ast_sub _ ins b =>
      if has_dup ins then
        Some ("noms dupliques dans la substitution" ++ print_namelist ins)
      else check_ast ct b
  | Ast_comp b1 b2 | Ast_par b1 b2 | Ast_ppar b1 b2
  | Ast_tensor b1 b2 | Ast_nest b1 b2 =>
      match check_ast ct b1 with
      | Some e => Some e
      | None => check_ast ct b2
      end
  end.

Fixpoint check_all (ct : list (string * nat * bool)) (l : list (string * big_ast)) : option string :=
  match l with
  | [] => None
  | (nom, a) :: r =>
      match check_ast ct a with
      | Some e => Some ("dans " ++ nom ++ " : " ++ e)
      | None => check_all ct r
      end
  end.

Definition solve_empty_innername : string :=
  "Proof. exact ns.emptyns_empty_set. Qed.".
Definition solve_eqnatc : string :=
  "Proof. apply eqnatc.MyEqNat_refl. Qed.".
Definition solve_djns_empty_left : string :=
  "Proof. exact (ns.djns_empty_left _). Qed.".

Fixpoint emit (ct : list (string * nat * bool)) (postab : list (string * nat))
    (N : nat) (a : big_ast) (i : nat) : string * string * nat :=
  match a with
  | Ast_ion ctrl names =>
      let nom := "bigInter" ++ nat_str i in
      let nomNames := "names_" ++ nom in
      let arite := nat_str (List.length names) in
      let namelist := print_namelist names in
      let poslist := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) names) in
      let ligne_names :=
        "Definition " ++ nomNames ++ " : nameset := from_list " ++ namelist ++ "." ++ nl in
      let def :=
        match lookup_ctrl ct ctrl 0 with
        | Some (idx, _ar, atomique) =>
            let constructeur := if atomique then "make_atom" else "make_ion" in
            "(* ion " ++ ctrl ++ " *)" ++ nl ++
            ligne_names ++
            "Definition " ++ nom ++ " := " ++ constructeur ++ " " ++
              nat_str N ++ " " ++ nat_str idx ++ " " ++ arite ++ " " ++ nomNames ++
              " (erefl _) (Logic.eq_sym (card_from_list_uniq " ++ namelist ++
              " ltac:(solve_uniq_pool " ++ poslist ++ ")))." ++ nl ++ nl
        | None =>
            "(* ERREUR: controle " ++ ctrl ++ " non declare *)" ++ nl ++
            ligne_names ++
            "Definition " ++ nom ++ " : bigraph 1 empty_set 1 " ++ nomNames ++ ". Admitted." ++ nl ++ nl
        end
      in (def, nom, S i)
  | Ast_id arite names =>
      let nom := "bigInter" ++ nat_str i in
      let def :=
        "(* id " ++ nat_str arite ++ " *)" ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_id " ++ nat_str arite ++
          " (from_list " ++ print_namelist names ++ ")." ++ nl ++ nl
      in (def, nom, S i)
  | Ast_closure nom_name =>
      let nom := "bigInter" ++ nat_str i in
      let def :=
        "(* closure " ++ nom_name ++ " *)" ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := closure " ++ nom_name ++ "." ++ nl ++ nl
      in (def, nom, S i)
  | Ast_close nom_name b =>
      let '(defb, nb, ib) := emit ct postab N b i in
      let r := root_count b in
      let xs := remove_str nom_name (outer_names_ast b) in
      let nom_id := "bigInter" ++ nat_str ib in
      let def_id :=
        "(* id " ++ nat_str r ++ " padding pour /" ++ nom_name ++ " *)" ++ nl ++
        "Definition " ++ nom_id ++ " : bigraph _ _ _ _ := bigraph_id " ++ nat_str r ++
          " (from_list " ++ print_namelist xs ++ ")." ++ nl ++ nl
      in
      let i_cl := S ib in
      let nom_cl := "bigInter" ++ nat_str i_cl in
      let def_cl :=
        "(* closure " ++ nom_name ++ " *)" ++ nl ++
        "Definition " ++ nom_cl ++ " : bigraph _ _ _ _ := closure " ++ nom_name ++ "." ++ nl ++ nl
      in
      let i_pad := S i_cl in
      let nom_pad := "bigInter" ++ nat_str i_pad in
      let poslist_xs := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) xs) in
      let poslist_n := print_namelist_ty "nat" [nat_str (lookup_pos postab nom_name)] in
      let def_pad :=
        "Lemma preuve_dis_i_" ++ nom_pad ++ " : ns.djns (get_innername " ++ nom_id ++ ") (get_innername " ++ nom_cl ++ ")." ++ nl ++
        "Proof." ++ nl ++
        "  constructor. unfold get_innername, " ++ nom_id ++ ", " ++ nom_cl ++ ". simpl." ++ nl ++
        "  try rewrite !singleton_from_list." ++ nl ++
        "  solve_disjoint_pool " ++ poslist_xs ++ " " ++ poslist_n ++ "." ++ nl ++
        "Qed." ++ nl ++
        "Lemma preuve_dis_o_" ++ nom_pad ++ " : ns.djns (get_outername " ++ nom_id ++ ") (get_outername " ++ nom_cl ++ ")." ++ nl ++
        "  Proof. exact (ns.djns_empty_right _). Qed." ++ nl ++
        "Definition " ++ nom_pad ++ " : bigraph _ _ _ _ := bigraph_tensor_product (dis_i:=preuve_dis_i_" ++ nom_pad ++
          ") (dis_o:=preuve_dis_o_" ++ nom_pad ++ ") " ++ nom_id ++ " " ++ nom_cl ++ "." ++ nl ++ nl
      in
      let i_final := S i_pad in
      let nom := "bigInter" ++ nat_str i_final in
      let def :=
        defb ++ def_id ++ def_cl ++ def_pad ++
        "Lemma preuve_p_" ++ nom ++ " : ns.eqns (get_innername " ++ nom_pad ++ ") (get_outername " ++ nb ++ ")." ++ nl ++
        "  Proof. solve_eqns " ++ nom_pad ++ " " ++ nb ++ ". Qed." ++ nl ++
        "Lemma preuve_eqsr_" ++ nom ++ " : eqnatc.eqnatc (get_site " ++ nom_pad ++ ") (get_root " ++ nb ++ ")." ++ nl ++
        "  " ++ solve_eqnatc ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_composition (p:=preuve_p_" ++ nom ++
          ") (eqsr:=preuve_eqsr_" ++ nom ++ ") " ++ nom_pad ++ " " ++ nb ++ "." ++ nl ++ nl
      in (def, nom, S i_final)
  | Ast_sub out_name ins b =>
      let '(defb, nb, ib) := emit ct postab N b i in
      let r := root_count b in
      let z := fold_left (fun acc n => remove_str n acc) ins (outer_names_ast b) in
      let nom_id := "bigInter" ++ nat_str ib in
      let def_id :=
        "(* id " ++ nat_str r ++ " padding pour " ++ out_name ++ "/{...} *)" ++ nl ++
        "Definition " ++ nom_id ++ " : bigraph _ _ _ _ := bigraph_id " ++ nat_str r ++
          " (from_list " ++ print_namelist z ++ ")." ++ nl ++ nl
      in
      let i_sub := S ib in
      let nom_sub := "bigInter" ++ nat_str i_sub in
      let def_sub :=
        "(* substitution " ++ out_name ++ "/{...} *)" ++ nl ++
        "Definition " ++ nom_sub ++ " : bigraph _ _ _ _ := substitution (from_list " ++ print_namelist ins ++ ") " ++ out_name ++ "." ++ nl ++ nl
      in
      let i_pad := S i_sub in
      let nom_pad := "bigInter" ++ nat_str i_pad in
      let poslist_z := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) z) in
      let poslist_ins := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) ins) in
      let poslist_out := print_namelist_ty "nat" [nat_str (lookup_pos postab out_name)] in
      let def_pad :=
        "Lemma preuve_dis_i_" ++ nom_pad ++ " : ns.djns (get_innername " ++ nom_id ++ ") (get_innername " ++ nom_sub ++ ")." ++ nl ++
        "Proof." ++ nl ++
        "  constructor. unfold get_innername, " ++ nom_id ++ ", " ++ nom_sub ++ ". simpl." ++ nl ++
        "  solve_disjoint_pool " ++ poslist_z ++ " " ++ poslist_ins ++ "." ++ nl ++
        "Qed." ++ nl ++
        "Lemma preuve_dis_o_" ++ nom_pad ++ " : ns.djns (get_outername " ++ nom_id ++ ") (get_outername " ++ nom_sub ++ ")." ++ nl ++
        "Proof." ++ nl ++
        "  constructor. unfold get_outername, " ++ nom_id ++ ", " ++ nom_sub ++ ". simpl." ++ nl ++
        "  try rewrite !singleton_from_list." ++ nl ++
        "  solve_disjoint_pool " ++ poslist_z ++ " " ++ poslist_out ++ "." ++ nl ++
        "Qed." ++ nl ++
        "Definition " ++ nom_pad ++ " : bigraph _ _ _ _ := bigraph_tensor_product (dis_i:=preuve_dis_i_" ++ nom_pad ++
          ") (dis_o:=preuve_dis_o_" ++ nom_pad ++ ") " ++ nom_id ++ " " ++ nom_sub ++ "." ++ nl ++ nl
      in
      let i_final := S i_pad in
      let nom := "bigInter" ++ nat_str i_final in
      let def :=
        defb ++ def_id ++ def_sub ++ def_pad ++
        "Lemma preuve_p_" ++ nom ++ " : ns.eqns (get_innername " ++ nom_pad ++ ") (get_outername " ++ nb ++ ")." ++ nl ++
        "  Proof. solve_eqns " ++ nom_pad ++ " " ++ nb ++ ". Qed." ++ nl ++
        "Lemma preuve_eqsr_" ++ nom ++ " : eqnatc.eqnatc (get_site " ++ nom_pad ++ ") (get_root " ++ nb ++ ")." ++ nl ++
        "  " ++ solve_eqnatc ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_composition (p:=preuve_p_" ++ nom ++
          ") (eqsr:=preuve_eqsr_" ++ nom ++ ") " ++ nom_pad ++ " " ++ nb ++ "." ++ nl ++ nl
      in (def, nom, S i_final)
  | Ast_comp b1 b2 =>
      let '(def1, n1, i1) := emit ct postab N b1 i in
      let '(def2, n2, i2) := emit ct postab N b2 i1 in
      let nom := "bigInter" ++ nat_str i2 in
      let def :=
        def1 ++ def2 ++
        "Lemma preuve_p_" ++ nom ++ " : ns.eqns (get_innername " ++ n1 ++ ") (get_outername " ++ n2 ++ ")." ++ nl ++
        "  Proof. solve_eqns " ++ n1 ++ " " ++ n2 ++ ". Qed." ++ nl ++
        "Lemma preuve_eqsr_" ++ nom ++ " : eqnatc.eqnatc (get_site " ++ n1 ++ ") (get_root " ++ n2 ++ ")." ++ nl ++
        "  " ++ solve_eqnatc ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_composition (p:=preuve_p_" ++ nom ++ ") (eqsr:=preuve_eqsr_" ++ nom ++ ") " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++ nl
      in (def, nom, S i2)
  | Ast_par b1 b2 =>
      let '(def1, n1, i1) := emit ct postab N b1 i in
      let '(def2, n2, i2) := emit ct postab N b2 i1 in
      let nom := "bigInter" ++ nat_str i2 in
      let poslist1 := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) (inner_names_ast b1 [])) in
      let poslist2 := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) (inner_names_ast b2 [])) in
      let def :=
        def1 ++ def2 ++
        "Lemma preuve_up_" ++ nom ++ " : UnionPossible " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++
        "Proof. solve_union_possible_pool " ++ poslist1 ++ " " ++ poslist2 ++ ". Qed." ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_merge_product (up:=preuve_up_" ++ nom ++ ") " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++ nl
      in (def, nom, S i2)
  | Ast_ppar b1 b2 =>
      let '(def1, n1, i1) := emit ct postab N b1 i in
      let '(def2, n2, i2) := emit ct postab N b2 i1 in
      let nom := "bigInter" ++ nat_str i2 in
      let poslist1 := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) (inner_names_ast b1 [])) in
      let poslist2 := print_namelist_ty "nat" (List.map (fun n => nat_str (lookup_pos postab n)) (inner_names_ast b2 [])) in
      let def :=
        def1 ++ def2 ++
        "Lemma preuve_up_" ++ nom ++ " : UnionPossible " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++
        "Proof. solve_union_possible_pool " ++ poslist1 ++ " " ++ poslist2 ++ ". Qed." ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_parallel_product (up:=preuve_up_" ++ nom ++ ") " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++ nl
      in (def, nom, S i2)
  | Ast_tensor b1 b2 =>
      let '(def1, n1, i1) := emit ct postab N b1 i in
      let '(def2, n2, i2) := emit ct postab N b2 i1 in
      let nom := "bigInter" ++ nat_str i2 in
      let def :=
        def1 ++ def2 ++
        "Lemma preuve_dis_i_" ++ nom ++ " : ns.djns (get_innername " ++ n1 ++ ") (get_innername " ++ n2 ++ ")." ++ nl ++
        "  " ++ solve_djns_empty_left ++ nl ++
        "Lemma preuve_dis_o_" ++ nom ++ " : ns.djns (get_outername " ++ n1 ++ ") (get_outername " ++ n2 ++ ")." ++ nl ++
        "  Admitted." ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := bigraph_tensor_product (dis_i:=preuve_dis_i_" ++ nom ++ ") (dis_o:=preuve_dis_o_" ++ nom ++ ") " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++ nl
      in (def, nom, S i2)
  | Ast_nest b1 b2 =>
      let '(def1, n1, i1) := emit ct postab N b1 i in
      let '(def2, n2, i2) := emit ct postab N b2 i1 in
      let nom := "bigInter" ++ nat_str i2 in
      let def :=
        def1 ++ def2 ++
        "Lemma preuve_empty_" ++ nom ++ " : ns.emptyns (get_innername " ++ n1 ++ ")." ++ nl ++
        "  " ++ solve_empty_innername ++ nl ++
        "Lemma preuve_eqs1r2_" ++ nom ++ " : eqnatc.eqnatc (get_site " ++ n1 ++ ") (get_root " ++ n2 ++ ")." ++ nl ++
        "  " ++ solve_eqnatc ++ nl ++
        "Definition " ++ nom ++ " : bigraph _ _ _ _ := nest (emptyi1:=preuve_empty_" ++ nom ++ ") (eqs1r2:=preuve_eqs1r2_" ++ nom ++ ") " ++ n1 ++ " " ++ n2 ++ "." ++ nl ++ nl
      in (def, nom, S i2)
  end.

Definition print_v (ct : list (string * nat * bool)) (a : big_ast) : string :=
  let postab := zip_positions (noms_ast a []) 0 in
  let '(def, _, _) := emit ct postab (List.length ct) a 0 in def.

Definition print_support : string :=
  "Lemma in_from_list (x : name) (l : seq name) :" ++ nl ++
  "  x \ins from_list l <-> x \in l." ++ nl ++
  "Proof." ++ nl ++
  "  induction l as [| y l' IH]." ++ nl ++
  "  - simpl. split." ++ nl ++
  "    + intro H. exfalso. exact (empty_empty x H)." ++ nl ++
  "    + intro H. rewrite in_nil in H. discriminate." ++ nl ++
  "  - simpl. rewrite in_add. rewrite in_cons. rewrite IH." ++ nl ++
  "    split." ++ nl ++
  "    - intros [Heq | Hin]." ++ nl ++
  "      + apply/orP. left. apply/eqP. exact Heq." ++ nl ++
  "      + apply/orP. right. exact Hin." ++ nl ++
  "    - move/orP => [Heq | Hin]." ++ nl ++
  "      + left. apply/eqP. exact Heq." ++ nl ++
  "      + right. exact Hin." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma card_from_list_uniq (l : seq name) :" ++ nl ++
  "  uniq l -> cardinal (from_list l) = size l." ++ nl ++
  "Proof." ++ nl ++
  "  induction l as [| x l' IH]." ++ nl ++
  "  - intro. simpl. apply card_empty_set." ++ nl ++
  "  - simpl. intro Huniq." ++ nl ++
  "    move/andP: Huniq => [Hnotin Huniq']." ++ nl ++
  "    erewrite card_add." ++ nl ++
  "    + f_equal. apply IH. exact Huniq'." ++ nl ++
  "    + rewrite in_from_list." ++ nl ++
  "      apply/negP. exact Hnotin." ++ nl ++
  "    + reflexivity." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma uniq_nth_map (pool : list name) (d : name) (Hu : uniq pool) :" ++ nl ++
  "  forall inds : list nat," ++ nl ++
  "    uniq inds -> all (fun i => (i < size pool)%N) inds ->" ++ nl ++
  "    uniq (map (nth d pool) inds)." ++ nl ++
  "Proof." ++ nl ++
  "  induction inds as [| i inds' IH]; intros Huniq Hbound." ++ nl ++
  "  - reflexivity." ++ nl ++
  "  - simpl in Huniq. move/andP: Huniq => [Hnotin Huniq']." ++ nl ++
  "    simpl in Hbound. move/andP: Hbound => [Hib Hbound']." ++ nl ++
  "    simpl. apply/andP; split." ++ nl ++
  "    + apply/negP => /mapP [j Hj Heq]." ++ nl ++
  "      move/negP: Hnotin => Hnotin. apply Hnotin." ++ nl ++
  "      have Hjb : (j < size pool)%N by move/allP: Hbound' => Hbound'; apply Hbound'." ++ nl ++
  "      have Hnu := nth_uniq d Hib Hjb Hu." ++ nl ++
  "      rewrite Heq eqxx in Hnu." ++ nl ++
  "      symmetry in Hnu. move/eqnP: Hnu => Hij." ++ nl ++
  "      rewrite Hij. exact Hj." ++ nl ++
  "    + apply IH." ++ nl ++
  "      * exact Huniq'." ++ nl ++
  "      * exact Hbound'." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma singleton_from_list (a : name) : ns.singleton a = ns.from_list [:: a]." ++ nl ++
  "Proof. reflexivity. Qed." ++ nl ++ nl ++
  "Lemma add_empty_from_list (a : name) : add a empty_set = ns.from_list [:: a]." ++ nl ++
  "Proof. reflexivity. Qed." ++ nl ++ nl ++
  "Lemma union_from_list (l1 l2 : seq name) :" ++ nl ++
  "  union (from_list l1) (from_list l2) == from_list (l1 ++ l2)." ++ nl ++
  "Proof." ++ nl ++
  "  rewrite eq_in. intro x." ++ nl ++
  "  rewrite in_union." ++ nl ++
  "  rewrite !in_from_list." ++ nl ++
  "  rewrite mem_cat." ++ nl ++
  "  split." ++ nl ++
  "  - move=> [H | H]; apply/orP; [left | right]; exact H." ++ nl ++
  "  - move/orP => [H | H]; [left | right]; exact H." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Add Parametric Morphism : union" ++ nl ++
  "  with signature (nst.eq ==> nst.eq ==> nst.eq) as union_mor." ++ nl ++
  "Proof." ++ nl ++
  "  move=> s1 s1' H1 s2 s2' H2." ++ nl ++
  "  apply eq_in => x. rewrite !in_union." ++ nl ++
  "  rewrite (eq_in_l H1) (eq_in_l H2). reflexivity." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma disjoint_from_list (l1 l2 : seq name) :" ++ nl ++
  "  all (fun x => x \notin l2) l1 -> disjoint (from_list l1) (from_list l2)." ++ nl ++
  "Proof." ++ nl ++
  "  move=> H." ++ nl ++
  "  unfold disjoint. rewrite empty_spec. move=> x." ++ nl ++
  "  rewrite in_inter !in_from_list." ++ nl ++
  "  move=> [Hx1 Hx2]." ++ nl ++
  "  move/allP: H => H." ++ nl ++
  "  move: (H x Hx1) => Hnot." ++ nl ++
  "  move/negP: Hnot => Hnot." ++ nl ++
  "  exact (Hnot Hx2)." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma disjoint_nth_map (pool : list name) (d : name) (Hu : uniq pool) :" ++ nl ++
  "  forall inds1 inds2 : list nat," ++ nl ++
  "    all (fun i => i \notin inds2) inds1 ->" ++ nl ++
  "    all (fun i => (i < size pool)%N) inds1 ->" ++ nl ++
  "    all (fun i => (i < size pool)%N) inds2 ->" ++ nl ++
  "    all (fun x => x \notin (map (nth d pool) inds2)) (map (nth d pool) inds1)." ++ nl ++
  "Proof." ++ nl ++
  "  move=> inds1 inds2 Hdisj Hb1 Hb2." ++ nl ++
  "  apply/allP => xx /mapP [i Hi Heqi]." ++ nl ++
  "  apply/negP => /mapP [j Hj Heqj]." ++ nl ++
  "  have Hib : (i < size pool)%N by move/allP: Hb1 => Hb1'; apply Hb1'." ++ nl ++
  "  have Hjb : (j < size pool)%N by move/allP: Hb2 => Hb2'; apply Hb2'." ++ nl ++
  "  have Hnu := nth_uniq d Hib Hjb Hu." ++ nl ++
  "  have Heq : nth d pool i = nth d pool j by rewrite -Heqi -Heqj." ++ nl ++
  "  rewrite Heq eqxx in Hnu." ++ nl ++
  "  symmetry in Hnu. move/eqnP: Hnu => Hij." ++ nl ++
  "  move/allP: Hdisj => Hdisj." ++ nl ++
  "  move: (Hdisj i Hi) => Hnotin." ++ nl ++
  "  move/negP: Hnotin. apply. rewrite Hij. exact Hj." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma disjoint_union_tree (t1 t2 : nameset) (l1 l2 : seq name) :" ++ nl ++
  "  t1 == from_list l1 -> t2 == from_list l2 ->" ++ nl ++
  "  all (fun x => x \notin l2) l1 -> disjoint t1 t2." ++ nl ++
  "Proof." ++ nl ++
  "  move=> Ht1 Ht2 Hall." ++ nl ++
  "  have Hd : disjoint (from_list l1) (from_list l2) := disjoint_from_list l1 l2 Hall." ++ nl ++
  "  unfold disjoint in Hd. rewrite empty_spec in Hd." ++ nl ++
  "  unfold disjoint. rewrite empty_spec. move=> x Hx." ++ nl ++
  "  apply (Hd x)." ++ nl ++
  "  move: Hx. rewrite !in_inter." ++ nl ++
  "  move=> [Hx1 Hx2]. split." ++ nl ++
  "  - apply (eq_in_l Ht1). exact Hx1." ++ nl ++
  "  - apply (eq_in_l Ht2). exact Hx2." ++ nl ++
  "Qed." ++ nl ++ nl ++
  "Lemma in_empty_iff (x : name) : x \ins empty_set <-> False." ++ nl ++
  "Proof. split. - exact (empty_empty x). - intro H; contradiction. Qed." ++ nl ++ nl ++
  "Local Opaque from_list singleton." ++ nl ++ nl ++
  "Ltac flatten_to_from_list :=" ++ nl ++
  "  try change empty_set with (from_list (@nil name));" ++ nl ++
  "  repeat (first [ rewrite union_from_list | rewrite singleton_from_list | rewrite add_empty_from_list ]; simpl);" ++ nl ++
  "  apply ns.from_list_perm; unfold ns.permutation; move=> ?;" ++ nl ++
  "  try rewrite !mem_cat; try rewrite !in_cons; try rewrite !in_nil;" ++ nl ++
  "  match goal with" ++ nl ++
  "  | |- is_true ?a <-> is_true ?b =>" ++ nl ++
  "      first [done | (have ->: a = b by btauto); done]" ++ nl ++
  "  end." ++ nl ++ nl ++
  "Ltac solve_eqns n1 n2 :=" ++ nl ++
  "  apply ns.eqns_same; unfold get_innername, get_outername, n1, n2; simpl;" ++ nl ++
  "  apply eq_in; intro x;" ++ nl ++
  "  repeat rewrite in_union;" ++ nl ++
  "  repeat rewrite in_add;" ++ nl ++
  "  repeat rewrite in_empty_iff;" ++ nl ++
  "  tauto." ++ nl ++ nl.

Fixpoint emit_pool_names (l : list string) (i : nat) : string :=
  match l with
  | [] => ""
  | n :: rest =>
      "Definition " ++ n ++ " : name := nth defaultInfT pool " ++ nat_str i ++ "." ++ nl ++
      emit_pool_names rest (S i)
  end.

Definition print_pool_header (noms : list string) : string :=
  let k := nat_str (List.length noms) in
  "Definition pool : list name := new_disjoint_infT_list [::] " ++ k ++ "." ++ nl ++
  "Lemma pool_uniq : uniq pool." ++ nl ++
  "Proof. exact (ndil_uniq [::] " ++ k ++ "). Qed." ++ nl ++
  "Lemma pool_size : size pool = " ++ k ++ "." ++ nl ++
  "Proof. exact (ndil_size [::] " ++ k ++ "). Qed." ++ nl ++
  emit_pool_names noms 0 ++
  "Definition names : nameset := from_list " ++ print_namelist noms ++ "." ++ nl ++
  "Ltac solve_uniq_pool inds :=" ++ nl ++
  "  change (uniq (map (nth defaultInfT pool) inds));" ++ nl ++
  "  apply uniq_nth_map; [exact pool_uniq | done | rewrite pool_size; done]." ++ nl ++
  "Ltac solve_disjoint_pool inds1 inds2 :=" ++ nl ++
  "  apply disjoint_from_list;" ++ nl ++
  "  change (all (fun z => z \notin (map (nth defaultInfT pool) inds2)) (map (nth defaultInfT pool) inds1));" ++ nl ++
  "  apply (disjoint_nth_map pool defaultInfT pool_uniq inds1 inds2);" ++ nl ++
  "  [ done | rewrite pool_size; done | rewrite pool_size; done ]." ++ nl ++
  "Ltac solve_union_possible_pool inds1 inds2 :=" ++ nl ++
  "  apply disjoint_innernames_implies_union_possible;" ++ nl ++
  "  eapply (disjoint_union_tree _ _" ++ nl ++
  "            (map (nth defaultInfT pool) inds1)" ++ nl ++
  "            (map (nth defaultInfT pool) inds2));" ++ nl ++
  "  [ flatten_to_from_list" ++ nl ++
  "  | flatten_to_from_list" ++ nl ++
  "  | apply (disjoint_nth_map pool defaultInfT pool_uniq inds1 inds2);" ++ nl ++
  "    [ done | rewrite pool_size; done | rewrite pool_size; done ] ]." ++ nl.

(* --- Fichier complet : plusieurs bigraphes nommes --- *)

Definition print_header_all (l : list (string * big_ast)) : string :=
  print_pool_header (noms_decls l []).

(* emet chaque bigraphe, en gardant le compteur global, + alias au nom declare *)
Fixpoint emit_decls (ct : list (string * nat * bool)) (postab : list (string * nat)) (N : nat)
    (l : list (string * big_ast)) (i : nat) : string * nat :=
  match l with
  | [] => ("", i)
  | (nom, a) :: r =>
      let '(def, res, i') := emit ct postab N a i in
      let alias :=
        "(* " ++ nom ++ " *)" ++ nl ++
        "Definition " ++ nom ++ " := " ++ res ++ "." ++ nl ++ nl in
      let '(reste, i'') := emit_decls ct postab N r i' in
      (def ++ alias ++ reste, i'')
  end.

(* en-tete fixe : imports + ouverture du module parametre + import de MakeBig *)
Definition entete : string :=
  "Require Import AbstractBigraphs Bijections Names SignatureBig MyBasics" ++ nl ++
  "               MathCompAddings PlaceAxioms Nesting ParallelProduct MergeProduct MakeBig." ++ nl ++
  "From Stdlib Require Import Nat List Equality FunctionalExtensionality ProofIrrelevance Permutation CRelationClasses OrderedType." ++ nl ++
  "From Stdlib Require Import Btauto." ++ nl ++
  "From mathcomp Require Import all_boot all_order." ++ nl ++
  "Import ListNotations." ++ nl ++ nl ++
  "Module Genere (np: InfType) (nst : NameSetType np)." ++ nl ++
  "  Import nst." ++ nl ++
  "  Module ns := NameSets np nst." ++ nl ++
  "  Import ns." ++ nl ++
  "  Import MySigP_as_nat." ++ nl ++
  "  Module Mk := MakeBig np nst." ++ nl ++
  "    Import Mk. Import Mk.b. Import Mk.NB." ++ nl ++
  "  Import mp pp mup tp c leb eb b b.n b.s n s MySigP_as_nat." ++ nl ++
  "  Import np." ++ nl ++ nl.

Definition pied : string := nl ++ "End Genere." ++ nl.

(* prend la table des controles et la liste des bigraphes.
   valide d'abord (controle inconnu, noms dupliques, arite incoherente) :
   en cas d'erreur, aucun texte Rocq n'est produit, seul le message
   d'erreur est renvoye (prefixe "ERREUR: ", convention lue par driver.ml) *)
Definition print_file (ct : list (string * nat * bool))
    (l : list (string * big_ast)) : string :=
  match check_all ct l with
  | Some msg => "ERREUR: " ++ msg
  | None =>
      let postab := zip_positions (noms_decls l []) 0 in
      let '(corps, _) := emit_decls ct postab (List.length ct) l 0 in
      entete ++ print_support ++ nl ++ print_header_all l ++ nl ++ corps ++ pied
  end.