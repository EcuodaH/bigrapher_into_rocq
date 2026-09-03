let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let write_file path contents =
  let oc = open_out_bin path in
  output_string oc contents;
  close_out oc

let error_prefix = "ERREUR: "

let starts_with prefix s =
  String.length s >= String.length prefix
  && String.sub s 0 (String.length prefix) = prefix

let () =
  if Array.length Sys.argv <> 3 then begin
    prerr_endline "usage : bigtranslate <entree.big> <sortie.v>";
    exit 1
  end;
  let entree = Sys.argv.(1) in
  let sortie = Sys.argv.(2) in
  let source = read_file entree in
  let resultat = Big2v.big2v source in
  if starts_with error_prefix resultat then begin
    Printf.eprintf "%s : %s\n" entree resultat;
    exit 1
  end;
  write_file sortie resultat;
  Printf.printf "OK : %s -> %s\n" entree sortie