# BigraphER → Rocq

Traducteur qui part d'une description de bigraphe écrite dans un langage texte simple (`.big`, inspiré de la syntaxe de [BigraphER](https://github.com/bigraph-tools/BigraphER)) et produit un fichier Rocq exploitable avec [BiCoq](https://gitlab.isae-supaero.fr/c.marcon/bicoq), la formalisation des bigraphes de Milner développée par Cécile Marcon. Le but : éviter d'avoir à réécrire chaque bigraphe à la main dans la syntaxe de BiCoq, où une structure de taille réaliste peut demander plusieurs centaines de lignes.

## Architecture

Contrairement à un transpilateur externe écrit en OCaml, l'intégralité de la chaîne de traduction (lexer, parser, arbre syntaxique, imprimeur) est écrite et vérifiée en Rocq, puis extraite vers OCaml pour obtenir un exécutable :

```
.big --> Lexer.v --> BigParser.v(y) --> BigAst.v --> PrintV.v --> .v
```

| Fichier | Rôle |
|---|---|
| `Lexer.v` | tokenise le fichier source `.big` |
| `BigParser.vy` | grammaire Menhir (backend Rocq), produit un `big_ast` (`BigAst.v`) |
| `BigAst.v` | arbre syntaxique : un constructeur par forme du langage (ion, composition, tensor, nest, par, ppar, id, closure, substitution) |
| `PrintV.v` | **source de vérité de la génération** — parcourt l'AST et imprime le texte Rocq final ; seul fichier à éditer pour changer ce qui est généré |
| `Translate.v` | assemble les étapes précédentes en `Translate.big2v : string -> string` |
| `Extract.v` | extrait `big2v` vers OCaml (`big2v.ml`/`.mli` — générés, à ne jamais éditer à la main) |
| `driver.ml` | CLI minimale : lit un `.big`, appelle `Big2v.big2v`, écrit le `.v` |

`PrintV.v` n'importe rien de BiCoq : il se contente d'imprimer du texte qui *ressemble* à des appels BiCoq. Seuls les `.v` **générés** en sortie ont besoin de BiCoq pour compiler.

## Prérequis

- Rocq / coq (testé avec Rocq 9.1.1)
- Menhir, avec son backend Rocq (`MenhirLib`)
- dune
- Pour compiler les `.v` générés : un checkout de [BiCoq](https://gitlab.isae-supaero.fr/c.marcon/bicoq), avec `MakeBig.v` (le prélude de preuve : `make_ion`, `make_atom`, lemmes de cardinalité) déposé dans son `src/`

Le traducteur lui-même (`translator/`) ne dépend d'aucun fichier de BiCoq : `-R . BigTool` suffit.

## Compilation

```bash
cd translator
make        # génère BigParser.v (Menhir), compile la chaîne Rocq, produit driver.exe
```

`make clean` supprime tout ce qui est généré (`*.vo`, `BigParser.v`, `big2v.ml`/`.mli`, `_build/`).

## Utilisation

```bash
make run IN=tests/deadlock.big OUT=tests/deadlock.v
# ou, une fois compilé :
dune exec ./driver.exe -- tests/deadlock.big tests/deadlock.v
```

## Syntaxe d'entrée (`.big`)

```
ctrl C = 2;
atomic ctrl D = 1;

big B = C{x,y} . (D{x} | id);
```

La brique de base d'une expression est l'**ion** : un contrôle appliqué à une liste de noms (`C{x,y}`). Les ions se combinent avec :

| Symbole | Opérateur |
|---|---|
| `.` | imbrication (nest) |
| `*` | composition (◦) |
| `+` | produit tensoriel (⊗) |
| `\|` | produit de fusion |
| `\|\|` | produit parallèle |

**Ces cinq opérateurs n'ont pas de priorité entre eux** : une expression s'évalue de gauche à droite, dans l'ordre où elle est écrite (`A . B * C` = `(A . B) * C`) ; seules des parenthèses explicites imposent un autre regroupement. C'est une simplification assumée par rapport à la vraie précédence de BigraphER (où `.` lie plus fort que les produits).

S'y ajoutent :
- l'identité — `id`, `id(n)`, `id(n, {x,y})`
- la fermeture d'un nom — `/x(expr)`, ou `/x` seule
- la substitution — `nom/{x,y}(expr)`, qui réexpose un ensemble de noms internes sous un nom externe unique

Un nom introduit par une closure (`/x`) est interne ; tout autre nom est externe (convention héritée de BigraphER).

## Ce que produit le générateur

Le fichier `.v` s'organise en un en-tête (imports, ouverture de module), trois lemmes génériques de support, un **pool de noms partagé** : tous les noms de liens du fichier sont générés d'un coup (`new_disjoint_infT_list`) et désignés par leur position dans ce pool, ce qui garantit que deux bigraphes du fichier partageant un nom pointent vers le même `name` Rocq — puis le corps : chaque nœud de l'AST est imprimé sous un nom frais `bigInterN` ; le bigraphe déclaré par `big nom = ...;` reçoit en plus un alias `Definition nom := bigInterN.`.

## Détection d'erreur précoce

Avant d'émettre le moindre texte, `print_file` valide l'AST (`check_all`/`check_ast`) et détecte trois erreurs structurelles : contrôle non déclaré, noms dupliqués dans un ion, arité déclarée incohérente avec l'usage. En cas d'erreur, `big2v` renvoie une chaîne préfixée `"ERREUR: "` ; `driver.ml` n'écrit alors aucun fichier `.v` et sort avec le code 1.

## Automatisation des preuves

Chaque opérateur composé génère une ou deux obligations de preuve :

| Opérateur | Obligation | Statut |
|---|---|---|
| nest (`.`) | face interne vide, site = racine | `Qed` (toujours vraies) |
| composition (`*`) | site = racine | `Qed` |
| composition (`*`) | noms correspondants | `Qed` (via `solve_eqns`/`btauto`) |
| merge (`\|`) / parallel (`\|\|`) | `UnionPossible` | `Qed` |
| tensor (`+`) | faces internes disjointes | `Qed` |
| tensor (`+`) | noms externes disjoints | **`Admitted`** — dépend réellement du `.big`, seul cas encore ouvert |

## Tests

`tests/` contient des `.big` couvrant les opérateurs, plus des cas aux limites dédiés : `l_id_neutral`, `l_closure_twice`, `l_comp_ion_ion`, `l_nest_atom`, `l_dup_names`, `l_unknown_ctrl`, `l_empty`, `l_closure_order`, `l_arity_mismatch`.

## Limites connues

- L'obligation `preuve_dis_o` du tensor reste `Admitted` (piste identifiée : raisonner sur les indices du pool, comme pour l'unicité des noms — non implémentée).
- Pas de règles de réaction ni de blocs de système de réécriture (`react`, `-->@`) : question sémantique non tranchée.
- Par rapport à BigraphER : pas de référencement d'un bigraphe déjà déclaré dans un autre, pas de contrôles paramétrés par une valeur, pas de `merge(n)`/`split(n)` n-aire, pas de `share`, pas de littéraux place-graph bas niveau.

## Historique

Un premier transpilateur, écrit directement en OCaml (analyse lexicale et syntaxique manuelle, toutes les preuves laissées `Admitted`), avait été développé par Balazs Palotas et l'équipe (voir *Accélérer la formalisation des bigraphes*, Palotas et al.). Ce dépôt reprend le même objectif avec une architecture différente : la chaîne de traduction est écrite et vérifiée en Rocq puis extraite, ce qui permet la détection d'erreur précoce et l'automatisation partielle des preuves décrites ci-dessus.
