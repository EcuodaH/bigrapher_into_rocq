Set Warnings "-notation-overridden, -parsing, -masking-absolute-name, -cannot-define-projection".

Require Import AbstractBigraphs.
Require Import Bijections.
Require Import Names.
Require Import SignatureBig.
Require Import MyBasics.
Require Import MathCompAddings.
Require Import PlaceAxioms.
Require Import Nesting.
Require Import ParallelProduct.
Require Import MergeProduct.

From Stdlib Require Import Nat List Equality FunctionalExtensionality ProofIrrelevance Permutation CRelationClasses OrderedType.
From mathcomp Require Import all_boot all_order.

Import ListNotations.

Module MakeBig (np: InfType) (nst : NameSetType np).

  Import nst.
  Module ns := NameSets np nst.
  Import ns.

  Module NB := NestingBig MySigP_as_nat np nst.
  Module b := Bigraphs MySigP_as_nat np nst.
  Import b.
  Import NB mp pp mup tp c leb eb b b.n b.s n s MySigP_as_nat.
  Import MySigP_as_nat.

  Lemma card_empty_set : cardinal empty_set = 0.
  Proof.
    rewrite <- card_empty.
    exact empty_set_empty.
  Qed.

  Lemma card_add_name (s : nameset) (n : name) :
    ~ n \ins s -> cardinal (add n s) = (cardinal s).+1.
  Proof.
    intro.
    pose proof @card_add.
    specialize (H0 s (add n s)).
    apply (H0 n).
    exact H.
    reflexivity.
  Qed.

(*  constructeurs ions et atomes  *)

  Definition make_ion (N i ar : nat) (o : nameset)
      (Hlt : i < N) (Hcard : Arity ar = cardinal o)
      : bigraph 1 empty_set 1 o.
  Proof.
    eapply (@discrete_ion (ordinal N) (@Ordinal N i Hlt) ar o).
    apply find_bij_big.
    exact Hcard.
  Defined.

  Definition make_atom (N i ar : nat) (o : nameset)
      (Hlt : i < N) (Hcard : Arity ar = cardinal o)
      : bigraph 0 empty_set 1 o.
  Proof.
    eapply (@discrete_atom (ordinal N) (@Ordinal N i Hlt) ar o).
    exact Hcard.
  Defined.

End MakeBig.