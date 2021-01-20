(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool List.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.


Set Implicit Arguments.



(* ==================================================================== *)
(* This template contains incomplete definitions that you have to       *)
(* fill. We always used the keyword `Definition` for all of them but    *)
(* you are free to change for a `Fixpoint` or an `Inductive`.           *)
(*                                                                      *)
(* If needed, it is perfectly fine to add intermediate definitions and  *)
(* local lemmas.                                                        *)

(* ==================================================================== *)
(* In this project, we are going to develop and prove correct an        *)
(* algorithm for deciding the membership of a word w.r.t. a given       *)
(* regular language - all these terms are going to be defined below     *)

(* This project lies in the domain of *formal languages*. The study     *)
(* of formal languages is a branch of theoretical computer science and  *)
(* is about that is interested in the purely syntactical aspects of     *)
(* of languages and as applications in different domains, ranging from  *)
(* the definition of  the grammar of programming languages to the field *)
(* of automated translation.                                            *)

(* As with natural languages, we first need to fix an alphabet. In our  *)
(* case, we are simply going to declare a type `A : Type` - i.e. we     *)
(* will use the same alphabet for all the formal languages we are going *)
(* to study. Inhabitants of `A` are called `letters`.                   *)

Parameter (A : Type).

(* -------------------------------------------------------------------- *)
(* A `word` is then simply a finite sequence of letters of `A`. We      *)
(* denote by A* the set of words over `A`. In Coq, we are going to      *)
(* represent words as lists whose elements are inhabitants of `A`. This *)
(* naturally leads to the following definition:                         *)

Notation word := (list A).

(* -------------------------------------------------------------------- *)
(* You can get an overview of the List library at the following URL:    *)
(* https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html      *)

(* -------------------------------------------------------------------- *)
(* In this setting, a `language` is simply a subset of A*. Assuming     *)
(* that `x` & `y` are letters of A, we can define the following         *)
(* languages:                                                           *)
(*                                                                      *)
(*  - the empty language: `L = ∅`;                                      *)
(*                                                                      *)
(*  - the language that contains only the empty word ε (i.e. the only   *)
(*    (word of length 0): L = {ε}`;                                     *)
(*                                                                      *)
(*  - the language that contains all the words solely composed of the   *)
(*    letter `x`: L = { ε, x, xx, xxx, ... } = { xⁿ | n ∈ ℕ } (here,    *)
(*    xⁿ stands for the word x…x, where x is repeated n times);         *)
(*                                                                      *)
(*  - the language that contains all the words of the form xⁿyⁿ:        *)
(*    L = { xⁿyⁿ | n ∈ ℕ };                                             *)
(*                                                                      *)
(*  - if we assume that A contains the letter '[' & ']', we can         *)
(*    define the language of well-balanced words for '[' & ']':         *)
(*    L = { w ∈ { [, ] }* | s.t. P(w) && Q(w) }, where                  *)
(*      - P(w) = any prefix of w contain no more ]'s then ['s           *)
(*      - Q(w) = the number of ['s and ]'s of w are equal.              *)

(* -------------------------------------------------------------------- *)
(* We can also combine languages to form other languages. For example,  *)
(* if L and G are languages, we can define:                             *)
(*                                                                      *)
(*  - the union of L & G            L ∪ G                               *)
(*  - the concatenation of L & G    { w1 · w2 | w1 ∈ L, w2 ∈ G }        *)
(*  - the intersection of L & G     L ∩ G                               *)
(*  - the complement of L           A* \ L                              *)
(*  - the Kleene closure of L       L* = { wⁿ | w ∈ L, n ∈ ℕ }          *)
(*  - the mirror of L               rev(L) = { rev(w) | w ∈ L }         *)

(* -------------------------------------------------------------------- *)
(* To define languages in Coq, we need a way to represent subsets       *)
(* of A*, i.e. subsets of the set of `word`'s. To that end, we are      *)
(* going to represent a set using its indicator function. (We remind    *)
(* that, given a subset F of an ambient set E, the indicator function   *)
(* of F is the function f_E from E to { ⊤, ⊥ } s.t.                     *)
(*                                                                      *)
(*                     f_E(x) = ⊤ iff x ∈ E                             *)

(* In Coq, the codomain of its indicator function is going to be a      *)
(* proposition: given a function `F : E -> Prop`, we say that x belongs *)
(* to `x` iff `f x` holds.                                              *)

Notation language := (word -> Prop).

(* -------------------------------------------------------------------- *)
(* From now use, we assume that L, G, H denote languages, x, y denote   *)
(* letters and that and w denotes a word.                               *)

Implicit Types (L G H : language) (x y : A) (w : word).

(* Definition of equality for lists *)
Definition head_l : forall x w y m, x::w = y::m -> x = y /\ w = m.
Proof.
move => x w y m e.
inversion e.
done.
Qed.


Lemma add_eq_0: forall n1 n2,0 = n1 + n2 -> n1 = 0 /\ n2 = 0.
Proof.
elim => [|n1 h1] [|n2]//=.
Qed.

Lemma n1Sn2: forall n1 n2, n1 + S n2 = S(n1 + n2).
Proof.
intros. done.
Qed.

(* -------------------------------------------------------------------- *)
(* From there, we can define the following languages                    *)

(* The empty language: no words belong to it.                           *)
(* (its indicator function always return `False`)                       *)
Definition lang0 : language :=
  fun w => False.

(* The language that only contains the empty word.                      *)
Definition lang1 : language :=
  fun w => w = nil.

(* Q1. We now ask you to define the following languages                 *)

(*  Given a word `w0`, the language that only contains the word `w0`.   *)
Definition langW w0 : language := 
  fun w => w = w0.

(* Given a sequence `ws` of words, the language that contains all the   *)
(* the words `ws` and only these words.                                 *)
Definition langF (ws : list word) : language :=
fun w => In w ws.
  
(* Given a letter `x`, the language that only contains the letter `x`   *)
(* seen as a word of length 1.                                          *)
Definition langA x : language := 
fun w => w = (x::nil).

(* The union of the two languages `L` and `G`.                          *)
Definition langU L G : language := 
fun w => L w \/ G w.

(* The intersection of the two languages `L` and `G`.                   *)
Definition langI L G : language := 
fun w => L w /\ G w.

(* The concatenation of the two languages `L` and `G`.                  *)
Definition langS L G : language := 
fun w => exists w1 w2, w = w1 ++ w2 /\ L w1 /\ G w2.

(* (Initial) definition for alternate Kleene definition *)
Fixpoint Ln L n : language :=
match n with
|0 => lang1
|S n => langS L (Ln L n)
end.

(* The Kleene closure of the language `L`                           *)
Inductive langK L : language :=
|Knil : langK L nil
|Kself w : L w -> langK L w
|Kconcat w1 w2 : langK L w1 -> langK L w2 -> langK L (w1 ++ w2).

(* Original definition for Kleene closure *)
Definition langK_2 L : language :=
fun w => exists n, Ln L n w.


(* The mirror of the language `L` (You can use the `rev`, that reversed *)
(* a list, from the standard library. *)
Definition langM L : language := 
fun w => L (rev w).

(* -------------------------------------------------------------------- *)
(* Given two languages, we will consider `L` & `G` equal iff they       *)
(* contain the same words:                                              *)

Definition eqL L G := forall w, L w <-> G w.

Infix "=L" := eqL (at level 90).

(* Lemmas for equality of languages *)

Lemma eqL_A (L G H:language): (L =L G) /\ (G =L H) -> (L =L H).
Proof.
intros. move: H0 => [LG GH].
split; intro.
+ apply GH. apply LG. done.
+ apply LG. apply GH. done.
Qed.

Lemma eqL_R L G : (L =L G) -> (G =L L).
Proof.
intros.
split.
+ apply H.
+ apply H.
Qed.

(* Exercise 2*)

Lemma concat0L L : langS lang0 L =L lang0.
Proof.
split. 
+ move => [w1 [w2 [eq [false l]]]].
  contradiction.
+ contradiction.
Qed.

Lemma concatL0 L : langS L lang0 =L lang0.
Proof. 
split. 
+ move => [w1 [w2 [eq [l false]]]]. contradiction.
+ contradiction.
Qed.

Lemma concat1L L : langS lang1 L =L L.
Proof.
split.
+ move => [w1 [w2 [eq [wnil lw2]]]].
  rewrite wnil in eq. simpl in eq. rewrite eq. apply lw2.
+ exists nil. exists w. done.
Qed.



Lemma concatL1 L : langS L lang1 =L L.
Proof.
unfold langS; unfold lang1.
split.
+ move => [w1 [w2 [eq [lw1 wnil]]]].
  rewrite wnil in eq.
  rewrite app_nil_r in eq.
  rewrite eq. 
  done.
+ move => Lw.
  exists w. exists nil.
  split.
  - rewrite app_nil_r. done.
  - done.
Qed.


Lemma concatA L G H : langS (langS L G) H =L langS L (langS G H).
Proof.
unfold langS.
split.
+ move => [w1 [w2 [eq1 [[w3 [w4 [eq2 [lw3 gw4] hw2]]]]]]].
  exists w3. exists (w4 ++ w2). 
  split.
  - rewrite eq1. rewrite eq2. symmetry. apply app_assoc.
  - split.
    * apply lw3.
    * exists w4. exists w2. done.
+ move => [w1 [w2 [eq1 [lw1 [w3 [w4 [eq2 [gw3 hw4]]]]]]]].
  exists (w1 ++ w3). exists w4.
  split.
  - rewrite eq1. rewrite eq2. apply app_assoc.
  - split.
    * exists w1. exists w3. done.
    * apply hw4.
Qed.

Lemma unionC L G : langU L G =L langU G L.
Proof.
unfold langU.
split; move => [l1 | l2].
+ right; done.
+ left; done.
+ right; done.
+ left; done.
Qed.

Lemma interC L G : langI L G =L langI G L.
Proof. 
split; move => [lw lg]; done.
Qed.



Lemma langKK L : langK (langK L) =L langK L.
Proof. 
split; move => L1. 
+ induction L1.
  - apply Knil.
  - apply H.
  - apply Kconcat.
    * apply IHL1_1.
    * apply IHL1_2. 
+ induction L1.
  - apply Knil.
  - apply Kself. apply Kself. apply H.
  - apply Kconcat.
    * apply IHL1_1.
    * apply IHL1_2.
Qed.


(* Note that, since languages are represented as indicator functions    *)
(* over `Prop`, we cannot assess that `L =L G` implies `L = G`.         *)
Check (nil).
(* ==================================================================== *)
(*                          REGULAR LANGUAGES                           *)

(* We are now interested in a subclass of languages called "regular"     *)
(* "languages": a language `L` is said to be regular iff one of the      *)
(* following holds:                                                     *)
(*                                                                      *)
(*  - L = ∅ or L = {ε} or L = {x} for some x ∈ A ;                      *)
(*  - L = L1 ∪ L2 for L1, L2 regular languages ;                        *)
(*  - L = L1 · L2 for L1, L2 regular languages ;                        *)
(*  - L = G* for G a regular language.                                  *)

(* This kind of inductive definitions can be encoded in Coq using       *)
(* an inductive predicate `regular : language -> Prop` s.t.             *)
(*                                                                      *)
(*             L is regular iff `regular L` holds                       *)

(* Q3. complete the following definition of the predicate `regular`:    *)

Inductive regular : language -> Prop :=
  (* Any language equivalent to a regular language is regular *)
  REq L G of regular L & L =L G : regular G

  (* The empty language is regular *)
| REmpty : regular lang0
| REword : regular lang1
| ROne x : regular (langA x)
| RUnion L G of regular L & regular G : regular (langU L G)
| RConc L G of regular L & regular G : regular (langS L G)
| RKleene L of regular L : regular (langK L)
.

(* -------------------------------------------------------------------- *)
(* Q4. prove that `langW w` is regular. 
                                *)
Lemma regularW w : regular (langW w).
Proof. 
induction w.
+ apply REword.
(* Apply REq *)
+ apply REq with (langS (langA a) (langW w)). 
(* Show that it's regular *)
  - apply RConc.
    * apply ROne.
    * apply IHw.
(* Show they are equal by double implication *)
  - split; move => L1.
    * move: L1 => [w1 [w2 [eq [la lw]]]].
      have p1: (a::w) = w1 ++ w2.
      ++  rewrite la.
          rewrite lw.
          done.
      ++  rewrite p1.
          done.
    * exists (a::nil), w.
      rewrite L1.
      split; try split; try done.
Qed.
    

(* -------------------------------------------------------------------- *)
(* Q5. prove that `langM L` is regular, given that L is regular.        *)

(* First we prove some helpful lemmas *)

Lemma revletter x: (fun w => langA x w) =L (fun w => langA x (rev w)).
Proof.
split; intros.
+ rewrite H.
  done.
+ have: rev (rev w) = rev (x::nil).
  - rewrite H. done.
  - rewrite rev_involutive.
    done.
Qed.

Lemma revnil: (fun w => lang1 w) =L (fun w => lang1 (rev w)).
Proof.
split; induction w; try done.
unfold lang1.
simpl.
move => hl.
symmetry in hl.
apply app_cons_not_nil in hl.
contradiction.
Qed.

Lemma revconc L G: (fun w => langS (langM G) (langM L) w) =L (fun w => langS L G (rev w)).
Proof.
unfold langS. unfold langM.
split; move => L1.
+ move: L1 => [w1 [w2 [r [l1 l2]]]].
  exists (rev w2). exists (rev w1). 
  split; try split; try done.
  - rewrite r. apply rev_app_distr.
+ move: L1 => [w1 [w2 [r [l1 l2]]]].
  exists (rev w2). exists (rev w1).
  split; try split; try rewrite rev_involutive; try done.
  - apply rev_eq_app. done.
Qed.

(*
Lemma ln_opp L n : Ln L (S n) =L langS (Ln L n) L.
Proof.
apply eqL_R. apply Ln_plus1l.
Qed.
Lemma lnrev L n w: Ln L n (rev w) <-> Ln (fun w0 => L (rev w0)) n w.
Proof.
induction n.
+ simpl. rewrite revnil. rewrite rev_involutive. done.
+ rewrite ln_opp. 
  split.
  - move => [w1 [w2 [r [l1 l2]]]].
    simpl. exists (rev w2). exists (rev w1).
    split;try split;try done.
    apply rev_eq_app. done.
    rewrite rev_involutive. done.
    
Admitted.
*)

Lemma nilrev w : rev w = nil -> w = nil.
intros.
induction w.
+ done. 
+ simpl in H. 
  apply app_eq_nil in H.
  destruct H. discriminate.
Qed.

Lemma revK L: langK (langM L) =L (fun w => langK L (rev w)).
Proof.
split; move => L1.
+ induction L1.
  - apply Knil.
  - apply Kself. done.
  - rewrite rev_app_distr. apply Kconcat. done. done. 
+ remember (rev w) as rw.
  move: w Heqrw. 
  induction L1. 
  - move => wn Heqrw. symmetry in Heqrw. apply nilrev in Heqrw. rewrite Heqrw. apply Knil.
  - move => wn Heqrw. apply Kself. rewrite Heqrw in H. done.
  - move => w Heqrw.  symmetry in Heqrw. apply rev_eq_app in Heqrw. rewrite Heqrw.
    apply Kconcat. apply IHL1_2. rewrite rev_involutive. done.
                    apply IHL1_1. rewrite rev_involutive. done.
Qed.

(* We now prove the main part of question 5 *)

Lemma regularM L : regular L -> regular (langM L).
Proof. 
move => reg.
unfold langM.
induction reg.
(* Case: REq *)
+ apply REq with (langM L).
  (* Regular *)
  - apply IHreg.
  (* Equality *)
  - unfold langM; split; apply H.
(* Case : REmpty *)
+ apply REmpty.
(* Case: REword *)
+ apply REq with (fun w => lang1 w).
  - apply regularW.
  - apply revnil.
(* Case: ROne *)
+ apply REq with (fun w => langA x w).
  - apply ROne.
  - apply revletter.
(* Case: RUnion *)
+ apply RUnion; try apply IHreg1; try apply IHreg2.
(* Case: RConc *)
+ apply REq with (fun w => langS (langM G) (langM L) w).
  - apply RConc. done. done.
  - apply revconc.
(* Case: RKleene *)
+ apply REq with (langK (langM L)). 
  - apply RKleene;done. 
  - apply revK.
Qed.


(* ==================================================================== *)
(*                        REGULAR EXPRESSIONS                           *)

(* Related to regular languages is the notion of regular expressions.   *)
(* A regular expression is a formal, syntactic expression that can      *)
(* later be interpreted as a regular language. Regular expressions are *)
(* pervasive in computer science, e.g. for searching for some text in   *)
(* a file, as it is possible with the `grep` command line tool.         *)
(*                                                                      *)
(* For instance, the command:                                           *)
(*                                                                      *)
(*    grep -E 'ab*a' foo.txt                                            *)
(*                                                                      *)
(* is going to print all the lines of `foo.txt` that contains a word    *)
(* of the form ab⋯ba (where the letter b can be repeated 0, 1 or more   *)
(* time. I.e., grep is going to find all the lines of `foo.txt` that    *)
(* contains a word that belongs in the formal language:                 *)
(*                                                                      *)
(*    L = { abⁿa | n ∈ ℕ }                                              *)
(*                                                                      *)
(* If you need to convince yourself that L is regular, note that:       *)
(*                                                                      *)
(*    L = { a } ∪ { b }* ∪ { a }                                        *)
(*                                                                      *)
(* In some sense, a regular expression is just a compact way to         *)
(* represent a regular language, and its definition is going to be      *)
(* close to the one of regular languages.                               *)
(*                                                                      *)
(* A regular expression is either:                                      *)
(*                                                                      *)
(*  - the constant ∅ or the constant ε or one letter from A             *)
(*  - the disjunction r1 | r2 of two regular expressions                *)
(*  - the concatenation r1 · r2 of two regular expressions              *)
(*  - the Kleene r* of some regular expression                          *)

(* We can represent regular expressions as a inductive type in Coq.     *)

(* Q6. complete the following definition:                               *)

Inductive regexp : Type :=
| RE_Empty : regexp 
| RE_Void  : regexp 
| RE_Atom : A -> regexp
| RE_Disjunct : regexp -> regexp -> regexp
| RE_Concat : regexp -> regexp -> regexp
| RE_Kleene : regexp -> regexp
.

Implicit Types (r : regexp).

(* We now have to formally relate regular expressions to regular       *)
(* languages. For that purpose, we are going to interpret a regular     *)
(* expression as a languages. If r is a regular expression, then we     *)
(* denote by language [r] as follows:                                   *)
(*                                                                      *)
(*   - [∅]       = ∅                                                    *)
(*   - [ε]       = ε                                                    *)
(*   - [a]       = { a } for a ∈ A                                      *)
(*   - [r₁ ∪ r₂] = [r₁] ∪ [r₂]                                          *)
(*   - [r₁ · r₂] = [r₁] · [r₂]                                          *)
(*   - [r*]      = [r]*                                                 *)

(* Q7. implement the Coq counterpart of the above definition:           *)

Fixpoint interp (r : regexp) {struct r} : language :=
  match r with
  | RE_Empty => lang0
  | RE_Void => lang1
  | RE_Atom A => langW (cons A nil)
  | RE_Disjunct r1 r2 => (langU (interp r1) (interp r2))
  | RE_Concat r1 r2 => (langS (interp r1) (interp r2))
  | RE_Kleene r1 => (langK (interp r1))
  end.

(* Q8. show that the interpretation of a regular expression is a        *)
(*     regular language:                                                *)

Lemma regular_regexp r : regular (interp r).
Proof. 
induction r; simpl.
+ apply REmpty.
+ apply REword.
+ apply ROne.
+ apply RUnion; done.
+ apply RConc; done.
+ apply RKleene; done.
Qed.

(* Q9. show that any regular language can be interpreted as a           *)
(*     regular expression:                                              *)

Lemma regexp_regular L : regular L -> exists r, L =L interp r.
Proof. 
move => reg.
(* Induction over the regular language *)
induction reg.
(* Case: Equivalent language *)
+ move: IHreg => [r H1]. 
  exists r. split; move => P.
  - apply H1. apply H. done.
  - apply H. apply H1. done.
(* Case: RE_Empty *)
+ exists RE_Empty. simpl. done.
(* Case: RE_Void *)
+ exists RE_Void. simpl. done.
(* Case: RE_Atom *)
+ exists (RE_Atom x). simpl. done.
(* Case: RE_Disjunct *)
+ move: IHreg1 => [r1 Lr]. move: IHreg2 => [r2 Gr].
  exists (RE_Disjunct r1 r2). simpl. unfold langU.
  split; rewrite Lr; rewrite Gr; done.
(* Case: RE_Concat *)
+ move: IHreg1 => [r1 Lr]. move: IHreg2 => [r2 Gr].
  exists (RE_Concat r1 r2). simpl. 
  unfold langS. split; move => [w1 [w2 [eq [lw int]]]];exists w1; exists w2;
  split;try split;try done. apply Lr. done. apply Gr. done.
  apply Lr. done. apply Gr. done.
(* Case: RE_Kleene *)
+ move: IHreg => [r IH].
  exists (RE_Kleene r). simpl.
  split; elim; intros.
  - apply Knil.
  - apply Kself. apply IH. done.
  - apply Kconcat. done. done.
  - apply Knil.
  - apply Kself. apply IH. done.
  - apply Kconcat. done. done.
Qed.


(* Of course, it may happen that two regular expressions represent      *)
(* the same language: r1 ~ r2 iff [r1] = [r2].                          *)

(* Q10. write a binary predicate eqR : regexp -> regexp -> Prop s.t.    *)
(*      eqR r1 r2 iff r1 and r2 are equivalent regexp.                  *)

(* They are equivalent if they are equivalent languages when interpreted *)
Definition eqR (r1 r2 : regexp) : Prop := eqL (interp r1) (interp r2).

Infix "~" := eqR (at level 90).

(* Q11. state and prove the following regexp equivalence:               *)
(*           (a|b)* ~ ( a*b* )*    
Not sure if a,b are regular expressions or letters, So we treated them as
expressions and it can easily be generalized with (RE_Atom a) and (RE_Atom b)
for example *)

Lemma langKUnion : forall a b w1 w2, (langK (interp a) w1) -> (langK (interp b) w2) -> 
    (langK (langU (interp a) (interp b)) w1) /\ (langK (langU (interp a) (interp b)) w2).
Proof.
intros.
split.
induction H. apply Knil. apply Kself. left. done.
apply Kconcat. apply IHlangK1. apply IHlangK2.
induction H0. apply Knil. apply Kself. right. done.
apply Kconcat. apply IHlangK1. apply IHlangK2.
Qed.


Lemma or_star_eq a b : (RE_Kleene (RE_Disjunct a b)) ~ (RE_Kleene (RE_Concat (RE_Kleene a) (RE_Kleene b))).
Proof.
split; simpl; move => L1.
+ induction L1.
  - apply Knil.
  - apply Kself. destruct H.
    * exists w, nil. split; try split. symmetry. apply app_nil_r.
      apply Kself. done. apply Knil.
    * exists nil, w. split; try split. apply Knil. apply Kself. done.
  - apply Kconcat. done. done.
+ induction L1.
  - apply Knil.
  - move: H => [w1 [w2 [eq [inta intb]]]]. rewrite eq. 
    apply Kconcat. 
    apply langKUnion with a b w1 w2 in inta. move: inta => [A B]. apply A. done.
    apply langKUnion with a b w1 w2 in inta. move: inta => [A B]. apply B. done.
  - apply Kconcat. done. done.
Qed.



(* ==================================================================== *)
(*                          REGEXP MATCHING                             *)

(* We now want to write a algorithm for deciding if a given word `w`    *)
(* matches a regular expression `r`, i.e. for deciding wether `w ∈ [r]` *)
(*                                                                      *)
(* For that purpose, we are going to use Brzozowski's derivatives.      *)
(*                                                                      *)
(* The idea of the algorithm is the following:                          *)
(*                                                                      *)
(* Given a letter `x` and an regular expression `r`, the Brzozowski's   *)
(* derivatives of `x` w.r.t. `r` is a regular expression x⁻¹·r s.t.     *)
(*                                                                      *)
(*    x · w ∈ [r] ⇔ w ∈ [x⁻¹·r]                                        *)
(*                                                                      *)
(* Assuming that we can compute a Brzozowski's derivative for any       *)
(* letter `x` and regular expression `r`, one can check that a word `w` *)
(* matches a regexp `r` as follows:                                     *)
(*                                                                      *)
(*   - if w = x · w' for some letter x and word w', we recursively      *)
(*     check that `w` matches `x⁻¹·r`; otherwise                        *)
(*   - if w = ε, then we directly check that [r] contains the empty     *)
(*     word - a property that is deciable.                              *)

(* Q12. write a nullity test `contains0` : regexp -> bool s.t.          *)
(*                                                                      *)
(*      ∀ r, contains0 r ⇔ ε ∈ [e]                                      *)

Fixpoint contains0 (r : regexp) : bool := 
            match r with
            |RE_Empty => false
            |RE_Void => true
            |RE_Atom w => false
            |RE_Disjunct r1 r2 => contains0 r1 || contains0 r2
            |RE_Concat r1 r2 => contains0 r1 && contains0 r2
            |RE_Kleene r1 => true
            end.


(* Q13. prove that your definition of `contains0` is correct:           *)

Lemma contains0_ok r : contains0 r <-> interp r nil.
Proof. 
(*unfold contains0.*)
split; move => prop;simpl;induction r;try done;simpl;simpl in prop.
+ unfold langU;case p1: (contains0 r1);rewrite p1 in IHr1;rewrite p1 in prop.
  - left;apply IHr1;try done.
  - right;case p2: (contains0 r2);rewrite p2 in prop;rewrite p2 in IHr2;auto.
+ unfold langS;exists nil;exists nil;simpl;split;try done.
case p1: (contains0 r1);rewrite p1 in IHr1;rewrite p1 in prop;
case p2: (contains0 r2);rewrite p2 in prop;rewrite p2 in IHr2;intuition.
+ apply Knil.
+ unfold langU in prop;move: prop => [left | right];intuition.
+ move: prop => [w1 [w2 [nil [int1 int2]]]].
symmetry in nil;apply app_eq_nil in nil;move: nil => [nil1 nil2].
rewrite nil1 in int1;rewrite nil2 in int2.
rewrite IHr1;try done;rewrite IHr2;done.


Qed.


(* We give below the definition of the Brzozowski's derivative:         *)
(*                                                                      *)
(*   - x⁻¹ · x         = ε                                              *)
(*   - x⁻¹ · y         = ∅ if x ≠ y                                     *)
(*   - x⁻¹ · ε         = ∅                                              *)
(*   - x⁻¹ · ∅         = ∅                                              *)
(*   - x⁻¹ · (r₁ | r₂) = (x⁻¹ · r₁) | (x⁻¹ · r₂)                        *)
(*   - x⁻¹ · (r₁ · r₂) = (x⁻¹ · r₁) · r₂ | E(r₁) · (x⁻¹ · r₂)           *)
(*   - x⁻¹ · r*        = (x⁻¹ · r) · r*                                 *)
(*                                                                      *)
(* where E(r) = ε if ε ∈ [r] & E(r) = ∅ otherwise.                      *)

(* Q14. write a function `Brzozowski` that computes a Brzozowski's      *)
(*      derivative as defined above.                                    *)
(*                                                                      *)
(* For that purpose, you may need to have a decidable equality over     *)
(* `A`. The parameter `Aeq` along with the axioms `Aeq_dec` give        *)
(* you such a decidable equality.                                       *)

Parameter Aeq : A -> A -> bool.

(* Here, `Aeq x y` has to be read as `Aeq x y = true`                   *)
Axiom Aeq_dec : forall (x y : A), Aeq x y <-> x = y.
Axiom Aeq_dec2 : forall (x y : A), Aeq x y = false <-> x <> y.
Axiom contfalse : forall r, contains0 r = false ->  interp r nil = False.





Fixpoint Brzozowski (x : A) (r : regexp) : regexp := 
            match r with
            |RE_Atom y => if (Aeq x y) then RE_Void else RE_Empty
            |RE_Disjunct r1 r2 => RE_Disjunct (Brzozowski x r1) (Brzozowski x r2)
            |RE_Concat r1 r2 => RE_Disjunct (RE_Concat (Brzozowski x r1) r2) 
            (if (contains0 r1) then (RE_Concat RE_Void (Brzozowski x r2)) else RE_Empty)
            |RE_Kleene r => RE_Concat (Brzozowski x r) (RE_Kleene r)
            |_ => RE_Empty
end.
(* Q15. write a function `rmatch` s.t. `rmatch r w` checks wether a     *)
(*      word `w` matches a given regular expression `r`.                *)

Fixpoint rmatch (r : regexp) (w : word) : bool := 
match w with 
|nil => contains0 r
|cons x w => (rmatch (Brzozowski x r) w)
end.

(* Q16. show that the `Brzozowski` function is correct.                 *)
Lemma cont : forall r, contains0 r  = true -> contains0 r.
Proof.
elim => [|||||]//=.
Qed.




Lemma Brzozowski_correct (x : A) (w : word) (r : regexp) :
  interp (Brzozowski x r) w -> interp r (x :: w).
Proof. 
move: x w.
induction r; simpl; try done; move => x w.
(*RE_Atom*)
+ case p1: (Aeq x a).
  - apply Aeq_dec in p1. move => wnil.
    rewrite wnil. rewrite p1. done.
  - contradiction.


(*RE_Disjunct *)
+ unfold langU.
  move => [Br1 | Br2].
  - left;apply IHr1;apply Br1.
  - right;apply IHr2; apply Br2.
(*RE_Concat*)
+ unfold langU. unfold langS;unfold lang1. move => [H | H].
  - move: H => [w1 [w2 [eq12 [br1 lr2]]]].
    * exists (x::w1);exists w2. 
      split; try split; try done.
        rewrite eq12. intuition.
        apply IHr1; done.
  - case p1: (contains0 r1);simpl. unfold langU. unfold langS;unfold lang1.
    * apply cont in p1. rewrite p1 in H. simpl in H. 
      move: H => [w1 [w2 [eq12 [br1 lr2]]]].
      rewrite br1 in eq12. simpl in eq12.
      exists nil; exists (x :: w2).
      split; try split; try done.
      rewrite eq12. intuition.
      apply contains0_ok. done.
      apply IHr2. done.
    * rewrite p1 in H. contradiction.

(*RE_Kleene*)
+ move => [w1 [w2 [eq [brx lnk]]]]. move: w w1 eq brx.
  induction lnk; intros.
  - symmetry in eq. rewrite app_nil_r in eq. symmetry in eq. rewrite eq. 
    apply Kself. apply IHr. done.
  - rewrite eq. remember (x::w1) as W. 
    have p1: x :: w1 ++ w = W ++ w. rewrite HeqW. done.
    rewrite p1. apply Kconcat; try rewrite HeqW; apply Kself. 
    apply IHr. done. done.
  - rewrite eq. remember (x::w0) as W. 
    have p1: x :: w0 ++ w1 ++ w2 = W ++ w1 ++ w2. rewrite HeqW. done.
    rewrite p1. apply Kconcat; try rewrite HeqW. apply Kself. apply IHr. done.
    apply Kconcat; done.
Qed.
(* Q17. show that `rmatch` is correct. *)

                            
Lemma rmatch_empty: forall w, rmatch RE_Empty w -> False.
Proof.
elim => [|]//=.
Qed.

Lemma rmatch_correct (r : regexp) (w : word):
  rmatch r w -> interp r w.
Proof. 
move : r.
induction w;simpl.
+ apply contains0_ok;done.
+ move => r br. 
  apply Brzozowski_correct. apply IHw.  done.
Qed.





(* Q18. (HARD - OPTIONAL) show that `rmatch` is complete.               *)







(*
Proof. 
elim => [|||||]//= H.
+ move: H => [h1 h2]. contradiction.
+ move: H => [h1 h2]. discriminate.
+ move => [h1 h2]. unfold langW in h2. 
  apply not_nil with H nil in h2. discriminate.
+ move => H1 r H2.
  case H1. 
  *)



(*
Lemma next x1 x2 : forall w1 w2, x1 :: w1 = x2 :: w2 -> x1 = x2 /\ w1 = w2.
Proof.
elim =>[|a1 w1 hl] [|a2 w2] eq //=.
split; try done. have: (x1 <> x2)

*)
Lemma backwards x w: forall w1 w2, x :: w = w1 ++ w2
 -> (exists w', w1 = x::w' /\ w = w' ++ w2 ) 
 \/ (exists w', w = w' /\ w1 = nil /\ w2 = x::w').
Proof.
elim => [|x1 w1 hl] [|x2 w2] eq //=.
+ right. exists w2. split;try split; try done;
  apply head_l in eq; move: eq => [h1 h2]. done. rewrite h1. done.

+ left. symmetry in eq. rewrite app_nil_r in eq.
  exists w1. split; apply head_l in eq; move: eq => [h1 h2].
  rewrite h1. done. rewrite h2. symmetry. apply app_nil_r.
+ left. apply head_l in eq. move: eq => [h1 h2].
  exists w1. split. rewrite h1. done. done.
Qed.
  

Lemma correct_Brzozowski (x : A) (w : word) (r : regexp) :
   interp r (x :: w) -> interp (Brzozowski x r) w.
Proof.
move: x w.
induction r; move => x w int; try done;simpl; simpl in int.
(*Atom*)
+ case p1: (Aeq x a);simpl. 
  - apply Aeq_dec in p1. simpl. rewrite p1 in int. unfold langW in int. 
    have p2: a :: w = a :: nil -> w = nil.
    * induction w;simpl; done.
    * apply p2 in int. done.
  - apply Aeq_dec2 in p1.
    apply head_l in int. move: int => [false other]. contradiction.
(*Disjunct*)
+ move: int => [l | r].
  left. apply IHr1. done.
  right. apply IHr2. done.
(*Concat*)
+ unfold langU. unfold langS.
  - move: int => [w1 [w2 [eq [int1 int2]]]].
    apply backwards in eq. move: eq => [[w' [eq1 eq2]] | [w' [eq1 [eq2 eq3]]]].
    * left. exists w', w2. split; try split; try done. apply IHr1.
    symmetry in eq1. rewrite eq1. done. 
    * right. case p1: (contains0 r1). 
      ++  exists nil, w'. rewrite eq1. split; try split; try done. apply IHr2.
      symmetry in eq3. rewrite eq3. done.
      ++ apply contfalse in p1. rewrite eq2 in int1. rewrite p1 in int1. contradiction.
    
  
(*Kleene*)
+ remember (x::w) as W. move: w x HeqW.

induction int; intros.
  - discriminate.
  - exists w0, nil. split; try split. symmetry. apply app_nil_r.
    apply IHr. symmetry in HeqW. rewrite HeqW. done. apply Knil.
  - symmetry in HeqW. apply backwards in HeqW. 
    move: HeqW => [[w' [eq1 eq2]] | [w' [eq1 [eq2 eq3]]]].
    * have langS1: langS (interp (Brzozowski x r)) (langK (interp r)) w'.
    apply IHint1 in eq1. done.
    move: langS1 => [le [ri [eqle [brle intri]]]].
    exists le, (ri ++ w2). split; try split; try done. 
    rewrite eq2. rewrite eqle. intuition. apply Kconcat; done.
    * apply IHint2. rewrite eq1. done.
Qed.
  
(*
+ move: int => [n ln]. induction n.
  - simpl in ln. unfold lang1 in ln. symmetry in ln. apply not_nil in ln. discriminate.
  - move: ln => [w1 [w2 [eq [l1 ln]]]].
      apply backwards in eq. move: eq => [[w' [eq1 eq2]] | [w' [eq1 [eq2 eq3]]]].
    * unfold langS. 
      exists w', w2. split; try split; try done.
      apply IHr. symmetry in eq1. rewrite eq1. done.
      exists n. done.
    * exists nil,w'. split; try split; try done. apply IHr. admit.
      exists n.
  *)
    

      
Lemma rmatch_complete (r : regexp) (w : word):
  interp r w -> rmatch r w.
Proof. 
move: r.

induction w; simpl; move => r rw.
+ apply contains0_ok. done.
+ apply IHw. apply correct_Brzozowski. done.
Qed.

(* Lemmas used for initial Kleene closure definition *)

(* Useful Lemmas regarding Ln: (we write langS L1 L) as L1 ++ L2)

Ln_plus1l gives us L ++ L^n =L L^(n+1) =L L^n ++ L

Ln_plus gives us L^n1 ++ L^n2 =L L^(n1 + n2)
*)

Lemma Ln_plus1l L n: (langS (Ln L n) L) =L Ln L (S n).
Proof.
induction n.
+ simpl. split;rewrite concatL1; apply concat1L.

+ simpl. split.
  - move => [w1 [w2 [eq [ln l]]]].
    move: ln => [w3 [w4 [eq2 [ln1 l1]]]].
    exists w3. exists (w4 ++ w2).
    split; try split;try done.
    rewrite eq. rewrite eq2. intuition.
    apply IHn. simpl.
    exists w4. exists w2.
    split; try split;try done.
  - move => [w1 [w2 [eq [l1 [w3 [w4 [eq2 [l2 ln2]]]]]]]].
    apply concatA.
    exists w1. exists(w3 ++ w4).
    split; try split;try done.
    rewrite eq. rewrite eq2. intuition.
    apply IHn.
    exists w3. exists w4.
    split; try split;try done.
Qed.


Lemma Ln_plus L: forall n1 n2, langS (Ln L n1) (Ln L n2) =L Ln L (n1 + n2).
Proof.
elim => [|n1 h1] n2//=.
+ apply concat1L.
+ split; move => L1.
  move: L1 => [w1 [w2 [eq [ls ln1]]]].
  move: ls => [w3 [w4 [eq2 [l1 ln2]]]].
  exists w3. exists (w4 ++ w2). split;try split; try done.
  rewrite eq. rewrite eq2. intuition.
  apply h1. exists w4. exists w2. split;try split;try done.
  
  move: L1 => [w1 [w2 [eq [ls ln2]]]].
  apply h1 in ln2.
  move: ln2 => [w3 [w4 [eq2 [ls2 ln3]]]].
  exists (w1++w3). exists (w4).
  split; try split; try done.
  rewrite eq. rewrite eq2. intuition.
  exists w1. exists w3. split;try split;done.
Qed.

(* 
  Next we have side Lemmas about langK
        (we write langK L as L^K)

  langKA gives L^K ++ L^K =L L^K

  and concat_langK gives L^K ++ (L^K)^n = L^K
*)

(*
Lemma langKA L : langS (langK L) (langK L) =L langK L.
Proof.
split; unfold langS. unfold langK. 
+ move => L1.
  move: L1 => [w1 [w2 [eq [[k1 ln1] [k2 ln2]]]]].
  exists (k1 + k2).
  induction k1;simpl;simpl in ln1. 
  - unfold lang1 in ln1. rewrite ln1 in eq.
    rewrite app_nil_l in eq. rewrite eq. done.
  - unfold langS. unfold langS in ln1. move: ln1 => [w3 [w4 [eq2 [l1 l2]]]].
    exists w3. exists (w4 ++ w2).
    split; try split; try done.
      * rewrite eq. rewrite eq2. intuition.
      * apply Ln_plus. unfold langS. exists w4. exists w2. 
        split;try split;try done.
+ move => [n ln].
  exists nil. exists w.
  split;try split;try done.
  - exists 0. done.
  - exists n. done.
Qed.
*)

(* To prove Lang_KK2 *)
 
Lemma concat_langK L : forall k w, langS (langK_2 L) (Ln (langK_2 L) k) w -> (langK_2 L) w .
Proof.
elim => [|k hk] w.
+ simpl. apply concatL1.
+ simpl. move => L1.
  move: L1 => [w1 [w2 [eq [[k2 lk2] ls]]]].
  move: ls => [w3 [w4 [eq2 [[k3 lk3] lnK2]]]].
  apply hk.
  exists (w1 ++ w3). exists w4.
  split;try split;try done. 
  rewrite eq. rewrite eq2. intuition.
  exists (k2 + k3).
  apply Ln_plus.
  exists w1. exists w3.
  split;try split; try done.
Qed.

Lemma eqK L: langK_2 L =L langK L.
Proof.
move => w.
split.
+ move => [n ln].
move: w ln.
induction n; intros.
simpl in ln. rewrite ln. apply Knil.
simpl in ln. move: ln => [w1 [w2 [eq [wnil lw2]]]].
apply IHn in lw2.
rewrite eq.
apply Kconcat. apply Kself. done. done.

+ elim.
exists 0. done.
exists 1. simpl. apply concatL1. done.
move => w1 w2 lw1 lk22 lk2.
move: lk22 => [n ln2].
move => [n' ln'].
exists (n + n'). 
apply Ln_plus. 
exists w1,w2. split;try split; try done.
Qed.

Lemma langKK_2 L : langK_2 (langK_2 L) =L langK_2 L.
Proof.
split; move => L1.
+ move: L1 => [k ln1].
  induction k.
  - exists 0. simpl. done.
  - move: ln1 => [w1 [w2 [eq [lgk ln]]]].
    apply concat_langK with k.
    exists w1. exists w2.
    split; try split; try done.
+ move: L1 => [n ln].
  exists 1. simpl. apply concatL1. exists n. done.
Qed.

Lemma revK_2 L: langK_2 (langM L) =L (fun w => langK_2 L (rev w)).
Proof.

split; move => [n ln]; exists n.
+ move: w ln. 
  induction n; move => w ln. 
  - simpl in ln. simpl. apply revnil. rewrite rev_involutive. done.
  - apply Ln_plus1l in ln. 
    simpl. move: ln => [w1 [w2 [eq [lm ln1]]]].
    exists (rev w2), (rev w1). 
    split; try split; try done.
    * rewrite eq. apply rev_app_distr.
    * apply IHn. done.
+ move: w ln.
  induction n; move => w ln. 
  - simpl in ln. simpl. apply revnil. done.
  - apply Ln_plus1l in ln. 
    simpl. move: ln => [w1 [w2 [eq [lm ln1]]]].
    exists (rev w2), (rev w1). 
    split; try split; try done.
    * apply rev_eq_app. done.
    * unfold langM. rewrite rev_involutive. done.
    * apply IHn. rewrite rev_involutive. done.
Qed.
Lemma Lneq1 L G n: (L =L G) -> (langS L (Ln L n)) =L (langS G (Ln L n)).
Proof.
intro.
split; move => [w1 [w2 [eq [l ln]]]];
exists w1; exists w2; split;try split; try done. 
apply H. done.
apply H. done.
Qed.
Lemma Lneq L G n: (L =L G) -> (Ln L n) =L (Ln G n).
Proof.
intro.
induction n; try done.
split; simpl; move => [w1 [w2 [eq [l ln]]]]. fold Ln in ln.
  + exists w1. exists w2. split; try split; try done. 
      * apply H. done.
      * apply IHn. done.
  + exists w1. exists w2. split; try split; try done. 
      * apply H. done.
      * apply IHn. done.
Qed. 
