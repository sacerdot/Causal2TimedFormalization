(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 3                  *)
(*                                                                        *)
(**************************************************************************)

(* This is a formalization of Section 2.1 and Section 3 of the paper
   "Causal Reversibility Implies Time Reversibility" by
   M. Bernardo, I. Lanese, A. Marin, C. A. Mezzina, S. Rossi, C. Sacerdoti Coen
   submitted at QEST2023

   The following table gives a correspondence of the definitions/theorems
   in the paper and the ones in the formalization.

   Definition 1 (reversible LTS with independence) | RLTSI
   Definition 2 (commuting square)                 | commuting_square
   Definition 3 (propagation of coinitial          | PCI (in complements.ma)
                 independence)
   Definition 4 (causal equivalence)               | equiv
   Proposition 1                                   | equiv_count_action
   Definition 5 (causal consistency)               | CC
   Definition 6 (uniqueness of pairs) +            | uniqueness_of_pairs
   Proposition 2
   Definition 7 (absence of self-loops) +          | absence_of_self_loops
   Proposition 3
   Definition 10 (reversible Markovian LTS         | RMLTSI
   with independence)
   rateprod                                        | rateprod
   Definition 11 (product preservation along       | PPS
   squares)
   Lemma 1                                         | rateprod_rev
   Theorem 2                                       | main
*)

include "basics/star.ma".
include "basics/lists/list.ma".
include "z_axioms.ma".

(* Labelled Transition Systems with a decidable equality over actions *)
record LTS : Type[1] ≝
 { states : Type[0]
 ; a_state : states
 ; transitions :> Type[0]
 ; actions : Type[0]
 ; eql : actions → actions → bool (* action equality is decidable *)
 ; eql_to_eq : ∀alpha,beta. eql alpha beta = true → alpha=beta
 ; eql_to_not_eq : ∀alpha,beta. eql alpha beta = false → alpha≠beta
 ; action_of : transitions → actions
 ; src : transitions → states
 ; dst : transitions → states
 ; transitions_is_relation:
    ∀a,b.
     src a = src b → dst a = dst b → action_of a = action_of b →
      a = b
 }.

lemma bool_elim:
 ∀P: bool → Prop. ∀b.
  (b=true → P true) →
  (b=false → P false) →
   P b.
 #P #b #H1 #H2 inversion b /2/
qed.

lemma eql_elim:
 ∀L: LTS.
  ∀P: bool → Prop.
   ∀alpha,beta.
    (alpha=beta → P true) →
    (alpha≠beta → P false) →
     P (eql L alpha beta).
 #L #P #alpha #beta #H1 #H2 @(bool_elim ? (eql … alpha beta)) /3/
qed.

lemma eql_refl: ∀L: LTS. ∀alpha: actions L. eql … alpha alpha = true.
 #L #alpha @eql_elim
 [ //
 | #abs cases (absurd ? abs) /2/ ]
qed.

(* coinitial actions *)
definition coinit ≝
 λL:LTS. λa,b:L.
  src … a = src … b.

(* cofinal actions *)
definition cofinal ≝
 λL:LTS. λa,b:L.
  dst … a = dst … b.

(* actions that can be made consecutive *)
definition follow ≝
 λL:LTS. λa,b:L.
  dst … a = src … b.

(* predicate over list of actions stating that the list of actions
   is a path *)
inductive is_path (L: LTS) : list L → Prop ≝
 | wf_empty : is_path … []
 | wf_sing : ∀a. is_path … [a]
 | wf_cons : ∀a,b:L. ∀p. follow … a b → is_path … (b::p) → is_path … (a::b::p).

(* "dst_path … P p" holds iff the path p terminates with the process P;
   "dst_path … P []" holds for all "P" *)
inductive dst_path (L: LTS) (P: states L) : list L → Prop ≝
 | dp_empty : dst_path … []
 | dp_snoc: ∀a: L. ∀p. dst … a = P → dst_path … (p@[a]).

(* "src_path … P p" holds iff the path p originates from the process P
   "src_path … P []" holds for all "P" *)
inductive src_path (L: LTS) (P: states L): list L → Prop ≝
 | sp_empty: src_path … []
 | sp_cons: ∀a:L. ∀p. src … a = P → src_path … (a::p).

(* coinitial paths
   the list of actions is not required to satisfy is_path
*)
definition coinit_path: ∀L: LTS. list L → list L → Prop ≝
 λL. λp,q. ∃P: states L. src_path … P p ∧ src_path … P q.

(* cofinal paths
   the list of actions is not required to satisfy is_path
*)
definition cofinal_path: ∀L: LTS. list L → list L → Prop ≝
 λL. λp,q. ∃P: states L. dst_path … P p ∧ dst_path … P q.

lemma src_path_cons:
 ∀L: LTS. ∀P,a,l. src_path L P (a::l) → src … a = P.
 #L #P #a #l #H inversion H
 [ #abs destruct ] #x #y #E #E2 destruct //
qed.

lemma dst_path_snoc:
 ∀L: LTS. ∀P,a,l. dst_path L P (l@[a]) → dst … a = P.
 #L #P #a #l #H inversion H
 [ #abs lapply (nil_to_nil … abs) * #_ #abs2 destruct ]
 #x #y #E #E2 lapply (append_l2_injective_r ??? [a] [x] … E2) //
 #EQ destruct //
qed.

lemma dst_path_cons:
 ∀L: LTS. ∀P,a,l. dst_path L P (a::l) → dst_path … P l.
 #L #P #a * // #b #l #H inversion H
 [ #abs destruct
 | #c * normalize [#_ #abs destruct] #x #s #K #EQ destruct /2/ ]
qed.

(* "follow_path … p q" holds iff the path "p" can be followed by "q"
   the two lists of actions are not required to satisfy is_path
*)
definition follow_path: ∀L: LTS. list L → list L → Prop ≝
 λL,p,q. ∃P: states L. dst_path … P p ∧ src_path … P q.

lemma is_path_append: ∀L: LTS. ∀p,q: list L.
 is_path … p → is_path … q → follow_path … p q → is_path … (p@q).
 #L #p #q #Hp elim Hp
 [ //
 | #a cases q normalize //
   #b #r #K1 * #P * #K2 #K3 %3 // inversion K2
   [#abs destruct
   | #c #q #H #EQ destruct lapply (src_path_cons … K3)
     lapply (dst_path_snoc … [] … K2) // ]
 | -Hp -p #a #b #p #H1 #H2 #II #H3 #H4
   %3 // @II // cases H4 #P * #K1 #K2 %{P} % //
   lapply (dst_path_cons … K1) #K1' lapply (dst_path_cons … K1') #K // ]
qed.

(* uses the non-emptyness of (states P) when p = [] to pick an arbitrary P *)
lemma src_path_exists: ∀L: LTS. ∀p. ∃P. src_path L P p.
 #L * /3/
qed.

lemma snoc_exists:
 ∀A.∀l: list A.
  l = [] ∨ ∃a,l'. l = l'@[a].
 #A #l elim l normalize /2/
 #hd #tl *
 [ * %2 %{hd} %{[]} //
 | * #a * #l' #EQ >EQ %2 %{a} %{(hd::l')} // ]
qed. 

lemma is_path_append': ∀L: LTS. ∀p,q: list L.
 is_path … (p@q) → is_path … p ∧ is_path … q ∧ follow_path … p q.
 #L #p elim p
 [ #q normalize cases (src_path_exists … q) /4/
 | -p #a #p #II #q normalize #H inversion H
   [ #abs destruct
   | #b #EQ destruct lapply (nil_to_nil … e0) * #EQ1 #EQ2 destruct /5/
   | #a' #b' #p' #H1 #H2 #_ #EQ destruct cases (II q) // *
     #K1 #K2 * #P * #L1 #L2 %
     [ % // cut (p = [] ∨ ∃x,l. p = x::l) [cases p /4/ ] *
      [ #EQ2 destruct //
      | * #y * #ll #EQ2 destruct %3 // ]       
     | %{P} % // change with ([a']@p) in match (a'::p);
       cases (snoc_exists … p)
       [ #EQ2 destruct normalize %2{[]} /2/
       | * #x * #ll #EQ2 destruct lapply (dst_path_snoc … L1) /2/ ]]]]
qed.

(* being a cycle
   the list of actions is not required to satisfy is_path
*)
definition is_cycle : ∀L: LTS. list L → Prop ≝
 λL,p. p ≠ [] ∧ follow_path … p p.

(* LTS with Independence *)
record LTSI : Type[1] ≝
 { lts :> LTS
 ; ind : relation lts
 ; sym_ind : symmetric … ind
(* ; sym_irr : irreflexive … ind   NOT USED
*)
 }.

(* Definition 2 in the paper *)
record commuting_square (L: LTSI) (t: L) (u: L) (u': L) (t': L) : Prop ≝
 { cs_coinit: coinit … t u
 ; cs_ind: ind … t u
 ; cs_follow1: follow … t u'
 ; cs_follow2: follow … u t'
 ; cs_cofinal: cofinal … u' t'
 ; cs_same_action1: action_of … t = action_of … t'
 ; cs_same_action2: action_of … u = action_of … u'
 }.

(* Reversible LTS with Indepdence
   Definition 1 in the paper *)
record RLTSI : Type[1] ≝
 { ltsi :> LTSI
(* ; square : square_prop ltsi   NOT USED *)
 ; is_fw : ltsi → bool
 ; rev : ltsi → ltsi
 ; dir_rev : ∀a. is_fw (rev a) = notb (is_fw a)
 ; action_rev:
    ∀a,b.
     action_of ? a = action_of … b →
      action_of … (rev a) = action_of … (rev b)
 ; src_rev : ∀a. src … (rev a) = dst … a
 ; dst_rev : ∀a. dst … (rev a) = src … a
 ; disjoint_fw_bk:
    ∀a,b. is_fw a ≠ is_fw b → eql … (action_of … a) (action_of … b) = false
 ; rev_rev : ∀a. rev (rev a) = a
 }.

lemma eql_rev_not:
 ∀L: RLTSI. ∀alpha. ∀a: L.
  eql … alpha (action_of … (rev … a)) = true →
   eql … alpha (action_of … a) = false.
 #L #alpha #a #E >(eql_to_eq … E)
 @disjoint_fw_bk >dir_rev /2/
qed.

lemma eql_not_rev:
 ∀L: RLTSI. ∀alpha. ∀a: L.
  eql … alpha (action_of … a) = true →
   eql … alpha (action_of … (rev … a)) = false.
 #L #alpha #a #E >(eql_to_eq … E)
 @disjoint_fw_bk >dir_rev /2/
qed.

let rec rev_path_aux (L: RLTSI) (l: list L) (acc: list L) on l : list L ≝
 match l with
 [ nil ⇒ acc
 | cons a p ⇒ rev_path_aux … p (rev … a::acc) ].

(* function to reverse a path *)
definition rev_path : ∀L: RLTSI. list L → list L ≝ λL. λl. rev_path_aux L l [].

lemma rev_path_acc:
 ∀L: RLTSI. ∀l,acc.
  rev_path_aux L l acc = rev_path_aux … l [] @ acc.
 #L #l elim l normalize
 [ //
 | #a #t #II >II /2/ ]
qed.

lemma rev_path_append_aux:
 ∀L: RLTSI.
  ∀l1,l2,acc.
   rev_path_aux L (l1@l2) acc =
    rev_path_aux … l2 (rev_path_aux … l1 acc).
 #L #l1 elim l1 normalize //
qed.

lemma rev_path_append:
 ∀L: RLTSI.
  ∀l1,l2.
   rev_path L (l1@l2) = rev_path … l2 @ rev_path … l1.
 normalize #L #l1 #l2
 lapply (rev_path_append_aux … l1 l2 []) #E >E
 >rev_path_acc //
qed.

lemma rev_path_aux_wf:
 ∀L: RLTSI. ∀l: list L. ∀acc: list L.
  is_path … l → (is_path … acc ∧ coinit_path … l acc) →
   is_path … (rev_path_aux … l acc).
 #L #l elim l
 [ #acc normalize #_ * //
 | #a #p #II #acc #Hap lapply (is_path_append' … [a] … Hap) **
   #L1 #L2 #L3 * #H1 * #P * #H2 lapply (src_path_cons … H2) -H2 #H2 #H3 @II // %
   [ @(is_path_append … [?]) // %{P} % // %2{[]} >dst_rev //
   | cases L3 #Q * #M1 #M2 %{Q} /5/ ]]
qed.

lemma rev_path_wf:
 ∀L: RLTSI. ∀l: list L. is_path … l → is_path … (rev_path … l).
 #L #l #H @rev_path_aux_wf // % // whd cases (src_path_exists … l) /3/
qed.

(* causal equivalence
   Definition 4 in the paper
*)
inductive equiv (L: RLTSI) : list L → list L → Prop ≝
   erefl: ∀p. equiv … p p
 | esym: ∀p,q. equiv … p q → equiv … q p
 | etrans: ∀p,q,r. equiv … p q → equiv … q r → equiv … p r
 | eclos: ∀p1,p,p',p2. equiv … p p' → equiv … (p1@p@p2) (p1@p'@p2)
 | ecancel: ∀a,b: L. rev … a = b → equiv … [a;b] []
 | eswap: ∀t,u,u',t'. commuting_square … t u u' t' → equiv … [t;u'] [u;t'].

(* an equivalent formulation of causal equivalence, used in the proof *)
inductive equiv' (L: RLTSI) : list L → list L → Prop ≝
   erefl': ∀p. equiv' … p p
 | esym': ∀p,q. equiv' … p q → equiv' … q p
 | etrans': ∀p,q,r. equiv' … p q → equiv' … q r → equiv' … p r
 | ecancel':
   ∀a,b: L. ∀p,s.
    rev … a = b → equiv' … (p@[a;b]@s) (p@s)
 | eswap':
   ∀t,u,u',t'.
    ∀p,s.
     commuting_square … t u u' t' → equiv' … (p@[t;u']@s) (p@[u;t']@s).

theorem equivp_to_equivp:
 ∀L. ∀l1,l2. equiv' L l1 l2 → ∀p1,p2. equiv' … (p1@l1@p2) (p1@l2@p2).
 #L #l1 #l2 #E elim E
 [1,2,3,4: /2/
 | #t #u #u' #t' #p #s #H #p1 #p2
   lapply (eswap' … (p1@p) (s@p2) H) #K
   >associative_append >associative_append
   >associative_append >associative_append
   <(associative_append … p1 p) <(associative_append … p1 p)
   @K ]
qed.
   
theorem equiv_to_equivp:
 ∀L. ∀l1,l2. equiv L l1 l2 → equiv' … l1 l2.
 #L #l1 #l2 #E elim E
 [1,2,3,4: /2/
 | #a #b #H @(ecancel' … [] [] H)
 | #t #u #u' #t' #H @(eswap' … [] [] H)
 ]
qed.

theorem equivp_to_equiv:
 ∀L. ∀l1,l2. equiv' L l1 l2 → equiv … l1 l2.
 #L #l1 #l2 #E elim E
 [1,2,3: /2/
 | #a #b #p #s #H 
  change with (equiv ? ? (p@[]@s)) /3/
 | /3/ ]
qed.

lemma if_then_else_elim:
 ∀A: Type[0]. ∀P: A → Prop. ∀b. ∀t1. ∀t2.
  (b=true → P t1) → (b=false → P t2) →
   P(if b then t1 else t2).
 #A #P #b #t1 #t2 #H1 #H2 @(bool_elim … b) /2/
qed.

definition match_action: ∀L: RLTSI. actions L → L → int ≝
 λL,alpha,a.
  if eql … alpha (action_of … a) then iS iO
  else if eql … alpha (action_of … (rev … a)) then iP iO
  else iO.

lemma match_action_eq:
 ∀L: RLTSI. ∀alpha. ∀a,b: L.
  action_of … a = action_of … b →
   match_action … alpha a = match_action … alpha b.
 #L #alpha #a #b #EQ normalize <EQ
 @if_then_else_elim #H >H // -H
 @if_then_else_elim #H
 [ >(? : eql … alpha (action_of … (rev … b)) = true) //
   <H @eq_f @action_rev //
 | >(? : eql … alpha (action_of … (rev … b)) = false) //
   <H @eq_f @action_rev // ]
qed. 

lemma match_action_rev:
 ∀L: RLTSI. ∀alpha: actions L. ∀a.
  iplus (match_action … alpha a) (match_action … alpha (rev … a)) = iO.
 #L #alpha #a normalize
 @if_then_else_elim >rev_rev #H
 [ >(eql_not_rev … H) >H normalize >iplus_iP //
 | >H @if_then_else_elim #K >K
   [ >iplus_iS //
   | // ]]
qed.

(* function to count how many times a label occurs in a path, where
   each occurrence adds 1 and each occurrence of the reverse label
   subtracts 1 *)
let rec count_action (L: RLTSI) (alpha: actions L) (l: list L) on l : int ≝
 match l with
 [ nil ⇒ iO
 | cons a t ⇒ iplus (match_action … alpha a) (count_action … alpha t) ].

lemma count_action_singleton:
 ∀L: RLTSI. ∀alpha. ∀a. count_action L alpha [a] = match_action … alpha a.
 normalize //
qed.

lemma count_action_append:
 ∀L: RLTSI. ∀alpha: actions L. ∀l1,l2: list L.
  count_action L alpha (l1@l2) =
   iplus (count_action L alpha l1) (count_action L alpha l2).
 #L #alpha #l1 elim l1
 [ normalize //
 | #a #t #II #l2 whd in match (count_action … ((a::t)@l2)); >II
   whd in match (count_action … (a::t)); // ]
qed.

(* Proposition 1 in the paper *)
lemma equiv_count_action:
 ∀L: RLTSI. ∀alpha. ∀l1,l2: list L.
  equiv … l1 l2 → count_action … alpha l1 = count_action … alpha l2.
 #L #alpha #l1 #l2 #E elim E
 [1,2,3: /2/
 | #p1 #p #p' #p2 #_ #II >count_action_append >count_action_append >II
   >count_action_append //
 | #a #b #H <H >(count_action_append … [a] [rev … a])
   >count_action_singleton >count_action_singleton @match_action_rev
 | #t #u #u' #t' * #_ #_ #_ #_ #_ #Et #Eu
   >(count_action_append … [t] [u']) >(count_action_append … [u] [t'])
   >count_action_singleton >count_action_singleton >(match_action_eq … Et)
   <(match_action_eq … Eu) // ]
qed.

(* causal consistency
   Definition 5 in the paper
*)
definition CC : RLTSI → Prop ≝
 λL.
  ∀r,s: list L.
   is_path … r →
   is_path … s →
   coinit_path … r s →
   cofinal_path … r s →
    equiv … r s.

(* Proposition 2 in the paper *)
theorem uniqueness_of_pairs:
 ∀L: RLTSI.
  CC L →
   ∀a,b: L.
    coinit … a b →
     cofinal … a b →
      a = b.
 #L #CC #a #b #CI #CF @(transitions_is_relation … CI CF)
 lapply (CC [a] [b] ????)
 [ %{(dst … a)} % %2{[]} //
 |2,3,4: /4/ 
 | #EQ lapply(equiv_count_action … (action_of … a) … EQ)
   normalize >eql_refl normalize @if_then_else_elim /2/
   #abs @if_then_else_elim #abs2 #abs3 cases (? : False) /2/]
qed.

(* Proposition 3 in the paper *)
theorem absence_of_self_loops:
 ∀L: RLTSI.
  CC L →
   ¬(∃a: L. src … a = dst … a).
 #L #CC % * #a #H lapply (uniqueness_of_pairs … CC a (rev … a) ??)
 [ whd >dst_rev //
 | whd >src_rev //
 | #abs lapply (disjoint_fw_bk … a (rev … a) ?)
   [ >dir_rev /2/
   | <abs #abs2 lapply (eql_to_not_eq … abs2) /2/ ]]
qed.

(* Every strange cancellative monoid is a cancellative monoid
   Every cancellative monoid has a strange cancellative monoid as submonoid
   Every abelian cancellative monoid is a strange cancellative monoid *)
record strange_cancellative_monoid : Type[1] ≝
 { fcarr :> Type[0]
 ; fop : fcarr → fcarr → fcarr
 ; fe : fcarr
 ; fop_assoc: associative … fop
 ; fe_neutral_left: ∀n. fop fe n = n
 ; fe_cancel:
    ∀n,n',x,m,m'. fop (fop n x) m = fop (fop n' x) m' ↔ fop n m = fop n' m'
 }.

(* Reversible Markovian LTS with Indepdence
   Definition 10 in the paper *)
record RMLTSI : Type[1] ≝
 { ltsir :> RLTSI
 ; F: strange_cancellative_monoid
 ; rate : ltsir → F
 }.

(* Product of rates over a path
   Also called ratedprod in the paper *)
let rec rateprod (L: RMLTSI) (p: list L) on p : F L ≝
 match p with
 [ nil ⇒ fe …
 | cons a q ⇒ fop … (rate … a) (rateprod … q) ].

lemma rateprod_append:
 ∀L: RMLTSI. ∀p,q: list L.
  rateprod … (p@q) = fop … (rateprod … p) (rateprod … q).
 #L #p elim p normalize /3/
qed.

(* Product Preservation along Squares
   Definition 11 in the paper *)
definition PPS: RMLTSI → Prop ≝
 λL.
  ∀t,u,u',t': L.
   ∀H:commuting_square … t u u' t'.
    rateprod … [t;u'] = rateprod … [u;t'] ∧
    rateprod … [rev … u'; rev … t] = rateprod … [rev … t'; rev … u].

lemma reverse_loop:
 ∀L: RMLTSI. ∀a,a': L.
  rev … a = a' →
   rev_path … [a;a'] = [a;a'].
 #L #a #a' #H <H normalize >rev_rev //
qed.

(* Lemma 1 in the paper *)
theorem rateprod_rev:
 ∀L: RMLTSI. CC L → PPS L →
  ∀p,q. equiv L p q →
(* Both useless hypotheses; the second is implied by equivalence;
   is_path … p →
   is_path … q → *)
    rateprod … p = rateprod … (rev_path … p) ↔
     rateprod … q = rateprod … (rev_path … q).
 #L #Hcc #Hro #p #q #E elim (equiv_to_equivp … E)
 [1,2,3: /2/
 | #a #b #p #s #R
   >rateprod_append >rateprod_append
   >rev_path_append >rev_path_append
   >rateprod_append >rateprod_append
   >(reverse_loop … R)
   >rateprod_append >rev_path_append >rateprod_append
   <fop_assoc /2/
 | #t #u #u' #t' #p #s #CS
   >rateprod_append >rateprod_append
   >rev_path_append >rev_path_append >rateprod_append >rateprod_append
   >rateprod_append >rateprod_append
   >rev_path_append >rev_path_append >rateprod_append >rateprod_append
   cases (Hro … CS) #Hro1 #Hro2 >Hro1
   whd in match (rev_path ??);
   whd in match (rev_path ??);
   >Hro2 /3/
qed.

(* Theorem 2 in the paper *)
theorem main:
 ∀L: RMLTSI. CC L → PPS L →
  ∀p: list L.
   is_cycle … p →
   is_path … p →
    rateprod … p = rateprod … (rev_path … p).
 #L #Hcc  #Hro *
 [ //
 | #a #p * #_ * #P * #Hdp #Hsp lapply (src_path_cons … Hsp) #Hs #WF
   lapply (rateprod_rev … (a::p) [a; rev … a] ?) //
   [ @Hcc /4/ %{P} % // %2{[a]} /3/
   | #H @(proj2 … H) normalize >rev_rev // ]]
qed.