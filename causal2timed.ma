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
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/star.ma".
include "basics/lists/list.ma".
include "z_axioms.ma".

record LTS : Type[1] ≝
 { procs : Type[0]
 ; in_procs : procs (* procs is not empty *)
 ; acts :> Type[0]  (* rename to transitions *)
 ; labels : Type[0]
 ; eql : labels → labels → bool (* labels must be decidable! *)
 ; eql_to_eq : ∀alpha,beta. eql alpha beta = true → alpha=beta
 ; eql_to_not_eq : ∀alpha,beta. eql alpha beta = false → alpha≠beta
 ; label_of : acts → labels
 ; src : acts → procs
 ; dst : acts → procs
 ; acts_is_relation:
    ∀a,b.
     src a = src b → dst a = dst b → label_of a = label_of b →
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

lemma eql_refl: ∀L: LTS. ∀alpha: labels L. eql … alpha alpha = true.
 #L #alpha @eql_elim
 [ //
 | #abs cases (absurd ? abs) /2/ ]
qed.

definition coinit ≝
 λL:LTS. λa,b:L.
  src … a = src … b.

definition cofinal ≝
 λL:LTS. λa,b:L.
  dst … a = dst … b.
  
definition follow ≝  (* rename to consecutive? *)
 λL:LTS. λa,b:L.
  dst … a = src … b.

inductive wf_path (L: LTS) : list L → Prop ≝
 | wf_empty : wf_path … []
 | wf_sing : ∀a. wf_path … [a]
 | wf_cons : ∀a,b:L. ∀p. follow … a b → wf_path … (b::p) → wf_path … (a::b::p).

(* "dst_path … P p" holds iff the path p terminates with the process P;
   "dst_path … P []" holds for all "P" *)
inductive dst_path (L: LTS) (P: procs L) : list L → Prop ≝
 | dp_empty : dst_path … []
 | dp_snoc: ∀a: L. ∀p. dst … a = P → dst_path … (p@[a]).

(* "src_path … P p" holds iff the path p originates from the process P
   "src_path … P []" holds for all "P" *)
inductive src_path (L: LTS) (P: procs L): list L → Prop ≝
 | sp_empty: src_path … []
 | sp_cons: ∀a:L. ∀p. src … a = P → src_path … (a::p).

definition coinit_path: ∀L: LTS. list L → list L → Prop ≝
 λL. λp,q. ∃P: procs L. src_path … P p ∧ src_path … P q.

definition cofinal_path: ∀L: LTS. list L → list L → Prop ≝
 λL. λp,q. ∃P: procs L. dst_path … P p ∧ dst_path … P q.

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

(* "follow_path … p q" holds iff the path "p" can be followed by "q" *)
definition follow_path: ∀L: LTS. list L → list L → Prop ≝
 λL,p,q. ∃P: procs L. dst_path … P p ∧ src_path … P q.

lemma wf_path_append: ∀L: LTS. ∀p,q: list L.
 wf_path … p → wf_path … q → follow_path … p q → wf_path … (p@q).
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

(* uses the non-emptyness of (procs P) when p = [] to pick an arbitrary P *)
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

lemma wf_path_append': ∀L: LTS. ∀p,q: list L.
 wf_path … (p@q) → wf_path … p ∧ wf_path … q ∧ follow_path … p q.
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

definition is_cycle : ∀L: LTS. list L → Prop ≝
 λL,p. p ≠ [] ∧ follow_path … p p.

record LTSI : Type[1] ≝
 { lts :> LTS
 ; ind : relation lts
 ; sym_ind : symmetric … ind
(* ; sym_irr : irreflexive … ind   NOT USED
*)
 }.

record commuting_square (L: LTSI) (t: L) (u: L) (u': L) (t': L) : Prop ≝
 { cs_coinit: coinit … t u
 ; cs_ind: ind … t u
 ; cs_follow1: follow … t u'
 ; cs_follow2: follow … u t'
 ; cs_cofinal: cofinal … u' t'
 ; cs_same_label1: label_of … t = label_of … t'
 ; cs_same_label2: label_of … u = label_of … u'
 }.

(* NOT USED
definition square_prop : LTSI → Prop ≝
 λL. ∀t,u: L.
  coinit … t u →
  ind … t u →
    ∃u',t'. commuting_square … t u u' t'.
*)

record LTSISR : Type[1] ≝
 { ltsi :> LTSI
(* ; square : square_prop ltsi   NOT USED *)
 ; is_fw : ltsi → bool
 ; rev : ltsi → ltsi
 ; dir_rev : ∀a. is_fw (rev a) = notb (is_fw a)
 ; label_rev:
    ∀a,b.
     label_of ? a = label_of … b →
      label_of … (rev a) = label_of … (rev b)
 ; src_rev : ∀a. src … (rev a) = dst … a
 ; dst_rev : ∀a. dst … (rev a) = src … a
 ; disjoint_fw_bk:
    ∀a,b. is_fw a ≠ is_fw b → eql … (label_of … a) (label_of … b) = false
 ; rev_rev : ∀a. rev (rev a) = a
 }.

lemma eql_rev_not:
 ∀L: LTSISR. ∀alpha. ∀a: L.
  eql … alpha (label_of … (rev … a)) = true →
   eql … alpha (label_of … a) = false.
 #L #alpha #a #E >(eql_to_eq … E)
 @disjoint_fw_bk >dir_rev /2/
qed.

lemma eql_not_rev:
 ∀L: LTSISR. ∀alpha. ∀a: L.
  eql … alpha (label_of … a) = true →
   eql … alpha (label_of … (rev … a)) = false.
 #L #alpha #a #E >(eql_to_eq … E)
 @disjoint_fw_bk >dir_rev /2/
qed.

let rec rev_path_aux (L: LTSISR) (l: list L) (acc: list L) on l : list L ≝
 match l with
 [ nil ⇒ acc
 | cons a p ⇒ rev_path_aux … p (rev … a::acc) ].

definition rev_path : ∀L: LTSISR. list L → list L ≝ λL. λl. rev_path_aux L l [].

lemma rev_path_acc:
 ∀L: LTSISR. ∀l,acc.
  rev_path_aux L l acc = rev_path_aux … l [] @ acc.
 #L #l elim l normalize
 [ //
 | #a #t #II >II /2/ ]
qed.

lemma rev_path_append_aux:
 ∀L: LTSISR.
  ∀l1,l2,acc.
   rev_path_aux L (l1@l2) acc =
    rev_path_aux … l2 (rev_path_aux … l1 acc).
 #L #l1 elim l1 normalize //
qed.

lemma rev_path_append:
 ∀L: LTSISR.
  ∀l1,l2.
   rev_path L (l1@l2) = rev_path … l2 @ rev_path … l1.
 normalize #L #l1 #l2
 lapply (rev_path_append_aux … l1 l2 []) #E >E
 >rev_path_acc //
qed.

lemma rev_path_aux_wf:
 ∀L: LTSISR. ∀l: list L. ∀acc: list L.
  wf_path … l → (wf_path … acc ∧ coinit_path … l acc) →
   wf_path … (rev_path_aux … l acc).
 #L #l elim l
 [ #acc normalize #_ * //
 | #a #p #II #acc #Hap lapply (wf_path_append' … [a] … Hap) **
   #L1 #L2 #L3 * #H1 * #P * #H2 lapply (src_path_cons … H2) -H2 #H2 #H3 @II // %
   [ @(wf_path_append … [?]) // %{P} % // %2{[]} >dst_rev //
   | cases L3 #Q * #M1 #M2 %{Q} /5/ ]]
qed.

lemma rev_path_wf:
 ∀L: LTSISR. ∀l: list L. wf_path … l → wf_path … (rev_path … l).
 #L #l #H @rev_path_aux_wf // % // whd cases (src_path_exists … l) /3/
qed.

(* causal equivalence *)
inductive equiv (L: LTSISR) : list L → list L → Prop ≝
   erefl: ∀p. equiv … p p
 | esym: ∀p,q. equiv … p q → equiv … q p
 | etrans: ∀p,q,r. equiv … p q → equiv … q r → equiv … p r
 | eclos: ∀p1,p,p',p2. equiv … p p' → equiv … (p1@p@p2) (p1@p'@p2)
 | ecancel: ∀a,b: L. rev … a = b → equiv … [a;b] []
 | eswap: ∀t,u,u',t'. commuting_square … t u u' t' → equiv … [t;u'] [u;t'].

inductive equiv' (L: LTSISR) : list L → list L → Prop ≝
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

definition match_label: ∀L: LTSISR. labels L → L → int ≝
 λL,alpha,a.
  if eql … alpha (label_of … a) then iS iO
  else if eql … alpha (label_of … (rev … a)) then iP iO
  else iO.

lemma match_label_eq:
 ∀L: LTSISR. ∀alpha. ∀a,b: L.
  label_of … a = label_of … b →
   match_label … alpha a = match_label … alpha b.
 #L #alpha #a #b #EQ normalize <EQ
 @if_then_else_elim #H >H // -H
 @if_then_else_elim #H
 [ >(? : eql … alpha (label_of … (rev … b)) = true) //
   <H @eq_f @label_rev //
 | >(? : eql … alpha (label_of … (rev … b)) = false) //
   <H @eq_f @label_rev // ]
qed. 

lemma match_label_rev:
 ∀L: LTSISR. ∀alpha: labels L. ∀a.
  iplus (match_label … alpha a) (match_label … alpha (rev … a)) = iO.
 #L #alpha #a normalize
 @if_then_else_elim >rev_rev #H
 [ >(eql_not_rev … H) >H normalize >iplus_iP //
 | >H @if_then_else_elim #K >K
   [ >iplus_iS //
   | // ]]
qed.

let rec count_label (L: LTSISR) (alpha: labels L) (l: list L) on l : int ≝
 match l with
 [ nil ⇒ iO
 | cons a t ⇒ iplus (match_label … alpha a) (count_label … alpha t) ].

lemma count_label_singleton:
 ∀L: LTSISR. ∀alpha. ∀a. count_label L alpha [a] = match_label … alpha a.
 normalize //
qed.

lemma count_label_append:
 ∀L: LTSISR. ∀alpha: labels L. ∀l1,l2: list L.
  count_label L alpha (l1@l2) =
   iplus (count_label L alpha l1) (count_label L alpha l2).
 #L #alpha #l1 elim l1
 [ normalize //
 | #a #t #II #l2 whd in match (count_label … ((a::t)@l2)); >II
   whd in match (count_label … (a::t)); // ]
qed.

lemma equiv_count_label:
 ∀L: LTSISR. ∀alpha. ∀l1,l2: list L.
  equiv … l1 l2 → count_label … alpha l1 = count_label … alpha l2.
 #L #alpha #l1 #l2 #E elim E
 [1,2,3: /2/
 | #p1 #p #p' #p2 #_ #II >count_label_append >count_label_append >II
   >count_label_append //
 | #a #b #H <H >(count_label_append … [a] [rev … a])
   >count_label_singleton >count_label_singleton @match_label_rev
 | #t #u #u' #t' * #_ #_ #_ #_ #_ #Et #Eu
   >(count_label_append … [t] [u']) >(count_label_append … [u] [t'])
   >count_label_singleton >count_label_singleton >(match_label_eq … Et)
   <(match_label_eq … Eu) // ]
qed.

(* causal consistency *)
definition cc : LTSISR → Prop ≝
 λL.
  ∀r,s: list L.
   wf_path … r →
   wf_path … s →
   coinit_path … r s →
   cofinal_path … r s →
    equiv … r s.

theorem at_most_one:
 ∀L: LTSISR.
  cc L →
   ∀a,b: L.
    coinit … a b →
     cofinal … a b →
      a = b.
 #L #CC #a #b #CI #CF @(acts_is_relation … CI CF)
 lapply (CC [a] [b] ????)
 [ %{(dst … a)} % %2{[]} //
 |2,3,4: /4/ 
 | #EQ lapply(equiv_count_label … (label_of … a) … EQ)
   normalize >eql_refl normalize @if_then_else_elim /2/
   #abs @if_then_else_elim #abs2 #abs3 cases (? : False) /2/]
qed.

record strange_cancellative_monoid : Type[1] ≝
 { fcarr :> Type[0]
 ; fop : fcarr → fcarr → fcarr
 ; fe : fcarr
 ; fop_assoc: associative … fop
 ; fe_neutral_left: ∀n. fop fe n = n
 ; fe_cancel:
    ∀n,n',x,m,m'. fop (fop n x) m = fop (fop n' x) m' ↔ fop n m = fop n' m'
 }.

record LTSISRR : Type[1] ≝
 { ltsir :> LTSISR
 ; F: strange_cancellative_monoid
 ; rate : ltsir → F
 }.

let rec rate_path (L: LTSISRR) (p: list L) on p : F L ≝
 match p with
 [ nil ⇒ fe …
 | cons a q ⇒ fop … (rate … a) (rate_path … q) ].

lemma rate_path_append:
 ∀L: LTSISRR. ∀p,q: list L.
  rate_path … (p@q) = fop … (rate_path … p) (rate_path … q).
 #L #p elim p normalize /3/
qed.

definition rates_opp: LTSISRR → Prop ≝
 λL.
  ∀t,u,u',t': L.
   ∀H:commuting_square … t u u' t'.
    rate_path … [t;u'] = rate_path … [u;t'] ∧
    rate_path … [rev … u'; rev … t] = rate_path … [rev … t'; rev … u].

lemma reverse_loop:
 ∀L: LTSISRR. ∀a,a': L.
  rev … a = a' →
   rev_path … [a;a'] = [a;a'].
 #L #a #a' #H <H normalize >rev_rev //
qed.

theorem rate_path_rev:
 ∀L: LTSISRR. cc L → rates_opp L →
  ∀p,q. equiv L p q →
(* Both useless hypotheses; the second is implied by equivalence;
   wf_path … p →
   wf_path … q → *)
    rate_path … p = rate_path … (rev_path … p) ↔
     rate_path … q = rate_path … (rev_path … q).
 #L #Hcc #Hro #p #q #E elim (equiv_to_equivp … E)
 [1,2,3: /2/
 | #a #b #p #s #R
   >rate_path_append >rate_path_append
   >rev_path_append >rev_path_append
   >rate_path_append >rate_path_append
   >(reverse_loop … R)
   >rate_path_append >rev_path_append >rate_path_append
   <fop_assoc /2/
 | #t #u #u' #t' #p #s #CS
   >rate_path_append >rate_path_append
   >rev_path_append >rev_path_append >rate_path_append >rate_path_append
   >rate_path_append >rate_path_append
   >rev_path_append >rev_path_append >rate_path_append >rate_path_append
   cases (Hro … CS) #Hro1 #Hro2 >Hro1
   whd in match (rev_path ??);
   whd in match (rev_path ??);
   >Hro2 /3/
qed.

theorem main:
 ∀L: LTSISRR. cc L → rates_opp L →
  ∀p: list L.
   is_cycle … p →
   wf_path … p →
    rate_path … p = rate_path … (rev_path … p).
 #L #Hcc  #Hro *
 [ //
 | #a #p * #_ * #P * #Hdp #Hsp lapply (src_path_cons … Hsp) #Hs #WF
   lapply (rate_path_rev … (a::p) [a; rev … a] ?) //
   [ @Hcc /4/ %{P} % // %2{[a]} /3/
   | #H @(proj2 … H) normalize >rev_rev // ]]
qed.