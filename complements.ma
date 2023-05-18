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

include "causal2timed.ma".

(* No longer needed for the result in the paper *)

definition PCI : RLTSI → Prop ≝
 λL.
  ∀t,u,u',t': L.
   commuting_square … t u u' t' →
    ind … u' (rev … t).

lemma reverse_square_ind:
 ∀L: RLTSI. PCI L →
  ∀t,u,u',t': L.
   commuting_square L t u u' t' →
    ind … (rev … u') (rev … t').
 #L #H #t #u #u' #t' #CC
 lapply(H … CC) #K
 @sym_ind
 @(H … (rev … t) … u)
 cases CC #CI #I #F1 #F2 #CF #L1 #L2 %
 [2,5,6,7: /2/
 |1,3: normalize >src_rev //
 | normalize >dst_rev //]
qed.

lemma reverse_square:
 ∀L: RLTSI. PCI L → ∀t,u,u',t': L.
  commuting_square L t u u' t' →
   commuting_square … (rev … u') (rev … t') (rev … t) (rev … u).
 #L #H #t #u #u' #t' * #CI #IN #Ftu' #ut' #CF #Lt #Lu %
 [ normalize >src_rev >src_rev //
 | @(reverse_square_ind … t u u' t') /2/ 
 | normalize >dst_rev >src_rev //
 | normalize >dst_rev >src_rev //
 | normalize >dst_rev >dst_rev //
 | /2/
 | /2/ ]
qed.
