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

include "arithmetics/nat.ma".

inductive int : Type[0] ≝
 | Pos: nat → int   (* n : ℕ ↦      n : ℤ *)
 | Neg: nat → int.  (* n : ℕ ↦ -(n+1) : ℤ *)

definition iO ≝ Pos O.

definition iS: int → int ≝
 λz.
  match z with
  [ Pos n ⇒ Pos (S n)
  | Neg n ⇒
      match n with
      [ O ⇒ Pos O
      | S m ⇒ Neg m]].

definition iP: int → int ≝
 λz.
  match z with
  [ Pos n ⇒
      match n with
      [ O ⇒ Neg O
      | S m ⇒ Pos m]
  | Neg n ⇒ Neg (S n)].

lemma iS_iP: ∀z. iS (iP z) = z.
 **//
qed.

lemma iP_iS: ∀z. iP (iS z) = z.
 **//
qed.

definition iplus: int → int → int ≝
 λz1,z2.
  match z1 with
  [ Pos n ⇒
     nat_rect_Type0 (λ_.int) z2 (λ_.iS) n 
  | Neg n ⇒
     nat_rect_Type0 (λ_.int) z2 (λ_.iP) (S n) ].

lemma iplus_iPl: ∀z1,z2. iplus (iP z1) z2 = iP (iplus z1 z2).
 #z1 #z2 whd in ⊢ (??%?); cases z1 // * // #m
 whd in ⊢ (??%?); whd in match (iplus ??);
 >iP_iS //
qed.
 
lemma iplus_iP: ∀z1,z2. iplus z1 (iP z2) = iP (iplus z1 z2).
 #z1 elim z1
 [ #n elim n // #m #II #z2 <iplus_iPl whd in match (iP (Pos ?));
   change with (iS (iplus (Pos m) (iP z2)) = ?) >II //
 | #n #z2
   change with (iP ? = iP (iP ?)) @eq_f
   elim n // #x #II change with (iP ? = iP (iP ?)); >II // ]
qed.

lemma iplus_iSl: ∀z1,z2. iplus (iS z1) z2 = iS (iplus z1 z2).
 #z1 #z2 whd in ⊢ (??%?); cases z1 // * [ change with (z2 = ?) >iS_iP // ] #m
 change with (iplus (Neg m) ? = ?) >(iplus_iPl (Neg m) ?) //
qed.

lemma iplus_iS: ∀z1,z2. iplus z1 (iS z2) = iS (iplus z1 z2).
 #z1 elim z1
 [ #n #z2
   elim n // #x #II change with (iS (iplus (Pos x) ?) = iS (iS (iplus (Pos x) ?)))
   >II //
 | #n elim n [ #z2 >iS_iP change with (iP ? = ?); >(iP_iS z2) // ]
   #m #II #z2 <iplus_iSl whd in match (iS (Neg ?));
   change with (iP (iplus (Neg m) (iS z2)) = ?) >II // ]
qed.

lemma iplus_assoc: associative … iplus.
 * #n elim n [ // |3: #y #z @iplus_iPl ] #m #II #y #z
 [ >(iplus_iSl (Pos m) ?) >iplus_iSl >(iplus_iSl (Pos m) ?) >II //
 | >(iplus_iPl (Neg m) ?) >iplus_iPl >(iplus_iPl (Neg m) ?) >II // ]
qed.

lemma iplus_neutral_r: ∀z. iplus z iO = z.
 * #n elim n // #m #II
 [ change with (iS ? = iS (Pos m)) | change with (iP ? = iP (Neg m)) ]
 @eq_f @II
qed.

lemma iplus_Pos_comm:
 (∀m.∀y:int.iplus (Pos m) y=iplus y (Pos m)).
 #m elim m
 [ #y change with (y = ?) >iplus_neutral_r //
 | #n #II #y change with (iS (iplus (Pos n) y) = ?) >II >(iplus_iS y (Pos n)) // ]
qed.

lemma iplus_Neg_comm:
 (∀m.∀y:int.iplus (Neg m) y=iplus y (Neg m)).
 #m elim m
 [ #y change with (iP y = ?) >(iplus_iP y (Pos O)) >iplus_neutral_r //
 | #n #II #y change with (iP (iplus (Neg n) y) = ?) >II >(iplus_iP y (Neg n)) // ]
qed.

lemma iplus_comm: commutative … iplus.
 * #m //
qed.

lemma iplus_neutral: ∀z. iplus iO z = z.
 //
qed.

lemma disj1: ∀z. iS z ≠ z.
 * #n normalize [% #H destruct @(absurd ? e0) // ] cases n normalize
 [|#x] % #abs destruct @(absurd ? e0) //
qed.

lemma disj2: ∀z. iP z ≠ iS z.
 ** normalize [2,4: #x] % #abs destruct @(absurd ? e0) /2/
qed.

include "z_axioms.ma".

definition Z_impl : Z_axioms ≝
 mk_Z_axioms int iO iS iP iS_iP iP_iS iplus iplus_iP iplus_iS iplus_assoc
  iplus_comm iplus_neutral disj1 disj2.
