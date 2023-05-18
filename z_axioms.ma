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

include "basics/relations.ma".

record Z_axioms : Type[1] ≝
 { x_int : Type[0]
 ; x_iO : x_int
 ; x_iS: x_int → x_int
 ; x_iP: x_int → x_int
 ; x_iS_iP: ∀z. x_iS (x_iP z) = z
 ; x_iP_iS: ∀z. x_iP (x_iS z) = z
 ; x_iplus: x_int → x_int → x_int
 ; x_iplus_iP: ∀z1,z2. x_iplus z1 (x_iP z2) = x_iP (x_iplus z1 z2)
 ; x_iplus_iS: ∀z1,z2. x_iplus z1 (x_iS z2) = x_iS (x_iplus z1 z2)
 ; x_iplus_assoc: associative … x_iplus
 ; x_iplus_comm: commutative … x_iplus
 ; x_iplus_neutral: ∀z. x_iplus x_iO z = z
 ; x_disj1: ∀z. x_iS z ≠ z
 ; x_disj2: ∀z. x_iP z ≠ x_iS z
 }.

axiom int : Type[0].
axiom iO : int.
axiom iS: int → int.
axiom iP: int → int.
axiom iS_iP: ∀z. iS (iP z) = z.
axiom iP_iS: ∀z. iP (iS z) = z.
axiom iplus: int → int → int.
axiom iplus_iP: ∀z1,z2. iplus z1 (iP z2) = iP (iplus z1 z2).
axiom iplus_iS: ∀z1,z2. iplus z1 (iS z2) = iS (iplus z1 z2).
axiom iplus_assoc: associative … iplus.
axiom iplus_comm: commutative … iplus.
axiom iplus_neutral: ∀z. iplus iO z = z.
axiom disj1: ∀z. iS z ≠ z.
axiom disj2: ∀z. iP z ≠ iS z.

definition axioms_ok : Z_axioms ≝ 
 mk_Z_axioms int iO iS iP iS_iP iP_iS
  iplus iplus_iP iplus_iS iplus_assoc iplus_comm iplus_neutral disj1 disj2.
