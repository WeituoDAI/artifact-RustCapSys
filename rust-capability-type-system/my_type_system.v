From lrust.lang Require Export notation.
From Stdlib Require Import PropExtensionalityFacts.
Inductive lft : Type :=
| static 
| const : positive -> lft.




Definition elctx_elt : Type := lft * lft.
Definition llctx_elt : Type := lft * (list lft).

Notation elctx := (list elctx_elt).
Notation llctx := (list llctx_elt).

Notation "κ1 ⊑ₑ κ2" := (@pair lft lft κ1 κ2) (at level 70).
Notation "κ ⊑ₗ κl" := (@pair lft (list lft) κ κl) (at level 70).


Inductive type :Type :=
| bool 
| int
| own_ptr : nat -> type -> type
| uniq_bor : lft -> type -> type
| shr_bor : lft -> type -> type
| uninit : nat -> type
| sum : list type -> type
| product2 : type -> type -> type
| fn : elctx -> list type -> type -> type
| unit0
(* | rec : type -> type -> type *)
.


Definition product := foldr product2 unit0.
Definition unit := product [].
Notation Π := product.

Axiom product2_unit0 : forall ty1, ty1 = (product2 ty1 unit0).

Fixpoint size (ty : type) {struct ty} : nat :=
match ty with
| bool => 1
| int => 1
| own_ptr _ _ => 1
| uniq_bor _ _ => 1
| shr_bor _ _ => 1
| uninit n => n
| sum tyl => S (max_list_with size tyl)
| product2 ty1 ty2 => (size ty1) + (size ty2)
| fn E tyl ty => size ty
| unit0 => 0
end.

(*Compute (size(Π [int;int;uninit 3])).*)


Definition path := expr.

Inductive tctx_elt : Type :=
| TCtx_hasty (p : path) (ty : type)
| TCtx_blocked (p : path) (κ : lft) (ty : type).

Notation tctx := (list tctx_elt).

Record cctx_elt : Type :=
    CCtx_iscont { cctxe_k : val; cctxe_L : llctx;
                  cctxe_n : nat; cctxe_T : list val → tctx }.

Notation cctx := (list cctx_elt).
Notation "k ◁cont( L , n , T )" := (CCtx_iscont k L n T)
  (at level 70, format "k  ◁cont( L , n , T )").

Notation "p ◁ ty" := (TCtx_hasty p ty%list) (at level 70).
Notation "p ◁{ κ } ty" := (TCtx_blocked p κ ty)
   (at level 70, format "p  ◁{ κ }  ty").
Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") .
Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }"). 


Inductive wr : Type :=
 | Read'
 | Write'.

Inductive safe_copy : type -> Prop:= 
 | Copy_unit0 : safe_copy unit0
 | Copy_bool : safe_copy bool 
 | Copy_int : safe_copy int
 | Copy_uninit : forall n , safe_copy (uninit n)
 | Copy_shr: forall κ ty, safe_copy (shr_bor κ ty)
 | Copy_sum: forall (tyl : list type), (forall ty, In ty tyl -> safe_copy ty) ->
            safe_copy (sum tyl)
 | Copy_product2 : forall ty1 ty2, safe_copy ty1 ->
                                 safe_copy ty2 ->
                                 safe_copy (product2 ty1 ty2)
 | Copy_fn : forall E tyl ty, 
             safe_copy (fn E tyl ty).


Lemma product_copy tys : Forall safe_copy tys -> safe_copy (product tys).
Proof.
  intros.
  unfold product.
  induction tys.
  simpl. eapply Copy_unit0.
  simpl.
  eapply Forall_cons in H.
  destruct H.
  eapply Copy_product2.
  apply H.
  eapply IHtys in H0.
  apply H0.
Qed.

Fixpoint safe_copyc (T:tctx) : Prop :=
match T with
| nil => safe_copy unit0
| t :: tls' => safe_copyc tls' /\ match t with
               | p' ◁ ty => safe_copy ty
               | p' ◁{ κ } ty => safe_copy ty 
               end
end  
.


Inductive safe_sync : type -> Prop :=
 | unit0_sync : safe_sync unit0
 | bool_sync : safe_sync bool
 | sync_sync : safe_sync int
 | uninit_sync : forall n , safe_sync (uninit n)
 | own_sync : forall n ty ,
                  safe_sync ty ->
                  safe_sync (own_ptr n ty)
 | uniq_sync : forall κ ty ,
                  safe_sync ty -> 
                  safe_sync (uniq_bor κ ty)
 | shr_sync : forall κ ty ,
                  safe_sync ty -> 
                  safe_sync (shr_bor κ ty)
 | sum_sync : forall (tyl : list type) ,
                  Forall safe_sync tyl ->
                  safe_sync (sum tyl)
 | product2_sync : forall ty1 ty2, 
                  safe_sync ty1 -> 
                  safe_sync ty2 ->
                  safe_sync (product2 ty1 ty2)
 | fn_sync : forall E tyl ty, 
             safe_sync (fn E tyl ty).

Lemma product_sync tys : Forall safe_sync tys -> safe_sync (product tys).
Proof.
  intros.
  unfold product.
  induction tys.
  simpl. eapply unit0_sync.
  simpl.
  eapply Forall_cons in H.
  destruct H.
  eapply product2_sync.
  apply H.
  eapply IHtys in H0.
  apply H0.
Qed.


Inductive safe_send : type -> Prop :=
 | unit0_send : safe_send unit0
 | bool_send : safe_send bool
 | int_send : safe_send int
 | uninit_send : forall n , safe_send (uninit n)
 | own_send : forall n ty ,
                  safe_send ty ->
                  safe_send (own_ptr n ty)
 | uniq_send : forall κ ty ,
                  safe_send ty -> 
                  safe_send (uniq_bor κ ty)
 | shr_send : forall κ ty ,
                  safe_sync ty ->
                  safe_send (shr_bor κ ty)
 | sum_send : forall (tyl : list type) ,
                  Forall safe_send tyl ->
                  safe_send (sum tyl)
 | product2_send : forall ty1 ty2 ,
                   safe_send ty1 -> 
                   safe_send ty2 -> 
                   safe_send (product2 ty1 ty2)
 | fn_send : forall E tyl ty, 
             safe_send (fn E tyl ty)
.

Lemma product_send tys : Forall safe_send tys -> safe_send (product tys).
Proof.
  intros.
  unfold product.
  induction tys.
  simpl. eapply unit0_send.
  simpl.
  eapply Forall_cons in H.
  destruct H.
  eapply product2_send.
  apply H.
  eapply IHtys in H0.
  apply H0.
Qed.

Fixpoint safe_sendc (T:tctx) : Prop :=
match T with
| nil => safe_send unit0
| t :: tls' => safe_sendc tls' /\ match t with
               | p' ◁ ty => safe_send ty
               | p' ◁{ κ } ty => safe_send ty 
               end
end  
.

Inductive incl :=
 | linl_l
 | linl_e.

Inductive safe_lifetime_lincl: elctx -> llctx -> lft -> lft -> Prop :=
 | lincl_refl_safe : forall E L (κ:lft) ,
   (*LINCL_REFL*)     safe_lifetime_lincl E L κ κ
 | lctx_lft_incl_static_safe : forall E L κ , 
   (*LINCL_STATIC*)   safe_lifetime_lincl E L κ static
 | lctx_lft_incl_local_safe: forall E (L:llctx) (κ κ':lft) (κs:list lft) ,
   (*LINCL_LOCAL*)    In (pair κ κs) L → 
                      In κ' κs → 
                      safe_lifetime_lincl E L κ κ'
 | lctx_lft_incl_local_trans_safe: forall E L κ κ' κ'' κs ,
    (*LINCL_TRANS*)    In (pair κ κs) L → 
                       In κ' κs → 
                       safe_lifetime_lincl E L κ' κ'' → 
                       safe_lifetime_lincl E L κ κ''
 | lctx_lft_incl_external_safe: forall E L κ κ' , 
    (*LINCL_EXTERN*)   In (pair κ κ') E → 
                       safe_lifetime_lincl E L κ κ'
 | lctx_lft_incl_external_trans_safe: forall E L κ κ' κ'' ,
                       In (pair κ κ') E → 
                       safe_lifetime_lincl E L κ' κ'' → 
                       safe_lifetime_lincl E L κ κ''.

Inductive safe_lifetime_lalive: elctx -> llctx -> lft -> Prop :=
 | lctx_lft_alive_static_safe : forall E L , 
   (*LALIVE_STATIC*)  safe_lifetime_lalive E L static
 | lctx_lft_alive_local_safe : forall E L κ κs ,
    (*LALIVE_LOCAL*)   In (pair κ κs) L → 
                       (forall κ', (In κ κs) ->
                          safe_lifetime_lalive E L κ') ->
                       safe_lifetime_lalive E L κ
 | lctx_lft_alive_incl : forall E L κ κ',
    (*LALIVE_INVL*)     safe_lifetime_lalive E L κ → 
                       safe_lifetime_lincl E L κ κ' → 
                       safe_lifetime_lalive  E L κ'.

Inductive safe_elctx_sat : elctx -> llctx -> elctx -> Prop :=
  | elctx_sat_nil :    forall E L , 
    (*ESAT-INCL*)      safe_elctx_sat E L []
  | elctx_sat_lft_incl : forall E L E' κ κ' ,
    (*ESAT-INCL*)      safe_lifetime_lincl E L κ κ'-> 
                       safe_elctx_sat E L E' -> 
                       safe_elctx_sat E L ((κ ⊑ₑ κ') :: E')
.

Inductive safe_subtyping : elctx -> llctx -> type -> type -> Prop := 
 | shr_mono : forall E L ty1 ty2 κ1 κ2,
 (*T_BOR_SHR*)     safe_lifetime_lincl E L κ2 κ1 ->  
 (*T_BOR_LFT_SHR*) safe_subtyping E L ty1 ty2 ->
                   safe_subtyping E L (shr_bor κ1 ty1) (shr_bor κ2 ty2)
 | uniq_mono_lft : forall E L ty1  κ1 κ2,
                   safe_lifetime_lincl E L κ2 κ1 ->  
 (*T_BOR_LFT_MUT*) 
                   safe_subtyping E L (uniq_bor κ1 ty1) (uniq_bor κ2 ty1)
 | uniq_mono_mut : forall E L ty1 ty2 κ1 ,
 (*T_BOR_MUT*)     safe_subtyping E L ty1 ty2 ->
                   safe_subtyping E L ty2 ty1->
                   safe_subtyping E L (uniq_bor κ1 ty1) (uniq_bor κ1 ty2)
 (*-------T-REC-UNFOLD ------*)
 | own_mono : forall E L ty1 ty2 n,
 (*T_OWN*)         safe_subtyping E L ty1 ty2 ->
                   safe_subtyping E L (own_ptr n ty1) (own_ptr n ty2)
 | t_refl : forall E L ty1,
 (*T_REFL*)        safe_subtyping E L ty1 ty1
 | t_trans : forall E L ty1 ty2 ty3,
 (*T_TRANS*)       safe_subtyping E L ty1 ty2 ->
                   safe_subtyping E L ty2 ty3 ->
                   safe_subtyping E L ty1 ty3
 | uninit_product_subtype_cons_r : forall E L (n:nat) ty tyl,
 (*T_UNINIT_PROD*)                  size ty ≤ n →
                   safe_subtyping E L (uninit (size ty)) ty →
                   safe_subtyping E L (uninit (n-(size ty))) (Π tyl) →
                   safe_subtyping E L (uninit n) (Π(ty :: tyl))
 (*------T-REC------*)
 | product2_mono : forall E L ty11 ty12 ty21 ty22,
                   safe_subtyping E L ty11 ty12 ->
                   safe_subtyping E L ty21 ty22 ->
                   safe_subtyping E L (product2 ty11 ty21) (product2 ty12 ty22)
(*  | product_momo' : forall E L tyl1 tyl2,
                   Forall2 (safe_subtyping E L) tyl1 tyl2 ->
                   safe_subtyping E L (product tyl1) (product tyl2) *)
 | sum_mono' : forall E L tyl1 tyl2,
                   Forall2 (safe_subtyping E L) tyl1 tyl2 ->
                   safe_subtyping E L (sum tyl1) (sum tyl2)
.

From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Classical.

Lemma uniq_mono : forall E L ty1 ty2 κ1 κ2,
 (*T_BOR_MUT*)     safe_lifetime_lincl E L κ2 κ1 ->  
 (*T_BOR_LFT_MUT*) safe_subtyping E L ty1 ty2 ->
                   safe_subtyping E L ty2 ty1->
                   safe_subtyping E L (uniq_bor κ1 ty1) (uniq_bor κ2 ty2).
Proof.
  intros.
  eapply t_trans.
  instantiate(1:= (&uniq{κ2} ty1)).
  eapply uniq_mono_lft. auto.
  eapply uniq_mono_mut; auto.
Qed.


Ltac tryfalse :=
try solve [congruence | discriminate | assumption].

Lemma product_momo' : forall E L tyl1 tyl2,
                   Forall2 (safe_subtyping E L) tyl1 tyl2 ->
                   safe_subtyping E L (product tyl1) (product tyl2).
Proof.
  intros E L tyl1.
  induction tyl1. intros. eapply Forall2_nil_inv_l in H; tryfalse.
  subst. eapply t_refl.
  induction tyl2. intros. eapply Forall2_nil_inv_r in H. subst. rewrite H. eapply t_refl.
  intros.
  simpl. eapply product2_mono. eapply Forall2_cons_1 in H. destruct H. eauto.
  eapply Forall2_cons_1 in H. destruct H. eapply IHtyl1 in H0. auto.
Qed.

Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E)
  (at level 50, left associativity).

Fixpoint hasty_ptr_offsets (p : path) (ptr: type → type) tyl (off : nat) : tctx :=
  match tyl with
  | [] => []
  | ty :: tyl =>
    (p +ₗ #off ◁ ptr ty) :: hasty_ptr_offsets p ptr tyl (off + (my_type_system.size ty))
  end.

Inductive safe_tctx_incl : elctx -> llctx -> tctx -> tctx -> Prop :=
 | subtype_tctx_incl : forall E L p ty1 ty2,
   (*C_SUBTYPE*)        safe_subtyping E L ty1 ty2 ->
                        safe_tctx_incl E L [p ◁ ty1] [p ◁ ty2]
 | copy_tctx_incl : forall E L p ty,
   (*C_COPY*)           safe_copy ty ->
                        safe_tctx_incl E L [p ◁ ty] [p ◁ ty; p ◁ ty]
 | contains_tctx_incl : forall E L T1 T2,
   (*C_WEAKEN?*)        T1 ⊆+ T2 ->
                        safe_tctx_incl E L T2 T1
(*  | tctx_split_own_prod : forall E L n tyl p ,
   (*C_SPLIT_OWM*)      safe_tctx_incl E L [p ◁ own_ptr n $ product tyl] (hasty_ptr_offsets p (own_ptr n) tyl 0)
 | tctx_merge_own_prod : forall E L n tyl ,
   (*C_SPLIT_OWM*)      tyl ≠ [] ->
                        forall p, safe_tctx_incl E L (hasty_ptr_offsets p (own_ptr n) tyl 0)
                   [p ◁ own_ptr n $ product tyl] *)
 | tctx_share_type :  forall E L p κ ty ,
   (*C_SHARE*)          safe_lifetime_lalive E L κ -> 
                        safe_tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &shr{κ}ty]
 | tctx_borrow_type : forall E L p ty n κ , 
   (*C_BORROW*)         safe_tctx_incl E L [p ◁ own_ptr n ty] [p ◁ &uniq{κ}ty; p ◁{κ} own_ptr n ty]
 | tctx_reborrow_uniq : forall E L p ty κ κ' ,
   (*C_REBORROW*)       safe_lifetime_lincl E L κ' κ ->
                        safe_tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &uniq{κ'}ty; p ◁{κ'} &uniq{κ}ty]
 | tctx_reborrow_shr : forall E L p ty κ κ' ,
   (*C_REBORROW*)       safe_lifetime_lincl E L κ' κ →
                        safe_tctx_incl E L [p ◁ &shr{κ}ty] [p ◁ &shr{κ'}ty; p ◁{κ} &shr{κ}ty]
 | tctx_incl_frame_l : forall E L T T1 T2 ,
   (*C_FRAME*)          safe_tctx_incl E L T1 T2 ->
                        safe_tctx_incl E L (T++T1) (T++T2)
 | tctx_incl_frame_r : forall E L T T1 T2 ,
   (*C_FRAME*)          safe_tctx_incl E L T1 T2 ->
                        safe_tctx_incl E L (T1++T) (T2++T)
(*  | tctx_split_uniq_prod : forall E L κ tyl p ,
   (*C_SPLIT_BOR*)      safe_tctx_incl E L [p ◁ &uniq{κ}(product tyl)]
                  (hasty_ptr_offsets p (uniq_bor κ) tyl 0)
 | tctx_merge_uniq_prod : forall E L κ tyl ,
   (*C_SPLIT_BOR*)       tyl ≠ [] ->
                         forall p, safe_tctx_incl E L (hasty_ptr_offsets p (uniq_bor κ) tyl 0)
                   [p ◁ &uniq{κ}(product tyl)]
 | tctx_split_shr_prod : forall E L κ tyl p ,
   (*C_SPLIT_BOR*)      safe_tctx_incl E L [p ◁ &shr{κ}(product tyl)]
                  (hasty_ptr_offsets p (shr_bor κ) tyl 0)
 | tctx_merge_shr_prod : forall E L κ tyl ,
   (*C_SPLIT_BOR*)       tyl ≠ [] ->
                         forall p, safe_tctx_incl E L (hasty_ptr_offsets p (shr_bor κ) tyl 0)
                   [p ◁ &shr{κ}(product tyl)] *)
 | tctx_incl_tran : forall E L T1 T2 T3,
                    safe_tctx_incl E L T1 T2 ->
                    safe_tctx_incl E L T2 T3 ->
                    safe_tctx_incl E L T1 T3
.

Definition safe_tctx_extract_ctx E L T T1 T2 : Prop :=
    safe_tctx_incl E L T1 (T++T2).

Definition safe_tctx_extract_hasty E L p ty T T' : Prop :=
    safe_tctx_incl E L T ((p ◁ ty)::T').

Inductive UnblockTctx : lft -> tctx -> tctx -> Prop :=
 | unblock_tctx_cons_unblock : forall T1 T2 p κ ty ,
   (*TUNBLOCK_UNNLOCK*) UnblockTctx κ T1 T2 ->
                        UnblockTctx κ ((p ◁{κ} ty)::T1) ((p ◁ ty)::T2)
 | unblock_tctx_cons : forall κ T1 T2 x ,
   (*TUNBLOCK_SKIP*)   UnblockTctx κ T1 T2 ->
   (*TUNBLOCK_HASTY*)  UnblockTctx κ (x::T1) (x::T2)
 | unblock_tctx_nil : forall κ,
   (*TUNBLOCK_EMPTY*) UnblockTctx κ [] []
.

Lemma copy_elem_of_tctx_incl : forall E L T p ty, 
              safe_copy ty ->
              p ◁ ty ∈ T ->
              safe_tctx_incl E L T ((p ◁ ty) :: T).
Proof.
  intros.
  generalize dependent H0.
  remember (p ◁ ty). induction 1 as [|???? IH]; subst.
   - assert(((p ◁ ty) :: l) = (((p ◁ ty)::nil) ++ l))by tauto.
     assert(((p ◁ ty) :: (p ◁ ty) :: l) = (((p ◁ ty) :: (p ◁ ty) :: nil) ++ l)) by tauto.     
     rewrite H1. rewrite H0.
     apply tctx_incl_frame_r.
     apply copy_tctx_incl. auto.
   - assert((y :: l) = ((y::nil)++l)) by tauto.
     assert(((p ◁ ty) :: y :: l) = (((p ◁ ty) :: y :: nil) ++ l)) by tauto.
     rewrite H2. rewrite H1. 
     eapply tctx_incl_tran.
     apply tctx_incl_frame_l, IH. auto.
     apply contains_tctx_incl, submseteq_swap. 
Qed.

Inductive safe_cctx_incl : elctx -> cctx -> cctx -> Prop :=
  | incl_cctx_incl : forall E C1 C2 ,
                     C1 ⊆ C2 ->
                     safe_cctx_incl E C2 C1
  | cctx_incl_cons : forall E k L n (T1 T2 : list val → tctx) C1 C2,
                     safe_cctx_incl E C1 C2 -> 
                     (∀ args, safe_tctx_incl E L (T2 args) (T1 args)) →
                     safe_cctx_incl E (k ◁cont(L, n , T1) :: C1) (k ◁cont(L, n, T2) :: C2).

Inductive safe_wr :  wr ->  elctx -> llctx -> type -> type -> type -> Prop :=
 | write_own_safe : forall E L n ty ty',
   (*TWRITE_OWN*)   size ty = size ty' ->
                    safe_wr Write' E L (own_ptr n ty') ty (own_ptr n ty)
 | read_own_copy_safe :  forall ty E L n, 
   (*TREAD-OWN-COPY*) safe_copy ty ->
                      safe_wr Read' E L (own_ptr n ty) ty (own_ptr n ty)
 | read_own_move_safe : forall E L ty n ,
   (*TREAD-OWN-MOVE*) safe_wr Read' E L (own_ptr n ty) ty (own_ptr n $ uninit (size ty))
 | read_shr :         forall E L κ ty ,
   (*TREAD-BOR*)      safe_copy ty -> 
                      safe_lifetime_lalive E L κ -> 
                      safe_wr Read' E L (shr_bor κ ty) ty (shr_bor κ ty)
 | read_uniq :        forall E L κ ty ,
   (*TREAD-BOR*)      safe_copy ty -> 
                      safe_lifetime_lalive E L κ -> 
                      safe_wr Read' E L (uniq_bor κ ty) ty (uniq_bor κ ty)
 | write_uniq :       forall E L κ ty ,
   (*TWRITE-BOR*)     safe_lifetime_lalive E L κ -> 
                      safe_wr Write' E L (uniq_bor κ ty) ty (uniq_bor κ ty). 

(* Inductive safe_w : elctx -> llctx -> type -> type -> type -> Prop :=
 | write_own_safe : forall E L n ty ty',
   (*TWRITE_OWN*)   size ty = size ty' ->
                    safe_w E L (own_ptr n ty') ty (own_ptr n ty)
 | write_uniq :       forall E L κ ty ,
   (*TWRITE-BOR*)     safe_lifetime_lalive E L κ -> 
                      safe_w E L (uniq_bor κ ty) ty (uniq_bor κ ty).

Inductive safe_r : elctx -> llctx -> type -> type -> type -> Prop :=
 | read_own_copy_safe :  forall ty E L n, 
   (*TREAD-OWN-COPY*) safe_copy ty ->
                      safe_r E L (own_ptr n ty) ty (own_ptr n ty)
 | read_own_move_safe : forall E L ty n ,
   (*TREAD-OWN-MOVE*) safe_r E L (own_ptr n ty) ty (own_ptr n $ uninit (size ty))
 | read_shr :         forall E L κ ty ,
   (*TREAD-BOR*)      safe_copy ty -> 
                      safe_lifetime_lalive E L κ -> 
                      safe_r E L (shr_bor κ ty) ty (shr_bor κ ty)
 | read_uniq :        forall E L κ ty ,
   (*TREAD-BOR*)      safe_copy ty -> 
                      safe_lifetime_lalive E L κ -> 
                      safe_r E L (uniq_bor κ ty) ty (uniq_bor κ ty). *)


(* 
From lrust.lang Require Export notation. *)
From lrust.lang Require Import heap proofmode memcpy.
(* From iris.prelude Require Import options. *)

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".
(* Local Open Scope expr_scope.   *)

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #☠
    else Free "n" "loc".

Definition memcpy : val :=
  rec: "memcpy" ["dst";"len";"src"] :=
    if: "len" ≤ #0 then #☠
    else "dst" <- !"src";;
         "memcpy" ["dst" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].

Notation "e1 <-{ n } ! e2" :=
  (memcpy (@cons expr e1%E
          (@cons expr (Lit n)
          (@cons expr e2%E nil))))
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") .

Notation "e1 <-{ n ',Σ' i } ! e2" :=
  (e1 <-{Σ i} () ;; e1+ₗ#1 <-{n} !e2)%E
  (at level 80, n, i at next level,
   format "e1  <-{ n ,Σ  i }  ! e2").


Set Warnings "-notation-overridden".

Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E)
  (at level 50, left associativity) .
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E)
  (at level 70) .
Notation "! e" := (Read Na1Ord e%E) (at level 9, format "! e").
Notation "e1 '<-{Σ' i } '()'" := (e1 <- #i)%E
  (only parsing, at level 80).
Notation "e1 '<-{Σ' i } e2" := (e1 <-{Σ i} () ;; e1+ₗ#1 <- e2)%E
  (at level 80, format "e1 <-{Σ  i }  e2") .

Notation "'let:' x := e1 'in' e2" :=
  ((Lam (@cons binder x%binder nil) e2%E) (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150).
Notation "'letcont:' k xl := e1 'in' e2" :=
  ((Lam (@cons binder k%binder nil) e2%E) [Rec k%binder xl%binder e1%E])
  (at level 102, k, xl at level 1, e1, e2 at level 150).
Notation "e1 ;; e2" := (let: <> := e1 in e2)%E
  (at level 100, e2 at level 200, format "e1  ;;  e2").
Notation "'case:' e0 'of' el" := (Case e0%E el%E)
  (at level 102, e0, el at level 150).
Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E)
  (at level 50, left associativity).
Notation "'call:' f args → k" := (f (@cons expr (λ: ["_r"], k ["_r"]) args))%E
  (only parsing, at level 102, f, args, k at level 1).
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (only parsing, at level 102, e1, e2, e3 at level 150).

(* Notation "'rec:' f xl := e" := (locked (RecV f%binder xl%binder e%E))
  (at level 102, f, xl at level 1, e at level 200).
Notation "'fnrec:' f xl := e" := (rec: f (BNamed "return"::xl) := e)%V
  (at level 102, f, xl at level 1, e at level 200).
Notation "'fn:' xl := e" := (fnrec: <> xl := e)%V
  (at level 102, xl at level 1, e at level 200).  *)

Definition box ty := own_ptr (my_type_system.size ty) ty.

(*  Lemma a: forall argsb e a, ((locked (RecV <>%binder (BNamed "return"::argsb)%binder e%E))) = a.
intros.
Check (fn: argsb := e).
  destruct (Rec <>%binder (BNamed "return"::argsb)%binder e%E). (fn: argsb := e).
  simpl. 

(locked (RecV <>%binder (BNamed "return"::argsb)%binder e%E))
 *)
                    
Inductive safe_type_Ins : elctx -> llctx -> tctx -> expr -> (val -> tctx) -> Prop :=
 | type_int_instr : forall E L z , 
   (*S-NUM*)                safe_type_Ins E L [] (#z) (λ v : val, [v ◁ int])
 | type_plus_instr : forall E L p1 p2 ,
                     (* forall T,
                       safe_type_Ins E L T p1 (λ v : val, [v ◁ int]) ->
                       safe_type_Ins E L T p2 (λ v : val, [v ◁ int]) ->  *)
   (*S-NAT-OP*)      safe_type_Ins E L [p1 ◁ int; p2 ◁ int] (BinOp PlusOp p1 p2) (λ v : val, [TCtx_hasty v int])
 | type_minus_instr : forall E L p1 p2 ,
                     (* forall T,
                       safe_type_Ins E L T p1 (λ v : val, [v ◁ int]) ->
                       safe_type_Ins E L T p2 (λ v : val, [v ◁ int]) ->  *)
   (*S-NAT-OP*)     safe_type_Ins E L [p1 ◁ int; p2 ◁ int] (p1 - p2) (λ v : val, [v ◁ int])
 | type_le_instr : forall E L p1 p2 ,
                     (* forall T,
                       safe_type_Ins E L T p1 (λ v : val, [v ◁ int]) -> 
                       safe_type_Ins E L T p2 (λ v : val, [v ◁ int]) ->  *)
   (*S-NAT-LEQ*)   safe_type_Ins E L [p1 ◁ int; p2 ◁ int] (p1 ≤ p2) (λ v : val, [v ◁ bool]) 
(*----- S-FN -----*)
 | type_fn : forall E L (argsb : list binder) ef e E' tyl ty T `{!Closed _ e} ,
                  safe_copyc T -> 
                  safe_sendc T ->
         (* Closed (<> :b: ("return" :: argsb)%binder +b+ []) e -> *)   
       IntoVal ef (fn: argsb := e) ->   
    length tyl = length argsb ->
    ∀ ϝ k (args : vec val (length argsb)),
        safe_type_fun (E')
                   [ϝ ⊑ₗ []]
                   [k ◁cont([ϝ ⊑ₗ []], 1 , λ v : list val, [(nth 0 v #1 :val) ◁ box ty])]
                   (zip_with (TCtx_hasty ∘ of_val) args
                             (box <$> tyl) ++ T)
                   (subst_v (BNamed "return" :: argsb) (k ::: args) e) (zip_with (TCtx_hasty ∘ of_val) args
                             (box <$> tyl) ++ T) ->
       safe_type_Ins E L T ef (λ v : val, [v ◁ (fn E' tyl ty)])
 | type_path_instr : forall E L p ty ,
   (*S-PATH*)        safe_type_Ins E L [p ◁ ty] p (λ v : val, [v ◁ ty])
 | type_new_instr_type : forall n E L,
   (*S-NEW*)             (0 ≤ n)%Z ->
                         let n' := Z.to_nat n in
                          safe_type_Ins E L [] (new [ #n ]%E) (λ v : val,[v ◁ own_ptr n' (uninit n')])
 | type_delete_instr : forall E L ty n p ,
   (*S-DELETE*)        Z.of_nat (my_type_system.size ty) = n ->
                       safe_type_Ins E L [p ◁ own_ptr (my_type_system.size ty) ty] (delete [ #n; p])%E (λ _, []) 
 | type_deref_instr_type : forall E L ty ty1 ty1' p, 
   (*S-DEREF*)         my_type_system.size ty = 1%nat ->
                       safe_wr Read' E L ty1 ty ty1' ->
                       safe_type_Ins E L [p ◁ ty1] (!p) (λ v, [p ◁ ty1'; v ◁ ty])
 | type_assign_instr_type : forall E L ty1 ty ty1' p1 p2 , 
   (*S-ASSGN*)         safe_wr Write' E L ty1 ty ty1' ->
                       safe_type_Ins E L [p1 ◁ ty1; p2 ◁ ty] (Write Na1Ord p1 p2) (λ _, [p1 ◁ ty1'])
 | type_sum_assign_instr : forall E L (i : nat) ty1 tyl ty ty2 p1 p2 ,
   (*S-SUM-ASSGN*)         tyl !! i = Some ty ->
                           safe_wr Write' E L ty1 (sum tyl) ty2 ->
                           safe_type_Ins E L [p1 ◁ ty1; p2 ◁ ty] (p1 <-{Σ i} p2) (λ _, [p1 ◁ ty2]) 
 | type_bool_instr_safe : forall E L(b : Datatypes.bool) , 
                               safe_type_Ins E L [] #b (λ v : val, [v ◁ bool])
   (*S_TRUE S_FALSE*)
 | type_deref_uniq_own_instr_safe : forall E L κ p n ty ,
   (*S-DEREF-BOR_OWN*)          safe_lifetime_lalive E L κ ->
                                (* (forall T, safe_type_Ins E L T p (λ v : val, [v ◁ &uniq{κ}(own_ptr n ty)])) -> *)
                                safe_type_Ins E L [p ◁ &uniq{κ}(own_ptr n ty)] (!p) (λ v : val, [v ◁ (&uniq{κ} ty)])
 | type_deref_shr_own_instr_safe : forall E L κ p n ty ,
   (*S-DEREF-BOR_OWN*)         safe_lifetime_lalive E L κ ->
                              (*  (forall T, safe_type_Ins E L T p (λ v : val, [v ◁ &shr{κ}(own_ptr n ty)])) -> *)
                               safe_type_Ins E L [p ◁ &shr{κ}(own_ptr n ty)] (!p) (λ v : val, [v ◁ (&shr{κ} ty)])
 | type_deref_uniq_uniq_instr_safe : forall E L κ κ' p ty ,
   (*S_DEREF_BOR_MUT*)         safe_lifetime_lalive E L κ -> 
                               safe_lifetime_lincl E L κ κ' ->
                               (* (forall T, safe_type_Ins E L T p (λ v : val, [v ◁ &uniq{κ}(&uniq{κ'}ty)])) -> *)
                               safe_type_Ins E L [p ◁ &uniq{κ}(&uniq{κ'}ty)] (!p) (λ v : val, [v ◁ (&uniq{κ} ty)])
 | type_deref_shr_uniq_instr_safe : forall E L κ κ' p ty ,
   (*S_DEREF_BOR_MUT*)         safe_lifetime_lalive E L κ -> 
                               safe_lifetime_lincl E L κ κ'->
                             (*   (forall T, safe_type_Ins E L T p (λ v : val, [v ◁ &shr{κ}(&uniq{κ'}ty)])) -> *)
                               safe_type_Ins E L [p ◁ &shr{κ}(&uniq{κ'}ty)] (!p) (λ v : val, [v ◁ (&shr{κ}ty)])
 | type_sum_unit_instr : forall E L (i : nat) tyl ty1 ty2 p ,
   (*S-SUM_ASSGN-UNIT*)  tyl !! i = Some unit ->
                         safe_wr Write' E L ty1 (sum tyl) ty2 ->
                         (* (forall T, safe_type_Ins E L T p (λ v : val, [v ◁ ty1])) -> *)
                         safe_type_Ins E L [p ◁ ty1] (p <-{Σ i} ()) (λ _, [p ◁ ty2])
 | type_sum_memcpy_instr_safe : forall E L (i : nat) tyl ty1 ty1' ty2 ty2' ty p1 p2 ,
   (*S_SUM_MEMCPY*)            tyl !! i = Some ty →
                               safe_wr Write' E L ty1 (sum tyl) ty1' ->
                               safe_wr Read' E L ty2 ty ty2'->
                               (* (forall T, safe_type_Ins E L T p1 (λ v : val, [v ◁ ty1])) ->
                               (forall T, safe_type_Ins E L T p2 (λ v : val, [v ◁ ty2])) -> *)
                               safe_type_Ins E L [p1 ◁ ty1; p2 ◁ ty2]
                                    (p1 <-{(my_type_system.size ty),Σ i} !p2) (λ _, [p1 ◁ ty1'; p2 ◁ ty2'])
 | type_memcpy_instr_safe : forall E L ty ty1 ty1' ty2 ty2' (n : Z) p1 p2 ,
   (*S_MEMCPY*)                            Z.of_nat ((my_type_system.size ty)) = n →
                               safe_wr Write' E L ty1 ty ty1'->
                               safe_wr Read' E L ty2 ty ty2'->
                              (*  (exists T, safe_type_Ins E L T p1 (λ v : val, [v ◁ ty1])) ->
                               (exists T, safe_type_Ins E L T p2 (λ v : val, [v ◁ ty2])) -> *)
                               safe_type_Ins E L [p1 ◁ ty1; p2 ◁ ty2] (p1 <-{n} !p2)
                                    (λ _, [p1 ◁ ty1'; p2 ◁ ty2'])
 with safe_type_fun : elctx -> llctx -> cctx -> tctx -> expr -> tctx -> Prop :=
 | type_let_type : forall E L T T1 T2 T3 C xb e e', 
   (*F-LET*)           Closed (xb :b: []) e' →
                       safe_type_Ins  E L T1 e T2 →
                       (∀ v : val, (safe_type_fun E L C (T2 v ++ T) (subst' xb v e') (T3 v))) ->
                       ∀ v : val, safe_type_fun E L C (T1 ++ T) (let: xb := e in e') (T2 v ++ T) 
 | typed_body_mono : forall E L C1 C2 T1 T2 T3 e,
   (*F-CONSEQUEBCE*) safe_cctx_incl E C2 C1 ->
                     safe_tctx_incl E L T2 T1 ->
                     safe_type_fun E L C1 T1 e T3->
                     safe_type_fun E L C2 T2 e T1 
 | type_cont : forall argsb L1 (T' : list val  -> _) E L2 C T T2 T3 econt e2 kb,
   (*F_LETCONT*)     Closed (kb :b: argsb +b+ []) econt -> 
                     Closed (kb :b: []) e2 ->
                     (∀ k, safe_type_fun E L2 (k ◁cont(L1, (length argsb), T') :: C) T (subst' kb k e2)T2 )  ->
     (∀ k (args : vec val (length argsb)),
          safe_type_fun E L1 (k ◁cont(L1, (length argsb), T') :: C) (T' args)
                     (subst_v (kb::argsb) (k:::args) econt) T3) ->
                     safe_type_fun E L2 C T (letcont: kb argsb := econt in e2) T
 | type_jump args argsv : forall E L C T k T' ,
   (*F_JUMP*)        Forall2 (λ a av, to_val a = Some av ∨ a = of_val av) args argsv ->
                     k ◁cont(L, (length argsv), T') ∈ C ->
                     safe_tctx_incl E L T (T' (list_to_vec argsv)) ->
                     safe_type_fun E L C T (k args) T 
 | type_newlft : forall E L C T T2 κs e ,
   (*F_NWELFT*)  Closed [] e ->
                 (∀ κ, safe_type_fun E ((κ ⊑ₗ κs) :: L) C T e T2) ->
                 safe_type_fun E L C T (Newlft ;; e) T
 | type_endlft : forall E L C T1 T2 T3 κ κs e ,
   (*F_ENDLFT*)   Closed [] e -> 
                 UnblockTctx κ T1 T2 ->
                 safe_type_fun E L C T2 e T3-> 
                 safe_type_fun E ((κ ⊑ₗ κs) :: L) C T1 (Endlft ;; e) T2
 | type_case_uniq' : forall E L C T T1 T2 p κ tyl el ,
   (*F_CASE_BOR*)safe_lifetime_lalive E L κ ->
                 Forall2 (λ ty e,
                  (safe_type_fun E L C ((p +ₗ #1 ◁ &uniq{κ}ty) :: T) e T1) ∨
                  (safe_type_fun E L C ((p ◁ &uniq{κ}(sum tyl)) :: T) e T2)) tyl el ->
                 safe_type_fun E L C ((p ◁ &uniq{κ}(sum tyl)) :: T) (case: !p of el) ((p ◁ &uniq{κ}(sum tyl)) :: T)
 | type_case_shr' :forall E L C T T1 T2 p κ tyl el ,
   (*F_CASE_BOR*)safe_lifetime_lalive E L κ ->
                 Forall2 (λ ty e,
                  (safe_type_fun E L C ((p +ₗ #1 ◁ &shr{κ}ty) :: T) e T1) ∨
                  (safe_type_fun E L C ((p ◁ &shr{κ}(sum tyl)) :: T) e T2)) tyl el ->
                 safe_type_fun E L C ((p ◁ &shr{κ}(sum tyl)) :: T) (case: !p of el) ((p ◁ &shr{κ}(sum tyl)) :: T)
 | type_case_own' : forall E L C T T1 T2 p n tyl el ,
   (*F_CASE_OWN*) Forall2 (λ ty e,
                  (safe_type_fun E L C ((p +ₗ #0 ◁ own_ptr n (uninit 1)) :: (p +ₗ #1 ◁ own_ptr n ty) ::
         (p +ₗ #(S (my_type_system.size ty)) ◁
            own_ptr n (uninit (max_list_with my_type_system.size tyl - (my_type_system.size ty)))) :: T) e T1) ∨
      (safe_type_fun E L C ((p ◁ own_ptr n (sum tyl)) :: T) e T2))
      tyl el ->
    safe_type_fun E L C ((p ◁ own_ptr n (sum tyl)) :: T) (case: !p of el) ((p ◁ own_ptr n (sum tyl)) :: T)
 | type_call : forall  κs E L C T T' T'' p (ps : list path)
   (*F_CALL*)       E' tyl' ty' k ,
    p ◁ fn E' tyl' ty' ∈ T →
    Forall (safe_lifetime_lalive E L) κs →
    (∀ ϝ, safe_elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> κs) ++ E) L (E')) →
    safe_tctx_extract_ctx E L (zip_with TCtx_hasty ps
                                   (box <$> tyl')) T T' →
    k ◁cont(L, 1 ,T'') ∈ C →
    (∀ ret : val, safe_tctx_incl E L ((ret ◁ box ty')::T') (T'' [# ret]))  →
    ∀ ret : val, safe_type_fun E L C T (call: p ps → k) (( ret ◁ box ty')::T')
 | type_if E L C T T' T'' e1 e2 p:
    p ◁ bool ∈ T →
    safe_type_fun E L C T e1 T'->
    safe_type_fun E L C T e2 T''->
    safe_type_fun E L C T (if: p then e1 else e2) T
(*  | type_equivalize_lft : forall E L C T1 T2 κ1 κ2 e ,
    (∀ tid, lft_ctx -∗ κ1 ⊑ κ2 -∗ κ2 ⊑ κ1 -∗ tctx_interp tid T1 -∗ tctx_interp tid T2) →
    (⊢ typed_body E L C T2 e) →
    ⊢ typed_body E ((κ1 ⊑ₗ [κ2]) :: L) C T1 e *)
.


(* Lemma tets3: forall E L C v,
safe_type_fun E L C ["p"◁int ; "p'"◁int] (let: "a" := (new [ #1 ]%E) in  "a")
(((λ v : val, [v ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1))]) v) ++ ["p"◁int ; "p'"◁int])

.
intros.
(* change(((λ v0 : val, [v0 ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1))])
     v)) with ((λ v0 : val, [] ++ [v0 ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1))])
     v). *)
change(["p"◁int ; "p'"◁int]) with ([] ++ ["p"◁int;"p'"◁int]).
eapply type_let_type.
simpl. unfold Closed. simpl. auto.
eapply type_new_instr_type. *)

(* Lemma type_case_uniq E L C T T' p κ tyl el :
  tctx_extract_hasty E L p (&uniq{κ}(sum tyl)) T T' →
  lctx_lft_alive E L κ →
  Forall2 (λ ty e,
      (safe_type_fun E L C ((p +ₗ #1 ◁ &uniq{κ}ty) :: T') e) ∨
      (typed_body E L C ((p ◁ &uniq{κ}(sum tyl)) :: T') e)) tyl el →
     safe_type_fun E L C T (case: !p of el). *)


(* Local Open Scope expr_scope.
 
Inductive safe_type_fun : elctx -> llctx -> cctx -> tctx -> expr -> Prop :=
 | type_let_type : forall E L T T1 T2 C xb e e',
   (*F-LET*)           Closed (xb :b: []) e' →
                       safe_type_Ins  E L T1 e T2 →
                       ∀ v : val, safe_type_fun E L C (T2 v ++ T) (subst' xb v e') ->
                       safe_type_fun E L C (T1 ++ T) (let: xb := e in e')
 | typed_body_mono : forall E L C1 C2 T1 T2 e,
   (*F-CONSEQUEBCE*) safe_cctx_incl E C2 C1 ->
                     safe_tctx_incl E L T2 T1 ->
                     safe_type_fun E L C1 T1 e->
                     safe_type_fun E L C2 T2 e 
 | type_cont : forall argsb L1 (T' : vec val (length argsb) -> _) E L2 C T econt e2 kb,
   (*F_LETCONT*)     Closed (kb :b: argsb +b+ []) econt -> 
                     Closed (kb :b: []) e2 ->
                     (∀ k, safe_type_fun E L2 (k ◁cont(L1, T') :: C) T (subst' kb k e2)) ->
     (∀ k (args : vec val (length argsb)),
          safe_type_fun E L1 (k ◁cont(L1, T') :: C) (T' args)
                     (subst_v (kb::argsb) (k:::args) econt)) ->
                     safe_type_fun E L2 C T (letcont: kb argsb := econt in e2)
 | type_jump args argsv : forall E L C T k T' ,
   (*F_JUMP*)        Forall2 (λ a av, to_val a = Some av ∨ a = of_val av) args argsv ->
                     k ◁cont(L, T') ∈ C ->
                     safe_tctx_incl E L T (T' (list_to_vec argsv)) ->
                     safe_type_fun E L C T (k args)
 | type_newlft : forall E L C T κs e ,
   (*F_NWELFT*)  Closed [] e ->
                 (∀ κ, safe_type_fun E ((κ ⊑ₗ κs) :: L) C T e) ->
                 safe_type_fun E L C T (Newlft ;; e)
 | type_endlft : forall E L C T1 T2 κ κs e ,
   (*F_ENDLFT*)   Closed [] e -> 
                 UnblockTctx κ T1 T2 ->
                 safe_type_fun E L C T2 e -> 
                 safe_type_fun E ((κ ⊑ₗ κs) :: L) C T1 (Endlft ;; e)
 *)


(*   Lemma type_jump args argsv E L C T k T' :
    (* We use this rather complicated way to state that
         args = of_val <$> argsv, only because then solve_typing
         is able to prove it easily. *)
    Forall2 (λ a av, to_val a = Some av ∨ a = of_val av) args argsv →
    k ◁cont(L, T') ∈ C →
    tctx_incl E L T (T' (list_to_vec argsv)) →
    ⊢ typed_body E L C T (k args).

  |type_call' : forall E L (κs : list lft) T p (ps : list path) 
                   {A} (fp : A → fn_params (length ps)) (k : val) x ,
               safe_type (Forall (lctx_lft_alive E L) κs) →
    (∀ ϝ, elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> κs) ++ E) L ((fp x).(fp_E) ϝ)) →
    safe_type ( ⊢ typed_body E L [k ◁cont(L, λ v : vec _ 1, ((v!!!0%fin:val) ◁ box (fp x).(fp_ty)) :: T)]
               ((p ◁ fn fp) ::
                zip_with TCtx_hasty ps (box <$> vec_to_list (fp x).(fp_tys)) ++
                T)
               (call: p ps → k))  *)
(* . *)

(* Lemma test2:
forall E L C (x y temp ret : val),
safe_type_fun E L
  C
  [x ◁ own_ptr 1 int; y ◁ own_ptr 1 int]
  (let: "x'" := !x
   in let: "y'" := !y
      in let: "r" := new [ #2 ]
         in "r" +ₗ #0 <- "x'" ;; "r" +ₗ #1 <- "y'" ;; delete [ #1 ; x] ;; 
         delete [ #1 ; y] ;; ret ["r"])  ((λ v : val , [x ◁ own_ptr 1 int; v ◁ int]) temp ++ [ y ◁ own_ptr 1 int] )
  
.
Proof.
  intros.
  change ([x ◁ own_ptr 1 int; y ◁ own_ptr 1 int]) with ([x ◁ own_ptr 1 int] ++  [y ◁ own_ptr 1 int] ).
  eapply type_let_type.
  simpl. unfold Closed. simpl.
  2:{   eapply type_deref_instr_type.
        eauto.
        eapply read_own_copy_safe. eapply Copy_int.
  }
  


  2:{

     intros x'. simpl_subst.
     eapply typed_body_mono with (C1 := C).
     eapply incl_cctx_incl. auto. 
     eapply contains_tctx_incl.

     instantiate (1:= λ v : val , [ y ◁ own_ptr 1 int ; x ◁ own_ptr 1 int; v ◁ int] ).
     simpl.
     eapply Permutation_submseteq.

     rewrite Permutation_swap.
     eapply Permutation_skip.
     rewrite Permutation_swap.
     eapply Permutation_skip.
     eauto.
     simpl.
     instantiate (1:= ((λ v : val , [y ◁ own_ptr 1 int; v ◁ int]) temp ++ [ x ◁ own_ptr 1 int; x' ◁ int] )).
     change ([y ◁ own_ptr 1 int; x ◁ own_ptr 1 int; x' ◁ int]) with
        ([y ◁ own_ptr 1 int] ++ [ x ◁ own_ptr 1 int; x' ◁ int]).
       eapply type_let_type.
  simpl. unfold Closed. simpl.
 *)


Local Close Scope expr_scope.
Fixpoint path_not_in_tctx (p:path) (T:tctx):Prop:=
match T with
 | nil => True
 | t::h => match t with
           | p' ◁ ty => if (expr_beq p p') then (False) 
                                           else (True /\ path_not_in_tctx p h)
           | p' ◁{ κ } ty => if (expr_beq p p') then (False) 
                                           else (True /\ path_not_in_tctx p h)
           end 
end
.
 
Lemma expr_eq : forall e , expr_beq e e = true.
Proof.
    fix FIX 1. 
    destruct e as [| | | |? el1| | | | | |? el1|]; simpl; try done;
    rewrite ?andb_True ?bool_decide_eq_true ?FIX; auto.

    rewrite andb_true_r.
    apply andb_true_intro; split; apply bool_decide_eq_true; auto.
    rewrite <- andb_assoc.
    rewrite andb_true_l.
    rewrite andb_true_r.
    rewrite bool_decide_eq_true. auto.
    {
      rewrite andb_true_l.
      revert el1.
      fix FIX1 1.
      intros.
      induction el1. auto.
      rewrite IHel1. rewrite FIX. auto.
    }
    rewrite andb_true_r. rewrite bool_decide_eq_true. auto.
    rewrite andb_true_r. rewrite andb_true_r. rewrite bool_decide_eq_true. auto.
    rewrite andb_true_l.    
    induction el1. auto.
    rewrite IHel1. rewrite FIX. clear FIX. auto.
Qed.

Definition lft_beq (t : lft) (t' : lft) : Datatypes.bool :=
match t, t' with
| static, static => true
| my_type_system.const n, my_type_system.const n'=> bool_decide (n = n') 
| _, _ => false
end
.

Definition elctx_elt_beq (t t':elctx_elt): Datatypes.bool :=
  match t, t' with
  | (k1 , k2) , (k1' , k2') => lft_beq k1 k1' && lft_beq k2 k2'
  end.

Fixpoint elctx_beq (el el': elctx) : Datatypes.bool :=
  match el, el' with
  | [], [] => true
  | eh::eq, eh'::eq' => elctx_elt_beq eh eh' && elctx_beq eq eq'
  | _, _ => false
  end.

Fixpoint type_beq (t : type) (t' : type) : Datatypes.bool :=
  let fix type_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => type_beq eh eh' && type_list_beq eq eq'
    | _, _ => false
    end
  in
  match t, t' with
  | bool, bool => true
  | int, int => true
  | own_ptr n ty , own_ptr n' ty' => bool_decide (n = n') && type_beq ty ty'
  | uniq_bor k ty , uniq_bor k' ty' => lft_beq k k' && type_beq ty ty'
  | shr_bor k ty , shr_bor k' ty' => lft_beq k k' && type_beq ty ty'
  | uninit n , uninit n' => bool_decide (n = n') 
  | sum tyl, sum tyl' => type_list_beq tyl tyl'
  | product2 ty1 ty2 , product2 ty1' ty2' => type_beq ty1 ty1' && type_beq ty2 ty2'
  | fn C tyl ty , fn C' tyl' ty' => elctx_beq C C' && type_list_beq tyl tyl' && type_beq ty ty'
  | unit0 , unit0 => true
  | _, _ => false
end
.


Definition tctx_elt_beq (t : tctx_elt) (t' : tctx_elt) : Datatypes.bool :=
match t, t' with
| TCtx_hasty p ty, TCtx_hasty p' ty' => expr_beq p p' && type_beq ty ty'
| TCtx_blocked p k ty, TCtx_blocked p' k' ty' 
                    => expr_beq p p' && lft_beq k k' && type_beq ty ty'
| _ , _ => false
end
.

Lemma lft_beq_correct (e1 e2 : lft) : lft_beq e1 e2 ↔ e1 = e2.
Proof.
  intros.
  destruct e1; destruct e2; try done. naive_solver.
Qed.

Lemma elctx_elt_beq_correct (e1 e2 : elctx_elt) : elctx_elt_beq e1 e2 ↔ e1 = e2.
Proof.
  intros.
  
  destruct e1; destruct e2; try done. 
  split. intros.
  unfold elctx_elt_beq in H.
  eapply andb_True in H. destruct H.
  rewrite lft_beq_correct in H.
  rewrite lft_beq_correct in H0.
  subst;eauto.
  intros. injection H as eq ;subst.
  simpl.
  eapply andb_True. split.
  rewrite lft_beq_correct. eauto.
  rewrite lft_beq_correct. eauto.
Qed.

Lemma elctx_beq_correct (e1 e2 : elctx) : elctx_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e2. induction e1 as [|el1h el1q]; intros e2; destruct e2; try done.
  split.
  intros. 
  simpl in H. eapply andb_True in H. destruct H.
  rewrite elctx_elt_beq_correct in H. subst.
  change (e :: el1q = e :: e2) with ([e] ++ el1q = [e] ++ e2).
  eapply app_inv_head_iff. eapply IHel1q. eauto.
  intros. injection H as eq;subst.
  simpl. eapply andb_True. split.
  rewrite elctx_elt_beq_correct. auto.
  rewrite IHel1q. auto.
Qed.  

Lemma type_beq_correct (e1 e2 : type) : type_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2;  fix FIX 1; intros e1 e2. 
  revert e2. induction e1;
  destruct e2; simpl; try done.
  - clear FIX. split. intros.
    eapply andb_True in H. destruct H.
    rewrite bool_decide_spec in H. eapply IHe1 in H0.
    subst;eauto.
    intros.
    injection H as eq ;subst.
    eapply andb_True. split. eauto.
    eapply IHe1. eauto.
  - clear FIX. split. intros.
    eapply andb_True in H. destruct H.
    rewrite lft_beq_correct in H. eapply IHe1 in H0.
    subst;eauto.
    intros.
    injection H as eq ;subst.
    eapply andb_True. split. eapply lft_beq_correct. eauto.
    eapply IHe1. eauto.
  - clear FIX. split. intros.
    eapply andb_True in H. destruct H.
    rewrite lft_beq_correct in H. eapply IHe1 in H0.
    subst;eauto.
    intros.
    injection H as eq ;subst.
    eapply andb_True. split. eapply lft_beq_correct. eauto.
    eapply IHe1. eauto.
  - clear FIX. naive_solver.
  - (* revert l0. induction l; destruct l0.
    clear FIX. naive_solver.
    clear FIX. naive_solver.
    clear FIX. naive_solver.
    split. intros. 
    eapply andb_True in H. destruct H.
    rewrite FIX in H. subst.
  - *)
    match goal with |- context [?F l l0] => assert (F l l0 ↔ l = l0) end.
   { revert l0. induction l as [|lh lq]; intros l0; destruct l0; try done.
      specialize (FIX lh). naive_solver. }
    clear FIX. naive_solver.
  - clear FIX.
    split;intros.
    rewrite andb_True in H. destruct H.
    eapply IHe1_1 in H.
    eapply IHe1_2 in H0. subst.
    eauto.
    injection H as eq;subst.
    rewrite andb_True . split.
    eapply IHe1_1 . eauto.
    eapply IHe1_2 . eauto.
  - {
  assert((fix type_list_beq (el el' : list type) {struct el} :
     Datatypes.bool :=
   match el with
   | [] => match el' with
           | [] => true
           | _ :: _ => false
           end
   | eh :: eq =>
       match el' with
       | [] => false
       | eh' :: eq' =>
           type_beq eh eh' && type_list_beq eq eq'
       end
   end) l0 l2 ↔ l0 = l2).
  { revert l2. induction l0 as [|lh lq]; intros l2; destruct l2; try done.
      specialize (FIX lh). naive_solver. }
    clear FIX.
    split;intros.
    rewrite andb_True in H0. destruct H0.
    rewrite andb_True in H0. destruct H0.
    eapply IHe1 in H1.
    eapply elctx_beq_correct in H0. 
    eapply H in H2. subst.
    eauto.
    injection H0 as eq;subst.
    rewrite andb_True. split.
    rewrite andb_True. split.
    eapply elctx_beq_correct. auto.
    eapply H. auto.
    eapply IHe1. auto.
  }
Qed.
    

Lemma tctx_elt_beq_correct (e1 e2 : tctx_elt) : tctx_elt_beq e1 e2 ↔ e1 = e2.
Proof.
(*   revert e1 e2;  fix FIX 1; intros e1 e2. *)
  destruct e1; destruct e2; simpl;try done.
  split;intros.
  rewrite andb_True in H. destruct H.
  rewrite expr_beq_correct in H.
  rewrite type_beq_correct in H0.
  subst. eauto.
  injection H as eq. subst.
  rewrite andb_True. split.
  rewrite expr_beq_correct. auto.
  rewrite type_beq_correct. auto.
  split;intros.
  rewrite andb_True in H. destruct H.
  rewrite andb_True in H. destruct H.
  rewrite type_beq_correct in H0.
  rewrite expr_beq_correct in H.
  rewrite lft_beq_correct in H1. subst.
  eauto.
  injection H as eq. subst.
  rewrite andb_True. split.
  rewrite andb_True. split.
  rewrite expr_beq_correct. auto.
  rewrite lft_beq_correct. auto.
  rewrite type_beq_correct. auto.
Qed.
  

Global Instance tctx_elt_dec_eq : EqDecision tctx_elt.
Proof.
 refine (λ e1 e2, cast_if (decide (tctx_elt_beq e1 e2))); by rewrite -tctx_elt_beq_correct.
Qed.




Lemma ini_plus_type:
forall E L (x y temp ret : val),
safe_type_fun E L
    [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]
  [x ◁ own_ptr 1 int; y ◁ own_ptr 1 int]
  (let: "x'" := !x
   in let: "y'" := !y
      in let: "r" := new [ #1 ]
        in let: "z" := BinOp PlusOp "x'" "y'"
         in "r" <- "z"  ;; delete [ #1 ; x] ;; 
         delete [ #1 ; y] ;; ret ["r"])  ((λ v : val , [x ◁ own_ptr 1 int; v ◁ int]) temp ++ [ y ◁ own_ptr 1 int] )
  
.
Proof.
  intros.
  change ([x ◁ own_ptr 1 int; y ◁ own_ptr 1 int]) with ([x ◁ own_ptr 1 int] ++  [y ◁ own_ptr 1 int] ).
  eapply type_let_type.
  simpl. unfold Closed. simpl.
  {
   unfold delete. simpl.
   eapply andb_prop_intro.
   split. 
   2:{ eapply andb_prop_intro. split;eauto. eapply is_closed_of_val. }
   eapply andb_prop_intro. split.
   2:{ eapply andb_prop_intro. split;eauto. eapply andb_prop_intro. split;eauto.
       eapply is_closed_of_val. }

(* Ltac is_closed_solver' :=
  match goal with
    | [ |- _ && _] => eapply andb_prop_intro;split;eauto
    | [ |- is_closed _ _] => eauto;try (eapply is_closed_of_val)
  end.

Ltac is_closed_solver'' :=
  match goal with
    | [ |- _ && _] => eapply andb_prop_intro;split;eauto
  end.

Ltac is_closed_solver := repeat progress is_closed_solver'.
   is_closed_solver. *)

   eapply andb_prop_intro. split;eauto.
   eapply andb_prop_intro. split;eauto.
   eapply andb_prop_intro. split;eauto.
   eapply andb_prop_intro. split;eauto.
   eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
   eapply andb_prop_intro. split;eauto.
   eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
   eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
   eapply andb_prop_intro. split;eauto.
   eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
   eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
  }
        eapply type_deref_instr_type.
        eauto.
        eapply read_own_copy_safe. eapply Copy_int.


     intros x'. simpl_subst.
     eapply typed_body_mono with (C1 := [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]).
     eapply incl_cctx_incl. auto. 
     eapply contains_tctx_incl.

     instantiate (1:= λ v : val , [ y ◁ own_ptr 1 int ; x ◁ own_ptr 1 int; v ◁ int] ).
     simpl.
     eapply Permutation_submseteq.

     rewrite Permutation_swap.
     eapply Permutation_skip.
     rewrite Permutation_swap.
     eapply Permutation_skip.
     eauto.
     simpl.
     instantiate (1:= ((λ v : val , [y ◁ own_ptr 1 int; v ◁ int]) temp ++ [ x ◁ own_ptr 1 int; x' ◁ int] )).
     change ([y ◁ own_ptr 1 int; x ◁ own_ptr 1 int; x' ◁ int]) with
        ([y ◁ own_ptr 1 int] ++ [ x ◁ own_ptr 1 int; x' ◁ int]).
       eapply type_let_type.

  { simpl. unfold Closed. simpl.
   unfold delete. simpl.
   eapply andb_prop_intro.
   split. 
   2:{ eapply andb_prop_intro. split;eauto. eapply andb_prop_intro. split;eauto.
       eapply is_closed_of_val.
     }
   eapply andb_prop_intro. split.
   2:{ eapply andb_prop_intro. split;eauto. eapply andb_prop_intro. split;eauto.
       eapply is_closed_of_val.
   }
   eapply andb_prop_intro. split. 2:eauto.
   eapply andb_prop_intro. split.
   2:{ eapply andb_prop_intro. split;eauto. eapply andb_prop_intro. split;eauto. 
       eapply is_closed_of_val. eapply andb_prop_intro. split;eauto.
       eapply is_closed_of_val.
     }
   eapply andb_prop_intro. split. eapply andb_prop_intro. split. eapply is_closed_of_val.
   auto. eapply andb_prop_intro. split. 2:auto.
   eapply andb_prop_intro. split. eapply is_closed_of_val.
   eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
  }
   eapply type_deref_instr_type.
   eauto.
   eapply read_own_copy_safe. eapply Copy_int.

    intros y'. simpl_subst.
     eapply typed_body_mono with (C1 := [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]).
     eapply incl_cctx_incl. auto. 
     eapply contains_tctx_incl.

     instantiate (1:= λ v : val , [y ◁ own_ptr 1 int; v ◁ int; x ◁ own_ptr 1 int; x' ◁ int] ).
     simpl.
     eapply Permutation_submseteq.
     eauto. simpl.
     change ([y ◁ own_ptr 1 int; y' ◁ int; x ◁ own_ptr 1 int; x' ◁ int])
      with ([]++[y ◁ own_ptr 1 int; y' ◁ int; x ◁ own_ptr 1 int; x' ◁ int]).

     instantiate(1:= (λ v : val , [v ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1)) ]) temp ++ [ y ◁ own_ptr 1 int;y' ◁ int; x ◁ own_ptr 1 int; x' ◁ int]  ).
     eapply type_let_type.
     2:{ 
        eapply type_new_instr_type.
        auto with zarith.
     }
    unfold Closed. simpl.
    eapply andb_prop_intro. split;eauto.
    2:{ eapply andb_prop_intro. split;eauto.
        eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
        eapply is_closed_of_val. }
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
 
    intros r. simpl_subst.
     eapply typed_body_mono with (C1 := [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]).
     eapply incl_cctx_incl. auto.
     eapply contains_tctx_incl.
     instantiate(1:= λ v : val,[ x' ◁ int;  
    y' ◁ int] ++ [v ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1)); 
    y ◁ own_ptr 1 int;x ◁ own_ptr 1 int]).
      simpl.
     eapply Permutation_submseteq.
     (* Search (_ ≡ₚ _). *)
     assert([x' ◁ int; y' ◁ int; r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1));
 y ◁ own_ptr 1 int; x ◁ own_ptr 1 int] ≡ₚ [ r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1));
 x' ◁ int; y' ◁ int; y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]).
     change([x' ◁ int; y' ◁ int; r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1));
 y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]) with ([x' ◁ int; y' ◁ int] ++ [r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1))] ++
 [y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]).
     change ([r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1)); 
    x' ◁ int; y' ◁ int; y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]) with ([r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1))] ++ 
    [x' ◁ int; y' ◁ int] ++ [y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]) .

    eapply Permutation_app_swap_app. rewrite H.
     eapply Permutation_skip.
     rewrite Permutation_swap.
     assert([y' ◁ int; x' ◁ int; y ◁ own_ptr 1 int; x ◁ own_ptr 1 int] ≡ₚ 
 [y ◁ own_ptr 1 int;y' ◁ int; x' ◁ int; x ◁ own_ptr 1 int]
    ).
    change([y' ◁ int; x' ◁ int; y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]) with
    ([y' ◁ int; x' ◁ int]++[ y ◁ own_ptr 1 int]++[ x ◁ own_ptr 1 int]).
    change([y ◁ own_ptr 1 int; y' ◁ int; x' ◁ int; x ◁ own_ptr 1 int]) with
    ([y ◁ own_ptr 1 int]++ [y' ◁ int; x' ◁ int] ++ [x ◁ own_ptr 1 int]).
    eapply Permutation_app_swap_app. rewrite H0.
     eapply Permutation_skip. eapply Permutation_skip. 
         rewrite Permutation_swap.
    eauto.
    simpl.
    change  [x' ◁ int; y' ◁ int; r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1));
   y ◁ own_ptr 1 int; x ◁ own_ptr 1 int] with
     ([x' ◁ int; y' ◁ int] ++ [r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1));
   y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]).
     eapply type_let_type.
    unfold Closed. simpl.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. eapply is_closed_of_val.
    eapply type_plus_instr. 
    intros z. simpl_subst.

     eapply typed_body_mono with (C1 := [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]).
     eapply incl_cctx_incl. auto.
     eapply contains_tctx_incl.
    
     instantiate(1:= λ v : val,[ r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1));v ◁ int;
    y ◁ own_ptr 1 int; x ◁ own_ptr 1 int] ).
     simpl. 
     eapply Permutation_submseteq.
         rewrite Permutation_swap.
     eauto.
     simpl. change [r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1)); 
   z ◁ int; y ◁ own_ptr 1 int; x ◁ own_ptr 1 int] with ([r ◁ own_ptr (Z.to_nat 1) (uninit (Z.to_nat 1)); 
   z ◁ int] ++ [ y ◁ own_ptr 1 int; x ◁ own_ptr 1 int]).
    
    eapply type_let_type.
    unfold Closed. simpl. 
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val. 
    eapply andb_prop_intro. split;eauto. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val. 
    eapply andb_prop_intro. split;eauto. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    eapply type_assign_instr_type.
    eapply write_own_safe. simpl. eauto.
      intros r'. simpl_subst.

     simpl. assert((uninit 1) = (product2 (uninit 1) unit0)).
     eapply product2_unit0.

     eapply typed_body_mono with (C1 := [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]).
     eapply incl_cctx_incl. auto.
     eapply contains_tctx_incl.
    
     instantiate(1:= λ v : val,[x ◁ own_ptr 1 int; r ◁ own_ptr (Z.to_nat 1) int ;
    y ◁ own_ptr 1 int ] ).
     simpl. 
     eapply Permutation_submseteq.
         rewrite Permutation_swap.
     eapply Permutation_skip.
     rewrite Permutation_swap.
     eapply Permutation_skip. eauto.
     simpl.
     change ([x ◁ own_ptr 1 int; r ◁ own_ptr (Z.to_nat 1) int; y ◁ own_ptr 1 int]) with
     ([x ◁ own_ptr 1 int] ++ [ r ◁ own_ptr (Z.to_nat 1) int; y ◁ own_ptr 1 int]).
    eapply type_let_type.
    unfold Closed. simpl. 
    eapply andb_prop_intro. split;eauto.
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    assert(1%nat = my_type_system.size int). eauto.
    rewrite H0. eapply type_delete_instr.
    eauto. simpl.
    intros.

     eapply typed_body_mono with (C1 := [ret ◁cont(L , 1, λ v : list val ,
                          [ nth 0 v #1 ◁ box int])]).
     eapply incl_cctx_incl. auto.
     eapply contains_tctx_incl.
    
     instantiate(1:= λ v : val,[y ◁ own_ptr 1 int; r ◁ own_ptr (Z.to_nat 1) int  ] ).
    eapply Permutation_submseteq.
    rewrite Permutation_swap. eauto.
    simpl.
    change ([y ◁ own_ptr 1 int; r ◁ own_ptr (Z.to_nat 1) int]) with ([y ◁ own_ptr 1 int] ++ [r ◁ own_ptr (Z.to_nat 1) int]).
    eapply type_let_type.
    unfold Closed. simpl. 
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    eapply andb_prop_intro. split;eauto. 
    eapply is_closed_of_val.
    assert(1%nat = my_type_system.size int). eauto.
    rewrite H0. eapply type_delete_instr.
    eauto.
    intros. simpl_subst.
    instantiate(1:= λ v ,[r ◁ own_ptr (Z.to_nat 1) int]). simpl.
    eapply type_jump.
    (* Search (Forall2 ). *)
    instantiate (1:= [r] ). eapply List.Forall2_cons.
    right. auto.
        (* Search (Forall2 ). *)
    eapply List.Forall2_nil.
    (* Search ( _  -> _ ∈ _). *)
    eapply head_Some_elem_of. simpl. eauto.
    simpl. eapply subtype_tctx_incl. unfold box.
    simpl. change(Z.to_nat 1) with 1%nat.
    eapply t_refl.
    Unshelve. exact x. exact x. exact x. exact x.
Qed.




Definition list_add_own (x:tctx_elt) (lst : list tctx_elt):= 
  ~(In x lst ) /\ ( (exists (p:path) (t:type) n a, x = TCtx_hasty p t /\ t = own_ptr n a /\ path_not_in_tctx p lst)
                             \/ (exists (p:path) (k:lft) (t:type) n a,x = TCtx_blocked p k t /\ t = own_ptr n a /\ path_not_in_tctx p lst))
.

(*Compute(path_not_in_tctx "p" ["p" ◁ int; "c" ◁ int]).*)
(* (exists p ty, tctx_elt = (p ◁ ty) /\ path_not_in_tctx p T1)
 *)
(* 
Ltac tryfalse :=
try solve [congruence | discriminate | assumption]. *)

Fixpoint member_of_own_in_type (ty:type): nat :=
match ty with
| own_ptr _ (own_ptr _ ty) => S ( S (member_of_own_in_type ty))
| own_ptr _ _ => 1
| _ => 0
end.

Fixpoint member_of_own_in_type' (ty:type): nat :=
match ty with
| own_ptr _ (own_ptr _ ty') => 2 + member_of_own_in_type' ty' 
| own_ptr _ _ => 1
| _ => 0
end.

Fixpoint member_of_own_in_type'' (ty:type): nat :=
match ty with
| own_ptr _ ty' => 1 + member_of_own_in_type'' ty' 
| _ => 0
end.



Fixpoint member_of_own_in_tctx (T:tctx): nat :=
match T with
| nil => 0
| t::h => match t with
          | p' ◁ ty => member_of_own_in_type ty + (member_of_own_in_tctx h)
          | p' ◁{ κ } ty => member_of_own_in_type ty + (member_of_own_in_tctx h)
          end
end.

Fixpoint member_of_own_in_tctx' (T:tctx): nat :=
match T with
| nil => 0
| t::h => match t with
          | p' ◁ ty => member_of_own_in_type'' ty + (member_of_own_in_tctx' h)
          | p' ◁{ κ } ty => member_of_own_in_type'' ty + (member_of_own_in_tctx' h)
          end
end.

(*
Compute member_of_own_in_tctx(["p" ◁ (own_ptr 1 (own_ptr 1 (own_ptr 1 (own_ptr 1 int)))); "p" ◁ own_ptr 1 int
; "p" ◁ int ; "p" ◁ (own_ptr 1 (own_ptr 1 int))]    
  ).

Compute member_of_own_in_type((own_ptr 1 (own_ptr 1 (own_ptr 1 (own_ptr 1 int))))).
*)

Definition own_add T1 T2: Prop := 
  member_of_own_in_tctx T1 < member_of_own_in_tctx T2.

Definition own_add' T1 T2: Prop := 
  member_of_own_in_tctx' T1 < member_of_own_in_tctx' T2.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
(*Search (_ = 0%nat).
Print Nat.eq_0_gt_0_cases.*)

Lemma Ins_own_not_add : forall E L I T1 (T2:val → tctx) v T2',
              safe_type_Ins  E L T1 I T2  ->
              T2' = T2 v ->
              own_add' T1 T2'->
              (exists n , I = new [n]%E ). 
Proof.
  intros.
  inversion H;subst;
   try (unfold own_add' in H1;
     simpl in H1;
     tryfalse).
   - lia.
   - lia.
   - exists (#n). auto.
   - inversion H3; subst.
     + destruct ty; simpl in H1; inversion H0; lia.
     + simpl in H1. lia.
     + simpl in H1. destruct ty; inversion H0; simpl in H1; lia.
     + simpl in H1. destruct ty; inversion H0; simpl in H1; lia.
   - simpl in H1.
     induction H2; simpl in H1; try lia.
   - simpl in H1.
(*      induction H3. simpl in H1. *)
     inversion H3. subst. simpl in H1; try lia.
     subst. simpl in H1. lia.
   - inversion H3; subst. simpl in H1; try lia.
     simpl in H1. lia.
   - inversion H3; subst; simpl in H1; try lia.
     inversion H4; subst; simpl in H1; try lia.
     inversion H4; subst; simpl in H1; try lia.
   - inversion H3; subst; simpl in H1; try lia.
       + inversion H4; subst; simpl in H1; try lia.
          * destruct ty; simpl in H1; try lia. inversion H2.
          * destruct ty; simpl in H1; try lia. inversion H2.
          * destruct ty; simpl in H1; try lia. inversion H2.
       + inversion H4; subst; simpl in H1; try lia.
Qed.

Lemma Ins_own_not_add' : forall E L I T1 (T2:val → tctx) v T2',
              safe_type_Ins  E L T1 I T2  ->
              T2' = T2 v ->
              (forall n , I ≠ new [n]%E ) ->
              ~ own_add' T1 T2' .
Proof.
  intros.
  unfold own_add'.
  inversion H;subst; simpl ; try lia.
   - tryfalse.
   - inversion H3; subst.
     + destruct ty; simpl; inversion H0; lia.
     + simpl. lia.
     + simpl. destruct ty; inversion H0; simpl; lia.
     + simpl. destruct ty; inversion H0; simpl; lia.
   - simpl.
     induction H2; simpl; try lia .
   - simpl in H1.
     inversion H3. subst. simpl; try lia.
     subst. simpl. lia.
   - inversion H3; subst. simpl; try lia.
     simpl. lia.
   - inversion H3; subst; simpl; try lia.
     inversion H4; subst; simpl; try lia.
     inversion H4; subst; simpl; try lia.
   - inversion H3; subst; simpl; try lia.
       + inversion H4; subst; simpl; try lia.
          * destruct ty; simpl; try lia. inversion H2.
          * destruct ty; simpl; try lia. inversion H2.
          * destruct ty; simpl; try lia. inversion H2.
       + inversion H4; subst; simpl; try lia.
Qed.


Definition read_instruction I p (T1:tctx) (T2:tctx) : Prop := 
       (I = (!p) (* \/ 
             (exists p1 ty i, I = (p1 <-{(my_type_system.size ty),Σ i} !p)) \/
             exists p1 n , I = (p1 <-{n} !p) *)) 
             /\ exists tctx_elt tctx_elt' tctx_elt'' n1 n2 (* κ *) ty v, 
                    ((tctx_elt = (p ◁ own_ptr n1 (own_ptr n2 ty)) (* \/ tctx_elt = (p ◁{ κ }  own_ptr n1 (own_ptr n2 ty)) *))
                    /\ tctx_elt ∈ T1
                    /\ (tctx_elt' = (v ◁ (own_ptr n2 ty)) (* \/ tctx_elt' = (v ◁{ κ } (own_ptr n2 ty)) *) )
                    /\ (tctx_elt'' = (p ◁ own_ptr n1 (uninit 1%nat)))
                    /\ tctx_elt' ∈ T2                        
)
.



(* Notation "p ◁ ty" := (TCtx_hasty p ty%list) (at level 70).
Notation "p ◁{ κ } ty" := (TCtx_blocked p κ ty)
   (at level 70, format "p  ◁{ κ }  ty"). *)


Ltac simpljoin :=
  match goal with
    | H:exists _,_ |- _ => destruct H
    | H:_/\_ |- _=> destruct H
    | _ => try (progress subst)
  end.

Ltac simpljoin1 := repeat progress simpljoin.

Fixpoint remove_first (A : Type) (eq_dec : ∀ x y : A,
                         {x = y} + {x ≠ y}) (x : A) (l : list A) {struct l}  : list A :=
match l with
    | [] => []
    | y :: tl =>
        if eq_dec x y
        then tl
        else y :: remove_first A eq_dec x tl
    end
.

Fixpoint remove_first_tctx_elt  (x : tctx_elt) (l : list tctx_elt) {struct l}  : list tctx_elt :=
match l with
    | [] => []
    | y :: tl =>
        if tctx_elt_beq x y
        then tl
        else y :: remove_first_tctx_elt x tl
    end
.



Definition capability_tran (T1 T2:tctx) :=
length T1 = length T2 
/\ (forall p ty, In (p ◁ ty) T2 -> exists I, In (I ◁ ty) T1 /\ 
            remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) T2 = remove_first tctx_elt tctx_elt_dec_eq (I ◁ ty) T1
                                   \/ In (p ◁ ty) T1
   )
(*       
/\ forall p κ ty, In (p ◁{ κ }  ty) T2 -> exists I, In (I ◁{ κ } ty) T1 /\ remove_first tctx_elt tctx_elt_dec_eq (p ◁{ κ }  ty) T2 = remove_first tctx_elt tctx_elt_dec_eq (I ◁{ κ }  ty) T1
                                   \/ In (p ◁{ κ }  ty) T1 *)
. 


Lemma safe_type_Ins_capability_not_add_part1 : forall E L I T1 (T2:val → tctx) v T2',
              safe_type_Ins  E L T1 I T2  ->
              T2' = T2 v ->
              forall tctx_elt ,In tctx_elt T2' /\  (list_add_own tctx_elt T1) ->
              (exists n , I = new [n]%E)
               \/ (exists p , I = p /\ capability_tran T1 T2') 
              \/ ( exists p, read_instruction I p T1 T2').

Proof.
  intros.

  inversion H; auto.
  1:{
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    
    destruct Hown as [Hown | Hown];
    apply in_inv in Hin;
    destruct Hin as [Heq | Hnil].
    destruct tctx_elt0.
    rewrite <- Heq in Hown.
    destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
    injection Heq as Hpeq.
    subst. tryfalse.
    tryfalse.
    tryfalse.
    destruct tctx_elt0.
    destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
    tryfalse.
    tryfalse.
    tryfalse.  
  }
  {
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    apply in_inv in Hin.
    destruct Hin as [Heq | Hnil].
    2:{
        assert( ~In tctx_elt0 []).
        eapply in_nil.
        tryfalse.
    }
      destruct Hown as [Hown | Hown];
      destruct tctx_elt0.
      rewrite <- Heq in Hown.
      destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
      injection Heq as Hpeq.
      subst. tryfalse.
      tryfalse.
      destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
      tryfalse.
      tryfalse.
  }
  {
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    apply in_inv in Hin.
    destruct Hin as [Heq | Hnil].
    2:{
        assert( ~In tctx_elt0 []).
        eapply in_nil.
        tryfalse.
    }
    destruct Hown as [Hown | Hown];
    destruct tctx_elt0.
    rewrite <- Heq in Hown.
    destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
    injection Heq as Hpeq.
    subst. tryfalse.
    tryfalse.
    destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
    tryfalse.
    tryfalse.
  }
  {
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    apply in_inv in Hin.
    destruct Hin as [Heq | Hnil].
    2:{
        assert( ~In tctx_elt0 []).
        eapply in_nil.
        tryfalse.
    }
    destruct Hown as [Hown | Hown];
    destruct tctx_elt0.
    rewrite <- Heq in Hown.
    destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
    injection Heq as Hpeq.
    subst. tryfalse.
    tryfalse.
    destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
    tryfalse.
    tryfalse.
  }
  {
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    apply in_inv in Hin.
    destruct Hin as [Heq | Hnil].
    2:{
        assert( ~In tctx_elt0 []).
        eapply in_nil.
        tryfalse.
    }
    destruct Hown as [Hown | Hown];
    destruct tctx_elt0.
    rewrite <- Heq in Hown.
    destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
    injection Heq as Hpeq.
    subst. tryfalse.
    tryfalse.
    destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
    tryfalse.
    tryfalse.
  }
  {
    right. left. exists p.
    split.
    auto.
    subst.
    unfold capability_tran. split.
    eauto.
    intros.
    eapply in_inv in H0.
    destruct H0. injection H0 as eq; subst.
    exists I.
    left. split.
    eapply in_eq.
    simpl. 
    destruct (tctx_elt_dec_eq (v ◁ ty0) (v ◁ ty0));
    destruct (tctx_elt_dec_eq (I ◁ ty0) (I ◁ ty0)); tryfalse.
    simpl in H0. exfalso. eauto.
  }
  {
    left.
    exists #n.
    auto.
  }
  { (*delete*)
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    assert(~ In tctx_elt0 []) by eapply in_nil.
    tryfalse.
  }
  { (*!p*)
    subst.
    destruct H1 as (Hin & Hnin & Hown).
    apply in_inv in Hin.
    destruct Hin as [Heq | Heq2].

    destruct Hown as [Hown | Hown];
    destruct tctx_elt0.
    rewrite <- Heq in Hown.
    destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
    injection Heq as Hpeq.
    subst.
    injection Heq2 as Hpeq.
    subst.
    unfold path_not_in_tctx in Hnop.
    rewrite expr_eq in Hnop. exfalso. auto.
    tryfalse.
    injection Heq as Hpeq.
    subst.
    destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
    tryfalse.
    tryfalse.
    destruct Heq2 as [Heq | Hnil].
    2:{
        assert( ~In tctx_elt0 []).
        eapply in_nil.
        tryfalse.
    }
    subst.
    destruct Hown as [Hown | Hown].
    2:{
      destruct Hown as (p' & k' & t' & n' & a & Heq2 & Hown & Hnop).
      tryfalse.
    }
    destruct Hown as (p' & t' & n' & a & Heq2 & Hown & Hnop).
    injection Heq2 as Hpeq.
    subst.
    inversion H3; auto; subst.
    inversion H0.

    right. right.
    unfold read_instruction.
    exists p.
     { split.
       auto.
       exists (p ◁ own_ptr n (own_ptr n' a)).
       exists (v ◁ own_ptr n' a).
       exists (p
          ◁ own_ptr n
              (uninit
                 (my_type_system.size (own_ptr n' a)))).
       exists n. exists n'. exists a. exists v.
       split; auto.
       split.
       eapply list_elem_of_singleton. auto.
       split. auto.
       split.
       simpl. auto.
       eapply list_elem_of_In.
       eapply in_cons.
       eapply in_eq.
        
     }
     inversion H0.
     inversion H0.
  }
  {
    subst.
    inversion H2.
    subst.
    destruct H1.
    eapply list_elem_of_In in H1.
    eapply list_elem_of_singleton in H1.
    subst.
    unfold list_add_own in H3.
    destruct H3.
    destruct H3.
    do 4 destruct H3. destruct H3. destruct H4. subst.
    injection H3 as Hpeq. subst.
    unfold path_not_in_tctx in H5.
    rewrite expr_eq in H5. exfalso. auto.
    do 5 destruct H3. destruct H3. tryfalse.
    destruct H1.
    eapply list_elem_of_In in H1.
    eapply list_elem_of_singleton in H1.
    subst.
    unfold list_add_own in H3.
    destruct H3.
    eapply not_in_cons in H1.
    destruct H1.
    tryfalse.
  }
  {
    subst.
    inversion H3. subst.
    destruct H1.
    eapply list_elem_of_In in H1.
    eapply list_elem_of_singleton in H1.
    subst.
    unfold list_add_own in H4.
    destruct H4.
    destruct H4.
    do 4 destruct H4. destruct H4. destruct H5. subst.
    injection H4 as Hpeq. subst.
    unfold path_not_in_tctx in H6.
    rewrite expr_eq in H6. exfalso. auto.
    do 5 destruct H4. destruct H4. tryfalse.
    destruct H1.
    eapply list_elem_of_In in H1.
    eapply list_elem_of_singleton in H1.
    subst.
    unfold list_add_own in H4.
    destruct H4.
    eapply not_in_cons in H1.
    destruct H1.
    tryfalse.
  }
  {
    subst.
    destruct H1.
    eapply list_elem_of_In in H0.
    eapply list_elem_of_singleton in H0.
    subst.
    unfold list_add_own in H1.
    destruct H1.
    destruct H1.
    do 5 destruct H1.
    injection H1 as Hpeq. subst.
    destruct H2; tryfalse.
    do 6 destruct H1. tryfalse.
  }
  {
    subst.
    destruct H1.
    eapply list_elem_of_In in H0.
    eapply list_elem_of_singleton in H0.
    subst.
    unfold list_add_own in H1.
    destruct H1.
    destruct H1.
    do 5 destruct H1.
    injection H1 as Hpeq. subst.
    destruct H3; tryfalse.
    do 6 destruct H1. tryfalse.
  }
  {
    subst.
    destruct H1.
    eapply list_elem_of_In in H0.
    eapply list_elem_of_singleton in H0.
    subst.
    unfold list_add_own in H1.
    destruct H1.
    destruct H1.
    do 5 destruct H1.
    injection H1 as Hpeq. subst.
    destruct H3; tryfalse.
    do 6 destruct H1. tryfalse.
  }
  {
    subst.
    destruct H1.
    eapply list_elem_of_In in H0.
    eapply list_elem_of_singleton in H0.
    subst.
    unfold list_add_own in H1.
    destruct H1.
    destruct H1.
    do 5 destruct H1.
    injection H1 as Hpeq. subst.
    destruct H4; tryfalse.
    do 6 destruct H1. tryfalse.
  }
  {
    subst.
    destruct H1.
    eapply list_elem_of_In in H0.
    eapply list_elem_of_singleton in H0.
    subst.
    unfold list_add_own in H1.
    destruct H1.
    destruct H1.
    do 5 destruct H1.
    injection H1 as Hpeq. subst.
    destruct H4; tryfalse.
    do 6 destruct H1. tryfalse.
  }
  {
    inversion H3.
    subst;
    destruct H1;
    eapply list_elem_of_In in H0;
    eapply list_elem_of_singleton in H0;
    subst;
    destruct H1.
    destruct H1.
    do 5 destruct H1.
    injection H1 as Hpeq. subst.
    destruct H4. unfold path_not_in_tctx in H4.
    rewrite expr_eq in H4. exfalso. auto.
    do 6 destruct H1. tryfalse.
    subst.
    destruct H1;
    eapply list_elem_of_In in H0;
    eapply list_elem_of_singleton in H0.
    subst.
    unfold list_add_own in H1.
    destruct H1.
    eapply not_in_cons in H0.
    destruct H0; tryfalse.
  }
  {
    inversion H4;
    subst.
    + inversion H3. 
      - subst.
        destruct H1.
        eapply in_inv in H1.
        destruct H1.
        * subst.  unfold list_add_own in H5.
          destruct H5.
          destruct H5.
          do 5 destruct H5. injection H5 as Hpeq. subst.
          destruct H6.  simpl in H6.
          rewrite expr_eq in H6. exfalso. auto.
          do 6 destruct H5. tryfalse.
        * 
          eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst.
          unfold list_add_own in H5.
          destruct H5.
          (* Search (~ In _ _). *)
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
      - subst.
        destruct H1.
        eapply in_inv in H1.
        destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          eapply not_in_cons in H1. destruct H1. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
   + inversion H3; subst.
      - destruct H1.
        eapply in_inv in H1.
        destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          injection H5 as Hpeq. destruct H6; subst.
          simpl in H7. rewrite expr_eq in H7. exfalso. auto.
          destruct H5. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          do 6 destruct H5. subst.
          injection H5 as Hpeq. destruct H6; subst.
          simpl in H7. rewrite expr_eq in H7. exfalso. destruct (expr_beq x p1); auto.
          destruct H7. auto.
          destruct H5. tryfalse.
      - destruct H1.
        eapply in_inv in H1.
        destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          eapply not_in_cons in H1. destruct H1. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          do 6 destruct H5. subst.
          injection H5 as Hpeq. destruct H6; subst.
          simpl in H7. rewrite expr_eq in H7. exfalso. destruct (expr_beq x p1); auto.
          destruct H7. auto.
          destruct H5. tryfalse.
   + inversion H3; subst.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          injection H5 as Hpeq. destruct H6; subst.
          simpl in H7. rewrite expr_eq in H7. exfalso. auto.
          destruct H5. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          eapply not_in_cons in H1. destruct H1. tryfalse.
          destruct H5; tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
   + inversion H3; subst.
      - destruct H1.
        eapply in_inv in H1.
        destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          injection H5 as Hpeq. destruct H6; subst.
          simpl in H7. rewrite expr_eq in H7. exfalso. auto.
          destruct H5. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          eapply not_in_cons in H1. destruct H1. tryfalse.
          destruct H5; tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
  }
  {
    subst.
    inversion H4; subst.
    + inversion H3; subst.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          injection H5 as Hpeq. destruct H6; subst.
          simpl in H7. rewrite expr_eq in H7. exfalso. auto.
          destruct H5. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H5. destruct H5.
          do 6 destruct H5. subst.
          eapply not_in_cons in H1. destruct H1. tryfalse.
          destruct H5; tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H5.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H6. destruct H6. tryfalse.
    + inversion H3; subst.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H2. destruct H2.
          do 6 destruct H2. subst.
          injection H2 as Hpeq. destruct H5; subst.
          simpl in H6. rewrite expr_eq in H6. exfalso. auto.
          destruct H2. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. do 7 destruct H2. subst.
          injection H2 as Hpeq. destruct H5; subst.
          simpl in H6. rewrite expr_eq in H6. exfalso. destruct (expr_beq x p1); auto.
          destruct H6. tryfalse.
          destruct H2. tryfalse.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H2. destruct H2.
          do 6 destruct H2. subst.
          eapply not_in_cons in H1. destruct H1. tryfalse.
          destruct H2; tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. do 7 destruct H2. subst.
          injection H2 as Hpeq. destruct H5; subst.
          simpl in H6. rewrite expr_eq in H6. exfalso. destruct (expr_beq x p1); auto.
          destruct H6. tryfalse.
          destruct H2. tryfalse.
   + inversion H3; subst.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H6. destruct H6.
          do 6 destruct H6. subst.
          injection H6 as Hpeq. destruct H7; subst.
          simpl in H8. rewrite expr_eq in H8. exfalso. auto.
          destruct H6. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H6.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H7. destruct H7. tryfalse.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H6. destruct H6.
          do 6 destruct H6. subst.
          eapply not_in_cons in H1. destruct H1. tryfalse.
          destruct H6; tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H6.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H7. destruct H7. tryfalse.
   + inversion H3; subst.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. unfold list_add_own in H6. destruct H6.
          do 6 destruct H6. subst.
          injection H6 as Hpeq. destruct H7; subst.
          simpl in H8. rewrite expr_eq in H8. exfalso. auto.
          destruct H6. tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H6.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H7. destruct H7. tryfalse.
     - destruct H1.
       eapply in_inv in H1.
       destruct H1.
        * subst. destruct H6.
          do 6 destruct H6. subst.
          eapply not_in_cons in H1. destruct H1. tryfalse.
          destruct H6; tryfalse.
        * eapply list_elem_of_In in H1;
          eapply list_elem_of_singleton in H1.
          subst. destruct H6.
          eapply not_in_cons in H1. destruct H1.
          eapply not_in_cons in H7. destruct H7. tryfalse.
  }
Qed.

Definition list_add_uniq (x:tctx_elt) (lst : list tctx_elt):= 
  ~(In x lst ) /\ (exists (p:path) (t:type) κ a, x = TCtx_hasty p t /\ t = &uniq{ κ } a /\ path_not_in_tctx p lst)
.


Definition read_instruction_uniq I p (T1:tctx) (T2:tctx) : Prop := 
             I = (!p) 
             /\ (exists tctx_elt tctx_elt' tctx_elt'' n1 κ  ty v, 
                    (tctx_elt = (p ◁ own_ptr n1 (uniq_bor κ ty)) (* \/ tctx_elt = (p ◁{ κ }  own_ptr n1 (own_ptr n2 ty)) *))
                    /\ tctx_elt ∈ T1
                    /\ (tctx_elt' = (v ◁ (uniq_bor κ ty)) (* \/ tctx_elt' = (v ◁{ κ } (own_ptr n2 ty)) *) )
                    /\ (tctx_elt'' = (p ◁ own_ptr n1 (uninit 1%nat)))
                    /\ tctx_elt'' ∈ T2
                    /\ tctx_elt' ∈ T2 ) 
      \/    I = (!p)  /\ 
            length T1 = length T2 /\(*  length T1 = 1%nat /\ *)
            forall p κ ty , In (p ◁ uniq_bor κ ty) T2 -> exists v κ' n,
                           In (v ◁ uniq_bor κ (own_ptr n ty)) T1 
                                    /\ remove_first tctx_elt tctx_elt_dec_eq (v ◁ uniq_bor κ (own_ptr n ty)) T1 = remove_first tctx_elt tctx_elt_dec_eq (p ◁ uniq_bor κ ty) T2
                        \/ In (v ◁ uniq_bor κ (uniq_bor κ' ty)) T1
                                    /\ remove_first tctx_elt tctx_elt_dec_eq (v ◁ uniq_bor κ (uniq_bor κ' ty)) T1 = remove_first tctx_elt tctx_elt_dec_eq (p ◁ uniq_bor κ ty) T2
                        \/ In (p ◁ uniq_bor κ ty) T1
.


Lemma safe_type_Ins_capability_not_add_part2 : forall E L I T1 (T2:val → tctx) v T2',
              safe_type_Ins  E L T1 I T2  ->
              T2' = T2 v ->
              forall tctx_elt ,In tctx_elt T2' /\

              (list_add_uniq tctx_elt T1) ->
  (exists p , I = p /\ capability_tran T1 T2') 
  \/ (exists p,read_instruction_uniq I p T1 T2'). 
          
Proof.
  intros.
  simpljoin1.
  inversion H; subst.
  - unfold list_add_uniq in H2.
    simpljoin1.
    eapply in_inv in H1.
    destruct H1;
    tryfalse. 
  - unfold list_add_uniq in H2.
    simpljoin1.
    eapply in_inv in H1.
    destruct H1;
    tryfalse. simpl in H1. exfalso. eauto. 
  - unfold list_add_uniq in H2.
    simpljoin1.
    eapply in_inv in H1.
    destruct H1;
    tryfalse. simpl in H1. exfalso. eauto. 
  - unfold list_add_uniq in H2.
    simpljoin1.
    eapply in_inv in H1.
    destruct H1;
    tryfalse. simpl in H1. exfalso. eauto. 
  - unfold list_add_uniq in H2.
    simpljoin1.
    eapply in_inv in H1.
    destruct H1;
    tryfalse. simpl in H1. exfalso. eauto. 
  - left. exists I.
    split;eauto.
    unfold capability_tran.
    split. simpl. eauto.
    intros. eapply in_inv in H0.  
    destruct H0. injection H0 as eq; subst.
    exists I. left.
    split. eapply in_eq.
    simpl.
    destruct (tctx_elt_dec_eq (v ◁ ty0) (v ◁ ty0)) ;
    destruct (tctx_elt_dec_eq (I ◁ ty0) (I ◁ ty0)); tryfalse.
    auto.
    simpl in H0. exfalso. auto.
(*     
    simpl. eauto. destruct v. simpl. destruct ty0. simpl.
    assert(tctx_elt_dec_eq (v ◁ ty0) (v ◁ ty0) = true).
    change (tctx_elt_dec_eq (v ◁ ty0) (v ◁ ty0)) with Datatypes.true.
    simpl. eauto.
    split.
    intros.
    eapply in_inv in H0. destruct H0.
    injection H0 as eq.
    subst.
    eexists. eapply in_eq.
    simpl in H0. exfalso. eauto.
    intros. eapply in_inv in H0. 
    destruct H0.
    tryfalse.
    simpl in H0. exfalso. eauto. *)
  - unfold list_add_uniq in H2.
    eapply in_inv in H1.
    destruct H1.
    simpljoin1. tryfalse.
    simpljoin1. tryfalse.
  - simpl in H1.
    exfalso. eauto.
  -
    inversion H3;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. inversion H4;subst;tryfalse.
    simpl in H1. exfalso; eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. destruct ty; tryfalse.
    injection H4 as eq; subst.
    right. exists p.
    unfold read_instruction_uniq.
    left. 
    split;eauto.
    do 7 eexists.
    split;eauto. split.
    eapply list_elem_of_singleton. eauto.
    split;eauto.
    split;eauto.
    split. 
    eapply list_elem_of_In. simpl. left. eauto.
    eapply list_elem_of_In. eapply in_cons.
    eapply in_eq.
    simpl in H1. exfalso. eauto.

    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    destruct ty; tryfalse.
    inversion H4.
    simpl in H1. exfalso; eauto.
    
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    injection H6 as eq;subst.
    assert(In (x ◁ &uniq{x1} x2) [x ◁ &uniq{x1} x2]).
    eapply in_eq. tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    destruct ty; tryfalse.
    inversion H4.
    simpl in H1. exfalso. eauto.

  - inversion H0;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso; eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. 
    injection H4 as eq;subst.
    assert(In (x ◁ &uniq{x1} x2) [x ◁ &uniq{x1} x2; p2 ◁ x2]).
    eapply in_eq. tryfalse.
    simpl in H1. exfalso. eauto.

  - inversion H3;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso;eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2. 
    simpljoin1.
    injection H5 as eq;subst.
    assert(In (x ◁ &uniq{x1} (sum tyl)) [x ◁ &uniq{x1} (sum tyl); p2 ◁ ty]).
    eapply in_eq.
    tryfalse.
    simpl in H1. exfalso. eauto.

  - eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H0. exfalso;eauto.

  - 
    right. exists p.
    unfold read_instruction_uniq.
    right.
    split;eauto.
    split. eauto.
(*     split. eauto. *)
    intros.
    eapply in_inv in H3.
    destruct H3.
    injection H3 as eq;subst.
    do 3 eexists.
    left. split. eapply in_eq.
    simpl. 
    destruct (tctx_elt_dec_eq (p ◁ &uniq{κ0} (own_ptr n ty0))
    (p ◁ &uniq{κ0} (own_ptr n ty0)));
    destruct (tctx_elt_dec_eq (v ◁ &uniq{κ0} ty0)
    (v ◁ &uniq{κ0} ty0));tryfalse.
    simpl in H3. exfalso. eauto.

  - eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    tryfalse.
    simpl in H1. exfalso; eauto.
  -
    right. exists p.
    unfold read_instruction_uniq.
    right.
    split;eauto.
    split. eauto.
(*     split. eauto. *)
    intros.
    eapply in_inv in H4.
    destruct H4.
    injection H4 as eq;subst.
    do 3 eexists.
    right. left.
    split. eapply in_eq.
    simpl.
    destruct (tctx_elt_dec_eq (p ◁ &uniq{κ0} (&uniq{κ'} ty0))
    (p ◁ &uniq{κ0} (&uniq{κ'} ty0)));
    destruct (tctx_elt_dec_eq (v ◁ &uniq{κ0} ty0)
    (v ◁ &uniq{κ0} ty0));tryfalse.
    simpl in H4. exfalso. eauto.

  - eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    tryfalse.
    simpl in H1. exfalso; eauto.
  - inversion H3;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p ◁ &uniq{κ} (sum tyl)) [p ◁ &uniq{κ} (sum tyl)]).
    eapply in_eq.
    tryfalse.
    simpl in H1. exfalso. eauto.
  - inversion H3;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    tryfalse.
    inversion H4;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. 
    assert(In (p2 ◁ &uniq{κ} ty)
         [p1 ◁ own_ptr n ty'; p2 ◁ &uniq{κ} ty]).
    eapply in_cons. eapply in_eq. tryfalse.
    simpl in H1. exfalso. eauto.
    inversion H4;subst.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} (sum tyl))
         [p1 ◁ &uniq{κ} (sum tyl); p2 ◁ own_ptr n ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} (sum tyl))
         [p1 ◁ &uniq{κ} (sum tyl); p2 ◁ own_ptr n ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} (sum tyl))
         [p1 ◁ &uniq{κ} (sum tyl); p2 ◁ &shr{κ0} ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} (sum tyl))
         [p1 ◁ &uniq{κ} (sum tyl); p2 ◁ &uniq{κ0} ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p2 ◁ &uniq{κ0} ty)
         [p1 ◁ &uniq{κ} (sum tyl); p2 ◁ &uniq{κ0} ty]).
    eapply in_cons. eapply in_eq.
    tryfalse.
    simpl in H1. exfalso. eauto.

  - inversion H3;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    tryfalse.
    inversion H4;subst.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1.
    destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. 
    assert(In (p2 ◁ &uniq{κ} ty)
         [p1 ◁ own_ptr n ty'; p2 ◁ &uniq{κ} ty]).
    eapply in_cons. eapply in_eq. tryfalse.
    simpl in H1. exfalso. eauto.
    inversion H4;subst.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} ty)
         [p1 ◁ &uniq{κ} ty; p2 ◁ own_ptr n ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} ty)
         [p1 ◁ &uniq{κ} ty; p2 ◁ own_ptr n ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} ty)
         [p1 ◁ &uniq{κ} ty; p2 ◁ &shr{κ0} ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1. tryfalse.
    simpl in H1. exfalso. eauto.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p1 ◁ &uniq{κ} ty)
         [p1 ◁ &uniq{κ} ty; p2 ◁ &uniq{κ0} ty]).
    eapply in_eq.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    unfold list_add_uniq in H2.
    simpljoin1.
    assert(In (p2 ◁ &uniq{κ0} ty)
         [p1 ◁ &uniq{κ} ty; p2 ◁ &uniq{κ0} ty]).
    eapply in_cons. eapply in_eq.
    tryfalse.
    simpl in H1. exfalso. eauto.
    Unshelve. exact κ0. exact 0%nat.
Qed. 


Definition read_instruction_shr I p (T1:tctx) (T2:tctx) : Prop := 
             I = (!p)
             /\ (exists tctx_elt tctx_elt' n1 κ' κ  ty v, 
                    (tctx_elt = (p ◁ own_ptr n1 (shr_bor κ ty)) \/ tctx_elt = (p ◁ uniq_bor κ' (shr_bor κ ty)) \/ tctx_elt = (p ◁ shr_bor κ' (shr_bor κ ty)) )
                    /\ tctx_elt ∈ T1
                    /\ (tctx_elt' = (v ◁ (shr_bor κ ty)) )
                    /\ tctx_elt' ∈ T2 )
        \/  (I = (!p)  /\ 
            length T1 = length T2 /\
            forall p κ ty , In (p ◁ shr_bor κ ty) T2 -> 
                  exists v n κ',
                           In (v ◁ shr_bor κ (own_ptr n ty)) T1 
                           /\ remove_first tctx_elt tctx_elt_dec_eq (v ◁ shr_bor κ (own_ptr n ty)) T1 = remove_first tctx_elt tctx_elt_dec_eq (p ◁ shr_bor κ ty) T2
                        \/ In (v ◁ shr_bor κ (uniq_bor κ' ty)) T1
                           /\ remove_first tctx_elt tctx_elt_dec_eq (v ◁ shr_bor κ (uniq_bor κ' ty)) T1 = remove_first tctx_elt tctx_elt_dec_eq (p ◁ shr_bor κ ty) T2
                        \/ In (p ◁ shr_bor κ ty) T1)
 .



Lemma safe_type_Ins_capability_not_add_part3 : forall E L I T1 (T2:val → tctx) v T2',
              safe_type_Ins  E L T1 I T2  ->
              T2' = T2 v ->
              forall tctx_elt (p:path) κ a,In tctx_elt T2' /\
              tctx_elt = TCtx_hasty p (&shr{ κ } a) ->
                (exists tctx_elt',
                In tctx_elt' T1 /\
                tctx_elt' = TCtx_hasty p (&shr{ κ } a))
              \/ 
                (exists p , I = p /\ capability_tran T1 T2') 
              \/ exists p, read_instruction_shr I p T1 T2'
                
.

Proof.
  intros.
  simpljoin1.
  inversion H;subst.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    destruct ty; tryfalse.
    injection H0 as eq;subst.
    right.
    left.
    exists I.
    split. eauto.
    unfold capability_tran.
    split. simpl. eauto.
    intros.
    eapply in_inv in H0. destruct H0.
    injection H0 as eq;subst.
    exists I.
    left.
    split. eapply in_eq.
    simpl.
    destruct (tctx_elt_dec_eq (v ◁ &shr{κ} a) (v ◁ &shr{κ} a));
    destruct (tctx_elt_dec_eq (I ◁ &shr{κ} a) (I ◁ &shr{κ} a));
    tryfalse.
    simpl in H0. exfalso. auto.
    simpl in H0. exfalso. auto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - simpl in H1.
    exfalso. eauto.
  - inversion H2;subst.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    right. right.
    unfold read_instruction_shr.
    exists p0.
    left.
    split; eauto.
    eapply in_inv in H1. destruct H1.
    destruct ty; tryfalse.
    2:{ simpl in H1. exfalso. auto. }
    injection H1 as eq; subst.
    do 7 eexists.
    split.
    left. eauto.
    split.
    eapply list_elem_of_singleton. eauto.
    split;eauto.
    eapply list_elem_of_In. simpl. 
    right. left. eauto.

    eapply in_inv in H1. destruct H1.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    2:{ simpl in H1. exfalso. auto. } 
    destruct ty;tryfalse.
    injection H1 as eq; subst.
    right. right. 
    exists p0. unfold read_instruction_shr.
    left.
    split;eauto.
    do 7 eexists.
    split. left. eauto.
    split.
    eapply list_elem_of_singleton. eauto.
    split. eauto.
    eapply list_elem_of_In. eapply in_cons.
    simpl. left. eauto.
    eapply in_inv in H1.
    destruct H1. injection H1 as eq;subst.
    left. 
    eexists. split;eauto.
    eapply in_eq.
    eapply in_inv in H1.
    destruct H1.
    destruct ty; tryfalse.
    2:{ simpl in H1. exfalso; eauto. }
    injection H1 as eq;subst.
    right. right. exists p0.
    unfold read_instruction_shr.
    left.
    split. eauto.
    do 7 eexists.
    split. right. right. eauto.
    split;eauto.
    eapply list_elem_of_singleton. eauto.
    split;eauto.
    eapply list_elem_of_In. eapply in_cons.
    simpl. left. eauto.

    eapply in_inv in H1. destruct H1.
    tryfalse.
    eapply in_inv in H1. destruct H1.
    2:{ simpl in H1. exfalso. auto. } 
    destruct ty;tryfalse.
    injection H1 as eq; subst.
    right. right. 
    exists p0. unfold read_instruction_shr.
    left.
    split;eauto.
    do 7 eexists.
    split. right. left. eauto.
    split.
    eapply list_elem_of_singleton. eauto.
    split. eauto.
    eapply list_elem_of_In. eapply in_cons.
    simpl. left. eauto.

  - inversion H0;subst.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1; exfalso; auto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1; exfalso; auto.

  - inversion H2;subst.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1; exfalso; auto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1; exfalso; auto.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto. 
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto. 
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    injection H1 as eq ;subst.
    2:{ simpl in H1. exfalso; auto. }
    right. right. exists p0.
    unfold read_instruction_shr.
    right.
    split;eauto.
    split.
    simpl. auto.
    intros.
    eapply in_inv in H1. destruct H1.
    2:{ simpl in H1. exfalso; auto. }
    injection H1 as eq;subst.    
    do 3 eexists. left.
    split.
    eapply in_eq.
    simpl.
    destruct (tctx_elt_dec_eq (p0 ◁ &shr{κ0} (own_ptr n ty))
    (p0 ◁ &shr{κ0} (own_ptr n ty)));
    destruct (tctx_elt_dec_eq (v ◁ &shr{κ0} ty) (v ◁ &shr{κ0} ty));
    tryfalse.
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto. 
  - eapply in_inv in H1.
    destruct H1; tryfalse.
    injection H1 as eq; subst.
    right. right.
    exists p0.
    unfold read_instruction_shr.
    right.
    split;eauto. 
    split;eauto.
    intros. eapply in_inv in H1.
    destruct H1.
    injection H1 as eq; subst.
    do 3 eexists.
    right. left. split.
    eapply in_eq.
    simpl.
    destruct (tctx_elt_dec_eq (p0 ◁ &shr{κ0} (&uniq{κ'} ty))
    (p0 ◁ &shr{κ0} (&uniq{κ'} ty)));
    destruct (tctx_elt_dec_eq (v ◁ &shr{κ0} ty) (v ◁ &shr{κ0} ty));
    tryfalse.
    simpl in H1. exfalso. eauto.
    simpl in H1. exfalso. eauto.
  - inversion H2;subst.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto. 
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
  - inversion H2;subst;inversion H3;subst.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.  
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    injection H1 as eq;subst.
    left. 
    eexists.
    split.
    eapply in_cons. eapply in_eq.
    eauto.
    simpl in H1.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto. 
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto. 
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    injection H1 as eq;subst.
    left. 
    eexists.
    split.
    eapply in_cons. eapply in_eq.
    eauto.
    simpl in H1.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto.
  - inversion H2;subst;inversion H3;subst.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.  
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H0.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    injection H1 as eq;subst.
    left. 
    eexists.
    split.
    eapply in_cons. eapply in_eq.
    eauto.
    simpl in H1.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto. 
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto. 
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    injection H1 as eq;subst.
    left. 
    eexists.
    split.
    eapply in_cons. eapply in_eq.
    eauto.
    simpl in H1.
    exfalso. eauto.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    eapply in_inv in H1.
    destruct H1; tryfalse.
    simpl in H1.
    exfalso. eauto.

    Unshelve. exact κ. exact κ.
    exact 0%nat. exact 0%nat. 
    exact κ0. exact 0%nat.
Qed.

Fixpoint capability_not_add_subtyping (ty1 ty2 :type)  {struct ty2}  : Prop :=
match ty2 with
| (own_ptr n' ty2') => match ty1 with 
                       | (own_ptr n ty1') => (ty1' = ty2' \/ capability_not_add_subtyping ty1' ty2' (*  \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *)  )
                       | _ => False
                       end
| (uniq_bor k' ty2') => match ty1 with 
                       | (uniq_bor k ty1') => (ty1' = ty2' \/ capability_not_add_subtyping ty1' ty2' (*  \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *) ) 
                       | _ => False
                       end
(* | product2 ty11 ty12 => match ty1 with
                       | product2 ty21 ty22 => ty11 = ty21 /\ ty12 = ty22 \/capability_not_add_subtyping ty21 ty11 /\ capability_not_add_subtyping ty22 ty12 
                       | (uninit n) => True(* capability_not_add_subtyping (uninit (my_type_system.size ty11)) ty11 /\ capability_not_add_subtyping (uninit (n-(my_type_system.size ty11))) ty12 \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *)
                       | _ => False
                       end *)
| _=> True
end.


Lemma capability_not_add_subtyping_tran :
forall ty2 ty1 ty3, 
  capability_not_add_subtyping ty1 ty2 ->
  capability_not_add_subtyping ty2 ty3 ->
 capability_not_add_subtyping ty1 ty3.
Proof.
(*   intros. generalize dependent ty2.  *)
  induction ty2; induction ty1;induction ty3;simpl in *;  intros;  try(exfalso; eapply H0); auto.
  destruct H;destruct H0; subst. left; auto. right. auto.
  right. auto. eapply IHty2 in H. right. eauto. auto.
  destruct H;destruct H0; subst. left; auto. right. auto.
  right. auto. eapply IHty2 in H. right. eauto. auto.
Qed.
   
Lemma safe_subtyping_capability_not_add E L (ty1 ty2 :type) :
  safe_subtyping E L ty1 ty2 ->
  capability_not_add_subtyping ty1 ty2.
Proof.
  intros.
  induction H; simpl; auto.
  destruct ty1; simpl; auto.
  destruct ty3; destruct ty1;destruct ty2; simpl in *;  try(exfalso; eapply IHsafe_subtyping2); auto.
  destruct IHsafe_subtyping1; destruct IHsafe_subtyping2; subst.
  left. auto. right. auto. right. auto. right. eapply capability_not_add_subtyping_tran; eauto.
  destruct IHsafe_subtyping1; destruct IHsafe_subtyping2; subst.
  left. auto. right. auto. right. auto. right. eapply capability_not_add_subtyping_tran; eauto.
Qed.

Fixpoint capability_not_add_subtyping2 (ty1 ty2 :type)  : Prop :=
match ty1,ty2 with
| (own_ptr n ty1'), (own_ptr n' ty2') => ((own_ptr n ty1') = (own_ptr n' ty2') \/ capability_not_add_subtyping2 ty1' ty2' (* \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *) )
| (uniq_bor k ty1'), (uniq_bor k' ty2') => (ty1' = ty2' \/ capability_not_add_subtyping2 ty1' ty2' (* \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *)) 
| (shr_bor k ty1'), (shr_bor k' ty2') => (ty1' = ty2' \/ capability_not_add_subtyping2 ty1' ty2' (* \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *)) 
| _ , (own_ptr n' ty2') => False
| _ , (uniq_bor k' ty2') => False
| _ , (shr_bor k' ty2') => False
| product2 ty21 ty22 , product2 ty11 ty12 => ty11 = ty21 /\ ty12 = ty22 \/capability_not_add_subtyping2 ty21 ty11 /\ capability_not_add_subtyping2 ty22 ty12 
                       (* \/ (exists E L ty31 ty32, safe_subtyping E L (product2 ty21 ty22)
      (product2 ty31 ty32) /\ safe_subtyping E L (product2 ty31 ty32)
      (product2 ty11 ty12)) *)

| (uninit n) , product2 ty11 ty12 => True
| _ ,product2 ty11 ty12 => False
| uninit n' , uninit n => n' = n
| _ , uninit n => False
| unit0 , unit0 => True
| _ , unit0 => False
| product2 ty11 ty12, _ => False
| _ , _ => True
end. 


Lemma capability_not_add_subtyping2_tran :
forall ty2 ty1 ty3, 
  capability_not_add_subtyping2 ty1 ty2 ->
  capability_not_add_subtyping2 ty2 ty3 ->
 capability_not_add_subtyping2 ty1 ty3.
Proof.
(*   intros. generalize dependent ty2.  *)
  induction ty2; induction ty1;induction ty3;simpl in *;  intros;  try(exfalso; eapply H0); auto.
  destruct H;destruct H0; subst. injection H as eq; subst. left; auto. right. injection H as eq; subst. auto.
  right. injection H0 as eq; subst. auto.  eapply IHty2 in H. right. eauto. auto.
  destruct H;destruct H0; subst. left; auto. right. auto.
  right. eauto. right. eapply IHty2 in H. eauto. auto.
  destruct H;destruct H0; subst. left; auto. right. auto.
  right. eauto. right. eapply IHty2 in H. eauto. auto.
  subst. auto. exfalso. auto.
  destruct H;destruct H0; subst. destruct H; destruct H0. subst. left; auto. right. destruct H. subst. auto.
  destruct H0. subst. right. auto.
  destruct H. destruct H0. right.
  split. eapply IHty2_1 in H. eauto. eauto.
  eapply IHty2_2 in H1. eauto. eauto.
Qed.


Lemma safe_subtyping_capability_not_add2 E L (ty1 ty2 :type) :
  safe_subtyping E L ty1 ty2 ->
  capability_not_add_subtyping2 ty1 ty2.
Proof.
  intros.
  induction H; simpl; auto.
  destruct ty1; simpl; auto.

  destruct ty3; destruct ty1;destruct ty2;
  simpl in *;  try(exfalso; eapply IHsafe_subtyping2); auto.
  destruct IHsafe_subtyping1; destruct IHsafe_subtyping2.
  injection H1 as eq. subst. left. auto. injection H1 as eq; subst.
  right. eauto.  injection H2 as eq;subst. right;auto.
  right. eapply capability_not_add_subtyping2_tran ;eauto.
  destruct IHsafe_subtyping1; destruct IHsafe_subtyping2; subst.
  left. auto. right. eauto. right;auto.
  right. eapply capability_not_add_subtyping2_tran ;eauto.
  destruct IHsafe_subtyping1; destruct IHsafe_subtyping2; subst.
  left. auto. right. eauto. right;auto.
  right. eapply capability_not_add_subtyping2_tran ;eauto.
  subst. auto. exfalso. eauto.
  destruct IHsafe_subtyping1; destruct IHsafe_subtyping2; subst.
  destruct H1; destruct H2; subst.
  left. auto. destruct H1. subst. right. auto.
  right. destruct H2; subst. auto.
  destruct H1; destruct H2. right.
  split. eapply capability_not_add_subtyping2_tran ;eauto.
  eapply capability_not_add_subtyping2_tran ;eauto.
Qed.

Fixpoint  type_in_product ty1 ty2 {struct ty2} : Prop :=
match ty2 with
| product2 ty1' ty2' => ty1 = ty1' \/ type_in_product ty1 ty2'
| _ => False
end
.
(*
Compute(product (int::bool::nil) ). 
*)
Fixpoint capability_not_add_subtyping3 (ty1 ty2 :type)  : Prop :=
match ty1, ty2 with
| (own_ptr n ty1'), (own_ptr n' ty2') => ((own_ptr n ty1') = (own_ptr n' ty2') \/ capability_not_add_subtyping3 ty1' ty2' (* \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *) )
| (uniq_bor k ty1'), (uniq_bor k' ty2') => (ty1' = ty2' \/ capability_not_add_subtyping3 ty1' ty2' (* \/ exists E L ty3',safe_subtyping E L ty1 ty3' /\ safe_subtyping E L ty3' ty2 *)) 
| _ , (own_ptr n' ty2') => False
| _ , (uniq_bor k' ty2') => False
| product2 ty21 ty22 , product2 ty11 ty12 => ty11 = ty21 /\ ty12 = ty22 \/capability_not_add_subtyping3 ty21 ty11 /\ capability_not_add_subtyping3 ty22 ty12 
                       \/ ty1 = ty11 \/ capability_not_add_subtyping3 ty1 ty12

| (uninit n) , product2 ty11 ty12 => True
| _ ,product2 ty11 ty12 => ty1 = ty11 \/  capability_not_add_subtyping3 ty1 ty12
| uninit n' , uninit n => n' = n
| _ , uninit n => False
(* | (sum tyl1), (sum tyl2) => match tyl1, tyl2 with
                            | ty1'::tyl1', nil => False
                            | nil , ty2'::tyl2' => False
                            | nil, nil => True
                            | ty1'::tyl1', ty2'::tyl2' => 
                                capability_not_add_subtyping2 ty1' ty2' /\ capability_not_add_subtyping2 (sum tyl1') (ty2')
                            end  *)
| unit0 , unit0 => True
| _ , unit0 => False
| product2 ty11 ty12, _ => False
| int , int  => True
| bool, bool => True
| _ , int => False
| _ , bool => False
| _ , _ => True
end. 


Definition capability_own_split_merge (T1 T2 :tctx ) : Prop := 
(exists tyl p n T T', (T1 = T ++ (hasty_ptr_offsets p (own_ptr n) tyl 0) ++ T'
                       /\ T2 = T ++ [p ◁ own_ptr n $ product tyl] ++ T'
          \/   T2 = T ++ (hasty_ptr_offsets p (own_ptr n) tyl 0) ++ T'
                       /\ T1 = T ++ [p ◁ own_ptr n $ product tyl] ++ T')).

Definition capability_uniq_split_merge (T1 T2 :tctx ) : Prop := 
(exists tyl p κ T T', (T1 = T ++ (hasty_ptr_offsets p (uniq_bor κ) tyl 0) ++ T'
                       /\ T2 = T ++ [p ◁ uniq_bor κ $ product tyl] ++ T'
          \/   T2 = T ++ (hasty_ptr_offsets p (uniq_bor κ) tyl 0) ++ T'
                       /\ T1 = T ++ [p ◁ uniq_bor κ $ product tyl] ++ T')).

Definition capability_shr_bor_split_merge (T1 T2 :tctx ) : Prop := 
(exists tyl p κ T T', (T1 = T ++ (hasty_ptr_offsets p (shr_bor κ) tyl 0) ++ T'
                       /\ T2 = T ++ [p ◁ shr_bor κ $ product tyl] ++ T'
          \/   T2 = T ++ (hasty_ptr_offsets p (shr_bor κ) tyl 0) ++ T'
                       /\ T1 = T ++ [p ◁ shr_bor κ $ product tyl] ++ T')).

Definition capability_split_merge (T1 T2 :tctx ) : Prop := 
     capability_own_split_merge T1 T2 
  \/ capability_uniq_split_merge T1 T2
  \/ capability_shr_bor_split_merge T1 T2.

Fixpoint get_OffsetOp_left_min (p:path) : path :=
match p with
| (p' +ₗ a) =>  get_OffsetOp_left_min p' 
| _ => p
end.

Fixpoint get_OffsetOp_left_list (p:path)  : list path :=
p :: (
match p with
| (p' +ₗ a) =>  p' :: get_OffsetOp_left_list p' 
| _ => nil
end )
.

Lemma get_OffsetOp_left_list_tran
  :forall x p x2,
     In x (get_OffsetOp_left_list p ) ->
     In x2 (get_OffsetOp_left_list x ) ->
     In x2 (get_OffsetOp_left_list p ).
Proof.
  induction x;try(
  intros; simpl in H0; destruct H0; subst; auto; exfalso; eapply H0).
  destruct op;try(
  intros; simpl in H0; destruct H0; subst; auto; exfalso; eapply H0).
  intros. simpl in *.
  destruct H0. subst. auto.
  destruct H0. subst.
  induction p; try( simpl in H; destruct H; tryfalse; exfalso;eapply H).
  destruct op; try( simpl in H; destruct H; tryfalse; exfalso;eapply H).
  simpl in H. destruct H. eapply expr_beq_correct in H. simpl in H.
  (* Search (expr_beq). *)
  eapply andb_prop_elim in H.
  destruct H. eapply expr_beq_correct in H. eapply expr_beq_correct in H0.
  simpl. right. left. auto. destruct H. subst.
  simpl. right. right. right. left. auto.
  simpl. right. right. eapply IHp1. auto.

  eapply IHx1;eauto.
  induction p; try( simpl in H; destruct H; tryfalse; exfalso;eapply H).
  destruct op; try( simpl in H; destruct H; tryfalse; exfalso;eapply H).
  simpl in H. destruct H. eapply expr_beq_correct in H. simpl in H.
  (* Search (expr_beq). *)
  eapply andb_prop_elim in H.
  destruct H. eapply expr_beq_correct in H. eapply expr_beq_correct in H1.
  simpl. right. left. auto. destruct H. subst.
  simpl. right. right. right. left. auto.
  simpl. right. right. eapply IHp1. auto.
Qed.

Fixpoint get_OffsetOp_left_list' (p:path)  : list path :=
match p with
| (p' +ₗ a) =>  p' :: get_OffsetOp_left_list' p' 
| _ => nil
end 
.

Lemma get_OffsetOp_left_list_tran' :forall x p x2,
     In x (get_OffsetOp_left_list' p ) ->
     In x2 (get_OffsetOp_left_list' x ) ->
     In x2 (get_OffsetOp_left_list' p ).
Proof.
  induction x;try(
  intros; simpl in H0; exfalso; eapply H0).
  destruct op;try(
  intros; simpl in H0; exfalso; eapply H0).
  intros. simpl in *.
  destruct H0. subst. 

  induction p; try( simpl in H;tryfalse).
  destruct op; try( simpl in H;tryfalse).
  simpl in H. destruct H. subst.

  simpl. right. left. auto.
  simpl. right. eapply IHp1. auto.

  eapply IHx1;eauto.
  induction p; try( simpl in H; exfalso;eapply H).
  destruct op; try( simpl in H; exfalso;eapply H).
  simpl in H. destruct H. subst.
  simpl. right. left. auto.
  simpl. right. eapply IHp1. auto.
Qed.


Fixpoint get_p_own_size_in_tctx (p:path) (T1:tctx): nat := 
match T1 with
| t::T1' => match t with
            | TCtx_hasty p' (own_ptr n ty) => 
                  if expr_beq (get_OffsetOp_left_min p') (get_OffsetOp_left_min p) 
                  then (n + get_p_own_size_in_tctx p T1')%nat
                  else (0%nat + get_p_own_size_in_tctx p T1')%nat
            | _ => 0 + get_p_own_size_in_tctx p T1'
            end
| nil => 0
end
.

Fixpoint get_p_own_uniq_size_in_tctx (p:path) (T1:tctx): nat := 
match T1 with
| t::T1' => match t with
            | TCtx_hasty p' (own_ptr n ty) => 
                  if expr_beq (get_OffsetOp_left_min p') p 
                  then (n + get_p_own_size_in_tctx p T1')%nat
                  else (0%nat + get_p_own_uniq_size_in_tctx p T1')%nat
            | TCtx_hasty p' (uniq_bor k ty) => 
                  if expr_beq (get_OffsetOp_left_min p') p 
                  then (my_type_system.size ty + get_p_own_size_in_tctx p T1')%nat
                  else (0 + get_p_own_uniq_size_in_tctx p T1')%nat
            | _ => 0 + get_p_own_size_in_tctx p T1'
            end
| nil => 0
end
.




Definition capability_not_add_part1 (T1 T2 :tctx ) : Prop := 
  forall tctx_elt p ty n,
         In tctx_elt T2 -> 
         tctx_elt = TCtx_hasty p (own_ptr n ty) ->
            (exists ty' tctx_elt' , tctx_elt' = TCtx_hasty p (own_ptr n ty')
            /\ In tctx_elt' T1 
            /\ capability_not_add_subtyping2 ty' ty)
         \/
            (exists  k ty' tctx_elt' , tctx_elt' = TCtx_blocked p k (own_ptr n ty')
            /\ In tctx_elt' T1 
            /\ capability_not_add_subtyping2 ty' ty
            )
 .

 
Definition capability_not_add_part2 (T1 T2 :tctx ) : Prop := 
  forall tctx_elt p k ty,
         In tctx_elt T2 -> 
         tctx_elt = TCtx_hasty p (uniq_bor k ty) ->
         (exists tctx_elt' n' ty' , tctx_elt' = TCtx_hasty p (own_ptr n' ty')
         /\ In tctx_elt' T1 
         /\ capability_not_add_subtyping2 ty' ty
         ) \/
        (exists k' ty' tctx_elt' , (tctx_elt' = TCtx_hasty p (uniq_bor k' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
        \/
         (exists n k ty' tctx_elt' , tctx_elt' = TCtx_blocked p k (own_ptr n ty')
            /\ In tctx_elt' T1 
            /\ capability_not_add_subtyping2 ty' ty)
        \/
         (exists k' k'' ty' tctx_elt' , (tctx_elt' = TCtx_blocked p k' (uniq_bor k'' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
.

Definition capability_not_add_part3 (T1 T2 :tctx ) : Prop := 
  forall tctx_elt p k n ty,
         In tctx_elt T2 -> 
         tctx_elt = TCtx_blocked p k (own_ptr n ty) ->
         (exists tctx_elt' ty', tctx_elt' = TCtx_hasty p (own_ptr n ty')
         /\ In tctx_elt' T1 
         /\ capability_not_add_subtyping2 ty' ty)
       \/(
          exists ty' k', In (TCtx_blocked p k' (own_ptr n ty')) T1 
          /\ capability_not_add_subtyping2 ty' ty
          )
         
.

Definition capability_not_add_part4 (T1 T2 :tctx ) : Prop := 
  forall tctx_elt p k n ty,
         In tctx_elt T2 -> 
         tctx_elt = TCtx_blocked p k (uniq_bor n ty) ->
         (exists ty' k' tctx_elt' , tctx_elt' = TCtx_hasty p (uniq_bor k' ty')
         /\ In tctx_elt' T1
         /\ capability_not_add_subtyping2 ty' ty)
       \/
         (exists n' ty' tctx_elt' , tctx_elt' = TCtx_hasty p (own_ptr n' ty')
         /\ In tctx_elt' T1 
         /\ capability_not_add_subtyping2 ty' ty)
       \/ 
         (exists ty' k' k'', In (TCtx_blocked p k' (uniq_bor k'' ty')) T1 
           /\ capability_not_add_subtyping2 ty' ty
          )
       \/ 
         (exists n' k' ty' tctx_elt' , tctx_elt' = TCtx_blocked p k' (own_ptr n' ty')
            /\ In tctx_elt' T1 
            /\ capability_not_add_subtyping2 ty' ty)
.


 
Definition capability_not_add_part5 (T1 T2 :tctx ) : Prop := 
  forall tctx_elt p k ty,
         In tctx_elt T2 -> 
         tctx_elt = TCtx_hasty p (shr_bor k ty) ->
        (exists k' ty' tctx_elt' , (tctx_elt' = TCtx_hasty p (shr_bor k' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
         \/
         (exists tctx_elt' n' ty' , tctx_elt' = TCtx_hasty p (own_ptr n' ty')
         /\ In tctx_elt' T1 
         /\ capability_not_add_subtyping2 ty' ty
         ) \/
        (exists k' ty' tctx_elt' , (tctx_elt' = TCtx_hasty p (uniq_bor k' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
        \/
         (exists n k ty' tctx_elt' , tctx_elt' = TCtx_blocked p k (own_ptr n ty')
            /\ In tctx_elt' T1 
            /\ capability_not_add_subtyping2 ty' ty)
        \/
         (exists k' k'' ty' tctx_elt' , (tctx_elt' = TCtx_blocked p k' (uniq_bor k'' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
        \/
        (exists k' k'' ty' tctx_elt' , (tctx_elt' = TCtx_blocked p k' (shr_bor k'' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)

.
  
Definition capability_not_add_part6 (T1 T2 :tctx ) : Prop := 
  forall tctx_elt p k k''' ty,
         In tctx_elt T2 -> 
         tctx_elt = TCtx_blocked p k (shr_bor k''' ty) ->
        (exists k' ty' tctx_elt' , (tctx_elt' = TCtx_hasty p (shr_bor k' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
         \/
        (exists k' k'' ty' tctx_elt' , (tctx_elt' = TCtx_blocked p k' (shr_bor k'' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
         \/
         (exists tctx_elt' n' ty' , tctx_elt' = TCtx_hasty p (own_ptr n' ty')
         /\ In tctx_elt' T1 
         /\ capability_not_add_subtyping2 ty' ty
         ) \/
        (exists k' ty' tctx_elt' , (tctx_elt' = TCtx_hasty p (uniq_bor k' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
        \/
         (exists n k ty' tctx_elt' , tctx_elt' = TCtx_blocked p k (own_ptr n ty')
            /\ In tctx_elt' T1 
            /\ capability_not_add_subtyping2 ty' ty)
        \/
         (exists k' k'' ty' tctx_elt' , (tctx_elt' = TCtx_blocked p k' (uniq_bor k'' ty') )
         /\ In tctx_elt' T1 /\ capability_not_add_subtyping2 ty' ty)
.
  

Lemma safe_tctx_incl_capability_not_add_tran' :
forall T2 T1 T3,  capability_not_add_part1 T1
                      T2
                    ∧ capability_not_add_part2
                        T1 T2
                    ∧ capability_not_add_part3
                        T1 T2
                    ∧ capability_not_add_part4
                        T1 T2
                    ∧ capability_not_add_part5
                        T1 T2
                    ∧ capability_not_add_part6
                        T1 T2
                    ->
                  capability_not_add_part1 T2
                      T3
                    ∧ capability_not_add_part2
                        T2 T3
                    ∧ capability_not_add_part3
                        T2 T3
                    ∧ capability_not_add_part4
                        T2 T3
                    ∧ capability_not_add_part5
                        T2 T3
                    ∧ capability_not_add_part6
                        T2 T3
                    ->
                capability_not_add_part1 T1 T3
                ∧ capability_not_add_part2 T1 T3
                ∧ capability_not_add_part3 T1 T3
                ∧ capability_not_add_part4 T1 T3
                ∧ capability_not_add_part5 T1 T3
                ∧ capability_not_add_part6 T1 T3
.
Proof.
  intros. 
  destruct H. destruct H1. destruct H2.
  destruct H0. destruct H4. destruct H5.
  destruct H3. destruct H6.
  destruct H7. destruct H8.
  rename H7 into Hp5; rename H8 into Hp5'.
  rename H9 into Hp6; rename H10 into Hp6'.
  split. 2:split. 3:split. 4:split. 5:split.
  - unfold capability_not_add_part1.
    intros.
    eapply H0 in H7. destruct H7. eauto.
    do 3 destruct H7. destruct H9. subst.
    eapply H in H9.
    destruct H9. eauto. 
    do 3 destruct H7. destruct H8. subst.
    left. do 3 eexists.
    split;eauto. split. eauto.
    eapply capability_not_add_subtyping2_tran; eauto.
    do 4 destruct H7. destruct H8. subst.
    right. do 4 eexists. eauto.
    split. eauto.
    eapply capability_not_add_subtyping2_tran; eauto.
    do 4 destruct H7. destruct H9. subst.
    eapply H2 in H9. destruct H9. eauto.
    do 3 destruct H7. destruct H8. subst.
    left. do 3 eexists. eauto.
    split. eauto. eapply capability_not_add_subtyping2_tran; eauto.
    right. do 3 destruct H7. do 4 eexists. eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran; eauto.
  - unfold capability_not_add_part2. intros.
    eapply H4 in H7. destruct H7. eauto.
    do 4 destruct H7. destruct H9. 
    subst. eapply H in H9.
    destruct H9. eauto.
    do 3 destruct H7. destruct H8. subst.
    left. do 5 eexists.
    eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    do 4 destruct H7. destruct H8. subst.
    right. right. left. do 5 eexists.
    eauto. split; eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. do 4 destruct H7.
    destruct H9. subst.
    eapply H1 in H9. destruct H9. eauto.
    do 4 destruct H7. destruct H8. subst.
    left. do 4 eexists. eauto.
    split. eauto. eapply capability_not_add_subtyping2_tran; eauto.
    destruct H7. do 4 destruct H7. destruct H8. subst.
    right. left.
    do 4 eexists. eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. do 5 destruct H7. destruct H8. subst.
    right. right. left. do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    do 5 destruct H7. destruct H8. subst.
    right. right. right. do 5 eexists.
    eauto. split. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    do 5 destruct H7. destruct H9. subst.
    eapply H2 in H9. destruct H9. eauto.
    do 3 destruct H7. destruct H8. subst.
    left. do 4 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    right. right. left. do 3 destruct H7. do 5 eexists.
    split;eauto. split;eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
    do 5 destruct H7. destruct H9. subst.
    eapply H3 in H9. destruct H9. eauto.
    simpljoin1. 
    right. left. do 4 eexists. eauto.
    split. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    left. do 4 eexists.
    eauto. split. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right.
    do 5 eexists. eauto.
    split. eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1. 
    right. right. left.
    do 5 eexists. eauto.
    split;eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
  - unfold capability_not_add_part3.
    intros. subst.
    eapply H5 in H7. destruct H7. eauto.
    do 3 destruct H7. destruct H8. subst.
    eapply H in H8. destruct H8. eauto.
    do 3 destruct H7. destruct H8. subst.
    left. do 3 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    do 4 destruct H7. destruct H8. subst.
    right. do 3 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    do 3 destruct H7.
    eapply H2 in H7. destruct H7. eauto.
    do 3 destruct H7. destruct H9. subst.
    left. do 3 eexists. eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    right. do 3 destruct H7.
    do 3 eexists. eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
  - unfold capability_not_add_part4.
    intros. subst. eapply H6 in H7.
    destruct H7. eauto.
    do 4 destruct H7. destruct H8. subst.
    eapply H1 in H8. destruct H8. eauto.
    do 4 destruct H7. destruct H8. subst.
    right. left. do 4 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. do 4 destruct H7. destruct H8. subst.
    left. do 4 eexists. eauto. 
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    do 5 destruct H7. destruct H8.
    subst. right. right. right.
    do 5 eexists. eauto. split; eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1. right. right. left.
    do 4 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. do 4 destruct H7. destruct H8. subst.
    eapply H in H8. destruct H8. eauto.
    do 3 destruct H7. destruct H8. subst.
    right. left. do 4 eexists. eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    do 4 destruct H7. destruct H8. subst.
    right. right. right. do 5 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. do 4 destruct H7.
    eapply H3 in H7. destruct H7. eauto.
    do 3 destruct H7. destruct H7. destruct H9. subst.
    left. do 4 eexists. eauto. split.
    eauto. eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. do 4 destruct H7. destruct H9. subst.
    right. left. do 4 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. do 4 destruct H7.
    right. right. left. do 4 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    do 5 destruct H7. destruct H9. subst.
    right. right. right. do 5 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    do 5 destruct H7. destruct H8. 
    eapply H2 in H8. destruct H8. eauto. subst. 
    destruct H8. do 2 destruct H7. destruct H8. subst.
    right. left. do 4 eexists. eauto.
    split;eauto. eapply capability_not_add_subtyping2_tran;eauto.
    do 3 destruct H8. subst. right. right. right.
    do 5 eexists. eauto. split. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
   
  - unfold capability_not_add_part5.
    intros. subst.
    unfold capability_not_add_part5 in Hp5'.
    eapply Hp5' in H7. 2:eauto.
    destruct H7.
    simpljoin1.
    eapply Hp5 in H8. 
    destruct H8. eauto.
    simpljoin1.
    left. do 4 eexists.
    eauto. split.
    eauto. eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.  

    destruct H7.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. right.
    do 5 eexists. eauto.
    split. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.  

    destruct H7. simpljoin1.
    eapply H in H8.
    destruct H8. eauto. simpljoin1.
    right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    eapply H1 in H8.
    destruct H8. eauto.
    simpljoin1.
    right;left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    eapply H2 in H8. destruct H8. eauto.
    simpljoin1.
    right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7.
    simpljoin1.
    eapply H3 in H8. destruct H8. eauto.
    simpljoin1.
    right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.


    simpljoin1.
    eapply Hp6 in H8.
    destruct H8. eauto.
    simpljoin1.
    left. 
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. right. right.
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. left.
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. left.
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. left.
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. left.
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

  - unfold capability_not_add_part6.
    intros.
    subst.
    eapply Hp6' in H7.
    destruct H7. eauto.
    simpljoin1.
    eapply Hp5 in H8.
    destruct H8. eauto. simpljoin1.
    left. 
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. right. left. 
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto. 
    destruct H7.
    simpljoin1.
    right. right. right. left. 
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. right. right. right. left. 
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. right. right. right. right. 
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. left.
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7.
    simpljoin1.
    eapply Hp6 in H8. destruct H8. eauto.
    simpljoin1.
    left.
    do 4 eexists. eauto.
    split;eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. left.
    do 4 eexists. eauto.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. left.
    do 4 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. left.
    do 4 eexists. eauto.
    split;eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. right. left.
    do 4 eexists. eauto.
    split;eauto.  split;eauto. 
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1. 
    right. right. right. right. right.
    do 4 eexists.
    split;eauto. split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    eapply H in H8.
    destruct H8. eauto. simpljoin1.
    right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    eapply H1 in H8.
    destruct H8. eauto.
    simpljoin1.
    right. right;left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7. simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. right. 
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7. simpljoin1.
    eapply H2 in H8. destruct H8. eauto.
    simpljoin1.
    right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

    destruct H7.
    simpljoin1.
    eapply H3 in H8. destruct H8. eauto.
    simpljoin1.
    right. right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. right. left.
    do 5 eexists. eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    destruct H7.
    simpljoin1.
    right. right. right. right. right.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto.
    split;eauto.
    eapply capability_not_add_subtyping2_tran;eauto.

Qed.

  
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Classical.

Lemma safe_subtyping_unit0: forall ty E L , 
 safe_subtyping E L unit0 ty -> ty ≠ unit0 -> False.
Proof.
  intros. induction H0.  
  assert(forall k ty, &shr{k} ty ≠ unit0). tryfalse.
  assert(forall k ty, &uniq{k} ty ≠ unit0). tryfalse.
  assert(forall n ty, own_ptr n ty ≠ unit0). tryfalse.
  assert(forall n, uninit n ≠ unit0). tryfalse.
  assert(forall ty11 ty21 , product2 ty11 ty21 ≠ unit0). tryfalse.
  assert(forall tyl1 , sum tyl1 ≠ unit0). tryfalse.
  induction H. specialize (H0 κ1). specialize (H0 ty1). tryfalse. 
  specialize (H1 κ1). specialize (H1 ty1). tryfalse.
  specialize (H1 κ1). specialize (H1 ty1). tryfalse.
  specialize (H2 n). specialize (H2 ty1). tryfalse.
  auto.
  assert(H':= H0).
  eapply IHsafe_subtyping1 in H'; eauto. subst.
  eapply IHsafe_subtyping2 in H0; eauto.
  specialize (H3 n). tryfalse.
  specialize (H4 ty11). specialize (H4 ty21). tryfalse.
  specialize (H5 tyl1). tryfalse.
Qed.

Lemma unit0_neq :  (forall k ty, &shr{k} ty ≠ unit0) /\
  (forall k ty, &uniq{k} ty ≠ unit0) /\
  (forall n ty, own_ptr n ty ≠ unit0) /\
  (forall n, uninit n ≠ unit0) /\
  (forall ty11 ty21 , product2 ty11 ty21 ≠ unit0) /\
  (forall tyl1 , sum tyl1 ≠ unit0). 
Proof.
  split. tryfalse.
  split. tryfalse.
  split. tryfalse.
  split. tryfalse.
  split. tryfalse.
  tryfalse.
Qed.

Lemma safe_subtyping_own_ptr_unit0 :
forall E L n1 n ty, safe_subtyping E L (own_ptr n1 unit0)
      (own_ptr n ty) -> ty ≠ unit0 ->
False.
Proof.
  intros. rename H0 into teq. (* induction H0. *) 
  assert(forall k ty, &shr{k} ty ≠ (own_ptr n1 unit0)). tryfalse.
  assert(forall k ty, &uniq{k} ty ≠ (own_ptr n1 unit0)). tryfalse.
  assert(forall n ty, ty ≠ unit0 -> own_ptr n ty ≠ (own_ptr n1 unit0)). tryfalse. 
  assert(forall n, uninit n ≠ (own_ptr n1 unit0)). tryfalse.
  assert(forall ty11 ty21 , product2 ty11 ty21 ≠ (own_ptr n1 unit0)). tryfalse.
  assert(forall tyl1 , sum tyl1 ≠ (own_ptr n1 unit0)). tryfalse.
  assert((own_ptr n1 unit0) ≠ (own_ptr n ty) ). intros. unfold not. 
  intros. injection H6 as eq. tryfalse.
  induction H. specialize (H1 κ1). specialize (H1 ty1). tryfalse. 
  specialize (H1 κ1). specialize (H1 ty1). tryfalse.
  specialize (H1 κ1). specialize (H1 ty1). tryfalse.
  { specialize (H2 n0). specialize (H2 ty1). assert(ty1 ≠ unit0 \/ ty1 = unit0) by tauto.  destruct H7; eauto.
  eapply H2 in H7. tryfalse.
  subst. eapply IHsafe_subtyping. tryfalse. tryfalse.  tryfalse.  tryfalse.  tryfalse.  tryfalse. tryfalse. }
  tryfalse.
  1:{ eapply IHsafe_subtyping1. eauto. eauto. eauto. eauto. eauto. eauto.
  unfold not. intros. subst. eapply IHsafe_subtyping2.
  eauto. eauto. eauto. eauto. eauto. eauto. auto. }
  specialize (H3 n0). tryfalse.
  specialize (H4 ty11). specialize (H4 ty21). tryfalse.
  specialize (H5 tyl1). tryfalse.
Qed.

(* Lemma safe_subtyping_uniq_ptr_unit0 :
forall E L n ty, safe_subtyping E L (uniq_bor n unit0)
      (uniq_bor n ty) -> ty ≠ unit0 -> False.
Proof.

Qed.  *)


Lemma safe_subtyping_own_ptr :
forall ty2 E L n ty1 , safe_subtyping E L ty1
      (own_ptr n ty2) -> exists n' ty', ty1 = own_ptr n' ty'.
Proof.
  intros.
  remember (own_ptr n ty2).
  generalize dependent n. generalize dependent ty2. 
 
  induction H; tryfalse.
  do 2 eexists. eauto. subst.
  do 2 eexists. eauto.
  subst.
  intros.

  eapply IHsafe_subtyping2 in Heqt.
  destruct Heqt. destruct H1.
  eapply IHsafe_subtyping1. eauto.
Qed.

Lemma safe_subtyping_own_ptr' :
forall ty2 E L n ty1 , safe_subtyping E L ty1
      (own_ptr n ty2) -> exists ty', ty1 = own_ptr n ty'.
Proof.
  intros.
  remember (own_ptr n ty2).
  generalize dependent n. generalize dependent ty2. 
 
  induction H; tryfalse.
   intros. injection Heqt as eq;subst.
  eexists. eauto. subst.
  intros.
  eexists. eauto.
  subst.
  intros.

  eapply IHsafe_subtyping2 in Heqt.
  destruct Heqt.
  eapply IHsafe_subtyping1. eauto.
Qed.

Lemma safe_subtyping_uniq_ptr :
forall ty2 E L n ty1 , safe_subtyping E L ty1
      (uniq_bor n ty2) -> exists n' ty', ty1 = uniq_bor n' ty'.
Proof.
  intros.
  remember (uniq_bor n ty2).
  generalize dependent n. generalize dependent ty2. 
 
  induction H; tryfalse.
  do 2 eexists. eauto.
  do 2 eexists. eauto.
  do 2 eexists. eauto.
  intros.

  eapply IHsafe_subtyping2 in Heqt.
  destruct Heqt. destruct H1.
  eapply IHsafe_subtyping1. eauto.
Qed.

Lemma safe_subtyping_shr_ptr :
forall ty2 E L n ty1 , safe_subtyping E L ty1
      (shr_bor n ty2) -> exists n' ty', ty1 = shr_bor n' ty'.
Proof.
  intros.
  remember (shr_bor n ty2).
  generalize dependent n. generalize dependent ty2. 
 
  induction H; tryfalse.
  do 2 eexists. eauto.
  do 2 eexists. eauto.

  intros.

  eapply IHsafe_subtyping2 in Heqt.
  destruct Heqt. destruct H1.
  eapply IHsafe_subtyping1. eauto.
Qed.

Lemma safe_subtyping_own_size_eq :
forall E L x x0 n ty,
  safe_subtyping E L (own_ptr x x0) (own_ptr n ty) ->
  x = n.
Proof.
  intros.

  
  remember (own_ptr x x0).
  eapply safe_subtyping_own_ptr' in H.
  simpljoin1.
  injection H as eq;subst. 
  auto.
Qed.
  

Lemma safe_tctx_incl_capability_not_add':
forall E L T1 T2 ,safe_tctx_incl E L T2 T1 -> 
(* forall tyl p n T T', T1 ≠ T ++ (hasty_ptr_offsets p (own_ptr n) tyl 0) ++ T' ->
forall p n tyl, T1 ≠ T ++ [p ◁ own_ptr n $ product tyl] ++ T' -> *)
    capability_not_add_part1 T2 T1 /\ capability_not_add_part2 T2 T1 /\
    capability_not_add_part3 T2 T1 /\ capability_not_add_part4 T2 T1 
    /\ capability_not_add_part5 T2 T1 /\ capability_not_add_part6 T2 T1
  .
Proof.
  intros. (* rename H0 into Hfalse1; rename H1 into Hfalse2.
  rename p into fp; rename p0 into fp0; 
  rename n into fn; rename n0 into fn0. *)
  induction H;subst.
  + (* left. *) split.
    remember ty1. remember ty2.
    unfold capability_not_add_part1. intros.
    apply in_inv in H0. destruct H0. subst.
    destruct ty2; tryfalse.
    assert(H3:=H).
    eapply safe_subtyping_own_ptr in H. do 2 destruct H.
    subst. injection H1 as eq. subst.
    left.
    do 3 eexists. split; eauto.
    split; eauto.  
    eapply list_elem_of_In. eapply list_elem_of_singleton.
    eapply safe_subtyping_own_size_eq in H3. subst. eauto.
    eapply safe_subtyping_capability_not_add2 in H3.
    destruct H3. injection H as eq;subst. destruct ty;simpl;auto.
    eauto.
    assert(~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part2. intros.
    apply in_inv in H0. destruct H0. subst.
    destruct ty2; tryfalse.
    assert(H3:=H). 
    eapply safe_subtyping_uniq_ptr in H. do 2 destruct H.
    subst. injection H1 as eq. subst.
    right. left.
    do 4 eexists. eauto. split; eauto.
    eapply list_elem_of_In. eapply list_elem_of_singleton. auto.
    eapply safe_subtyping_capability_not_add2 in H3.
    simpl in H3. destruct H3. subst. destruct ty;simpl;auto.
    eauto.
    assert(~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split. unfold capability_not_add_part3.
    intros. apply in_inv in H0. destruct H0. subst.
    destruct ty2;tryfalse.
    simpl in H0;exfalso;auto.
    split.
    unfold capability_not_add_part4.
    intros. apply in_inv in H0. destruct H0. subst.
    destruct ty2;tryfalse.
    simpl in H0;exfalso;auto.
    split.
    unfold capability_not_add_part5.
    intros. apply in_inv in H0. destruct H0. subst.
    destruct ty2;tryfalse.
    assert(H':= H).
    eapply safe_subtyping_shr_ptr in H. do 2 destruct H. subst.
    injection H1 as eq;subst.
    left. do 5 eexists.
    eapply in_eq.
    eapply safe_subtyping_capability_not_add2 in H'.
    simpl in H'.  destruct H'.
    subst. destruct ty;simpl;eauto.
    eauto.
    simpl in H0. exfalso. eauto.
    unfold capability_not_add_part6.
    intros. apply in_inv in H0. destruct H0. subst.
    destruct ty2;tryfalse.
    simpl in H0;exfalso;auto.
  + split. unfold capability_not_add_part1. intros.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    simpl in H0. exfalso;auto.
    split. unfold capability_not_add_part2. intros.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    simpl in H0. exfalso;auto.
    split. unfold capability_not_add_part3. intros.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    simpl in H0. exfalso;auto.
    split. unfold capability_not_add_part4. intros.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    simpl in H0. exfalso;auto.
    split.
    unfold capability_not_add_part5.
    intros.
    apply in_inv in H0. destruct H0. subst;tryfalse.
    injection H1 as eq. subst.
    left. do 4 eexists.
    eauto. split. eapply in_eq.
    destruct ty0;simpl;eauto.
    apply in_inv in H0. destruct H0. subst;tryfalse.
    injection H1 as eq. subst.
    left. do 4 eexists.
    eauto. split. eapply in_eq.
    destruct ty0;simpl;eauto. 
    simpl in H0; exfalso; eauto.
    unfold capability_not_add_part6. intros.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    apply in_inv in H0. destruct H0. inversion H;subst;tryfalse.
    simpl in H0. exfalso;auto.
  + 
    (* left.  *)split. generalize dependent T2.
    induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part1.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros. 
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1.
    unfold capability_not_add_part1. intros.
    apply in_inv in H2; destruct H2.  subst. (* left. *) 
    left.
    exists ty. exists (p ◁ own_ptr n ty). 
    split. auto. split. auto. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here. 
    destruct ty;simpl; eauto. eauto.
    split.  
    generalize dependent T2. induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part2.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part2. intros. 
    apply in_inv in H2; destruct H2.  subst.
    right. left.
    exists k. exists ty. exists (p ◁ &uniq{k} ty). 
    split. auto. split. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here.
    destruct ty; simpl ; auto.
    eauto.
    split.  
    generalize dependent T2. induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part3.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part3. intros. 
    apply in_inv in H2; destruct H2.  subst.
    right.
    exists ty. exists k. 
    split. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here.
    destruct ty; simpl ; auto.
    eauto.
    split.
    generalize dependent T2. induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part4.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part4. intros. 
    apply in_inv in H2; destruct H2.  subst.
    right. right. left.
    exists ty. exists k. exists n. 
    split. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here.
    destruct ty; simpl ; auto.
    eauto.
    split. 
    generalize dependent T2. induction T1.  intros.

    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part5.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part5. intros. 
    apply in_inv in H2; destruct H2.  subst.
    left.
    exists k. exists ty. eexists. 
    split. eauto. split. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here.
    destruct ty; simpl ; auto.
    eapply H1; eauto.
    generalize dependent T2. induction T1.  intros.

    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part6.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part6. intros. 
    apply in_inv in H2; destruct H2.  subst.
    right. left.
    exists k. exists k'''. exists ty. eexists. 
    split. eauto. split. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here.
    destruct ty; simpl ; auto.
    eapply H1; eauto.

  + split.
    unfold capability_not_add_part1. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split. 
    unfold capability_not_add_part2. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part3. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part4. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part5.
    intros. subst. eapply in_inv in H0.
    destruct H0.
    injection H0 as eq;subst.
    right. right. left.
    do 4 eexists.
    eauto. split ;eauto.
    eapply in_eq.
    destruct ty0;simpl; eauto.
    simpl in H0. exfalso; eauto.
    unfold capability_not_add_part6. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
  + split.
    unfold capability_not_add_part1. intros.
    eapply in_inv in H. destruct H. subst; tryfalse.
    eapply in_inv in H. destruct H. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part2. intros. left.
    eapply in_inv in H; destruct H. subst. injection H0 as eq; subst.
    do 4 eexists. split; eauto. split.  
    eapply list_elem_of_In. eapply list_elem_of_singleton. auto.
    destruct ty0;simpl ;auto.
    eapply in_inv in H; destruct H. subst. tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split. unfold capability_not_add_part3. intros.
    eapply in_inv in H. destruct H. subst; tryfalse.
    eapply in_inv in H. destruct H. subst; tryfalse.
    left. injection H0 as eq;subst.
    do 3 eexists. eauto. split.
    eapply list_elem_of_In. eapply list_elem_of_singleton. auto.
    destruct ty0;simpl ;auto.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
     split.
    unfold capability_not_add_part4. intros.
    eapply in_inv in H. destruct H. subst; tryfalse.
    eapply in_inv in H. destruct H. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part5. intros.
    eapply in_inv in H. destruct H. subst; tryfalse.
    eapply in_inv in H. destruct H. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    unfold capability_not_add_part6. intros.
    eapply in_inv in H. destruct H. subst; tryfalse.
    eapply in_inv in H. destruct H. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.

  + split. 
    unfold capability_not_add_part1. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part2. intros. right. left.
    eapply in_inv in H0. destruct H0. subst. injection H1 as eq;subst.
    exists κ. exists ty0. eexists. split; eauto.
    split; eauto. eapply list_elem_of_In. eapply list_elem_of_singleton. auto.
    destruct ty0;simpl;auto.
    eapply in_inv in H0. destruct H0. subst. tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part3.
    intros. 
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    simpl in H0. exfalso. auto.
    split.
    unfold capability_not_add_part4. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    injection H1 as eq;subst.
    left. do 4 eexists. eauto.
    split. eapply list_elem_of_In. eapply list_elem_of_singleton. auto.
    destruct ty0;simpl;auto.
    simpl in H0. exfalso. auto.
    split.
    unfold capability_not_add_part5.
    intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    unfold capability_not_add_part6.
    intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
  + split.
    unfold capability_not_add_part1. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part2. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0.  subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part3. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0.  subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part4. intros.
    eapply in_inv in H0. destruct H0. subst; tryfalse.
    eapply in_inv in H0. destruct H0.  subst; tryfalse.
    assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    split.
    unfold capability_not_add_part5.
    intros.
    simpljoin1.
    eapply in_inv in H0.
    destruct H0.
    injection H0 as eq;subst.
    left. do 3 eexists.
    split;eauto.
    split;eauto.
    eapply in_eq. destruct ty0;simpl;auto.
    eapply in_inv in H0.
    destruct H0. tryfalse.
    simpl in H0. exfalso. eauto.
    unfold capability_not_add_part6.
    intros. subst.
    eapply in_inv in H0.
    destruct H0. tryfalse.
    eapply in_inv in H0.
    destruct H0.
    injection H0 as eq;subst.
    left. do 3 eexists.
    split;eauto.
    split;eauto.
    eapply in_eq. 
    destruct ty0;simpl ;eauto.
    simpl in H0; exfalso;eauto.

  + 
    split. (* generalize dependent T1. generalize dependent T2. *)
    induction T. intros. rename IHsafe_tctx_incl into H0.
    simpl. destruct H0; auto. 
    intros. destruct IHsafe_tctx_incl. unfold capability_not_add_part1 in *.
    intros. eapply in_inv in H2. 
    destruct H2. subst.
    left.
    do 3 eexists. split; eauto. split. eauto.  
    eapply in_or_app. left. eapply in_eq.
    destruct ty; simpl ;auto.
    eapply IHT in H2. 2:eauto. destruct H2. do 3 destruct H2.
    destruct H4. subst.
    left.
    exists x. eexists.
    split. eauto. split;eauto.
    eapply in_app_or in H4. destruct H4. eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.
    right. do 4 destruct H2. destruct H4. subst.
    exists x. exists x0. eexists. split. eauto.
    split;eauto.
    eapply in_app_or in H4. destruct H4. eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.

    split. induction T. intros.
    simpl. destruct IHsafe_tctx_incl; auto.
    destruct H1. auto.
    intros. destruct IHsafe_tctx_incl. destruct H1. unfold capability_not_add_part2 in *.
    intros.   
    eapply in_inv in H3. destruct H3. subst.
    right. left.
    do 4 eexists. split; eauto. split. eauto.  
    eapply in_or_app. left. eapply in_eq.
    destruct ty;simpl; auto.
    eapply IHT in H3. 2:eauto. destruct H3.  
    do 3 destruct H3. destruct H3. destruct H5. subst.
    left. eexists. exists x0. exists x1. split. eauto.
    split. eauto.
    eapply in_app_or in H5. destruct H5. eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.
    auto.
    destruct H3. do 4 destruct H3. destruct H5.
    right. left. subst. 
    exists x. exists x0. eexists.
    split. eauto. split. eauto.
    eapply in_app_or in H5. destruct H5.  eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.
    auto.
    destruct H3.
    right. right. left. do 5 destruct H3. destruct H5. subst.
    exists x. exists x0. exists x1. eexists.
    eauto. split;eauto.
    split;eauto.
    eapply in_app_or in H5. destruct H5.  eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.
    simpljoin1. right. right. right.
    do 5 eexists. eauto. split;eauto.
    eapply in_app_or in H5. destruct H5.  eapply in_or_app.
    left. eapply in_cons. eauto. eapply in_or_app. right. auto.
      
    destruct IHsafe_tctx_incl. destruct H1. destruct H2.  
    split. induction T. intros. simpl. auto.
    simpl. unfold capability_not_add_part3 in *.
    intros.   
    eapply in_inv in H4. destruct H4. right. subst.
    exists ty. exists k.
    split; eauto. 2:{destruct ty;simpl;auto. }
    left. eauto.
    eapply IHT in H4. 2:eauto. destruct H4.  
    do 3 destruct H4. destruct H6. subst.
    left. eexists. exists x0. split. eauto.
    split. eauto.
    eapply in_app_or in H6. destruct H6. right.
    eapply in_or_app. left. auto.
    right. eapply in_or_app. right. auto. auto.
    right. do 3 destruct H4. subst.
    exists x. exists x0.
    split. 
    eapply in_app_or in H4. destruct H4. 
    eapply in_cons. eapply in_or_app. left. auto.
    eapply in_cons. eapply in_or_app. right. auto.
    auto.
    induction T. intros. simpl. auto.
    split.
    destruct H3 as (H3 & H4').
    destruct IHT as (IHT & IHT').
    simpl. unfold capability_not_add_part4 in *.
    intros.   
    eapply in_inv in H4. destruct H4. right. right. left. subst.
    exists ty. exists k. exists n.
    split; eauto. 2:{destruct ty;simpl;auto. }
    left. eauto.
    eapply IHT in H4. 2:eauto. destruct H4.  
    do 4 destruct H4. destruct H6. subst.
    left. exists x. exists x0. eexists. split. eauto.
    split. right. eauto. auto. 
    destruct H4. do 4 destruct H4. destruct H6. subst.
    right. left. exists x. exists x0. eexists.
    split;eauto. split. right. auto. auto.
    destruct H4. do 4 destruct H4.
    right. right. left. exists x. exists x0. exists x1.
    split. right. eauto. eauto.
    do 5 destruct H4. destruct H6.
    right. right. right. 
    do 5 eexists. eauto. split.
    right. auto. auto.
    
    simpljoin1.
    split. intros. simpl.
    clear - H5 H7.
    unfold capability_not_add_part5 in *.
    intros.   
    eapply in_inv in H. destruct H. subst.
    left.
    do 4 eexists. split; eauto. split. eauto. 
    simpl. 
    left. eauto.
    destruct ty;simpl; auto.
    eapply H5 in H. 2:eauto. destruct H.  
    simpljoin1.
    left. do 3 eexists.
    split. eauto. split.
    eapply in_app_or in H1. destruct H1.
    simpl. right. eapply in_or_app.
    left. eauto. eapply in_cons. auto. eapply in_or_app. right. auto.
    auto.
    destruct H. simpljoin1.
    right. left. subst. 
    do 3 eexists.
    split. eauto. split. eauto.
    eapply in_app_or in H1. destruct H1.
    simpl. right.
    eapply in_or_app.
    left. eauto. eapply in_cons. eapply in_or_app. right. auto.
    auto.
    destruct H. simpljoin1.
    right. right. left. 
    do 4 eexists.
    eauto. split;eauto.
    eapply in_app_or in H1. destruct H1. 
    simpl. right. eapply in_or_app.
    left. eauto.
    eapply in_cons. eapply in_or_app. right. auto.
    destruct H. simpljoin1.
    right. right. right. left. 
    do 4 eexists. split.
    eauto. split;eauto.
    eapply in_app_or in H1. destruct H1. 
    simpl. right. eapply in_or_app.
    left. eauto.
    eapply in_cons. eapply in_or_app. right. auto.
    destruct H. simpljoin1.
    right. right. right. right. left. 
    do 4 eexists.
    eauto. split;eauto.
    split.
    eapply in_app_or in H1. destruct H1. 
    simpl. right. eapply in_or_app.
    left. eauto.
    eapply in_cons. eapply in_or_app. right. auto.
    eauto. 
    simpljoin1. right. right. right. right. right.
    do 5 eexists. eauto. split;eauto.
    eapply in_app_or in H1. destruct H1.
    simpl. right. eapply in_or_app.
    left. eauto. eapply in_cons. eapply in_or_app. right. auto.

    clear - H6 H8.
    unfold capability_not_add_part6 in *.
    intros.   
    eapply in_inv in H. destruct H. subst.
    right. left.
    do 4 eexists. split; eauto. split. eauto. 
    simpl. 
    left. eauto. eauto.
    destruct ty;simpl; auto.
    eapply H6 in H. 2:eauto.
    destruct H.  
    simpljoin1.
    left. do 3 eexists.
    split. eauto. split.
    eapply in_app_or in H1. destruct H1.
    simpl. right. eapply in_or_app.
    left. eauto. eapply in_cons. auto. eapply in_or_app. right. auto.
    auto.
    destruct H. simpljoin1.
    right. left. subst. 
    do 4 eexists.
    split. eauto. split. eauto.
    eapply in_app_or in H1. destruct H1.
    simpl. right.
    eapply in_or_app.
    left. eauto. eapply in_cons. eapply in_or_app. right. auto.
    auto.
    destruct H. simpljoin1.
    right. right. left. 
    do 4 eexists.
    eauto. split;eauto.
    eapply in_app_or in H1. destruct H1. 
    simpl. right. eapply in_or_app.
    left. eauto.
    eapply in_cons. eapply in_or_app. right. auto.
    destruct H. simpljoin1.
    right. right. right. left. 
    do 4 eexists. split.
    eauto. split;eauto.
    eapply in_app_or in H1. destruct H1. 
    simpl. right. eapply in_or_app.
    left. eauto.
    eapply in_cons. eapply in_or_app. right. auto.
    destruct H. simpljoin1.
    right. right. right. right. left. 
    do 4 eexists.
    eauto. split;eauto.
    split.
    eapply in_app_or in H1. destruct H1. 
    simpl. right. eapply in_or_app.
    left. eauto.
    eapply in_cons. eapply in_or_app. right. auto.
    eauto. 
    simpljoin1. right. right. right. right. right.
    do 5 eexists. eauto. split;eauto.
    eapply in_app_or in H1. destruct H1.
    simpl. right. eapply in_or_app.
    left. eauto. eapply in_cons. eapply in_or_app. right. auto.

  +
    split. (* generalize dependent T1. generalize dependent T2. *)
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r. destruct IHsafe_tctx_incl; auto.
    intros. destruct IHsafe_tctx_incl. unfold capability_not_add_part1 in *.
    intros. eapply in_app_or in H2. destruct H2. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H4. 2:eauto. destruct H4. do 3 destruct H4. destruct H5. subst.
    left.
    exists x. eexists. split. eauto.
    split. eauto. eapply in_or_app. eapply in_app_or in H5.
    destruct H5. left. auto. right. eapply in_cons. auto. eauto.
    right. do 4 destruct H4. destruct H5. subst.
    do 4 eexists. eauto. split.
    eapply in_or_app. eapply in_app_or in H5.
    destruct H5. left. eauto. right. eapply in_cons. auto. eauto.
    subst. left. do 3 eexists. eauto.
    split. eapply in_or_app. right. eauto.
    destruct ty;simpl ;eauto.
    destruct IHsafe_tctx_incl. destruct H1. destruct H2.
    split.
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r.  auto.
    unfold capability_not_add_part2 in *.
    intros. eapply in_app_or in H4. destruct H4. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H6. 2:eauto. destruct H6. do 4 destruct H6. destruct H7. subst.
    left. do 3 eexists. split. eauto.
    split. eapply in_app_or in H7. destruct H7.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H6. do 4 destruct H6. destruct H7.
    right. left. subst. do 4 eexists.
    eauto. split. eapply in_app_or in H7.
    destruct H7. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    auto. destruct H6.
    do 5 destruct H6. destruct H7. subst.
    right. right. left. do 5 eexists. eauto.
    split. eapply in_app_or in H7. destruct H7.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    simpljoin1. right. right. right.
    do 5 eexists. eauto.
    split. eapply in_app_or in H7. destruct H7.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto. eauto.


    right. left. do 4 eexists.
    eauto. split. eapply in_or_app. right. eauto.
    destruct ty;simpl;auto.
    split.
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r. auto.
    unfold capability_not_add_part3 in *.
    intros. eapply in_app_or in H4. destruct H4. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H6. 2:eauto. destruct H6. do 3 destruct H6. destruct H7. subst.
    left. do 4 eexists. 
    eapply in_app_or in H7. destruct H7.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    do 3 destruct H6.
    right. subst. do 3 eexists.
    eapply in_app_or in H6.
    destruct H6. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    auto. right.
    subst. do 3 eexists. 
    eapply in_or_app. right. eauto.
    destruct ty;simpl;auto.
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r. auto.
    destruct H3 as (H3 & H4').
    destruct IHT as (IHT & IHT').
    split.
    unfold capability_not_add_part4 in *.
    intros. eapply in_app_or in H4. destruct H4. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H6. 2:eauto. destruct H6. do 4 destruct H6. destruct H7. subst.
    left. do 4 eexists. eauto. split. 
    eapply in_app_or in H7. destruct H7.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H6.
    do 4 destruct H6. destruct H7. subst.
    right. left. do 4 eexists. eauto.
    split. eapply in_app_or in H7. destruct H7.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H6. do 4 destruct H6.
    right. right. left. do 4 eexists.
    eapply in_app_or in H6.
    destruct H6. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    auto.
    do 5 destruct H6. destruct H7. subst.
    right. right. right. do 5 eexists. eauto.
    split.  eapply in_app_or in H7.
    destruct H7.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    right. right. left. subst. do 4 eexists. 
    eapply in_or_app. right. eauto. 
    destruct ty;simpl;auto.

    split. simpljoin1.
    clear - H6 H4.
    unfold capability_not_add_part5 in *.
    intros. eapply in_app_or in H. destruct H. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply H4 in H1. 2:eauto. destruct H1.
    simpljoin1.
    left. do 4 eexists. eauto. split. 
    eapply in_app_or in H2. destruct H2.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H1.
    simpljoin1.
    right. left. do 4 eexists. eauto.
    split. eapply in_app_or in H2. destruct H2.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H1.
    simpljoin1.
    right. right. left. do 4 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    auto.
    destruct H1.
    simpljoin1.
    right. right. right. left. do 5 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    destruct H1.
    simpljoin1.
    right. right. right. right. left. do 5 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right. right. right. do 5 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    simpljoin1.
    left. do 5 eexists. eauto.
    eapply in_or_app. right. eauto. destruct ty;simpl;eauto.
    
    simpljoin1.
    clear - H7 H5.
    unfold capability_not_add_part6 in *.
    intros. eapply in_app_or in H. destruct H. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply H5 in H1. 2:eauto. destruct H1.
    simpljoin1.
    left. do 4 eexists. eauto. split. 
    eapply in_app_or in H2. destruct H2.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H1.
    simpljoin1.
    right. left. do 5 eexists. eauto.
    split. eapply in_app_or in H2. destruct H2.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    destruct H1.
    simpljoin1.
    right. right. left. do 4 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    auto.
    destruct H1.
    simpljoin1.
    right. right. right. left. do 5 eexists. eauto.
    eapply in_app_or in H2.
    destruct H2.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    destruct H1.
    simpljoin1.
    right. right. right. right. left. do 5 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right. right. right. do 5 eexists. eauto.
    split.
    eapply in_app_or in H2.
    destruct H2.
    eapply in_or_app. left. eauto. 
    eapply in_or_app. right. eapply in_cons. eauto. eauto.
    simpljoin1.
    right. left. do 5 eexists. eauto.
    split.
    eapply in_or_app. right. eauto. destruct ty;simpl;eauto.

  + eapply safe_tctx_incl_capability_not_add_tran';eauto.
    Unshelve. exact E. exact L. exact E. exact L.
    exact E. exact L. exact E. exact L.
    exact E. exact L. exact E. exact L.
Qed.





Lemma UnblockTctx_capability_not_add: 
forall κ T1 T2, UnblockTctx κ T2 T1 ->
capability_not_add_part1 T2 T1 /\ capability_not_add_part2 T2 T1 /\
    capability_not_add_part3 T2 T1 /\ capability_not_add_part4 T2 T1 .
Proof.
  intros.
  induction H;subst.
  + simpljoin1.
    split.
    unfold capability_not_add_part1.
    intros. eapply in_inv in H4. destruct H4.
    subst. destruct ty; tryfalse.
    injection H5 as eq. subst.
    right. do 4 eexists. eauto.
    split. eapply in_eq.
    destruct ty0;simpl;auto.
    subst. eapply H0 in H4.
    destruct H4. eauto.
    simpljoin1. left.
    do 4 eexists. eapply in_cons. eauto.
    eauto.
    right. simpljoin1. do 4 eexists. eauto.
    split. eapply in_cons. eauto. eauto.
    
    split. unfold capability_not_add_part2.   
    intros. eapply in_inv in H4. destruct H4.
    subst. injection H5 as eq; subst.
    right. right. right. 
    do 4 eexists. split;eauto.
    split. eapply in_eq.
    destruct ty0;simpl;auto.
    subst. eapply H1 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left. do 5 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.

    split. unfold capability_not_add_part3.   
    intros. eapply in_inv in H4.  destruct H4.
    tryfalse.
    subst. eapply H2 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. do 3 eexists.
    eapply in_cons. eauto. eauto.

    unfold capability_not_add_part4.   
    intros. eapply in_inv in H4.  destruct H4.
    tryfalse.
    subst. eapply H3 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left.
    do 4 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right.
    do 5 eexists. 
    eauto. split. eapply in_cons. eauto. eauto.

  + simpljoin1.
    split. unfold capability_not_add_part1.
    intros. eapply in_inv in H4. destruct H4.
    subst.
    left. do 4 eexists. eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H0 in H4.
    destruct H4. eauto.
    simpljoin1. left.
    do 4 eexists. eapply in_cons. eauto.
    eauto.
    right. simpljoin1. do 4 eexists. eauto.
    split. eapply in_cons. eauto. eauto.
    
    split. unfold capability_not_add_part2.   
    intros. eapply in_inv in H4. destruct H4.
    subst.
    right. left. 
    do 4 eexists. split;eauto.
    split. eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H1 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left. do 5 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.

    split. unfold capability_not_add_part3.   
    intros. eapply in_inv in H4.  destruct H4.
    subst. right.
    do 3 eexists. 
    eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H2 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. do 3 eexists.
    eapply in_cons. eauto. eauto.

    unfold capability_not_add_part4.   
    intros. eapply in_inv in H4.  destruct H4.
    subst. right. right. left.
    do 3 eexists. split.
    eapply in_eq. 
    destruct ty;simpl;eauto.
    subst. eapply H3 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left.
    do 4 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right.
    do 5 eexists. 
    eauto. split. eapply in_cons. eauto. eauto.

  + split.
    unfold capability_not_add_part1.
    intros. simpl in H. exfalso. auto.
    split.
    unfold capability_not_add_part2.
    intros. simpl in H. exfalso. auto.
    split.
    unfold capability_not_add_part3.
    intros. simpl in H. exfalso. auto.
    unfold capability_not_add_part4.
    intros. simpl in H. exfalso. auto.
Qed.


Lemma UnblockTctx_capability_not_add': 
forall κ T1 T2, UnblockTctx κ T2 T1 ->
    capability_not_add_part1 T2 T1 /\ capability_not_add_part2 T2 T1 /\
    capability_not_add_part3 T2 T1 /\ capability_not_add_part4 T2 T1 /\
    capability_not_add_part5 T2 T1 /\ capability_not_add_part6 T2 T1.
Proof.
  intros.
  induction H;subst.
  + simpljoin1.
    rename H4 into H4'.
    rename H5 into H5'.
    split.
    unfold capability_not_add_part1.
    intros. eapply in_inv in H4. destruct H4.
    subst. destruct ty; tryfalse.
    injection H5 as eq. subst.
    right. do 4 eexists. eauto.
    split. eapply in_eq.
    destruct ty0;simpl;auto.
    subst. eapply H0 in H4.
    destruct H4. eauto.
    simpljoin1. left.
    do 4 eexists. eapply in_cons. eauto.
    eauto.
    right. simpljoin1. do 4 eexists. eauto.
    split. eapply in_cons. eauto. eauto.
    
    split. unfold capability_not_add_part2.   
    intros. eapply in_inv in H4. destruct H4.
    subst. injection H5 as eq; subst.
    right. right. right. 
    do 4 eexists. split;eauto.
    split. eapply in_eq.
    destruct ty0;simpl;auto.
    subst. eapply H1 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left. do 5 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.

    split. unfold capability_not_add_part3.   
    intros. eapply in_inv in H4.  destruct H4.
    tryfalse.
    subst. eapply H2 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. do 3 eexists.
    eapply in_cons. eauto. eauto.

    split.
    unfold capability_not_add_part4.   
    intros. eapply in_inv in H4.  destruct H4.
    tryfalse.
    subst. eapply H3 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left.
    do 4 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right.
    do 5 eexists. 
    eauto. split. eapply in_cons. eauto. eauto.
    
    split. unfold capability_not_add_part5.   
    intros. eapply in_inv in H4. destruct H4.
    subst. injection H5 as eq; subst.
    right. right. right. right. right.  
    do 4 eexists. split;eauto.
    split. eapply in_eq.
    destruct ty0;simpl;auto.
    subst. eapply H4' in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. left.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. right. left.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. right. right.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.

    unfold capability_not_add_part6.   
    intros. eapply in_inv in H4.  destruct H4.
    tryfalse.
    subst. eapply H5' in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 5 eexists. eauto.
    split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left.
    do 4 eexists. eauto.
    split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. left.
    do 5 eexists. 
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto. split. 
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right. right. right. 
    do 5 eexists. eauto. split. 
    eapply in_cons. eauto. eauto.

  + simpljoin1.
    rename H4 into H4'.
    rename H5 into H5'.
    split. unfold capability_not_add_part1.
    intros. eapply in_inv in H4. destruct H4.
    subst.
    left. do 4 eexists. eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H0 in H4.
    destruct H4. eauto.
    simpljoin1. left.
    do 4 eexists. eapply in_cons. eauto.
    eauto.
    right. simpljoin1. do 4 eexists. eauto.
    split. eapply in_cons. eauto. eauto.
    
    split. unfold capability_not_add_part2.   
    intros. eapply in_inv in H4. destruct H4.
    subst.
    right. left. 
    do 4 eexists. split;eauto.
    split. eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H1 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left. do 5 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.

    split. unfold capability_not_add_part3.   
    intros. eapply in_inv in H4.  destruct H4.
    subst. right.
    do 3 eexists. 
    eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H2 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists.
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. do 3 eexists.
    eapply in_cons. eauto. eauto.

    split.
    unfold capability_not_add_part4.   
    intros. eapply in_inv in H4.  destruct H4.
    subst. right. right. left.
    do 3 eexists. split.
    eapply in_eq. 
    destruct ty;simpl;eauto.
    subst. eapply H3 in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left.
    do 4 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right.
    do 5 eexists. 
    eauto. split. eapply in_cons. eauto. eauto.

    split. unfold capability_not_add_part5.   
    intros. eapply in_inv in H4. destruct H4.
    subst.
    left. 
    do 4 eexists. split;eauto.
    split. eapply in_eq.
    destruct ty;simpl;auto.
    subst. eapply H4' in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. left.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. right. left.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. right. right.
    do 4 eexists. split;eauto.
    split. eapply in_cons. eauto. eauto.

    unfold capability_not_add_part6.   
    intros. eapply in_inv in H4.  destruct H4.
    subst. right. left.
    do 5 eexists. split.
    split.
    eapply in_eq. 
    destruct ty;simpl;eauto.
    subst. eapply H5' in H4.
    destruct H4. eauto.
    simpljoin1.
    left. do 5 eexists.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. left. do 5 eexists. 
    eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. left.
    do 4 eexists. eauto. split.
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. left.
    do 5 eexists. 
    eapply in_cons. eauto. eauto.
    destruct H4.
    simpljoin1.
    right. right. right. right. left.
    do 5 eexists. eauto. split. 
    eapply in_cons. eauto. eauto.
    simpljoin1.
    right. right. right. right. right.
    do 5 eexists. eauto. split. 
    eapply in_cons. eauto. eauto.

  + split.
    unfold capability_not_add_part1.
    intros. simpl in H. exfalso. auto.
    split.
    unfold capability_not_add_part2.
    intros. simpl in H. exfalso. auto.
    split.
    unfold capability_not_add_part3.
    intros. simpl in H. exfalso. auto.
    split.
    unfold capability_not_add_part4.
    intros. simpl in H. exfalso. auto.
    split.
    unfold capability_not_add_part5.
    intros. simpl in H. exfalso. auto.
    unfold capability_not_add_part6.
    intros. simpl in H. exfalso. auto.
Qed.


Definition capability_not_add_1 T T' := 
   capability_not_add_part1 T T' /\
   capability_not_add_part2 T T' /\
   capability_not_add_part3 T T' /\
   capability_not_add_part4 T T' /\
   capability_not_add_part5 T T' /\
   capability_not_add_part6 T T'.


(* Lemma safe_type_Ins_capability_not_add_patr2 : forall E L I T1 (T2:val → tctx) v T2',
              safe_type_Ins  E L T1 I T2  ->
              T2' = T2 v ->
              forall tctx_elt ,In tctx_elt T2' /\

              (list_add_uniq tctx_elt T1) ->
  (exists p , I = p /\ capability_tran T1 T2') 
  \/ (exists p,read_instruction_uniq I p T1 T2').  *)

Definition capability_not_add_2 T1 I T2' :=
  (forall tctx_elt ,In tctx_elt T2' /\  (list_add_own tctx_elt T1) ->
              (exists n , I = new [n]%E) 
              \/ (exists p , I = p /\ capability_tran T1 T2') 
              \/ ( exists p, read_instruction I p T1 T2'))
  /\ 
  (forall tctx_elt ,In tctx_elt T2' /\

              (list_add_uniq tctx_elt T1) ->
  (exists p , I = p /\ capability_tran T1 T2') 
  \/ (exists p,read_instruction_uniq I p T1 T2'))
  /\ 
  (forall tctx_elt p κ a, In tctx_elt T2' /\

              tctx_elt = TCtx_hasty p (&shr{ κ } a) ->
              (exists tctx_elt',
                In tctx_elt' T1 /\
                tctx_elt' = TCtx_hasty p (&shr{ κ } a))
            \/ (exists p , I = p /\ capability_tran T1 T2') 
            \/ (exists p,read_instruction_shr I p T1 T2'))

.

Lemma member_of_own_in_tctx'_app_r :
  forall T1 T0,
  member_of_own_in_tctx' (T1 ++ T0) = (member_of_own_in_tctx' T1 + member_of_own_in_tctx' T0)%nat.
Proof.
  intros.
  induction T1.
  simpl. eauto.
  simpl. destruct a.
  rewrite  <- Nat.add_assoc. 
  rewrite Nat.add_cancel_l. eauto.
  rewrite  <- Nat.add_assoc. 
  rewrite Nat.add_cancel_l. eauto.
Qed.

Lemma capability_not_add_1_eq T:
  capability_not_add_1 T T.
Proof.
  unfold capability_not_add_1.
  split. 
  unfold capability_not_add_part1.
  intros.
  left.
  do 3 eexists. eauto.
  split;eauto. 
  destruct ty;simpl;eauto.
  split. 
  unfold capability_not_add_part2.
  intros.
  right. left.
  do 4 eexists. eauto.
  split;eauto. 
  destruct ty;simpl;eauto.
  split. 
  unfold capability_not_add_part3.
  intros. subst.
  right.
  do 3 eexists. eauto.
  destruct ty;simpl;eauto.
  split.
  unfold capability_not_add_part4.
  intros. subst.
  right. right. left.
  do 4 eexists. eauto.
  destruct ty;simpl;eauto.
  split.
  unfold capability_not_add_part5.
  intros. subst.
  left. do 4 eexists.
  eauto. split. eauto.
  destruct ty;simpl;eauto.
  unfold capability_not_add_part6.
  intros. subst. 
  right. left. do 4 eexists.
  split;eauto. split.
  eauto. destruct ty;simpl;eauto.
Qed.

Lemma member_of_own_in_tctx'_app :
forall T1 T2 T0,
  member_of_own_in_tctx' (T1 ++ T0) < member_of_own_in_tctx' (T2 ++ T0) ->
  member_of_own_in_tctx' T1 < member_of_own_in_tctx' T2.
Proof.
  intros.
  rewrite member_of_own_in_tctx'_app_r in H.
  rewrite member_of_own_in_tctx'_app_r in H.
  simpl in H.
  lia.
Qed.

Lemma remove_first_app_r x T1 T0 :
  In x T1 ->
  remove_first tctx_elt tctx_elt_dec_eq x (T1 ++ T0) =
  remove_first tctx_elt tctx_elt_dec_eq x T1 ++ T0.
Proof.
  intros.
  induction T1.
  simpl in H. exfalso. auto.
  eapply in_inv in H. destruct H.
  simpl. destruct (tctx_elt_dec_eq x a);eauto;tryfalse.
  eapply IHT1 in H.
  simpl. destruct (tctx_elt_dec_eq x a). auto.
  rewrite H. eauto.
Qed.

Lemma cap_unforgeabilibty: 
forall E L C T T' e, safe_type_fun E L C T e T'->
                   capability_not_add_1 T T' 
                 \/ (exists xb e0 e',e = (let: xb := e0 in e') 
                      /\  capability_not_add_2 T e0 T')
                 \/ exists p ps k, e =(call: p ps → k).
Proof.
intros. 
  inversion H; subst.
 -
  right. left. do 3 eexists.
  split. eauto.
  unfold capability_not_add_2.
  split. 2:split.
  + 
  intros.
  simpljoin1.
  eapply in_app_or in H3.
  destruct H3.
  2:{
    unfold list_add_own in H4.
    simpljoin1.
    assert(In tctx_elt0 (T1 ++ T0)).
    eapply in_or_app.
    right. eauto.
    tryfalse.
  }
  eapply safe_type_Ins_capability_not_add_part1 in H1.

  2:{ instantiate (1:=v). eauto. }
  2:{ instantiate (1:= tctx_elt0).
      split.
      eauto.
      unfold list_add_own in *.
      simpljoin1.
      split;eauto.
      unfold not.
      intros.
      assert(In tctx_elt0 (T1 ++ T0)).
      eapply in_or_app.
      left. eauto. tryfalse.
      destruct H5.
      left. simpljoin1.
      do 5 eexists. eauto.
      split;eauto.
      clear -H7.
      induction T1. simpl. auto.
      destruct a; simpl in *.
      destruct (expr_beq x p). auto.
      split;eauto.
      destruct H7.
      eapply IHT1 in H0. eauto.
      destruct (expr_beq x p). auto.
      split;eauto.
      destruct H7.
      eapply IHT1 in H0. eauto.
      right.
      simpljoin1.
      do 5 eexists. eauto.
      split;eauto.
      split;eauto.
      clear -H7.
      induction T1. simpl. auto.
      destruct a; simpl in *.
      destruct (expr_beq x p). auto.
      split;eauto.
      destruct H7.
      eapply IHT1 in H0. eauto.
      destruct (expr_beq x p). auto.
      split;eauto.
      destruct H7.
      eapply IHT1 in H0. eauto.
   }
   destruct H1.
   left. eauto.
   destruct H1.
   right. left. simpljoin1. exists x.
   split. eauto.
   clear - H5.
   unfold capability_tran in *.
   simpljoin1.
   split. 
   rewrite length_app. rewrite length_app.
   rewrite H. eauto.
    
   intros. 
   eapply in_app_or in H1.
   destruct H1.
   assert(H1' := H1).
   eapply H0 in H1.
   simpljoin1.
   destruct H1. simpljoin1. 
   exists x.
   left. split.
   eapply in_or_app. left. eauto.
   clear - H1 H1' H2.
   assert(remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) (T2 v ++ T0) 
         = remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) (T2 v) ++ T0).
   eapply remove_first_app_r. eauto.
   rewrite H.
   assert(remove_first tctx_elt tctx_elt_dec_eq (x ◁ ty) (T1 ++ T0) 
          = remove_first tctx_elt tctx_elt_dec_eq (x ◁ ty) T1 ++ T0).
   eapply remove_first_app_r. eauto.
   rewrite H0.
   rewrite H2.
   eauto.
   eexists.
   right. eapply in_or_app.
   left. eauto.
   eexists. right.
   eapply in_or_app. right. eauto.
   right. right.
   simpljoin1. exists x.
   unfold read_instruction in *.
   simpljoin1. split;eauto.
   do 8 eexists. eauto.
   split.
   instantiate(1:= x5). instantiate(1:= x4). instantiate(1:= x3).
   eapply elem_of_app. left. eauto.
   split;eauto.
   split;eauto.
   instantiate(1:= x6).
   eapply elem_of_app. left. eauto.
  +
   intros.
   simpljoin1.
   eapply in_app_or in H3.
   destruct H3.
   2:{
    unfold list_add_uniq in H4.
    simpljoin1.
    assert(In (x ◁ &uniq{x1} x2) (T1 ++ T0)).
    eapply in_or_app.
    right. eauto.
    tryfalse.
  }
  eapply safe_type_Ins_capability_not_add_part2 in H1.
  
  2:{ instantiate (1:=v). eauto. }
  2:{ instantiate (1:= tctx_elt0).
      split.
      eauto.
      unfold list_add_uniq in *.
      simpljoin1.
      split;eauto.
      unfold not.
      intros.
      assert(In (x ◁ &uniq{x1} x2) (T1 ++ T0)).
      eapply in_or_app.
      left. eauto. tryfalse.
      do 5 eexists. eauto.
      split;eauto.
      clear -H7.
      induction T1. simpl. auto.
      destruct a; simpl in *.
      destruct (expr_beq x p). auto.
      split;eauto.
      destruct H7.
      eapply IHT1 in H0. eauto.
      destruct (expr_beq x p). auto.
      split;eauto.
      destruct H7.
      eapply IHT1 in H0. eauto.
    }
   destruct H1.
   left. eauto.
   simpljoin1. exists x.
   split. eauto.
   clear - H5.
   unfold capability_tran in *.
   simpljoin1.
   split. 
   (* Search (length(_ ++ _)). *)
   rewrite length_app. rewrite length_app.
   rewrite H. eauto.
    
   intros. 
   eapply in_app_or in H1.
   destruct H1.
   assert(H1' := H1).
   eapply H0 in H1.
   simpljoin1.
   destruct H1. simpljoin1. 
   exists x.
   left. split.
   eapply in_or_app. left. eauto.
   clear - H1 H1' H2.
   assert(remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) (T2 v ++ T0) 
         = remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) (T2 v) ++ T0).
   eapply remove_first_app_r. eauto.
   rewrite H.
   assert(remove_first tctx_elt tctx_elt_dec_eq (x ◁ ty) (T1 ++ T0) 
          = remove_first tctx_elt tctx_elt_dec_eq (x ◁ ty) T1 ++ T0).
   eapply remove_first_app_r. eauto.
   rewrite H0.
   rewrite H2.
   eauto.
   eexists.
   right. eapply in_or_app.
   left. eauto.
   eexists. right.
   eapply in_or_app. right. eauto.
   right.
   unfold read_instruction_uniq in *.
   simpljoin1.

   destruct H1. simpljoin1.
   exists x. left. split;eauto.
   do 7 eexists.
   split;eauto.
   split;eauto.
   eapply elem_of_app. left. eauto.
   split;eauto. split;eauto.
   split;eauto.
   eapply elem_of_app. left. eauto.
   eapply elem_of_app. left. eauto.
   simpljoin1.
(* 
   unfold list_add_uniq in H4.
   simpljoin1.
   eapply H6 in H3.
   do 4 destruct H3.
   simpljoin1. *)
   exists x. right. split. eauto.
   split.
   rewrite length_app.
   rewrite length_app.
   rewrite H5. eauto.
   intros.
   eapply in_app_or in H1.
   destruct H1.
   assert(H1':=H1).
   eapply H6 in H1. simpljoin1.
   destruct H1. simpljoin1. 
   do 3 eexists.
   left. split.
   eapply in_or_app. left. eauto.
   rewrite remove_first_app_r.
   rewrite remove_first_app_r.
   rewrite H7. eauto.
   eauto. eauto.
   destruct H1. simpljoin1.
   do 3 eexists. right. left.
   split. eapply in_or_app.
   left. eauto.
   rewrite remove_first_app_r.
   rewrite remove_first_app_r.
   rewrite H7. eauto.
   eauto. eauto.
   do 3 eexists. right. right.
   eapply in_or_app. left. eauto.
   do 3 eexists. right. right. 
   eapply in_or_app. right. eauto.
  
  +intros.
   simpljoin1.
   eapply in_app_or in H3.
   destruct H3.
   2:{
    left. 
    assert(In (p ◁ &shr{κ} a) (T1 ++ T0)).
    eapply in_or_app.
    right.  eauto.
    eexists.
    split;eauto.
  }
  eapply safe_type_Ins_capability_not_add_part3 in H1.
  
  2:{ instantiate (1:=v). eauto. }
  2:{ split.
      instantiate (1:= (p ◁ &shr{κ} a)). eauto.
      eauto.

    }
   destruct H1. simpljoin1.
   left.  exists ((p ◁ &shr{κ} a)). 
   split.
   eapply in_or_app. left. auto.
   eauto.

   destruct H1.
   simpljoin1.
   right. left.
   eexists. split;eauto.
   clear - H4.
   unfold capability_tran in *.
   simpljoin1.
   split. 
   rewrite length_app. rewrite length_app.
   rewrite H. eauto.
    
   intros. 
   eapply in_app_or in H1.
   destruct H1.
   assert(H1' := H1).
   eapply H0 in H1.
   simpljoin1.
   destruct H1. simpljoin1. 
   exists x.
   left. split.
   eapply in_or_app. left. eauto.
   clear - H1 H1' H2.
   assert(remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) (T2 v ++ T0) 
         = remove_first tctx_elt tctx_elt_dec_eq (p ◁ ty) (T2 v) ++ T0).
   eapply remove_first_app_r. eauto.
   rewrite H.
   assert(remove_first tctx_elt tctx_elt_dec_eq (x ◁ ty) (T1 ++ T0) 
          = remove_first tctx_elt tctx_elt_dec_eq (x ◁ ty) T1 ++ T0).
   eapply remove_first_app_r. eauto.
   rewrite H0.
   rewrite H2.
   eauto.
   eexists.
   right. eapply in_or_app.
   left. eauto.
   eexists. right.
   eapply in_or_app. right. eauto.
   right. right.
   unfold read_instruction_shr in *.
   simpljoin1.

   destruct H1. simpljoin1.
   exists x. left. split;eauto.
   do 7 eexists.
   split;eauto.
   split;eauto.
   eapply elem_of_app. left. eauto.
   split;eauto.
   eapply elem_of_app. left. eauto.

   simpljoin1.
(* 
   unfold list_add_uniq in H4.
   simpljoin1.
   eapply H6 in H3.
   do 4 destruct H3.
   simpljoin1. *)
   exists x. right. split. eauto.
   split.
   rewrite length_app.
   rewrite length_app.
   rewrite H4. eauto.
   intros.
   eapply in_app_or in H1.
   destruct H1.
   assert(H1':=H1).
   eapply H5 in H1. simpljoin1.
   destruct H1. simpljoin1. 
   do 3 eexists.
   left. split.
   eapply in_or_app. left. eauto.
   rewrite remove_first_app_r.
   rewrite remove_first_app_r.
   rewrite H6. eauto.
   eauto. eauto.
   destruct H1. simpljoin1.
   do 3 eexists. right. left.
   split. eapply in_or_app.
   left. eauto.
   rewrite remove_first_app_r.
   rewrite remove_first_app_r.
   rewrite H6. eauto.
   eauto. eauto.
   do 3 eexists. right. right.
   eapply in_or_app. left. eauto.
   do 3 eexists. right. right. 
   eapply in_or_app. right. eauto.
  
  -
   eapply safe_tctx_incl_capability_not_add' in H1.
   left. unfold capability_not_add_1. 
   eauto.
  -
   left.
   eapply capability_not_add_1_eq.
  -
   left.
   eapply capability_not_add_1_eq.
  -
   left.
   eapply capability_not_add_1_eq.
  -
   left.
   eapply UnblockTctx_capability_not_add' in H1.
   eauto.
  -
   left.
   eapply capability_not_add_1_eq.
  -
   left.
   eapply capability_not_add_1_eq.
  -
   left.
   eapply capability_not_add_1_eq.
  -

   right. right.
   do 3 eexists. eauto.
  -
   left.
   eapply capability_not_add_1_eq.
   Unshelve. exact p. exact p.
   exact p. exact p.
   exact κ. exact x2. exact p.
   exact κ. exact x2. exact p.
   exact κ. exact 0%nat.
   exact p. exact p.
   exact κ. exact 0%nat.
   exact p. exact 0%nat.
   exact κ. exact p.
   exact 0%nat. exact κ. 
Qed.


Lemma write_capbility_check :
  forall E L ty1 ty2 ty3, safe_wr Write' E L ty1 ty2 ty3 ->
  (exists n ty', ty1 = own_ptr n ty') \/ exists k ty', ty1 = uniq_bor k ty' 
.
Proof.
  intros.
  inversion H;subst. 
  left.
  exists n. exists ty'.
  auto.
  right. 
  exists κ. exists ty2.
  auto.
Qed.

Definition write_expr_check e p1 p2:= 
     e = (p1 <- p2)%E \/ (exists i, e = (p1 <- #i ;; p1 +ₗ #1 <- p2))
              \/ (exists i, e = (p1 <-{Σ i} ()))
              \/ (exists i ty, e = (p1 <- #i ;; 
                                      p1 +ₗ #1 <-{
                                      my_type_system.size ty} !p2))
              \/ exists n, e = (p1 <-{n} !p2)
              
.

Lemma Ins_write_capbility_check : 
forall E L T1 e v T2 p1 p2 (T2':val -> tctx) , safe_type_Ins E L T1 e T2' ->
                       T2 = T2' v ->
                       write_expr_check e p1 p2 ->
(*                        (forall T T' ty , T1 = T ++ [e ◁ ty] ++ T' ->
                                       T2 = T ++ ([v ◁ ty]) ++ T' -> False ) -> *)
 (*                       (forall T T' E' tyl ty, T1 = T ++ T1 ++ T' ->
                                       T2 = T ++ ([v ◁ fn E' tyl ty]) ++ T' -> False ) ->
 *) 
(*                        (forall E' tyl ty, 
                                       T2 = [v ◁ fn E' tyl ty] -> False ) -> *)

    (exists tctx_elt ty n k, (tctx_elt = TCtx_hasty p1 (own_ptr n ty) \/
                           tctx_elt = TCtx_hasty p1 (uniq_bor k ty) )
                           /\ In tctx_elt T1 ) 
    \/ (exists ty,In (e ◁ ty) T1 /\ In (v ◁ ty) T2 ).
Proof.
  intros. rename H1 into H'.
  unfold write_expr_check in H'.
  inversion H;subst;try( do 4 (destruct H' as [ H' | H' ];simpljoin; tryfalse;simpljoin1;tryfalse)).
  2:{
    right.
    eexists. split. simpl. left. eauto. left. eauto.
   (* split.
    instantiate(1:=[]).  instantiate(1:=ty). instantiate(1:=[]). 
    simpl . eauto. simpl. eauto. *)
  }
  {
  unfold IntoVal in H3.
  destruct H'. subst. simpl in H3.
  From lrust.lang Require Export notation.
  destruct ((fn: argsb := e0)%V); tryfalse.
  destruct H0. destruct H0. subst.
  simpl in H3.  destruct ((fn: argsb := e0)%V); tryfalse.
  destruct H0. destruct H0. subst.
  simpl in H3.  destruct ((fn: argsb := e0)%V); tryfalse.
  destruct H0. do 2 destruct H0. subst.
  simpl in H3.  destruct ((fn: argsb := e0)%V); tryfalse.
  destruct H0.  subst.
  simpl in H3.  destruct ((fn: argsb := e0)%V); tryfalse.
  }
(* split. instantiate(1:=[]).  instantiate(1:=[]).
  rewrite <- app_nil_end. eauto.
  rewrite <- app_nil_end. eauto. *)
  + left. inversion H1;subst. destruct H'.
    injection H2 as eq. subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    destruct H2; simpljoin1; tryfalse.
    destruct H2; simpljoin1; tryfalse.
    injection H2 as eq. subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    destruct H2; simpljoin1; tryfalse.
    destruct H'.
    injection H2 as eq. subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
    destruct H2; simpljoin1; tryfalse.
    destruct H2; simpljoin1; tryfalse.
    injection H2 as eq. subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
    destruct H2; simpljoin1; tryfalse.
  + left. inversion H2;subst. 
    destruct H'. tryfalse.
    destruct H3; simpljoin1; tryfalse.
    injection H3 as eq. subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    destruct H3; simpljoin1; tryfalse.
    destruct H3; simpljoin1; tryfalse.
    destruct H'. tryfalse.
    destruct H3; simpljoin1; tryfalse.
    injection H3 as eq. subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
    destruct H3; simpljoin1; tryfalse.
    destruct H3; simpljoin1; tryfalse.
  + left. inversion H2;subst. destruct H'.
    injection H3 as eq. subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    destruct H3; simpljoin1; tryfalse.
    destruct H3; simpljoin1; tryfalse.
    injection H3 as eq. subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    destruct H3; simpljoin1; tryfalse.
    destruct H'.
    injection H3 as eq. subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
    destruct H3; simpljoin1; tryfalse.
    destruct H3; simpljoin1; tryfalse.
    injection H3 as eq. subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
    destruct H3; simpljoin1; tryfalse.
  + left. inversion H2;subst.
    injection H0 as eq;subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    injection H0 as eq;subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
  + left. inversion H2;subst.
    injection H0 as eq;subst.
    do 4 eexists.
    split. left. eauto.
    simpl. left. eauto.
    injection H0 as eq;subst.
    do 4 eexists.
    split. right. eauto.
    simpl. left. eauto.
  Unshelve. exact static. exact static.
  exact 0%nat. exact 0%nat.
  exact static. exact 0%nat.
  exact static. exact static.
  exact 0%nat. exact 0%nat.
  exact static. exact 0%nat.
  exact static. exact 0%nat.
Qed.


Lemma have_own :
forall E L T1 T2 p n ty, safe_tctx_incl E L T1 T2 ->
                       In (p ◁ own_ptr n ty)  T2 ->
                    exists ty', In (p ◁ own_ptr n ty')  T1.
Proof.
  intros. generalize dependent ty.
  induction H;subst.
  + intros. simpl in H0. destruct H0. 2:{exfalso;eauto. }
    injection H0 as eq;subst.
    eapply safe_subtyping_own_ptr' in H.
    destruct H. subst. eexists. simpl. left. eauto.
  + intros. simpl in H0. destruct H0.
    injection H0 as eq. subst.
    inversion H. 
    destruct H0. injection H0 as eq. subst.
    inversion H. exfalso;eauto.
  + intros. eapply list_elem_of_In in H0.
    eapply elem_of_submseteq in H0. 2:{eauto. }
    eexists. eapply list_elem_of_In. eauto.
  + intros. simpl in H0. destruct H0. injection H0 as eq. tryfalse.
    exfalso. eauto.
  + intros. simpl in H0. destruct H0. injection H as eq. tryfalse.
    simpl in H. destruct H. tryfalse.
    exfalso. eauto.
  + intros. simpl in H0. destruct H0. injection H0 as eq. tryfalse.
    simpl in H0. destruct H0. tryfalse.
    exfalso. eauto.
  + intros. simpl in H0. destruct H0. injection H0 as eq. tryfalse.
    simpl in H0. destruct H0. tryfalse.
    exfalso. eauto.
  + intros. eapply list_elem_of_In in H0. eapply elem_of_app in H0.
    destruct H0.
    eexists. eapply list_elem_of_In. eapply elem_of_app. left.
    eauto.  eapply list_elem_of_In in H0. eapply IHsafe_tctx_incl in H0.
    destruct H0.
    eexists. eapply list_elem_of_In. eapply elem_of_app. right. eapply list_elem_of_In in H0.  eauto.
  + intros. eapply list_elem_of_In in H0. eapply elem_of_app in H0.
    destruct H0.
    eapply list_elem_of_In in H0. eapply IHsafe_tctx_incl in H0.
    destruct H0.
    eexists. eapply list_elem_of_In. eapply elem_of_app. left. eapply list_elem_of_In in H0.  eauto.
    eexists. eapply list_elem_of_In. eapply elem_of_app. right. eauto.
  + intros. eapply IHsafe_tctx_incl2 in H1. destruct H1.
    eapply IHsafe_tctx_incl1 in H1. destruct H1.
    eexists. eauto.
Qed.

Definition read_expr_check e p2:= 
     e = !p2 \/ (exists p1 ty i, e = (p1 <-{(my_type_system.size ty),Σ i} !p2))
             \/ (exists n p1, e = (p1 <-{n} !p2)).

Lemma Ins_read_capbility_check : 
forall E L T1 e v T2 p2 (T2':val -> tctx) , safe_type_Ins E L T1 e T2' ->
                       T2 = T2' v ->
                       read_expr_check e p2 ->
(*                        (forall T T' ty , T1 = T ++ [e ◁ ty] ++ T' ->
                                       T2 = T ++ ([v ◁ ty]) ++ T' -> False ) -> *)
 (*                       (forall T T' E' tyl ty, T1 = T ++ T1 ++ T' ->
                                       T2 = T ++ ([v ◁ fn E' tyl ty]) ++ T' -> False ) ->
 *) 
(*                        (forall E' tyl ty, 
                                       T2 = [v ◁ fn E' tyl ty] -> False ) -> *)

    (exists tctx_elt ty n k, (tctx_elt = TCtx_hasty p2 (own_ptr n ty) \/
                           tctx_elt = TCtx_hasty p2 (uniq_bor k ty) \/
                             tctx_elt = TCtx_hasty p2 (shr_bor k ty)                                         )
                           /\ In tctx_elt T1 ) 
    \/ (exists ty,In (e ◁ ty) T1 /\ In (v ◁ ty) T2 ).
Proof.
  intros. rename H1 into H'.
  unfold read_expr_check in H'.

  inversion H;subst;try( do 3 (destruct H' as [ H' | H' ];simpljoin; tryfalse;simpljoin1;tryfalse)).
(*   2:{
    right.
    eexists. split. simpl. left. eauto. left. eauto.
   (* split.
    instantiate(1:=[]).  instantiate(1:=ty). instantiate(1:=[]). 
    simpl . eauto. simpl. eauto. *)
  } *)
  {
  unfold IntoVal in H3.
  destruct H'. subst. simpl in H3.
  From lrust.lang Require Export notation.
  destruct ((fn: argsb := e0)%V); tryfalse.
  destruct H0. do 3 destruct H0. subst.
  simpl in H3.  destruct ((fn: argsb := e0)%V); tryfalse.
  destruct H0. destruct H0. subst.
  simpl in H3.  destruct ((fn: argsb := e0)%V); tryfalse.
  }
(* split. instantiate(1:=[]).  instantiate(1:=[]).
  rewrite <- app_nil_end. eauto.
  rewrite <- app_nil_end. eauto. *)
  + right. exists ty. split.
    simpl. left. eauto.
    simpl. left. eauto.
  + destruct H'.
    injection H0 as eq. subst.
    inversion H2; subst.
    left. do 4 eexists. split.
    left. eauto. simpl. left. eauto.
    left. do 4 eexists. split.
    left. eauto. simpl. left. eauto.
    left. do 4 eexists. split.
    right. right. eauto. simpl. left. eauto.
    left. do 4 eexists. split.
    right. left. eauto. simpl. left. eauto.
    destruct H0. do 3 destruct H0. inversion H0.
    do 2 destruct H0. inversion H0.
  + destruct H'.
    injection H0 as eq. subst.
    left. do 4 eexists.
    split. right. left. eauto.
    simpl. left. eauto.
    destruct H0. do 3 destruct H0. inversion H0.
    do 2 destruct H0. inversion H0.
  + destruct H'.
    injection H0 as eq. subst.
    left. do 4 eexists.
    split. right. right. eauto.
    simpl. left. eauto.
    destruct H0. do 3 destruct H0. inversion H0.
    do 2 destruct H0. inversion H0.
  + destruct H'.
    injection H0 as eq. subst.
    left. do 4 eexists.
    split. right. left. eauto.
    simpl. left. eauto.
    destruct H0. do 3 destruct H0. inversion H0.
    do 2 destruct H0. inversion H0.
  + destruct H'.
    injection H0 as eq. subst.
    left. do 4 eexists.
    split. right. right. eauto.
    simpl. left. eauto.
    destruct H0. do 3 destruct H0. inversion H0.
    do 2 destruct H0. inversion H0.
  + destruct H'. inversion H0.
    destruct H0.
    do 3 destruct H0. injection H0 as eq. subst.
    inversion H3; subst.
    left. do 4 eexists. split.
    left. eauto.
    simpl. right. left. eauto.
    left. do 4 eexists. split.
    left. eauto.
    simpl. right. left. eauto.
    left. do 4 eexists. split.
    right. right. eauto.
    simpl. right. left. eauto.
    left. do 4 eexists. split.
    right. left. eauto.
    simpl. right. left. eauto.
    do 2 destruct H0. inversion H0.

  + left. destruct H'. inversion H0.
    destruct H0. do 3 destruct H0.
    inversion H0.
    do 2 destruct H0. injection H0 as eq. subst.
    inversion H3; subst.
    do 4 eexists. split.
    left. eauto. simpl. right. left. eauto.
    do 4 eexists. split.
    left. eauto. simpl. right. left. eauto.
    do 4 eexists. split.
    right. right. eauto. simpl. right. left. eauto.
    do 4 eexists. split.
    right. left. eauto. simpl. right. left. eauto.
  Unshelve. exact static. exact static.
  exact 0%nat. exact 0%nat.
  exact 0%nat. exact 0%nat.
  exact 0%nat. exact 0%nat.
  exact static. exact static. exact 0%nat.
  exact 0%nat. exact static. exact static. 
  exact 0%nat. exact 0%nat.
Qed.

Definition capability_not_add_part1' (T1 T2 :tctx ) : Prop := 
  forall (tctx_elt0 : tctx_elt) (p : path) (ty : type) (n : nat),
    In tctx_elt0 T2
    → tctx_elt0 = (p ◁ own_ptr n ty)
      → (∃ (ty' : type) (tctx_elt' : tctx_elt),
           tctx_elt' = (p ◁ own_ptr n ty')
           ∧ In tctx_elt' T1).

Definition capability_not_add_part2' (T1 T2 :tctx ) : Prop := 
  forall (tctx_elt0 : tctx_elt) (p : path) (k : lft) (ty : type),
    In tctx_elt0 T2
    → tctx_elt0 = (p ◁ &uniq{k} ty)
      → (∃ (tctx_elt' : tctx_elt) (n' : nat) (ty' : type),
           tctx_elt' = (p ◁ own_ptr n' ty')
           ∧ In tctx_elt' T1 )
        ∨ (∃ (k' : lft) (ty' : type) (tctx_elt' : tctx_elt),
             tctx_elt' = (p ◁ &uniq{k'} ty')
             ∧ In tctx_elt' T1).

Definition capability_not_add_part3' (T1 T2 :tctx ) : Prop := 
  forall (tctx_elt0 : tctx_elt) (p : path) (k : lft) (ty : type),
    In tctx_elt0 T2
    → tctx_elt0 = (p ◁ &shr{k} ty)
      → (∃ (k' : lft) (ty' : type) (tctx_elt' : tctx_elt),
           tctx_elt' = (p ◁ &shr{k'} ty')
           ∧ In tctx_elt' T1)
        ∨ (∃ (tctx_elt' : tctx_elt) (n' : nat) (ty' : type),
             tctx_elt' = (p ◁ own_ptr n' ty')
             ∧ In tctx_elt' T1)
          ∨ (∃ (k' : lft) (ty' : type) (tctx_elt' : tctx_elt),
               tctx_elt' = (p ◁ &uniq{k'} ty')
               ∧ In tctx_elt' T1).


Lemma safe_tctx_incl_capability_not_add_tran'' :
forall T2 T1 T3,  capability_not_add_part1' T1
                      T2
                    ∧ capability_not_add_part2'
                        T1 T2
                    ∧ capability_not_add_part3'
                        T1 T2
                    ->
                  capability_not_add_part1' T2
                      T3
                    ∧ capability_not_add_part2'
                        T2 T3
                    ∧ capability_not_add_part3'
                        T2 T3
                    ->
                capability_not_add_part1' T1 T3
                ∧ capability_not_add_part2' T1 T3
                ∧ capability_not_add_part3' T1 T3.
Proof.
  intros.
  split.
  simpljoin1.
  unfold capability_not_add_part1' in *.
  intros. eapply H0 in H5. 2:eauto.
  simpljoin1.
  eapply H in H7. simpljoin1. 2:eauto.
  do 3 eexists. eauto. eauto.
  split. unfold capability_not_add_part2'.
  intros. simpljoin1.
  eapply H3 in H1. destruct H1. eauto.
  simpljoin1. eapply H in H2.
  destruct H2. eauto. simpljoin1.
  left. do 3 eexists. split;eauto.
  simpljoin1. eapply H5 in H2.
  destruct H2. eauto. simpljoin1.
  left. do 3 eexists. split;eauto.
  simpljoin1. right. do 3 eexists. split;eauto.
  simpljoin1.
  unfold capability_not_add_part3'. intros.
  eapply H2 in H5.
  destruct H5. eauto.
  simpljoin1. eapply H4 in H7.
  destruct H7. eauto.
  simpljoin1.
  left. do 3 eexists. split;eauto.
  destruct H5. simpljoin1. 
  right. left. do 3 eexists. split;eauto.
  simpljoin1. right. right.
  do 3 eexists. eauto.
  destruct H5.
  simpljoin1. eapply H in H7.
  destruct H7. eauto. simpljoin1.
  right. left. do 3 eexists. split;eauto.
  simpljoin1. eapply H3 in H7.
  destruct H7. eauto.
  simpljoin1. right. left. do 3 eexists. eauto.
  simpljoin1. right. right. do 3 eexists. split; eauto.
Qed.   



Lemma safe_tctx_incl_cap_not_add :
forall E L T1 T2, safe_tctx_incl E L T1 T2 ->
                capability_not_add_part1' T1 T2
                ∧ capability_not_add_part2' T1 T2
                ∧ capability_not_add_part3' T1 T2.
Proof.
  intros.
  induction H.
  -
    remember ty1. remember ty2.
    split.
    unfold capability_not_add_part1'. intros.
    apply in_inv in H0. destruct H0. subst.
    destruct ty2; tryfalse.
    assert(H3:=H).
    eapply safe_subtyping_own_ptr in H. do 2 destruct H.
    subst. injection H1 as eq. subst.
    do 3 eexists. split; eauto.  
    eapply list_elem_of_In. eapply list_elem_of_singleton.
    eapply safe_subtyping_own_size_eq in H3. subst. eauto.
    simpl in H0. exfalso. eauto.
    split.
    unfold capability_not_add_part2'. intros.
    apply in_inv in H0. destruct H0. subst.
    destruct ty2; tryfalse.
    assert(H3:=H). 
    eapply safe_subtyping_uniq_ptr in H. do 2 destruct H.
    subst. injection H1 as eq. subst.
    right. 
    do 4 eexists. eauto. 
    eapply list_elem_of_In. eapply list_elem_of_singleton. auto.
    assert(~In tctx_elt0 []) by eapply in_nil. tryfalse.
    unfold capability_not_add_part3'.
    intros. apply in_inv in H0. destruct H0. subst.
    destruct ty2;tryfalse.
    assert(H':= H).
    eapply safe_subtyping_shr_ptr in H. do 2 destruct H. subst.
    injection H1 as eq;subst.
    left. do 3 eexists.
    split ;eauto.
    eapply list_elem_of_In. eapply list_elem_of_singleton.
    eauto.
    simpl in H0. exfalso. eauto.
  - split. 
    unfold capability_not_add_part1'. intros.
    subst. simpl in H0.
    destruct H0. injection H0 as eq. subst.
    do 3 eexists. eauto. simpl. left. eauto.
    destruct H0. injection H0 as eq. subst.
    do 3 eexists. eauto. simpl. left. eauto. exfalso. eauto.
    split. 
    unfold capability_not_add_part2'. intros.
    subst. simpl in H0.
    destruct H0. injection H0 as eq. subst.
    inversion H.
    destruct H0. injection H0 as eq. subst.
    inversion H. exfalso. eauto.
    unfold capability_not_add_part3'. intros.
    subst. simpl in H0.
    destruct H0. injection H0 as eq. subst.
    left.
    do 3 eexists. eauto. simpl. split. eauto.
    left. eauto. left. 
    destruct H0. injection H0 as eq. subst.
    do 3 eexists. eauto. split;eauto. simpl. left. eauto.
    exfalso. eauto.
  -
(* left.  *)split. generalize dependent T2.
    induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part1'.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros. 
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1.
    unfold capability_not_add_part1'. intros.
    apply in_inv in H2; destruct H2.  subst. (* left. *) 
    exists ty. exists (p ◁ own_ptr n ty). 
    split. auto. rewrite H. eapply list_elem_of_In.
    eapply list_elem_of_here. 
    destruct ty;simpl; eauto. eauto.
    split.  
    generalize dependent T2. induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part2'.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part2'. intros. 
    apply in_inv in H2; destruct H2.  subst.
    right. 
    exists k. exists ty. exists (p ◁ &uniq{k} ty). 
    split. auto. eapply list_elem_of_In.
    rewrite H.
    eapply list_elem_of_here.
    subst. eapply H1 in H2.
    destruct H2. eauto. simpljoin1.
    left. do 3 eexists. split;eauto.
    simpljoin1.
    right. do 3 eexists. split;eauto.  
    generalize dependent T2. induction T1.  intros. 
    (* Search (_ ⊆+ []). eapply submseteq_nil_r in H0. subst. *)
    unfold capability_not_add_part3'.
    intros. assert(Hnil:~In tctx_elt0 []) by eapply in_nil. tryfalse.
    intros.
    eapply submseteq_cons_l in H. destruct H. destruct H.
    eapply submseteq_cons in H0. instantiate(1:=a) in H0.
    rewrite <- H in H0.
    assert (T1 ⊆+ T2) by auto. eapply contains_tctx_incl in H0.
    eapply IHT1 in H1. 
    unfold capability_not_add_part3'. intros. 
    apply in_inv in H2; destruct H2.  subst.
    left. 
    exists k. exists ty. exists (p ◁ &shr{k} ty). 
    split. auto. eapply list_elem_of_In.
    rewrite H.
    eapply list_elem_of_here.
    subst. eapply H1 in H2.
    destruct H2. eauto. simpljoin1.
    left. do 3 eexists. split;eauto.
    destruct H2. simpljoin1.
    right. left. do 3 eexists. eauto.
    simpljoin1. right. right. do 3 eexists. eauto.
  - split. unfold capability_not_add_part1'.
    intros.
    simpl in H0. destruct H0. subst. tryfalse.
    exfalso. eauto.
    split.
    unfold capability_not_add_part2'. intros.
    simpl in H0. destruct H0. subst. tryfalse.
    exfalso. eauto.
    unfold capability_not_add_part3'. intros.
    simpl in H0. destruct H0. subst. tryfalse.
    injection H1 as eq. intros. subst.
    right. right. do 3 eexists. split. eauto.
    simpl. left. eauto.
    exfalso. eauto.
  - split. unfold capability_not_add_part1'.
    intros. simpl in H. destruct H. subst. tryfalse.
    destruct H. subst. tryfalse.
    exfalso. eauto.
    split. unfold capability_not_add_part2'.
    intros. simpl in H.
    destruct H. subst. injection H0 as eq.
    subst. left. do 3 eexists. split. eauto.
    simpl. left. eauto.
    destruct H. tryfalse. exfalso. eauto.
    unfold capability_not_add_part3'.
    intros. simpl in H.
    destruct H. subst. tryfalse.
    destruct H. subst. tryfalse.
    exfalso. auto.
  - split.
    unfold capability_not_add_part1'. intros.
    destruct H0. subst. tryfalse.
    destruct H0. subst. tryfalse.
    exfalso; auto.
    split.
    unfold capability_not_add_part2'. intros.
    destruct H0. subst. tryfalse.
    injection H1 as eq; subst.
    right. do 3 eexists.
    split; eauto. simpl. left. eauto.
    destruct H0. subst. tryfalse.
    exfalso; auto.
    unfold capability_not_add_part3'. intros.
    destruct H0. subst. tryfalse.
    destruct H0. subst. tryfalse.
    exfalso; auto.
  - split.
    unfold capability_not_add_part1'. intros.
    destruct H0. subst. tryfalse.
    destruct H0. subst. tryfalse.
    exfalso; auto.
    split.
    unfold capability_not_add_part2'. intros.
    destruct H0. subst. tryfalse.
    destruct H0. subst. tryfalse.
    exfalso; auto.
    unfold capability_not_add_part3'. intros.
    destruct H0. subst. tryfalse.
    injection H1 as eq; subst.
    left. do 3 eexists.
    split; eauto. simpl. left. eauto.
    destruct H0. subst. tryfalse.
    exfalso; auto.
  - split. (* generalize dependent T1. generalize dependent T2. *)
    induction T. intros. rename IHsafe_tctx_incl into H0.
    simpl. destruct H0; auto. 
    intros. destruct IHsafe_tctx_incl. unfold capability_not_add_part1' in *.
    intros. eapply in_inv in H2. 
    destruct H2. subst.
    do 3 eexists. split; eauto.   
    eapply in_or_app. left. eapply in_eq.
    eapply IHT in H2. 2:eauto. destruct H2. do 2 destruct H2.
    subst.
    exists x. eexists.
    split. eauto. right. eauto.
    split. induction T. intros.
    simpl. destruct IHsafe_tctx_incl; auto.
    destruct H1. auto.
    intros. destruct IHsafe_tctx_incl. destruct H1. unfold capability_not_add_part2' in *.
    intros.   
    eapply in_inv in H3. destruct H3. subst.
    right. 
    do 4 eexists. eauto.  
    eapply in_or_app. left. eapply in_eq.
    eapply IHT in H3. 2:eauto. destruct H3.  
    do 3 destruct H3. destruct H3. subst.
    left. eexists. exists x0. exists x1. split. eauto.
    eapply in_app_or in H5. destruct H5. eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.
    simpljoin1.
    right. 
    exists x. exists x0. eexists.
    split. eauto.
    eapply in_app_or in H5. destruct H5.  eapply in_or_app.
    left. eapply in_cons. auto. eapply in_or_app. right. auto.
    (* generalize dependent T1. generalize dependent T2. *)
    induction T. intros. rename IHsafe_tctx_incl into H0.
    destruct H0; auto. destruct H1. eauto.
    intros. destruct IHsafe_tctx_incl. destruct H1. unfold capability_not_add_part3' in *.
    intros.   
    eapply in_inv in H3. destruct H3. subst.
    left.
    do 4 eexists. eauto.  
    eapply in_or_app. left. eapply in_eq.
    eapply IHT in H3. 2:eauto. destruct H3.  
    do 3 destruct H3. destruct H3. subst.
    left. eexists. exists x0. eexists. split. eauto.
    eapply in_app_or in H5. destruct H5. eapply in_or_app.
    left. eapply in_cons. auto.  eauto.
    simpl. right. eapply in_or_app. right. auto.
    destruct H3.  
    do 3 destruct H3. destruct H3. subst.
    right. left. do 3 eexists. split. eauto.
    eapply in_app_or in H5. destruct H5. eapply in_or_app.
    left. eapply in_cons. auto.  eauto.
    simpl. right. eapply in_or_app. right. auto.
    simpljoin1. right. right.
    do 3 eexists. split. eauto.
    simpl. right. eauto.
  - split. (* generalize dependent T1. generalize dependent T2. *)
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r. destruct IHsafe_tctx_incl; auto.
    intros. destruct IHsafe_tctx_incl. unfold capability_not_add_part1' in *.
    intros. eapply in_app_or in H2. destruct H2. 
    assert(forall T, In tctx_elt0 (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H4. 2:eauto. destruct H4. do 2 destruct H4. subst.
    do 2 eexists. split. eauto.
    eapply in_or_app. eapply in_app_or in H5.
    destruct H5. left. eauto. right. eapply in_cons. auto.
    do 3 eexists. eauto. subst. 
    eapply in_or_app. right. eauto.
    split.
    simpljoin1.
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r.  auto.
    unfold capability_not_add_part2' in *.
    intros. subst. eapply in_app_or in H3. destruct H3. 
    assert(forall T, In (p ◁ &uniq{k} ty) (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H4. 2:eauto. destruct H4. do 4 destruct H4. subst.
    left. do 3 eexists. split. eauto.
    eapply in_app_or in H5. destruct H5.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    do 4 destruct H4.
    right. subst. do 4 eexists.
    eauto. eapply in_app_or in H5.
    destruct H5. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    right. do 4 eexists. eauto.
    eapply in_or_app. right. eauto.
    simpljoin1.
    induction T. intros. rewrite app_nil_r. rewrite app_nil_r.  auto.
    unfold capability_not_add_part3' in *.
    intros. subst. eapply in_app_or in H3. destruct H3. 
    assert(forall T, In (p ◁ &shr{k} ty) (T2 ++ T)).
    intros. eapply in_or_app. left. auto.  
    eapply IHT in H4. 2:eauto. destruct H4. do 4 destruct H4. subst.
    left. do 3 eexists. split. eauto.
    eapply in_app_or in H5. destruct H5.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    do 5 destruct H4.
    right. left. subst. do 4 eexists.
    eauto. eapply in_app_or in H5.
    destruct H5. eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. eauto.
    right. right. subst. do 4 eexists. eauto.
    eapply in_app_or in H5. destruct H5.
    eapply in_or_app. left. eauto.
    eapply in_or_app. right. eapply in_cons. auto. eauto.
    left. do 4 eexists. eauto. eapply in_or_app. 
    right. eauto.
  - eapply safe_tctx_incl_capability_not_add_tran''.
    eauto. eauto.
  Unshelve. exact E. exact L.
    exact E. exact L. exact E. exact L.
Qed.
 

(* Lemma determinism:forall t t' t'' σ σ' σ'' list list',
  (prim_step t σ [] t' σ' list) ->
  (prim_step t σ [] t'' σ'' list') -> expr_beq t' t''.
Proof.
  intros.
  eapply head_reducible_prim_step in H.
  2:{
    eapply head_reducible_no_obs_reducible.
    unfold head_reducible_no_obs.
  eapply fill_prim_step in H.
  e  
 *)
(* Lemma safe_tctx_incl_bool_tran E L T0 T4 p:
 safe_tctx_incl E L T0 T4 ->
 In ((!p)%E ◁ bool) T4 ->
 In ((!p)%E ◁ bool) T0.
Proof.
  intros.
  induction H;subst.
  - simpl in H0.
    destruct H0. 
    injection H0 as eq;subst. remember bool.
    induction H; tryfalse.  subst; try( simpl; left;  eauto).
    assert(H':= Heqt).
    eapply IHsafe_subtyping2 in Heqt.
    simpl in Heqt. destruct Heqt.
    injection H1 as eq. subst.
    eapply IHsafe_subtyping1. auto.
    exfalso. eauto. exfalso. eauto.
  - simpl in H0. destruct H0.
    injection H0 as eq. subst.
    simpl. left. eauto.
    simpl. auto.
  - Search (_ ⊆+ _ -> _ ).
     *)
    


(* Lemma Fun_case_read_check :
forall E L C T1 T2 p el, safe_type_fun E L C T1 (case: !p of el) T2 ->
                          (exists tctx_elt ty n k, (tctx_elt = TCtx_hasty p (own_ptr n ty) \/
                           tctx_elt = TCtx_hasty p (uniq_bor k ty) \/
                             tctx_elt = TCtx_hasty p (shr_bor k ty)                                         )
                           /\ In tctx_elt T1 )
                           \/ In (TCtx_hasty (!p) bool) T1 .
Proof.
   intros.
   remember (case: !p of el). 
   induction H;inversion Heqe.
   - subst.
   eapply IHsafe_type_fun in H2.
   destruct H2. simpljoin1. destruct H2.  subst.
   eapply safe_tctx_incl_cap_not_add in H0.
   simpljoin1.
   eapply H0 in H3. destruct H3.
   eauto. left. simpljoin1.   do 4 eexists.
   split. left. eauto. eauto.
   destruct H2. subst.
   eapply safe_tctx_incl_cap_not_add in H0.
   simpljoin1.
   eapply H2 in H3. destruct H3. eauto.
   left.
   simpljoin1. do 4 eexists.
   split. left. eauto. eauto.
   left.
   simpljoin1. do 4 eexists.
   split. right. left. eauto. eauto.
   subst.
   eapply safe_tctx_incl_cap_not_add in H0.
   simpljoin1.
   eapply H4 in H3. destruct H3. eauto.
   left.
   simpljoin1. do 4 eexists.
   split. right. right. eauto. eauto.
   destruct H3. left.
   simpljoin1. do 4 eexists.
   split. left. eauto. eauto.
   simpljoin1. left. do 4 eexists.
   split. right. left. eauto. eauto.
   clear H IHsafe_type_fun H1.
   Search (In _ _).
   induction T1. simpl in H2. exfalso. eauto.
   simpl in H2. destruct H2.
   subst. clear IHT1.
   { inversion H0;
     subst. 
    + right. clear H0. remember bool.  induction H4; tryfalse.
      simpl. left. eauto.
      assert(H:= Heqt).
      eapply IHsafe_subtyping2 in Heqt.
      simpl in Heqt. destruct Heqt. injection H0 as eq;subst.
      eapply IHsafe_subtyping1. eauto.
      exfalso. eauto.
    + right. simpl. left. eauto.
    + Search (_ :: _ ⊆+ _).
      eapply 

 inversion H4;subst. right. simpl. left. eauto.

   simpl in H2.

  - do 4 eexists. split. right. left.
   eauto. simpl.
   left. eauto.
  - do 4 eexists. 
   split. right. right. eauto.
   simpl. left. eauto.
  - do 4 eexists. 
   split. left. eauto.
   simpl. left. eauto.
  - 
   right.submseteq_cons_l in H.
      destruct H. destruct H. Search (_ ≡ₚ _).
      right. Search (_ -> In _ _ ).
      Search (_ ≡ₚ _). eapply Permutation_sym in H.
      eapply Permutation_in in H.
      eauto. simpl. left. eauto.
    + assert(In ((!p)%E ◁ bool) (((!p)%E ◁ bool) :: T1)).
      simpl. left. eauto.
      rewrite <- H in H1.
      right. Search (In _ (_ ++ _)).
      eapply in_or_app. eapply in_app_or in H1.
      destruct H1. left. auto.
      eapply

  }

 inversion H4;subst. right. simpl. left. eauto.

   simpl in H2.

  - do 4 eexists. split. right. left.
   eauto. simpl.
   left. eauto.
  - do 4 eexists. 
   split. right. right. eauto.
   simpl. left. eauto.
  - do 4 eexists. 
   split. left. eauto.
   simpl. left. eauto.
  - 
   right.

*)






