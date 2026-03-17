From lrust.typing.examples Require Import my_type_system_v4.
From lrust.lang Require Import notation.
From lrust.lang Require Import races.
From lrust.lang Require Export lang heap.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Definition eval_path:= to_val. 


(* 定义值的四种形式 *)

Inductive value : expr -> Prop :=
  |LitV' (l : base_lit) : value (Lit l)
  |RecV' (f : binder) (xl : list binder) (e : expr) : value (Rec f xl e ).


(* 判断两个类型是否相等 *)

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

(* RustBelt中的类型相等引理 *)

Lemma type_beq_correct(e1 e2 : type) : type_beq e1 e2 ↔ e1 = e2.
Admitted.


(* 指令规则中的类型权能语义解释 *)

Definition int_is_val:= forall E L (T: tctx_elt) (Tl: tctx) p1 p2 VT , safe_type_Ins E L Tl p1 VT ->
                        (In T Tl) -> T = TCtx_hasty p2 int -> (exists z ,  expr_beq p2 (Lit (LitInt z))).

Definition own_ptr_is_val:= forall E L (T: tctx_elt) (Tl: tctx) p1 p2 VT n ty (σ:state) , 
                            safe_type_Ins E L Tl p1 VT ->
                            (In T Tl) -> T = TCtx_hasty p2 (own_ptr n ty) -> 
                            (exists l (v:val),  (expr_beq p2 (Lit (LitLoc l)) /\ σ !! l = Some (RSt O, v) )).

Definition mut_ptr_is_val:= forall E L (T: tctx_elt) (Tl: tctx) p1 p2 VT k ty (σ:state) , 
                            safe_type_Ins E L Tl p1 VT ->
                            (In T Tl) -> T = TCtx_hasty p2 (uniq_bor k ty) -> 
                            (exists l (v:val),  expr_beq p2 (Lit (LitLoc l)) /\ σ !! l = Some (RSt O, v) ).

Definition shr_ptr_is_val:= forall E L (T: tctx_elt) (Tl: tctx) p1 p2 VT k ty (σ:state) n,
                            safe_type_Ins E L Tl p1 VT ->
                            (In T Tl) -> T = TCtx_hasty p2 (shr_bor k ty) ->
                            (exists l (v:val),  expr_beq p2 (Lit (LitLoc l)) /\ σ !! l = Some (RSt n, v)).

Definition path_is_val:= forall E L (T: tctx_elt) (Tl: tctx) p1 p2 VT ty , safe_type_Ins E L Tl p1 VT ->
                        (In T Tl) -> T = TCtx_hasty p2 ty -> exists v, eval_path p2 = Some v.


(* 函数体规则中的简单类型权能语义解释 *)

Definition fun_mut:= forall E L C Tl T p e κ ty (σ:state) tyl , 
                     safe_type_fun E L C Tl e -> (In T Tl) -> T =  (p ◁ &uniq{κ}ty) /\ ~ type_beq ty (sum tyl)  -> 
                    (exists l (v:val),  expr_beq p (Lit (LitLoc l))/\ σ !! l = Some (RSt O, v)).

Definition fun_shr:= forall E L C Tl T p e κ ty (σ:state) n tyl, 
                     safe_type_fun E L C Tl e -> (In T Tl) -> T =  (p ◁ &shr{κ}ty) /\ ~ type_beq ty (sum tyl)  -> 
                     (exists l (v:val),  expr_beq p (Lit (LitLoc l))/\ σ !! l = Some (RSt n, v)).

Definition fun_own:= forall E L C Tl T p e n ty (σ:state) tyl, 
                     safe_type_fun E L C Tl e -> (In T Tl) ->
                     T =  (p ◁ own_ptr n ty) /\ ~ type_beq ty (sum tyl) -> 
                    (exists l (v:val),  expr_beq p (Lit (LitLoc l)) /\ σ !! l = Some (RSt O, v)).


(* 函数体规则中的复合类型权能语义解释 *)

Definition fun_mut':= forall E L C Tl T p e κ ty (σ:state) tyl , 
                     safe_type_fun E L C Tl e -> (In T Tl) -> T =  (p ◁ &uniq{κ}ty) /\  type_beq ty (sum tyl)  -> 
                    (exists l (i:nat),  expr_beq p (Lit (LitLoc l))/\ σ !! l = Some (RSt O, #i) /\ i <  length tyl).

Definition fun_shr':= forall E L C Tl T p e κ ty (σ:state) n tyl, 
                     safe_type_fun E L C Tl e -> (In T Tl) -> T =  (p ◁ &shr{κ}ty) /\  type_beq ty (sum tyl)  -> 
                     (exists l (i:nat),  expr_beq p (Lit (LitLoc l))/\ σ !! l = Some (RSt n, #i)/\ i <  length tyl).

Definition fun_own':= forall E L C Tl T p e n ty (σ:state) tyl, 
                     safe_type_fun E L C Tl e -> (In T Tl) ->
                     T =  (p ◁ own_ptr n ty) /\ type_beq ty (sum tyl) -> 
                    (exists l (i:nat),  expr_beq p (Lit (LitLoc l)) /\ σ !! l = Some (RSt O, #i)/\ i <  length tyl).

Definition bool_is_val:=forall (p:expr) (T:tctx), (p ◁ bool) ∈ T -> 
                         (expr_beq p (Lit (LitInt 0%Z)) \/ expr_beq p (Lit (LitInt 1%Z))).


Definition fn_is_function:= forall p E tyl ty (T:tctx) , (p ◁ fn E tyl ty) ∈ T -> 
                            exists f xl e, expr_beq p (Rec f xl e).


Lemma eval_path_val: forall p v, eval_path p = Some v -> to_val p = Some v.
Proof.
  intros.
  destruct p;tryfalse. Qed.


(* 所有权类型只能由所有权类型转换而来 *)

Lemma safe_subtyping_own: forall ty2 E L n ty1 , safe_subtyping E L ty1
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


(* 单个所有权权能不可伪造 *)

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
  + intros. eapply elem_of_list_In in H0.
    eapply elem_of_submseteq in H0. 2:{eauto. }
    eexists. eapply elem_of_list_In. eauto.
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
  + intros. eapply elem_of_list_In in H0. eapply elem_of_app in H0.
    destruct H0.
    eexists. eapply elem_of_list_In. eapply elem_of_app. left.
    eauto.  eapply elem_of_list_In in H0. eapply IHsafe_tctx_incl in H0.
    destruct H0.
    eexists. eapply elem_of_list_In. eapply elem_of_app. right. eapply elem_of_list_In in H0.  eauto.
  + intros. eapply elem_of_list_In in H0. eapply elem_of_app in H0.
    destruct H0.
    eapply elem_of_list_In in H0. eapply IHsafe_tctx_incl in H0.
    destruct H0.
    eexists. eapply elem_of_list_In. eapply elem_of_app. left. eapply elem_of_list_In in H0.  eauto.
    eexists. eapply elem_of_list_In. eapply elem_of_app. right. eauto.
  + intros. eapply IHsafe_tctx_incl2 in H1. destruct H1.
    eapply IHsafe_tctx_incl1 in H1. destruct H1.
    eexists. eauto.
Qed.


(* 所有权权能列表不可伪造 *)

Lemma Tctx_have_own: forall E L T (ps:list path) tyl' T' p  , safe_tctx_incl E L T
        (zip_with TCtx_hasty ps (box <$> tyl') ++ T') -> p ∈ ps-> length ps = length tyl' ->
        exists n ty , In (p ◁ own_ptr n ty) T.
Proof.
 intros.
  generalize dependent tyl'. induction ps.
  - eapply elem_of_nil in H0. exfalso. eauto.
  - intros.
    destruct tyl'.
    inversion H1.
    eapply elem_of_cons in H0. destruct H0. subst.
    simpl in H. eapply have_own in H.
    eauto. unfold box. simpl. left. eauto.
    eapply IHps in H0. eauto.
    simpl in H.
    eapply tctx_incl_tran. eapply H.
    eapply contains_tctx_incl.
    eapply submseteq_cons.
    eauto.
    simpl in H1. eauto.
Qed. 


(* Progress定理：对于任意一条满足RustCapSys类型规则的表达式t，要么已经到达终止状态，
                要么可以在内存状态σ下执行一步，执行结果为t′且内存状态被修改为σ′。 *)

Theorem progress : forall  E L C T (t:language.expr lrust_lang) 
                            (σ : language.state lrust_lang), 
                            safe_type_fun E L C T t  -> int_is_val  -> own_ptr_is_val  -> mut_ptr_is_val -> shr_ptr_is_val ->
              path_is_val -> fun_mut'-> fun_shr' -> fun_own' -> bool_is_val -> fun_own -> 
             value t \/ exists t' σ' list , prim_step t σ [] t' σ' list .
Proof.
  intros. rename H4 into Hpath. rename H5 into Hfmut'. 
  rename H6 into Hfshr'. rename H7 into Hfown'. rename H8 into Hbool. rename H9 into Hfown. 
  induction H. 
  1:{ clear H7.  inversion H4.
      1:{(* #z *) right. eexists. exists σ ,[]. eapply Ectx_step.
          1:{ instantiate(1:= (let: xb := LitV z in e')).
              instantiate(1:= nil). eauto. }
          2:{ eapply BetaS.
              + eapply Forall_cons.
                - eauto.
                - eapply Forall_nil. 
              + eauto.
              + simpl. eauto. }
          1:{ eauto. } }
      1:{(* plus *) subst. assert(H4':=H4). eapply H0 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ int).  simpl. eauto. }
          2:{ instantiate(1:= p1). eauto. }
          1:{ eapply H0 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ int). simpl. eauto. }
              2:{ instantiate(1:= p2). eauto. }
              1:{ eapply expr_beq_correct in H7. eapply expr_beq_correct in H4. 
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= (p1 + p2)%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil ).
                      eauto. }
                  2:{ subst. eapply BinOpS. eapply BinOpPlus. }
                  1:{ eauto. } } }}
      1:{(* minus *) subst. assert(H4':=H4). eapply H0 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ int).  simpl. eauto. }
          2:{ instantiate(1:= p1). eauto. }
          1:{ eapply H0 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ int).  simpl. eauto. }
              2:{ instantiate(1:= p2). eauto. }
              1:{ eapply expr_beq_correct in H4. eapply expr_beq_correct in H9. 
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= (p1 - p2)%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil ).
                      eauto. }
                  2:{ subst. eapply BinOpS. eapply BinOpMinus. }
                  1:{ eauto. } } }}
     1:{(* le *) subst. assert(H4':=H4). eapply H0 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ int). simpl. eauto. }
          2:{ instantiate(1:= p1). eauto. }
          1:{ eapply H0 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ int). simpl. eauto. }
              2:{ instantiate(1:= p2). eauto. }
              1:{ eapply expr_beq_correct in H4. eapply expr_beq_correct in H9. 
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= (p1 ≤ p2)%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil ).
                      eauto. }
                  2:{ subst. eapply BinOpS. eapply BinOpLe. }
                  1:{ eauto. } } } }
    1:{(* function *) right. eexists. exists σ ,[]. eapply Ectx_step.
        1:{ instantiate(1:= (let: xb := e in e')).
            instantiate(1:= []).
            eauto. }
        2:{ eapply BetaS.
            + eapply Forall_cons.
              - unfold IntoVal in H9. rewrite <- H9. rewrite to_of_val. eauto.
              - eapply Forall_nil. 
            + eauto.
            + eauto. }
        1:{ eauto. } }
    2:{(* new *) right. eexists. exists σ ,[]. eapply Ectx_step.
        1:{ instantiate(1:= new' [ #n]%E ).
            instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil ).
            eauto. }
        2:{ unfold new'. eapply BetaS.
            + eapply Forall_cons.
                - eauto.
                - eapply Forall_nil. 
              + unfold Closed. simpl. eauto.
              + eauto. }
        1:{ eauto. } }
    2:{(* delete *)subst.  eapply H1 in H4. induction H4.
        2:{ instantiate(1:= p ◁ own_ptr (my_type_system_v4.size ty) ty). 
            simpl. eauto. }
        2:{ instantiate(1:= ty). 
            instantiate(1:= my_type_system_v4.size ty). eauto. }
        1:{ destruct H4. destruct H4. eapply expr_beq_correct in H4. 
            right. eexists. exists σ ,[]. eapply Ectx_step.
            1:{ instantiate(1:= delete' [ #(my_type_system_v4.size ty); p]%E).
                instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil).
                eauto. }
            2:{ unfold delete'. eapply BetaS.
                + eapply Forall_cons.
                  - eauto.
                  - subst. eapply Forall_cons.
                    1:{ eauto. }
                    1:{ eapply Forall_nil. }
                + unfold Closed. eauto.   
                + simpl. eauto. }
            1:{ eauto. } } }
   2:{(* !p *) inversion H8.
       1:{ subst. eapply H1 in H4. induction H4.
           2:{ instantiate(1:= p ◁ own_ptr n ty). simpl. eauto. }
           2:{ eauto. }
           1:{ destruct H4. destruct H4.
               eapply expr_beq_correct in H4.
               right. eexists. eexists. exists []. eapply Ectx_step.
               1:{ instantiate(1:= !p).
                   instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                   eauto. }
               2:{ subst. eapply ReadNa1S. 
                    eauto. }
               1:{ eauto. } } }
       1:{ subst. eapply H1 in H4. induction H4.
           2:{ instantiate(1:= p ◁ own_ptr n ty).
               simpl. eauto. }
           2:{ eauto. }
           1:{ destruct H4. destruct H4.
               eapply expr_beq_correct in H4.
               right. eexists. eexists. exists []. eapply Ectx_step.
               1:{ instantiate(1:= !p).
                   instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                   eauto. }
               2:{ subst. eapply ReadNa1S. 
                   eauto. }
               1:{ eauto. } } }
      2:{ subst. eapply H2 in H4. induction H4.
          2:{ instantiate(1:= p ◁ &uniq{κ} ty). 
              simpl. eauto. }
          2:{ eauto. }
          1:{ destruct H4. destruct H4.
              right. eexists. eexists. exists []. eapply Ectx_step.
              1:{ instantiate(1:= !p).
                   instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                   eauto. }
              2:{ eapply expr_beq_correct in H4. subst.  eapply ReadNa1S.
                  eauto. }
              1:{ eauto. } } }
      1:{ subst. eapply H3 in H4. induction H4.
          2:{ instantiate(1:= p ◁ &shr{κ} ty). 
              simpl. eauto. }
          2:{ eauto. }
          1:{ destruct H4. destruct H4.
              right. eexists. eexists. exists []. eapply Ectx_step.
              1:{ instantiate(1:= !p).
                   instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                   eauto. }
              2:{ eapply expr_beq_correct in H4. subst. eapply ReadNa1S.
                  instantiate(1:= 0%nat) in H10.
                  eauto. }
              1:{ eauto. } } } }
    4:{(* bool *) right. eexists. exists σ,[]. eapply Ectx_step. 
        1:{ instantiate(1:= (let: xb := LitV b in e')).
            instantiate(1:= nil). 
            eauto. }
        2:{ eapply BetaS. 
            + eapply Forall_cons.
              - eauto.
              - eapply Forall_nil.
            + eauto.
            + eauto. }
        1:{ eauto. } }
    4:{(* mut_own_!p *) subst. eapply H2 in H4. induction H4.
        2:{ instantiate(1:= p ◁ &uniq{κ} (own_ptr n ty)).
            simpl. eauto. }
        2:{ eauto. }
        1:{ destruct H4. destruct H4. eapply expr_beq_correct in H4.
            right. eexists. eexists. exists []. eapply Ectx_step.
            1:{ instantiate(1:= !p).
                instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                eauto. }
            2:{ subst. eapply ReadNa1S.  eauto. }
            1:{ eauto. } } }
    4:{(* shr_own_!p *) subst. eapply H3 in H4. induction H4.
        2:{ instantiate(1:= p ◁ &shr{κ} (own_ptr n ty)).
            simpl. eauto. }
        2:{ eauto. }
        1:{ destruct H4. destruct H4. eapply expr_beq_correct in H4.
            right. eexists. eexists. exists []. eapply Ectx_step.
            1:{ instantiate(1:= !p).
                instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                eauto. }
            2:{ subst. eapply ReadNa1S.
                instantiate(1:= 0%nat) in H9. eauto. }
            1:{ eauto. } } }
    4:{(* mut_mut_!p *) subst. eapply H2 in H4. induction H4.
        2:{ instantiate(1:= p ◁ &uniq{κ} (&uniq{κ'} ty) ).
            unfold In. eauto. }
        2:{ eauto. }
        1:{ destruct H4. destruct H4.
            eapply expr_beq_correct in H4. 
            right. eexists. eexists. exists []. eapply Ectx_step.
            1:{ instantiate(1:= !p).
                instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                eauto. }
            2:{ subst. eapply ReadNa1S.  eauto. }
            1:{ eauto. } } }
    4:{(* shr_mut_!p *) subst. eapply H3 in H4. induction H4.
        2:{ instantiate(1:= p ◁ &shr{κ} (&uniq{κ'} ty)).
            simpl. eauto. }
        2:{ eauto. }
        1:{ destruct H4.  destruct H4.
            eapply expr_beq_correct in H4.
            right. eexists. eexists. exists []. eapply Ectx_step.
            1:{ instantiate(1:= !p).
                instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                eauto. }
            2:{ subst. eapply ReadNa1S.
                instantiate(1:= 0%nat) in H10. eauto. }
            1:{ eauto. } } }
   2:{(* assign *) inversion H7.
        1:{ subst. assert(H4':= H4). eapply H1 in H4. induction H4.
            2:{ instantiate(1:= p1 ◁ own_ptr n ty').
                simpl. eauto. }
            2:{ eauto. }
            1:{ destruct H4. destruct H4.
                eapply expr_beq_correct in H4. eapply Hpath in H4'. induction H4'.
                2:{ instantiate(1:= p2 ◁ ty). simpl.  eauto. }
                2:{ eauto. }
                1:{ right. eexists. eexists. exists []. eapply Ectx_step.
                    1:{ instantiate(1:= Write Na1Ord p1 p2).
                        instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil). 
                        eauto. }
                    2:{ subst. eapply WriteNa1S.
                        2:{ eauto. }
                        1:{ eapply eval_path_val.  eauto. } }
                    1:{ eauto. } } } }
          1:{ subst. assert(H4':=H4). eapply H2 in H4. induction H4.
              2:{ instantiate(1:= p1 ◁ &uniq{κ} ty). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4.
                  eapply expr_beq_correct in H4. eapply Hpath in H4'. induction H4'.
                  2:{ instantiate(1:= p2 ◁ ty ). simpl. eauto. }
                  2:{ eauto. }
                  1:{ right. eexists. eexists. exists []. eapply Ectx_step.
                      1:{ instantiate(1:= Write Na1Ord p1 p2).
                          instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil).
                          eauto. }
                      2:{ rewrite H4. eapply WriteNa1S.
                          1:{ eapply eval_path_val. eauto. }
                          1:{ eauto. } }
                      1:{ eauto. } } } } }
  1:{(* path *) subst. eapply Hpath in H4. induction H4.
      2:{ instantiate(1:= e ◁ ty). simpl. eauto. }
      2:{ eauto. }
      1:{ right. eexists. eexists. exists []. eapply Ectx_step.
          1:{ instantiate(1:= let: xb := e in e').
              instantiate(1:= nil). 
              eauto. }
          2:{ eapply BetaS.
              1:{ eapply Forall_cons. 
                  1:{ eapply eval_path_val in H4. rewrite  H4. eauto. }
                  1:{ eapply Forall_nil. } }
              1:{ eauto. }
              1:{ eauto. } }
          1:{ eauto. } } }
  1:{(* sum-assign *) subst. assert(H4' := H4). inversion H8.
      1:{ subst. eapply H1 in H4. destruct H4.
          1:{ instantiate(1:= p1 ◁ own_ptr n ty' ). simpl. eauto. }
          1:{ eauto. }
          1:{ eapply Hpath in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ ty). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4.
                 right. eexists. eexists. exists []. 
                  eapply expr_beq_correct in H4. eapply Ectx_step.
                 1:{ simpl. instantiate(1:= Write Na1Ord p1 #i). 
                     instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [<>]%binder (Write Na1Ord (p1 +ₗ #1) p2 )%E)) (@nil val) []) 
                     (@cons ectx_item (AppRCtx (RecV <> [xb]%binder e') (@nil val) []) nil)). 
                     simpl. eauto. }
                  2:{ rewrite H4. eapply WriteNa1S.
                      1:{ eauto. }
                      1:{ eapply H13. } }
                  1:{ eauto. } } } }
     1:{ subst. eapply H2 in H4. induction H4.
         2:{ instantiate(1:= p1 ◁ &uniq{κ} (sum tyl)). simpl. eauto. }
         2:{ eauto. }
         1:{ destruct H4. destruct H4.
             right. eexists. eexists. exists []. 
             eapply expr_beq_correct in H4. eapply Ectx_step.
             1:{ simpl. instantiate(1:= Write Na1Ord p1 #i). 
                 instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [<>]%binder (Write Na1Ord (p1 +ₗ #1) p2 )%E)) (@nil val) []) 
                 (@cons ectx_item (AppRCtx (RecV <> [xb]%binder e') (@nil val) []) nil)). 
                 simpl. eauto. }
             2:{ rewrite H4. eapply WriteNa1S.
                 1:{ eauto. }
                 1:{ eapply H12. } }
             1:{ eauto. } } } }
  1:{(* sum-assign-unit *) inversion H8.
      1:{ subst. eapply H1 in H4. induction H4.
          2:{ instantiate(1:= p ◁ own_ptr n ty'). simpl. eauto. }
          2:{ eauto. }
          1:{ destruct H4. destruct H4.
              right. eexists. eexists. exists []. 
              eapply expr_beq_correct in H4. eapply Ectx_step.
              1:{ instantiate(1:= (p <- #i)%E).
                  instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil ).
                  simpl. eauto. }
              2:{ rewrite H4. eapply WriteNa1S.
                  1:{ eauto. }
                  1:{ eapply H10. } }
              1:{ eauto. } } }
      1:{ subst. eapply H2 in H4. induction H4.
          2:{ instantiate(1:= p ◁ &uniq{κ} (sum tyl)). simpl. eauto. }
          2:{ eauto. }
          1:{ destruct H4. destruct H4.
              right. eexists. eexists. exists []. 
              eapply expr_beq_correct in H4. eapply Ectx_step.
              1:{ instantiate(1:= (p <- #i)%E).
                  instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil ).
                  simpl. eauto. }
              2:{ rewrite H4. eapply WriteNa1S.
                  1:{ eauto. }
                  1:{ eapply H10. } }
              1:{ eauto. } } } }
  2:{(* memcpy *) inversion H8;inversion H9.
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H1 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ own_ptr n0 ty'). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H1 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ own_ptr n1 ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  right.  eexists. exists σ ,[].  eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ eapply expr_beq_correct in H4. eapply expr_beq_correct in H12. 
                      rewrite H4;rewrite H12.
                      eapply BetaS  .
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } }                      
                      1:{ unfold Closed. eauto. }
                      1:{ eauto. } }
                  1:{ eauto. } } } }
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H1 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ own_ptr n0 ty'). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H1 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ own_ptr n1 ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ eapply expr_beq_correct in H4. eapply expr_beq_correct in H12. rewrite H4;rewrite H12.
                      unfold memcpy'. eapply BetaS  .
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } }                      
                      1:{ unfold Closed. eauto. }
                      1:{ eauto. } }
                  1:{ eauto. } } } }
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H1 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ own_ptr n0 ty'). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H3 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ &shr{κ} ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  eapply expr_beq_correct in H4; eapply expr_beq_correct in H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ rewrite H4; rewrite H12. eapply BetaS.
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } }                      
                      1:{ unfold Closed. eauto. }
                      1:{ eauto. } }
                  1:{ eauto. } } } }
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H1 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ own_ptr n0 ty'). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H2 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ &uniq{κ} ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  eapply expr_beq_correct in H4; eapply expr_beq_correct in H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ rewrite H4; rewrite H12. eapply BetaS.
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } }                      
                      1:{ unfold Closed. eauto. }
                      1:{ eauto. } }
                  1:{ eauto. } } } }
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H2 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ &uniq{κ} ty0). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H1 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ own_ptr n0 ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  eapply expr_beq_correct in H4; eapply expr_beq_correct in H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ rewrite H4;rewrite H12. eapply BetaS.
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } }                      
                      1:{ unfold Closed. eauto. }
                      1:{ simpl. eauto. } }
                 1:{ eauto. } } } }
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H2 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ &uniq{κ} ty0). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H1 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ own_ptr n0 ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  eapply expr_beq_correct in H4; eapply expr_beq_correct in H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ rewrite H4;rewrite H12. eapply BetaS.
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } }                      
                      1:{ unfold Closed. eauto. }
                      1:{ eauto. } }
                 1:{ eauto. } } } }
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H2 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ &uniq{κ} ty0). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H3 in H4'.  induction H4'.
              2:{ instantiate(1:= p2 ◁ &shr{κ0} ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  eapply expr_beq_correct in H4; eapply expr_beq_correct in H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ rewrite H4;rewrite H12. eapply BetaS.
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } } 
                      2:{ eauto. }
                      1:{ unfold Closed. eauto. } }
                  1:{ eauto. } } } } 
      1:{ subst E L T1 T2 ty2 ty ty2' ty1 ty1'. assert(H4':= H4). eapply H2 in H4. induction H4.
          2:{ instantiate(1:= p1 ◁ &uniq{κ} ty0). simpl. eauto. }
          2:{ eauto. }
          1:{ eapply H2 in H4'. induction H4'.
              2:{ instantiate(1:= p2 ◁ &uniq{κ0} ty3). simpl. eauto. }
              2:{ eauto. }
              1:{ destruct H4. destruct H4. destruct H12. destruct H12.
                  eapply expr_beq_correct in H4; eapply expr_beq_correct in H12.
                  right. eexists. exists σ ,[]. eapply Ectx_step.
                  1:{ instantiate(1:= memcpy'[p1; #n; p2]%E).
                      instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [xb]%binder e')) (@nil val) []) nil  ).
                      simpl. eauto. }
                  2:{ rewrite H4;rewrite H12. eapply BetaS.
                      1:{ eapply Forall_cons.
                          + eauto.
                          + eapply Forall_cons.
                            - eauto.
                            - eapply Forall_cons.
                              { eauto. }
                              { eapply Forall_nil. } } 
                      2:{ eauto. }
                      1:{ unfold Closed. eauto. } }
                  1:{ eauto. } } } } }
    1:{(* sum-memcpy *) inversion H8.
        1:{ subst. eapply H1 in H4. induction H4.
            2:{ instantiate(1:= p1 ◁ own_ptr n ty'). simpl. eauto. }
            2:{ eauto. }
            1:{ destruct H4. destruct H4.
                right. eexists. eexists. exists []. eapply Ectx_step.
                1:{ instantiate(1:= (p1 <- #i)%E).
                    instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [<>]%binder 
                    (memcpy.memcpy [p1 +ₗ #1; #(my_type_system_v4.size ty); p2])%E)) (@nil val) []) 
                    (@cons ectx_item (AppRCtx (RecV <> [xb]%binder e') (@nil val) []) nil)). 
                    simpl. eauto. }
                2:{ eapply expr_beq_correct in H4. rewrite H4. eapply WriteNa1S.
                    1:{ eauto. }
                    1:{ eapply H12. } }
                1:{ eauto. } } }
        1:{ subst. eapply H2 in H4. induction H4.
            2:{ instantiate(1:= p1 ◁ &uniq{κ} (sum tyl)). simpl. eauto. }
            2:{ eauto. }
            1:{ destruct H4. destruct H4.
                right. eexists. eexists. exists []. eapply Ectx_step.
                1:{ instantiate(1:= (p1 <- #i)%E).
                    instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [<>]%binder 
                    (memcpy.memcpy [p1 +ₗ #1; #(my_type_system_v4.size ty); p2])%E)) (@nil val) []) 
                    (@cons ectx_item (AppRCtx (RecV <> [xb]%binder e') (@nil val) []) nil)). 
                    simpl. eauto. }
                2:{ eapply expr_beq_correct in H4. rewrite H4. eapply WriteNa1S.
                    1:{ eauto. }
                    1:{ eapply H12. } }
                1:{ eauto. } } } } }
  1:{(* conseq *) eauto. }
  1:{(* letcont *) right. eexists. exists σ,[]. eapply Ectx_step.
      1:{ instantiate(1:= let: kb := (rec: kb argsb := econt)%E in e2).
          instantiate(1:= []). simpl. eauto. }
      2:{ eapply BetaS.
          1:{ eapply Forall_cons.
              + simpl. case_match;tryfalse. eauto.
              + eapply Forall_nil. }
          1:{ unfold Closed. eauto. }
          1:{ eauto. } }
      1:{ eauto. } }
  2:{(* newlft *) right. eexists. exists σ,[]. eapply Ectx_step.
      1:{ instantiate(1:= let: <> := #☠ in e).
          instantiate(1:=[]).
          simpl. eauto. }
      2:{ eapply BetaS.
          1:{ eapply Forall_cons.
              + simpl. eauto.
              + eapply Forall_nil. }
          1:{ simpl. eauto. }
          1:{ eauto. } }
      1:{ eauto. } }
  2:{(* endlft *) right. eexists. exists σ,[]. eapply Ectx_step.
      1:{ instantiate(1:=  (let: <> := #☠ in #☠) ).
          instantiate(1:= @cons ectx_item (AppRCtx ((RecV <> [<>]%binder e)) (@nil val) []) nil  ).
          simpl. eauto. }
      2:{ eapply BetaS.
          1:{ eapply Forall_cons.
              + simpl. eauto.
              + eapply Forall_nil. } 
          1:{ unfold Closed. eauto. }
          1:{ simpl. eauto. } }
      1:{ eauto. } } 
   2:{(* case_uniq *)  eapply type_case_uniq' in H.
       2:{ eauto. }
       1:{ eapply Hfmut' in H;eauto.   destruct H. 
           1:{ instantiate(1:= p ◁ &uniq{κ} (sum tyl)). simpl. eauto. }
           1:{ split. eauto. eapply type_beq_correct. eauto.  }
           1:{ destruct H. destruct H. destruct H5. eapply expr_beq_correct in H. 
               right. eexists. eexists.  exists []. eapply Ectx_step.
               1:{ instantiate(1:= !p).
                   instantiate(1:= @cons ectx_item (CaseCtx el) nil).
                   simpl. eauto. }
               2:{ rewrite H. eapply ReadNa1S.  eauto. }
               1:{ eauto. } } } }
  2:{(* case_shr *) eapply type_case_shr' in H.
      2:{ eauto. }
      1:{ eapply Hfshr' in H;eauto. destruct H.
          1:{ instantiate(1:= p ◁ &shr{κ} (sum tyl)). simpl. eauto. }
          1:{ split. eauto. eapply type_beq_correct. eauto. }
          1:{ destruct H. destruct H. destruct H5. eapply expr_beq_correct in H. 
              right. eexists. eexists.  exists []. eapply Ectx_step.
              1:{ instantiate(1:= !p).
                  instantiate(1:= @cons ectx_item (CaseCtx el) nil).
                  simpl. eauto. }
              2:{ rewrite H. eapply ReadNa1S.
                  instantiate(1:= 0%nat ) in H5. eauto. }
              1:{ eauto. } } } }
  2:{(* case_own *) eapply type_case_own' in H.
      eapply Hfown' in H. destruct H.
      1:{ instantiate(1:= p ◁ own_ptr n (sum tyl)). simpl. eauto. }
      1:{ split. eauto. eapply type_beq_correct. eauto. }
      1:{ destruct H. destruct H. destruct H4. eapply expr_beq_correct in H. 
          right. eexists. eexists.  exists []. eapply Ectx_step.
          1:{ instantiate(1:= !p).
              instantiate(1:= @cons ectx_item (CaseCtx el) nil).
              simpl. eauto. }
          2:{ rewrite H. eapply ReadNa1S.  eauto. }
          1:{ eauto. } } }
  3:{(* if *) eapply Hbool in H. destruct H.
      1:{ eapply expr_beq_correct in H. 
          right. eexists. eexists.  exists []. eapply Ectx_step.
          1:{ instantiate(1:= case: p of [e2; e1]).
              instantiate(1:= nil). simpl. eauto. }
          2:{ rewrite H. eapply CaseS.
              + lia.
              + simpl. eauto. }
          1:{ eauto. } }
      1:{ eapply expr_beq_correct in H. 
          right. eexists. eexists.  exists []. eapply Ectx_step.
          1:{ instantiate(1:= case: p of [e2; e1]).
              instantiate(1:= nil). simpl. eauto. }
          2:{ rewrite H. eapply CaseS.
              + lia.
              + simpl. eauto. }
          1:{ eauto. } } }
  1:{(* jump k *) rewrite H6. 
      assert(exists e', subst_l xl args e = Some e').
      1:{ clear H6 Closed0 H.  
          generalize dependent args. 
          induction xl. intros. simpl. induction args.
          + eauto.
          + inversion H7.
          + intros. simpl. destruct args. 
            - inversion H7. 
            - simpl in H7. injection H7 as eq. eapply IHxl in eq. destruct eq.
              eexists. eapply fmap_Some_2. eapply H. }
      destruct H8.
      right. eexists. eexists. eexists. eapply Ectx_step.
      1:{ instantiate(1:= (RecV f xl e) args).
          instantiate(1:= nil). eauto. }
      1:{ eauto. }
      1:{ eapply BetaS. 
          1:{ clear H4 H5 H7 H8 T'.  generalize dependent argsv.
              induction args. 
            1:{ eauto.  } 
            1:{ intros.  destruct argsv.
                1:{ inversion H. }
                1:{ eapply Forall_cons.
                    1:{ eapply Forall2_cons_1 in H. destruct H. destruct H.
                        1:{  rewrite H. eauto. }
                        1:{ rewrite H. rewrite to_of_val. eauto. } }
                    1:{ eapply Forall2_cons_1 in H. destruct H.
                        eapply IHargs. eapply H4. } } } } 
          1:{ eauto. } 
          1:{ simpl.
              eapply fmap_Some_2. eapply H8. } } } 
  1:{(* call *) 
     assert(exists e', subst_l argsb ps e = Some e').
     { assert(length argsb = length ps). 
       + eauto.
       + clear Closed0 H10 H6 H9 H11.
         generalize dependent ps. induction argsb. intros. simpl. induction ps.
          - eauto.
          - inversion H12.
          - intros. simpl.  destruct ps.
            * inversion H12.
            * simpl in H12. injection H12 as eq. eapply IHargsb in eq. destruct eq.
              eexists. eapply fmap_Some_2. eauto. }
     assert(H10':= H10). simpl in H10. unfold IntoVal in H10. simpl in H10.
     destruct H12.
     right. eexists. eexists. eexists. eapply Ectx_step.
     1:{ instantiate(1:= p ((λ: ["_r"], k ["_r"])%E :: ps)).
         instantiate(1:= nil).
         simpl. eauto. }
     2:{ rewrite <- H10. eapply BetaS.
         2:{ eauto. }
         1:{ (* assert(H12':= H12).  *) eapply type_call in H5;eauto. eapply Forall_cons.
             + simpl. case_match;tryfalse.
               - eauto.
               - assert(Closed ["_r"] (k ["_r"]%E)).
                 1:{ unfold Closed. simpl. rewrite andb_true_r. eapply is_closed_of_val. }
                 1:{ tryfalse. }
             + unfold safe_tctx_extract_ctx in H6. induction ps.
               - eapply Forall_nil.
               - eapply list.Forall_forall. intros.
                 eapply Tctx_have_own in H13;eauto. destruct H13. destruct H13.
                 assert(H13':= H13). 
                 destruct x2. 
(* repeat ty != sum tyl *)
                 7:{ eapply Hfown' in H13;eauto. destruct H13.
                     split. eauto. eapply type_beq_correct. eauto. 
                     destruct H13. destruct H13. 
                     eapply expr_beq_correct in H13. rewrite H13. eauto. }
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 eapply Hfown in H13';eauto; destruct H13';
                 try split; eauto; unfold type_beq;  eauto; 
                 destruct H14; destruct H14;
                 eapply expr_beq_correct in H14; rewrite H14; eauto.
                 }
          1:{ simpl. eapply fmap_Some_2. eapply fmap_Some_2. eauto. } }
      1:{ eauto. }
    Unshelve. exact σ.  
    + simpl. unfold Closed. simpl. rewrite andb_true_r. 
      eapply andb_True. split.
      2:{ eapply is_closed_to_val. eapply eval_path_val in H12. eauto. }
      1:{ eapply type_sum_assign_instr in H8.
          2:{ eauto. }
          2:{ eapply H9. }
          2:{ eapply H10. }
          1:{ eapply H1 in H8. destruct H8.
              1:{ instantiate(1:= p1 ◁ own_ptr n ty'). simpl. eauto. }
              1:{ eauto. }
              1:{ destruct H4. destruct H4. eapply expr_beq_correct in H4. eapply is_closed_to_val.
                  rewrite H4. eauto. } } }
    + simpl. eauto.
    + simpl. unfold Closed. simpl. rewrite andb_true_r. 
      eapply andb_True. split.
      - eapply H2 in H4'. destruct H4'.
        1:{ instantiate(1:= p1 ◁ &uniq{κ} (sum tyl)). simpl. eauto. }
        1:{ eauto. }
        1:{ destruct H4. destruct H4. eapply expr_beq_correct in H4. eapply is_closed_to_val.
            rewrite H4. eauto. }
      - eapply Hpath in H4'. destruct H4'.
        1:{ instantiate(1:= p2 ◁ ty). simpl. eauto. }
        1:{ eauto. }
        1:{ eapply is_closed_to_val. eapply eval_path_val in H4. eauto. }
    + simpl. eauto. 
    + exact σ. + exact σ. + exact σ. + exact σ. + exact σ. + exact 0%nat.
    + exact σ. + exact σ. + exact σ. + exact σ. + exact σ. + exact σ. + exact σ. + exact σ.
    + exact 0%nat. + exact σ. + exact σ. + exact σ.
    + simpl. unfold Closed. simpl. eapply andb_True. split. 
      - eapply is_closed_of_val.
      - rewrite andb_true_r. rewrite andb_true_r. eapply andb_True. split.
        1:{ eapply expr_beq_correct in H4. rewrite H4. 
            eapply is_closed_to_val. eauto. }
        1:{ eapply type_sum_memcpy_instr_safe in H8;eauto.
            eapply Hpath in H8. destruct H8;eauto.
            1:{ instantiate(1:= ty2).
                instantiate(1:= p2). simpl. eauto. }      
            1:{ eapply eval_path_val in H8.  eapply is_closed_to_val. eauto. } }
    + simpl. eauto.
    + simpl. unfold Closed. simpl. eapply andb_True. split. 
      - eapply is_closed_of_val.
      - rewrite andb_true_r. rewrite andb_true_r. eapply andb_True. split.
        1:{ eapply expr_beq_correct in H4. rewrite H4.
            eapply is_closed_to_val. eauto. }
        1:{ eapply type_sum_memcpy_instr_safe in H8;eauto.
            eapply Hpath in H8. destruct H8;eauto.
            1:{ instantiate(1:= ty2).
                instantiate(1:= p2). simpl. eauto. }    
            1:{ eapply eval_path_val in H8. eapply is_closed_to_val. eauto. } }
    + simpl. eauto.
    + exact σ. + exact σ. + exact tyl'. + exact σ. + exact tyl'. + exact σ. + exact tyl'. 
    + exact σ. + exact tyl'. + exact σ. + exact tyl'. + exact σ. + exact tyl'. 
    + exact σ. + exact tyl'. + exact σ. + exact tyl'. + exact σ. + exact tyl'. }
     Unshelve. exact σ. exact σ.
Qed. 


(* endlft;e 执行第一步是确定的：执行skip的第一步 *)

Lemma determinism_endlft1: forall e  t' t'' σ σ' σ'' list list', Closed (<> :b: [<>]%binder +b+ []) e ->
  (prim_step (Skip ;; e) σ [] t' σ' list) ->
  (prim_step (Skip ;; e) σ [] t'' σ'' list')  -> expr_beq t' t''.
Proof.
  intros.
  assert((Skip ;; e)%E =
  (ectx_language.fill (@cons ectx_item (AppRCtx ((RecV <> [<>]%binder e)) (@nil val) []) nil) Skip)).
  simpl. eauto.
  rewrite  H2 in H0.
  eapply head_reducible_prim_step_ctx in H0.
  2:{ unfold head_reducible. do 4 eexists. eapply BetaS.
      eapply Forall_cons. simpl. eauto. eauto. 
      simpl. unfold Closed. eapply is_closed_to_val. eauto.
      simpl. eauto. }
  destruct H0. destruct H0. subst.
  rewrite  H2 in H1.
  eapply head_reducible_prim_step_ctx in H1.
  2:{ unfold head_reducible. do 4 eexists. eapply BetaS.
      eapply Forall_cons. simpl. eauto. eauto. 
      simpl. unfold Closed. eapply is_closed_to_val. eauto.
      simpl. eauto. }
  destruct H1. destruct H0. rewrite H0. simpl.
  inversion H3. subst. simpl in H14.
  inversion H1. subst. simpl in H16.
  injection H14 as eq ;subst.
  injection H16 as eq ;subst.
  eapply andb_prop_intro.
  split. rewrite expr_eq. eauto.
  rewrite andb_true_r.
  rewrite expr_eq. eauto.
Qed.


(* endlft;e 执行第二步是确定的：执行skip的第二步 *)

Lemma determinism_endlft2: forall e  t' t'' σ σ' σ'' list list', Closed (<> :b: [<>]%binder +b+ []) e -> 
  (prim_step (#☠ ;; e) σ [] t' σ' list) ->
  (prim_step (#☠ ;; e) σ [] t'' σ'' list')  -> expr_beq t' t''.
Proof.
  intros.
  eapply head_reducible_prim_step in H0.
  2:{ unfold head_reducible. do 4 eexists.
      eapply BetaS.
      eapply Forall_cons. eauto. eauto. 
      simpl. eauto. 
      simpl. eauto. }
  simpl in H0. inversion H0. subst.
  simpl in H12. injection H12 as eq. rewrite <- eq.
  eapply head_reducible_prim_step in H1.
  2:{ unfold head_reducible. do 4 eexists.
      eapply BetaS.
      eapply Forall_cons. eauto. eauto. 
      simpl. eauto. 
      simpl. eauto. }
  simpl in H1. inversion H1. subst.
  simpl in H14. injection H14 as eq'. rewrite eq'.
  rewrite expr_eq. eauto.
Qed. 


(* 分支语句执行第一步是确定的：第一步的结果必然是增加读锁 *)

Lemma determinism_case1: forall E L C T p el  t' t'' σ σ' σ'' list list' κ tyl n  ,
  (safe_type_fun E L C ((p ◁ &uniq{κ}(sum tyl)) :: T) (case: !p of el) \/ 
  safe_type_fun E L C ((p ◁ &shr{κ}(sum tyl)) :: T) (case: !p of el) \/ 
  safe_type_fun E L C ((p ◁ own_ptr n (sum tyl)) :: T) (case: !p of el)) -> fun_mut' -> fun_shr' -> fun_own' ->
  (prim_step (case: !p of el) σ [] t' σ' list) ->
  (prim_step (case: !p of el) σ [] t'' σ'' list')  -> expr_beq t' t'' /\ σ' = σ''.
Proof.
  intros.
  assert((case: !p of el) = (ectx_language.fill (@cons ectx_item (CaseCtx el) nil) !p)).
  { simpl. eauto. }
  rewrite H5 in H4. rewrite H5 in H3.
  destruct H.
  eapply H0 in H. destruct H.
  instantiate(1:= p ◁ &uniq{κ} (sum tyl)). simpl. eauto.
  split. eauto. 
  eapply type_beq_correct. eauto.
  destruct H. destruct H. destruct H6.
  eapply expr_beq_correct in H.
  eapply head_reducible_prim_step_ctx in H3.
  2:{ unfold head_reducible. 
      do 4 eexists. rewrite H.
      eapply ReadNa1S.
      eauto. }
  destruct H3. destruct H3.
  eapply head_reducible_prim_step_ctx in H4.
  2:{ unfold head_reducible. 
      do 4 eexists. rewrite H.
      eapply ReadNa1S.
      eauto. }
  destruct H4. destruct H4.
  inversion H8;subst.
  inversion H9;subst.
  rewrite H10. split.
  rewrite expr_eq. eauto.
  simpl in H10. injection H10 as eq. 
  rewrite eq in H11. rewrite H3 in H11.
  injection H11 . intros.
  subst. eauto.
  destruct H.
  eapply H1 in H. destruct H.
  instantiate(1:= p ◁ &shr{κ} (sum tyl)).
  simpl. eauto.
  split. eauto.
  eapply type_beq_correct. eauto.
  destruct H. destruct H. destruct H6.
  eapply expr_beq_correct in H.
  instantiate(1:= 0%nat) in H6.
  eapply head_reducible_prim_step_ctx in H3.
  2:{ unfold head_reducible. 
      do 4 eexists. rewrite H.
      eapply ReadNa1S.
      eauto. }
  destruct H3. destruct H3.
  eapply head_reducible_prim_step_ctx in H4.
  2:{ unfold head_reducible. 
      do 4 eexists. rewrite H.
      eapply ReadNa1S.
      eauto. }
  destruct H4. destruct H4.
  inversion H9;subst.
  inversion H8;subst.
  rewrite H10. split.
  rewrite expr_eq. eauto.
  injection H10 as eq. rewrite eq.
  subst. rewrite H11 in H3.
  injection H3 . intros. 
  subst. eauto.
  eapply H2 in H. destruct H.
  instantiate(1:= p ◁ own_ptr n (sum tyl)).
  simpl. eauto.
  split. eauto.
  eapply type_beq_correct. eauto.
  destruct H. destruct H. destruct H6.
  eapply expr_beq_correct in H.
  eapply head_reducible_prim_step_ctx in H3.
  2:{ unfold head_reducible. 
      do 4 eexists. rewrite H.
      eapply ReadNa1S.
      eauto. }
  destruct H3. destruct H3.
  eapply head_reducible_prim_step_ctx in H4.
  2:{ unfold head_reducible. 
      do 4 eexists. rewrite H.
      eapply ReadNa1S.
      eauto. }
  destruct H4. destruct H4.
  inversion H9;subst.
  inversion H8;subst.
  injection H10 as eq. 
  rewrite eq. split.
  rewrite expr_eq. eauto.
  subst. rewrite H3 in H11.
  injection H11. intros.
  subst. eauto.
Qed.
  

(* 分支语句执行第二步是确定的：读取当前解引用位置的值 *)
Lemma determinism_case2: forall (x:loc)  el x1 x0 t' t'' σ σ' σ'' list list',
  prim_step (case: Read Na2Ord #x of  el) (<[x:=(RSt (S x1), #x0)]> σ) [] t' σ' list ->
  prim_step (case: Read Na2Ord #x of  el) (<[x:=(RSt (S x1), #x0)]> σ) [] t'' σ'' list' ->
  expr_beq t' t'' /\ σ' = σ''.
Proof. 
  intros.
  assert((case: Read Na2Ord #x of el) = (ectx_language.fill (@cons ectx_item (CaseCtx el) nil) (Read Na2Ord #x))).
  { simpl. eauto. }
  rewrite H1 in H.
  eapply head_reducible_prim_step_ctx in H.
  2:{ unfold head_reducible.
      do 4 eexists.
      eapply ReadNa2S. 
      unfold ectx_language.state in *.  eapply lookup_insert. }
  destruct H. destruct H.
  rewrite H1 in H0.
  eapply head_reducible_prim_step_ctx in H0.
  2:{ unfold head_reducible.
      do 4 eexists.
      eapply ReadNa2S.
      unfold ectx_language.state in *.
      eapply lookup_insert. }
  destruct H0. destruct H0.
  inversion H2;subst.
  inversion H3;subst.
  rewrite H5 in H0.
  injection H0. intros. 
  subst. split.
  rewrite expr_eq. eauto.
  eauto.
Qed.


(* 分支语句执行第三步是确定的：根据解引用结果确定执行哪条分支语句 *)
Lemma determinism_case3: forall (x0:nat)  el σ σ' σ'' t' t'' list list', x0 < length el ->
  prim_step (case: #x0 of  el) σ [] t' σ' list -> 
  prim_step (case: #x0 of  el) σ [] t'' σ'' list' -> expr_beq t' t'' /\ σ' = σ''.
Proof.
  intros.
  eapply head_reducible_prim_step in H0.
  2:{ unfold head_reducible.
      do 4 eexists.
      eapply CaseS. lia.
      eapply list_lookup_lookup_total_lt. lia. }
  eapply head_reducible_prim_step in H1.
  2:{ unfold head_reducible.
      do 4 eexists.
      eapply CaseS. lia.
      eapply list_lookup_lookup_total_lt. lia. }
  inversion H0.
  inversion H1.
  split. 
  rewrite H6 in H14.
  injection H14 as eq. subst.
  rewrite expr_eq. eauto.
  rewrite <- H8. rewrite <- H16.
  eauto.
Qed.
    
 

(* Preservation定理：对于任意一条类型良好的表达式t，其执行三步内的结果t′、t′′或t′′′ 依然是类型良好的，满足RustCapSys的类型规则。 *)


Theorem preservation: forall E L2 C2 T2 t t' t'' t''' σ σ' σ'' σ'''  list list' list'',
             safe_type_fun E L2 C2 T2 t  -> prim_step t σ [] t' σ' list -> 
             prim_step t' σ' [] t'' σ'' list' -> prim_step t'' σ'' [] t''' σ''' list'' ->
             bool_is_val -> fun_mut' -> fun_shr' -> fun_own' -> 
             exists T' L' C', safe_type_fun E L' C' T' t' \/ safe_type_fun E L' C' T' t'' \/ 
             safe_type_fun E L' C' T' t''' \/
             (exists (argsv : Datatypes.list val) args (k:val) 
             (T' : vec val (length argsv)  → tctx) p , 
             (t = ( k args) \/ t = p ((λ: ["_r"], k ["_r"])%E :: args)) /\ (k ◁cont(L2, T') ) ∈ C2 ) .
Proof with auto.
  intros. generalize dependent t' . 
  rename H3 into Hbool.
  rename H4 into Hfmut'. rename H5 into Hfshr'. rename H6 into Hfown'. 
  induction H;intros t' HT HE.
  + destruct H4. specialize (H1 x).
    eapply fill_prim_step in HT. eapply of_to_val in H4.
    instantiate(1:= []) in HT. eapply head_reducible_prim_step in HT.
    1:{ simpl in HT. inversion HT;subst. simpl in H15. injection H15 as eq. 
        rewrite <- eq. eexists. eexists. eexists. left. eapply H1. }
    1:{ simpl. unfold head_reducible. eexists. eexists. eexists. eexists. 
        eapply BetaS.
        1:{ rewrite <- H4. eapply Forall_cons.
            - rewrite to_of_val. eauto.
            - eapply Forall_nil. }  
        1:{ simpl. eauto. }
        1:{ simpl. eauto. } } 
  + eapply IHsafe_type_fun in HT;eauto. destruct HT. destruct H3. destruct H3.
    destruct H3. 1:{ do 3 eexists. left. eapply H3. }
    destruct H3. 1:{ do 3 eexists. right. left. eapply H3. }
    destruct H3. 1:{ do 3 eexists. right. right. left. eauto. }
    do 3 eexists. right. right. right. destruct H3. destruct H3. destruct H3. 
    destruct H3. destruct H3. destruct H3.  eexists.
    exists x3. exists x4. clear IHsafe_type_fun H0 H1. induction H.  
    eapply elem_of_subseteq in H4;eauto. eapply elem_of_list_In in H4.
    simpl in H4. destruct H4. injection H1 as eq. subst.  exists T0. exists x6.
    split.  destruct H3. left. eauto. right. eauto. eauto. eapply elem_of_list_In. simpl. left. eauto.
    eapply  elem_of_list_In in H1. eapply IHsafe_cctx_incl in H1. eauto.
    destruct H1. destruct H1. destruct H1. destruct H1. 
    exists x7. exists x6.
    split. left. eauto. eapply elem_of_list_further. eauto. exists x7. 
    eexists x8.  split. right. eauto. eapply elem_of_list_further. eauto.
  + eapply fill_prim_step in HT. instantiate(1:= []) in HT.
    eapply head_reducible_prim_step in HT. 
    2:{ simpl. unfold head_reducible. eexists. eexists. eexists. eexists.
        eapply BetaS.
        1:{ eapply Forall_cons. simpl. case_match;tryfalse.
            - eauto.
            - eapply Forall_nil. }
        1:{ simpl. eauto. }
        1:{ simpl. eauto. } }
    1:{ assert(exists v, to_val ((rec: kb argsb := econt)%E) = Some v).
        1:{ simpl. case_match;tryfalse. eauto. }
        destruct H6.
        simpl in HT. inversion HT;subst. simpl in H17.
        injection H17 as eq. rewrite <- eq. eexists. eexists. eexists.
        eapply of_to_val in H6. rewrite <- H6.
        specialize (H1 x). left. eapply H1. }
  + do 3 eexists. right. right. right.  exists argsv. exists args. exists k.
     exists T'. exists e. split. left. eauto.  eauto. 
  + eapply fill_prim_step in HT. instantiate(1:= []) in HT.
    eapply head_reducible_prim_step in HT. 
    2:{ simpl. unfold head_reducible. eexists. eexists. eexists. eexists.
        eapply BetaS.
        - eapply Forall_cons. eauto. eapply Forall_nil.
        - simpl. eauto.
        - simpl. eauto. }
    inversion HT;subst. simpl in H13. injection H13 as eq.
    rewrite <- eq. eexists. eexists. eexists. eauto.
  + (assert(prim_step (ectx_language.fill (@cons ectx_item (AppRCtx ((RecV <> [<>]%binder e)) (@nil val) []) nil) Skip) σ []
     (ectx_language.fill (@cons ectx_item (AppRCtx ((RecV <> [<>]%binder e)) (@nil val) []) nil) (Lit LitPoison)) σ [] )).
    { eapply Ectx_step.
      instantiate(1:= Skip). eauto. eauto. eapply BetaS. 
      eapply Forall_cons. eauto. eauto. simpl. unfold Closed. eapply is_closed_to_val. eauto.
      simpl. eauto. }
    assert( prim_step (ectx_language.fill [] (ectx_language.fill [SeqCtx e] #☠)) σ' [] 
    (ectx_language.fill [] e) σ' []). 
    { eapply Ectx_step. instantiate(1:= let: <> := #☠ in e). instantiate(1:= []). eauto.
      2:{ simpl.  eapply BetaS. eapply Forall_cons. eauto. eauto. simpl. eauto. simpl. eauto. } 
      eauto. }  simpl in H3. simpl in H4. 
     eapply determinism_endlft1 in H3.
    2:{ simpl. eauto. }
    2:{ instantiate(3:= t'). eauto. } 
    1:{ eapply expr_beq_correct in H3. 
        rewrite H3 in HE. eapply determinism_endlft2 in HE.
        2:{ eauto. }
        2:{ instantiate(3:= e). eauto. }
        1:{ eapply expr_beq_correct in HE. subst. eexists. eexists. eexists.
            right. left. eauto. } }
  + assert(H0':= H0). eapply type_case_uniq' in H0;eauto. assert(H':= H0).
    eapply Hfmut' in H0. destruct H0.
    instantiate(1:= (p ◁ &uniq{κ} (sum tyl))). simpl. eauto. 
    eauto. split. eauto. instantiate(1:= tyl). eapply type_beq_correct.
    eauto. destruct H0. destruct H0. destruct H1.  
    assert( exists  n , prim_step (ectx_language.fill (@cons ectx_item (CaseCtx el) nil) !p) σ [] 
            (case: Read Na2Ord p of el) (<[x:=(RSt $ S n, #x0)]>σ) []).
    { eexists.  eapply Ectx_step.
      instantiate(1:= !p). eauto.
      2:{ eapply expr_beq_correct in H0.
          rewrite H0. eapply ReadNa1S . destruct H3. eauto. } simpl.  eauto. } 
    destruct H4.  
    assert(exists σ', prim_step (ectx_language.fill (@cons ectx_item (CaseCtx el) nil) (Read Na2Ord #x)) (<[x:=(RSt (S x1), #x0)]> σ) [] 
            (case: #x0 of el) σ' []).
    { eexists. eapply Ectx_step. 
      instantiate(1:= (Read Na2Ord #x)). eauto.
      2:{ instantiate(2:= #x0). eapply ReadNa2S. Search(<[_:=_]> _ !! _ = Some _). 
          unfold ectx_language.state in *. unfold state in *.
          eapply lookup_insert.
       } simpl. eauto. }
    assert(H0'':= H0'). 
    eapply Forall2_length in H0'. 
    assert(exists e', prim_step (case: #x0 of el) σ'' [] e' σ'' []).
    { eexists. eapply Ectx_step. simpl.
      instantiate(1:=(case: #x0 of  el)%E).
      instantiate(1:= []). eauto. eauto. 
      eapply CaseS. lia.
      Search ( _ -> _ !! _ = Some _).
      eapply list_lookup_lookup_total_lt.
      rewrite <- H0'. lia.
    }
   destruct H5. destruct H6. 
   eapply determinism_case1 in HT;eauto. destruct HT.
   eapply expr_beq_correct in H7. subst.
   eapply expr_beq_correct in H0;subst.
   eapply determinism_case2 in HE.
    2:{ simpl in H5. 
        instantiate(3:= (case: #x0 of el)).
        eauto. }
    destruct HE.
    eapply expr_beq_correct in H0. subst.
    eapply determinism_case3 in H2.
    2:{ rewrite <- H0'. lia. }
    2:{ instantiate(3:= x3). eauto. } 
    destruct H2. eapply expr_beq_correct in H0. 
    eapply Forall2_lookup_r in H0''. destruct H0''. destruct H7.
    2:{ eapply head_reducible_prim_step in H6.
        2:{  unfold head_reducible. do 4 eexists.
        eapply CaseS. lia. eapply list_lookup_lookup_total_lt. lia. }
        inversion H6. eauto. } 
    destruct H8.
    rewrite <- H0. 
    do 3 eexists.
    right. right. left. eauto.
    rewrite <- H0.
    do 3 eexists.
    right. right. left. eauto.
  + eapply type_case_shr' in H;eauto. assert(H':= H).
    eapply Hfshr' in H. destruct H.
    instantiate(1:= p ◁ &shr{κ} (sum tyl) ).
    simpl. eauto.
    split. eauto.
    eapply type_beq_correct. eauto.
    destruct H. destruct H. 
    instantiate(1:= 0%nat) in H1.
    eapply expr_beq_correct in H. 
    assert(exists n,prim_step (case: !p of el) σ [] (case: Read Na2Ord p of el)  (<[x:=(RSt $ S n, #x0)]>σ) []).
    { eexists. eapply Ectx_step.
      instantiate(1:= !p).
      instantiate(1:= [CaseCtx el]).
      simpl. eauto.
      2:{ rewrite H.
          eapply ReadNa1S. destruct H1. eauto. }
      eauto. }
    destruct H3.
    assert(exists σ', prim_step (case: Read Na2Ord #x of el) (<[x:=(RSt (S x1), #x0)]> σ) [] 
           (case: #x0 of el)  σ' []).
    { eexists. eapply Ectx_step.
      instantiate(1:= Read Na2Ord #x).
      instantiate(1:= [CaseCtx el]).
      simpl. eauto. 
      2:{ eapply ReadNa2S.
          unfold ectx_language.state in *.
          eapply lookup_insert. }
      eauto. }
    destruct H4.
    assert(H0':= H0). 
    eapply Forall2_length in H0. 
    assert(exists e', prim_step (case: #x0 of el) σ'' [] e' σ'' []).
    { eexists. eapply Ectx_step.
      instantiate(1:= (case: #x0 of el)).
      instantiate(1:= []).
      simpl. eauto.
      2:{ eapply CaseS. lia.
          eapply list_lookup_lookup_total_lt.
          destruct H1. lia. }
      eauto. }  
    destruct H5. 
    simpl in H3. simpl in H4.
    eapply determinism_case1 in HT;eauto. destruct HT. 
    eapply expr_beq_correct in H6. subst.
    eapply determinism_case2 in HE;eauto. destruct HE.
    eapply expr_beq_correct in H. subst.
    eapply determinism_case3 in H2;eauto. destruct H2.
    eapply expr_beq_correct in H. subst.
    2:{ lia. }
    eapply Forall2_lookup_r in H0'.
    2:{ eapply head_reducible_prim_step in H5.
        2:{ unfold head_reducible. do 4 eexists.
            eapply CaseS. lia.
            eapply list_lookup_lookup_total_lt.
            lia. }
        inversion H5;subst. eauto. }
    destruct H0'. destruct H. destruct H2.
    eexists. eexists. eexists.
    right. right. left. eauto.
    eexists. eexists. eexists.
    right. right. left. eauto.
  + assert(H':= H).
    eapply type_case_own' in H'. assert(H'':= H').
    eapply Hfown' in H'. destruct H'.
    instantiate(1:= p ◁ own_ptr n (sum tyl)).
    simpl. eauto.
    split. eauto.
    eapply type_beq_correct. eauto.
    destruct H0. destruct H0. destruct H1.
    eapply expr_beq_correct in H0.
    assert(exists n,prim_step (case: !p of el) σ [] (case: Read Na2Ord p of el)  (<[x:=(RSt $ S n, #x0)]>σ) []).
    { eexists. eapply Ectx_step.
      instantiate(1:= !p).
      instantiate(1:= [CaseCtx el]).
      simpl. eauto.
      2:{ rewrite H0.
          eapply ReadNa1S.  eauto. }
      eauto. }
    destruct H4.
    assert(exists σ', prim_step (case: Read Na2Ord #x of el) (<[x:=(RSt (S x1), #x0)]> σ) [] 
           (case: #x0 of el)  σ' []).
    { eexists. eapply Ectx_step.
      instantiate(1:= Read Na2Ord #x).
      instantiate(1:= [CaseCtx el]).
      simpl. eauto. 
      2:{ eapply ReadNa2S.
          unfold ectx_language.state in *.
          eapply lookup_insert. }
      eauto. }
    destruct H5.
    assert(H':=H).
    eapply Forall2_length in H'.
    assert(exists e', prim_step (case: #x0 of el) σ'' [] e' σ'' []).
    { eexists. eapply Ectx_step.
      instantiate(1:= (case: #x0 of el)).
      instantiate(1:= []).
      simpl. eauto.
      2:{ eapply CaseS. lia.
          eapply list_lookup_lookup_total_lt.
          destruct H1. lia. }
      eauto. } 
    destruct H6.
    eapply determinism_case1 in HT;eauto. destruct HT. 
    eapply expr_beq_correct in H7. subst.
    eapply determinism_case2 in HE;eauto. destruct HE. 
    eapply expr_beq_correct in H0. subst.
    eapply determinism_case3 in H2;eauto. destruct H2. 
    eapply expr_beq_correct in H0. subst.
    2:{ lia. }
    eapply Forall2_lookup_r in H.
    2:{ eapply head_reducible_prim_step in H6.
        2:{ unfold head_reducible. do 4 eexists.
            eapply CaseS. lia.
            eapply list_lookup_lookup_total_lt. lia. }
        inversion H6;subst. eauto. }
    destruct H. destruct H. destruct H0.
    do 3 eexists. 
    right. right. left. eauto.
    do 3 eexists. 
    right. right. left. eauto.
  + do 3 eexists.
    right. right. right. exists [LitV LitPoison ]. exists ps. exists k. exists T''.
    eexists p. split. right. eauto. eauto.
  + eapply fill_prim_step in HT. 
    instantiate(1:= []) in HT. eapply head_reducible_prim_step in HT.
    2:{ unfold head_reducible. eexists.
        eapply Hbool in H. destruct H.
        eapply expr_beq_correct in H. subst.
        eexists. eexists. eexists.
        eapply CaseS. lia. simpl. eauto.
        eapply expr_beq_correct in H. subst.
        eexists. eexists. eexists.
        eapply CaseS. lia. simpl. eauto. } 
    eapply Hbool in H. destruct H. 
    eapply expr_beq_correct in H. subst.
    inversion HT;subst. simpl in H6. injection H6 as eq. rewrite <- eq. 
    eexists. eexists. eexists. 
    left. eauto.
    eapply expr_beq_correct in H. subst.
    inversion HT;subst. simpl in H6.
    injection H6 as eq. rewrite <- eq. 
    eexists. eexists. eexists. eauto.
    Unshelve. exact T1. exact L. exact C1. exact T.
    exact L. exact C. exact static. exact x0. exact x0.
    exact static. exact T. exact L. exact C.
Qed.
      
    
     
     





      