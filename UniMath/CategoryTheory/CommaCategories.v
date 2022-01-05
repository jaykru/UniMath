(** **********************************************************

Benedikt Ahrens March 2016, Anthony Bordg May 2017


************************************************************)


(** **********************************************************

Contents :

        - special comma categories (c ↓ K),
          called [cComma] (constant Comma)
        - forgetful functor [cComma_pr1]
        - morphism [f : C ⟦c, c'⟧] induces
          [functor_cComma_mor : functor (c' ↓ K) (c ↓ K)]
        - general comma categories [comma_category]
          - projection functors ([comma_pr1], [comma_pr2])

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Local Open Scope cat.

Section const_comma_category_definition.

Context (M C : category) (K : functor M C) (c : C).

Definition ccomma_object : UU := ∑ m, C⟦c, K m⟧.
Definition ccomma_morphism (a b : ccomma_object) : UU
  := ∑ f : _ ⟦pr1 a, pr1 b⟧, pr2 a · #K f = pr2 b.

Definition isaset_ccomma_morphism a b : isaset (ccomma_morphism a b).
Proof.
  apply (isofhleveltotal2 2).
  - apply homset_property.
  - intro.
    apply hlevelntosn.
    apply homset_property.
Qed.

Definition cComma_mor_eq a b (f f' : ccomma_morphism a b)
  : pr1 f = pr1 f' -> f = f'.
Proof.
  intro H.
  apply subtypePath.
  intro. apply homset_property.
  exact H.
Qed.

Definition ccomma_id a : ccomma_morphism a a.
Proof.
  exists (identity _ ).
  abstract (
  intermediate_path (pr2 a · identity _ );
   [ apply maponpaths; apply functor_id |];
  apply id_right
  ).
Defined.

Definition ccomma_comp a b d :
  ccomma_morphism a b -> ccomma_morphism b d -> ccomma_morphism a d.
Proof.
  intros f g.
  exists (pr1 f · pr1 g).
  abstract (
  rewrite functor_comp;
  rewrite assoc;
  rewrite (pr2 f);
  apply (pr2 g)
   ).
Defined.

Definition ccomma_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists ccomma_object.
  exact ccomma_morphism.
Defined.

Definition ccomma_precategory_data : precategory_data.
Proof.
  exists ccomma_precategory_ob_mor.
  split.
  - exact ccomma_id.
  - exact ccomma_comp.
Defined.

Definition is_precategory_ccomma_precategory_data
  : is_precategory ccomma_precategory_data.
Proof.
  repeat split.
  - intros. apply cComma_mor_eq.
    simpl. apply id_left.
  - intros. apply cComma_mor_eq.
    simpl. apply id_right.
  - intros. apply cComma_mor_eq.
    simpl. apply assoc.
  - intros. apply cComma_mor_eq.
    simpl. apply assoc'.
Qed.

Definition cComma_precat : precategory.
Proof.
  exists ccomma_precategory_data.
  exact is_precategory_ccomma_precategory_data.
Defined.

Lemma has_homsets_cComma_precat: has_homsets cComma_precat.
Proof.
  red.
  intros a b.
  apply isaset_total2.
  - apply homset_property.
  - intro.
    apply hlevelntosn.
    apply homset_property.
Qed.

Definition cComma : category := cComma_precat ,, has_homsets_cComma_precat.


Definition ccomma_pr1_functor_data : functor_data cComma M.
Proof.
  exists pr1.
  intros a b f. exact (pr1 f).
Defined.

Lemma is_functor_ccomma_pr1 : is_functor ccomma_pr1_functor_data.
Proof.
  split.
  - intro a. apply idpath.
  - intros ? ? ? ? ?. apply idpath.
Qed.

Definition cComma_pr1 : cComma ⟶ M := tpair _ _ is_functor_ccomma_pr1.


End const_comma_category_definition.

Section lemmas_on_const_comma_cats.


Context (M C : category).

Local Notation "c ↓ K" := (cComma _ _ K c) (at level 3).

Context (K : functor M C).
Context {c c' : C}.
Context (h : C ⟦c, c'⟧).


Definition cComma_mor_ob : c' ↓ K → c ↓ K.
Proof.
  intro af.
  exists (pr1 af).
  exact (h · pr2 af).
Defined.

Definition cComma_mor_mor (af af' : c' ↓ K) (g : c' ↓ K ⟦af, af'⟧)
  : c ↓ K ⟦cComma_mor_ob af, cComma_mor_ob af'⟧.
Proof.
  exists (pr1 g).
  abstract (
    simpl;
    rewrite <- assoc;
    rewrite (pr2 g);
    apply idpath
    ).
Defined.

Definition cComma_mor_functor_data : functor_data (c' ↓ K) (c ↓ K).
Proof.
  exists cComma_mor_ob.
  exact cComma_mor_mor.
Defined.

Lemma is_functor_cComma_mor_functor_data : is_functor cComma_mor_functor_data.
Proof.
  split.
  - intro. apply cComma_mor_eq.
    apply idpath.
  - intros ? ? ? ? ?. apply cComma_mor_eq.
    apply idpath.
Qed.

Definition functor_cComma_mor : c' ↓ K ⟶ c ↓ K := tpair _ _ is_functor_cComma_mor_functor_data.

End lemmas_on_const_comma_cats.


(** * The general comma categories *)

Section general_comma_categories.

Local Open Scope cat.

Context {C D E: category}.
Variable S : D ⟶ C.
Variable T : E ⟶ C.

Local Open Scope type_scope.
Local Open Scope cat.

Definition comma_cat_ob : UU := ∑ ed : ob E × ob D, C⟦T (pr1 ed), S (pr2 ed)⟧.

Definition comma_cat_mor : comma_cat_ob -> comma_cat_ob -> UU :=
  λ abf : comma_cat_ob,
    (λ cdg : comma_cat_ob,
             ∑ kh : E⟦pr1 (pr1 abf), pr1 (pr1 cdg)⟧ × D⟦pr2 (pr1 abf), pr2 (pr1 cdg)⟧, pr2 (abf) · #S(pr2 kh) = #T(pr1 kh) · pr2 (cdg)).

Definition comma_cat_ob_mor : precategory_ob_mor := make_precategory_ob_mor comma_cat_ob comma_cat_mor.

Definition comma_cat_id : ∏ edf : comma_cat_ob_mor, comma_cat_ob_mor ⟦ edf, edf ⟧.
Proof.
  intro edf. cbn.
  exists (make_dirprod (identity (pr1 (pr1 edf))) (identity (pr2 (pr1 edf)))). cbn.
  abstract (
    rewrite 2 functor_id;
    rewrite id_right;
    rewrite id_left;
    apply idpath
    ).
Defined.

Definition comma_cat_comp : ∏ uvf xyg zwh : comma_cat_ob, comma_cat_mor uvf xyg → comma_cat_mor xyg zwh → comma_cat_mor uvf zwh.
Proof.
  intros uvf xyg zwh ijp klq.
  exists (make_dirprod (pr1 (pr1 ijp) · pr1 (pr1 klq)) (pr2 (pr1 ijp) · pr2 (pr1 klq))).
  abstract (
    cbn;
    rewrite 2 functor_comp;
    rewrite assoc;
    rewrite (pr2 ijp);
    rewrite <- assoc;
    rewrite (pr2 klq);
    rewrite assoc;
    apply idpath
    ).
Defined.

Definition comma_cat_id_comp : precategory_id_comp comma_cat_ob_mor := make_dirprod comma_cat_id comma_cat_comp.

Definition comma_cat_data : precategory_data := tpair _ comma_cat_ob_mor comma_cat_id_comp.

Definition comma_cat_data_id_left :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), identity abf · hkp = hkp .
Proof.
  intros abf cdg hkp.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_left.
    + cbn. apply id_left.
  - cbn. apply (homset_property C).
Qed.

Definition comma_cat_data_id_right :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), hkp · identity cdg = hkp .
Proof.
  intros abf cdg hkp.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_right.
    + cbn. apply id_right.
  - cbn. apply (homset_property C).
Qed.

Definition comma_cat_data_assoc :
  ∏ (stf uvg xyh zwi : comma_cat_data) (jkp : stf --> uvg) (lmq : uvg --> xyh) (nor : xyh --> zwi), jkp · (lmq · nor) = (jkp · lmq) · nor .
Proof.
  intros stf uvg xyh zwi jkp lmq nor.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply assoc.
    + cbn. apply assoc.
  - apply (homset_property C).
Qed.

Definition comma_cat_data_assoc' :
  ∏ (stf uvg xyh zwi : comma_cat_data) (jkp : stf --> uvg) (lmq : uvg --> xyh) (nor : xyh --> zwi), (jkp · lmq) · nor = jkp · (lmq · nor).
Proof.
  intros stf uvg xyh zwi jkp lmq nor.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply assoc'.
    + cbn. apply assoc'.
  - apply (homset_property C).
Qed.

Definition is_precategory_comma_cat_data : is_precategory comma_cat_data :=
  make_is_precategory comma_cat_data_id_left comma_cat_data_id_right comma_cat_data_assoc comma_cat_data_assoc'.

Definition comma_precategory : precategory := make_precategory comma_cat_data is_precategory_comma_cat_data.

Lemma has_homsets_comma_precat : has_homsets comma_precategory.
Proof.
  unfold has_homsets, comma_precategory.
  cbn; unfold comma_cat_ob, comma_cat_mor; cbn.
  intros ? ?.
  apply isaset_total2.
  - apply isaset_dirprod; apply homset_property.
  - intro.
    apply hlevelntosn.
    apply homset_property.
Qed.

Definition comma_category : category := comma_precategory ,, has_homsets_comma_precat.


(** ** Projection functors *)

Definition comma_domain : comma_category ⟶ E.
Proof.
  use make_functor.
  - use make_functor_data.
    + intros uvf; exact (dirprod_pr1 (pr1 uvf)).
    + intros ? ? mor; exact (dirprod_pr1 (pr1 mor)).
  - abstract ( use make_dirprod; [intro; apply idpath | intros ? ? ? ? ?; apply idpath] ).
Defined.

Definition comma_codomain : comma_category ⟶ D.
Proof.
  use make_functor.
  - use make_functor_data.
    + intros uvf; exact (dirprod_pr2 (pr1 uvf)).
    + intros ? ? mor; exact (dirprod_pr2 (pr1 mor)).
  - abstract ( use make_dirprod; [intro; apply idpath | intros ? ? ? ? ?; apply idpath] ).
Defined.

End general_comma_categories.





Section cc_comma.
  (* Context (C D : category). *)
  (* Context (F : C ⟶ D). *)

  Definition cc_structure (C: category) : UU := ∑
                                                                (chosen_terminal : Terminal C)
                                                                (choice_prods: BinProducts C),
                                                                Exponentials choice_prods.

  Definition cc_category := ∑ (C: category), cc_structure C.
  Definition cccat_to_cat : cc_category -> category := pr1.

  Coercion cccat_to_cat: cc_category >-> category.
  Definition cccat_to_ccs : forall {C : cc_category}, cc_structure C := pr2.
  Coercion cccat_to_ccs: cc_category >-> cc_structure.

  Definition has_terminal {C} (c: cc_structure C) : Terminal C := pr1 c.
  Definition has_prods {C} (c : cc_structure C) : BinProducts C := pr1 (pr2 c).


  Definition has_exponentials {C} (c : cc_structure C) : Exponentials _ := (pr2 (pr2 c)).
  Definition ExpF {C : cc_category} : C → C ⟶ C.
    epose has_exponentials.
    unfold Exponentials, is_exponentiable in *.
    intro X.
    epose (is_left_adjoint_constprod_functor2 _ _ (e C X)).

    unfold is_left_adjoint in i.
    intros.
    exact (pr1 i).
    Show Proof.                 (* TODO: tidy *)
  Defined.



  Definition term_ob {C} (c : cc_structure C) : C := (pr1 (pr1 c)).

  Definition ProdF {C : cc_category} (x : C): C ⟶ C.
  eapply (constprod_functor1 (has_prods C) x).
  Defined.



  Definition chosen_prod {C : cc_category} (x y : C): C := ProdF x y.

  (* TODO: remove me? *)
  Lemma chosen_prod_ok { C : cc_category } (x y : C): chosen_prod x y = pr1 (pr1 (has_prods C x y)).
    auto.
  Defined.

(* exponentiation is defined by the right-adjoint to the functor _ × x, namely _^ˣ *)

  Notation " y ^ x " := (ExpF x y). (* exponentiation by x *)

  Definition is_cc_functor {C: cc_category} {D: cc_category}
                        (F : C ⟶ D) : UU
    := (iso (term_ob D) (F (term_ob C))) ×

         (∏ (x y: C), iso (F (chosen_prod x y))
                                     (chosen_prod (F x) (F y))) ×

         (∏ (x y : C), iso (F (ExpF x y)) (ExpF (F x) (F y))).

Definition cc_functor (C D : cc_category) := ∑ (F : C ⟶ D), is_cc_functor F.

  Definition term_iso {C D : cc_category} {F: C ⟶ D}
             (c: is_cc_functor F)  := pr1 c.

  Definition prod_iso {C D : cc_category} {F: C ⟶ D}
             (c: is_cc_functor F) := pr1(pr2 c).

  Definition exp_iso {C D : cc_category} {F: C ⟶ D}
             (c: is_cc_functor F) := pr2 (pr2 c).

Lemma iso_inv_before_iso : ∏ {C : category} {a b : C} (I: iso a b), iso_inv_from_iso I · I = identity b.
  intros.
  erewrite iso_inv_to_right.
  reflexivity.
  simpl.
  rewrite id_left.
  reflexivity.
Defined.

Lemma iso_to_term_is_term: ∏ {C : category} (t_C : Terminal C) (t' : C), iso (TerminalObject t_C) t' -> isTerminal C t'.
  Proof.
    intros.
    unfold isTerminal.
    intros.
    unfold iscontr.
    unshelve econstructor.
    exact (TerminalArrow t_C a · X).
    intros.
    assert (t · iso_inv_from_iso X = TerminalArrow t_C a).
    eapply TerminalArrowUnique.
    rewrite <-X0.
    rewrite <-assoc.
    rewrite (@iso_inv_before_iso C t_C t' X).
    rewrite id_right.
    reflexivity.
Defined.

Lemma iso_to_term_is_term': ∏ {C : category} (t_C : Terminal C) (t' : C), iso (TerminalObject t_C) t' -> Terminal C.
  intros.
  exact (make_Terminal _  (iso_to_term_is_term t_C t' X)).
Defined.

Lemma cc_func_of_term_is_term : forall {C D : cc_category} {F : C ⟶ D},
    is_cc_functor F -> isTerminal _ (F (term_ob C)).
  intros C D F F_is_cc.
  eapply iso_to_term_is_term.
  apply F_is_cc.
Defined.

Lemma iso_trans : ∏ {C : category} { a b c : C }, iso a b → iso b c → iso a c.
  intros ? ? ? ? f g.
  unshelve econstructor.
  + exact ( f · g ).
  + eapply is_iso_comp_of_isos.
Defined.

Lemma iso_sym : ∏ {C : category} { a b : C }, iso a b → iso b a.
  intros ? ? ? f; eapply iso_inv_from_iso; auto.
Defined.

Lemma prod_swap_iso : ∏ {C : cc_category} {c d : C}, iso (chosen_prod c d) (chosen_prod d c).
  unfold chosen_prod.
  unfold ProdF.
  intros.
  edestruct (FunctorCategory.iso_to_nat_iso _ _ (flip_iso (has_prods C) d)) as [α α_nat_iso].
  unfold nat_iso, is_nat_iso in α_nat_iso.
  epose proof (make_iso _ (α_nat_iso _)) as i.
  eapply iso_sym.
  eapply i.
Defined.

  Definition transpose {C : cc_category} {X Y Z : C} (f : C ⟦ ((constprod_functor1 (has_prods C) X) Y) , Z ⟧ ) : C⟦X, Z^Y ⟧.
    epose (Hadj := pr2 (has_exponentials C _)).
    unshelve eapply (adjunction_hom_weq Hadj _ _ _).
    eapply  (compose (nat_trans_constprod_functor1 _ _ _) f).
  Defined.

  Definition exp_precomp : ∏ {C : cc_category} {X Y Z : C} (f : C ⟦ X , Z ⟧ ),
           C ⟦Y^Z, Y^X⟧.

    intros.
    epose (Hadj := pr2 (has_exponentials C _)).
    unshelve epose (is_left_adjoint_constprod_functor2 _ _ Hadj) as Hadj2.
    epose (ε := counit_from_left_adjoint Hadj2).

    unshelve eapply (transpose (_ ·  (ε _))).
    {
      unfold Hadj2.
      eapply (BinProductOfArrows _ _ _ (identity _) f).
    }
    Show Proof.
  Defined.

  Definition exp_postcomp {C : cc_category} {X Y Z : C} (f : C ⟦X, Z⟧) : C ⟦X ^ Y, Z ^ Y⟧ := # (ExpF _) f.

  Lemma right_adjoint_is_ExpF {C: cc_category} {x y : C}: (right_adjoint (has_exponentials C x)) y = ExpF x y.
    simpl.
    unfold ExpF.
    simpl.
    auto.
  Defined.

  Lemma expF_canonical_form {C: cc_category} (x y : C):  pr1 (ExpF y) x = x ^ y.
    reflexivity.
  Defined.

  Lemma gluing_cc_along_cc_BinProducts :
    ∏ (C : cc_category) (R : cc_category) (T : C ⟶ R),
           is_cc_functor T →
           BinProducts (comma_category T (functor_identity R)).
      (* binary products *)
      unfold BinProducts.
      unfold BinProduct.
      intros.
      unshelve econstructor.
      {
        unshelve econstructor.

        { (* product object *)
          destruct c as [[c_R c_C] int_c].
          destruct d as [[d_R d_C] int_d].

          pose (has_prods R) as prods_R.
          unfold BinProducts, BinProduct, isBinProduct in prods_R.
          specialize (prods_R c_R d_R).
          destruct prods_R as [[P' [pi1' pi2']] _].

          unshelve econstructor.
          { (* pair *)
            constructor; [exact  P' | exact (chosen_prod c_C d_C)].
          }
          { (* interpretation *)
            simpl in *.
            pose (prods_R := has_prods R (T c_C) (T d_C)).
            unfold BinProducts, BinProduct, isBinProduct in prods_R.
            pose (P := pr1 (pr1 prods_R)).
            pose (prod_UP := pr2 prods_R).
            destruct X as [_ [prod_iso _]].
            eapply (postcompose ((iso_inv_from_iso (prod_iso _ _)))).
            specialize (prod_UP P' (pi1' · int_c) (pi2' · int_d)).
            destruct prod_UP as [[pair _] _].
            unfold chosen_prod.
            unfold has_prods.
            eapply pair.
          }

        }

        {
          (* product projection *)
          destruct c as [[c_R c_C] int_c];
          destruct d as [[d_R d_C] int_d];
          cbv beta;
          constructor.
          {
            (* first projection *)
            unshelve econstructor.
            constructor;
            simpl in *.
            {
              pose (prods_R := has_prods R c_R d_R).
              unfold BinProducts, BinProduct, isBinProduct in prods_R.
              pose (P := pr1 (pr1 prods_R)).
              pose (pi1 := pr1 (pr2 (pr1 prods_R))).
              pose (pi2 := pr2 (pr2 (pr1 prods_R))).
              simpl in pi1, pi2.
              pose (ump_prod := pr2 prods_R).
              simpl in ump_prod.
              exact pi1.
            }
            {
              pose (prods_C := has_prods C c_C d_C).
              unfold BinProducts, BinProduct, isBinProduct in prods_C.
              pose (P := pr1 (pr1 prods_C)).
              pose (pi1 := pr1 (pr2 (pr1 prods_C))).
              pose (pi2 := pr2 (pr2 (pr1 prods_C))).
              simpl in pi1, pi2.
              pose (ump_prod := pr2 prods_C).
              simpl in ump_prod.
              exact pi1.
            }
            {
              simpl in *.
              pose (pi1R := pr1 (pr2 (pr1 (has_prods R c_R d_R)))).
              pose (pi1C := pr1 (pr2 (pr1 (has_prods C c_C d_C)))).
              simpl in pi1R,pi1C.
              unfold postcompose.
              erewrite <-(_ : pi1R = pr1 (pr2 (pr1 (has_prods R c_R d_R)))).
              erewrite <-(_ : pi1C = pr1 (pr2 (pr1 (has_prods C c_C d_C)))).
              admit.

            }
          }
          {
            admit.
          }


        }
      }
      {
        match goal with
          | [ |- isBinProduct _ _ _ ?prod ?pi1 ?pi2 ] =>
              let HProd := fresh prod_def in
              pose (HProd := prod);
              let HPi1 := fresh "pi1" in
              pose (HPi1 := pi1);
              let HPi2 := fresh "pi2" in
              pose (HPi2 := pi2)
        end.
        fold prod_def pi1 pi2.

        unfold isBinProduct.
        intros.

        simpl.
        admit.
      }
    Admitted.

  Lemma gluing_cc_along_cc_Terminal :
    ∏ {C R : cc_category}
      {T : C ⟶ R} {T_cc : is_cc_functor T},
Terminal (comma_category T (functor_identity R)).
    intros.
    (* terminal object in gl *)
      (* ( termob(D) , termob_iso? , termob(C)) *)
      unfold Terminal.
      unshelve econstructor.
      unshelve econstructor.
      { exact (term_ob R ,, term_ob C). }
      { simpl.
        match goal with
          | [ H: is_cc_functor _ |- _ ] => exact (term_iso H)
        end.
      }
      { unfold isTerminal.
        intros.
        unfold iscontr.
        unshelve econstructor.
        { (* canonical morphism into termob *)
          unshelve econstructor.
          split.
          {
            simpl.
            exact (TerminalArrow (has_terminal R) (pr1 (pr1 a))) .
          }
          {
            simpl.
            exact (TerminalArrow (has_terminal C) (pr2 (pr1 a))) .
          }
          {
            simpl.
            destruct a as [[a_R a_C] int_a].
            simpl.
            simpl in *.

            unshelve epose TerminalArrowUnique.
            { exact R. }

            match goal with
              | [ H: is_cc_functor _ |- _ ] => epose (make_Terminal _ (cc_func_of_term_is_term H))
            end.
            specialize (p t a_R).
            transitivity (TerminalArrow t a_R); auto.
          }
        }
        {
          intro.
          destruct t as [[syn sem] comma_condition].
          simpl in comma_condition.
          destruct a as [[a_R a_C] int_a].
          simpl in *.
          eassert (syn = TerminalArrow _ _).
          eapply TerminalArrowUnique.
          eassert (sem = TerminalArrow _ _).
          eapply TerminalArrowUnique.
          unfold has_terminal.
          generalize comma_condition.
          subst.
          (* rewrite X1, X2. *)
          intros.
          clear comma_condition.
          rename comma_condition0 into comma_condition.
          unshelve eapply PartA.pair_path2.
          {
            simpl.
            constructor; exact syn || exact sem.
          }
          subst; (* rewrite X1, X2; *)
          reflexivity.
          repeat match goal with
                   | [ H: syn = _ |- _ ] => progress rewrite H
                   | [ H: sem = _ |- _ ] => progress rewrite H
                 end;
          reflexivity.
          simpl.
          unfold transportf.
          unfold constr1.
          simpl.
          repeat match goal with
                   | [ H: syn = _ |- _ ] => progress rewrite <-H
                   | [ H: sem = _ |- _ ] => progress rewrite <-H
                 end.
          (* match goal with *)
          (* | [ |- _ = _ _ ?r ] => unshelve erewrite (_ : comma_condition = r) *)
          (* end. *)
          {
            Check comma_condition.
            Check (int_a · # T (TerminalArrow (has_terminal C) a_C)).

            assert (has_homsets R).
            { unfold cc_category in R.
              destruct R as [cat ccs].
              destruct cat.
              simpl.
              auto. }
            match goal with
              | [ H: has_homsets _ |- _ ] => unfold has_homsets in H
            end.
            Check (int_a · # T (TerminalArrow (has_terminal C) a_C)).
            match goal with
              | [ H: context[isaset _] |- _ ] =>
                  specialize (H a_R (T (has_terminal C)));
                  unfold isaset in H;
                  unfold isaprop in H;
                  simpl in H;
                  unfold iscontr in H;
                  simpl in H;
                  edestruct (H _ _ comma_condition) as [cntr pf];
                  eapply cntr
            end.
          }
        }
      }
Abort. (* COQBUG Defined and Qed both fail here, report anomaly at clib/int.ml:45*)


Section gluing_cc_along_cc.
  Context {C R : cc_category} {T : C ⟶ R}.
  Context {R_pbs : Pullbacks R}. (* R needs pullbacks so that we can define the exponential objects
                                    in the gluing category *)
  Context (T_cc : is_cc_functor T).



  Definition comma_exponential (one two : (comma_category T (functor_identity R))):
    (comma_category T (functor_identity R)).
    destruct one as [[R1 Δ1] q1].
    destruct two as [[R2 Δ2] q2].

    pose (has_exponentials C) as HExpC.
    unfold Exponentials in HExpC.
    unfold is_exponentiable in HExpC.
    epose (ε := counit_from_left_adjoint (HExpC _)).

    match goal with
      | [ H: is_cc_functor _ |- _ ] =>
          epose proof (p := (precomp_with prod_swap_iso (inv_from_iso (prod_iso H _ _))) · # T(ε _))
    end.
    simpl in p.
    unshelve epose (pb := Pullback (exp_postcomp q2) (transpose(p) · ?[f])).
    {
      shelve.
    }
    {
      simpl.
      unfold HExpC.
      repeat rewrite right_adjoint_is_ExpF in *.
      pose (exp_precomp (Y := T Δ2) q1).
      simpl in p0.
      Unset Printing Notations.
      Fail rewrite (expF_canonical_form Δ2 Δ1). (* coq BUG *)
      Set Printing Notations.
      (* GOAL:
               R [ T Δ2 ^ T (Δ2 ^ (Δ2 ^ Δ1)), T Δ2 ^ R1 ]
       *)
      eapply p0.
    }

    unshelve epose ( _ : pb).
    unfold pb.
    match goal with
      | [ H: Pullbacks _ |- _ ] =>
          unfold Pullbacks in H;
          specialize (H _ _ _ (exp_postcomp q2) (transpose p · exp_precomp q1));
          eapply H
    end .
    simpl in p0.
    edestruct p0 as [[P [p1 p2]] P_pullback].
    simpl in *.
    unfold HExpC in p2.
    unshelve econstructor.
    { unshelve econstructor; exact P || exact (Δ2 ^ Δ1). }
    { simpl.
      eapply p2. }
  Defined.

  Theorem gluing_cc_along_cc_is_cc : cc_structure (comma_category T (functor_identity R)).
  Proof.
    intros.
    unfold cc_structure.
    constructor.
    { (* terminal object in gl *)
      (* ( termob(D) , termob_iso? , termob(C)) *)
      unfold Terminal.
      unshelve econstructor.
      unshelve econstructor.
      { exact (term_ob R ,, term_ob C). }
      { simpl.
        match goal with
          | [ H: is_cc_functor _ |- _ ] => exact (term_iso H)
        end.
      }
      { unfold isTerminal.
        intros.
        unfold iscontr.
        unshelve econstructor.
        { (* canonical morphism into termob *)
          unshelve econstructor.
          split.
          {
            simpl.
            exact (TerminalArrow (has_terminal R) (pr1 (pr1 a))) .
          }
          {
            simpl.
            exact (TerminalArrow (has_terminal C) (pr2 (pr1 a))) .
          }
          {
            simpl.
            destruct a as [[a_R a_C] int_a].
            simpl.
            simpl in *.

            unshelve epose TerminalArrowUnique.
            { exact R. }

            match goal with
              | [ H: is_cc_functor _ |- _ ] => epose (make_Terminal _ (cc_func_of_term_is_term H))
            end.
            specialize (p t a_R).
            transitivity (TerminalArrow t a_R); auto.
          }
        }
        {
          intro.
          destruct t as [[syn sem] comma_condition].
          simpl in comma_condition.
          destruct a as [[a_R a_C] int_a].
          simpl in *.
          eassert (syn = TerminalArrow _ _).
          eapply TerminalArrowUnique.
          eassert (sem = TerminalArrow _ _).
          eapply TerminalArrowUnique.
          unfold has_terminal.
          generalize comma_condition.
          subst.
          (* rewrite X1, X2. *)
          intros.
          clear comma_condition.
          rename comma_condition0 into comma_condition.
          unshelve eapply PartA.pair_path2.
          {
            simpl.
            constructor; exact syn || exact sem.
          }
          subst; (* rewrite X1, X2; *)
          reflexivity.
          repeat match goal with
                   | [ H: syn = _ |- _ ] => progress rewrite H
                   | [ H: sem = _ |- _ ] => progress rewrite H
                 end;
          reflexivity.
          simpl.
          unfold transportf.
          unfold constr1.
          simpl.
          repeat match goal with
                   | [ H: syn = _ |- _ ] => progress rewrite <-H
                   | [ H: sem = _ |- _ ] => progress rewrite <-H
                 end.
          (* match goal with *)
          (* | [ |- _ = _ _ ?r ] => unshelve erewrite (_ : comma_condition = r) *)
          (* end. *)
          {
            Check comma_condition.
            Check (int_a · # T (TerminalArrow (has_terminal C) a_C)).

            assert (has_homsets R).
            { unfold cc_category in R.
              destruct R as [cat ccs].
              destruct cat.
              simpl.
              auto. }
            match goal with
              | [ H: has_homsets _ |- _ ] => unfold has_homsets in H
            end.
            Check (int_a · # T (TerminalArrow (has_terminal C) a_C)).
            match goal with
              | [ H: context[isaset _] |- _ ] =>
                  specialize (H a_R (T (has_terminal C)));
                  unfold isaset in H;
                  unfold isaprop in H;
                  simpl in H;
                  unfold iscontr in H;
                  simpl in H;
                  edestruct (H _ _ comma_condition) as [cntr pf];
                  eapply cntr
            end.
          }
        }

      }
    }
    {
      unshelve econstructor.
      { eapply gluing_cc_along_cc_BinProducts; auto. }
      {
        match goal with
          | [  |- Exponentials ?binprods ] => let Hbinprods := fresh "binprods" in
                                            pose  binprods as Hbinprods;
                                            fold Hbinprods
        end.
        unfold Exponentials.
        intros.
        unfold is_exponentiable.
        (* GOAL: the functor (a × -) is a left adjoint *)
        unfold Core.is_left_adjoint, Core.are_adjoints.
        unshelve eexists.
        {
          (*  exponentiation functor (_ ^ a) *)
          (* The exponential objects (R₂,q₂,Δ₂)^(R₁,q₁,Δ₁) in the category are (R, q, Δ₂^Δ₁) in the
            pullback object in the square: *)
          (*  R -------------- r -------------> R₂^R₁
             |                                   |
             |                                   |
             q                                postcomp q₂
             |                                   |
             |                                   |
             |                                   |
             v                                   v
          T(Δ₂^Δ₁) -- precomp(p) · q₁^* --->  T(Δ₂)^R₁. *)

          unshelve econstructor.
          { unshelve econstructor.
            {  intro input.
               exact (comma_exponential a input).
            }
            {
              intros.
              cbn beta.
              epose (postcomp_with X).
              unshelve econstructor.
            }

            intros.

          }

          admit.
        }

  Admitted.
End gluing_cc_along_cc.
