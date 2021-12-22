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

Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.Core.Isos.
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
  Definition term_ob {C} (c : cc_structure C) : C := (pr1 (pr1 c)).

  Definition chosen_prod {C : cc_category} (x y : C): C.
      pose proof (has_prods C) as prods_C.
      unfold BinProducts, BinProduct, isBinProduct in prods_C.
      specialize (prods_C x y).
      destruct prods_C as [[P [pi1 pi2]] _].
      exact P.
Defined.


    Definition chosen_exp {C : cc_category} (x y : C): C := (pr1 (has_exponentials C x) y). (* defined by the right-adjoint to the functor _ × x, namely _^ˣ *)

  Notation " y ^ x " := (chosen_exp x y). (* exponentiation by x *)

  Definition is_cc_functor {C: cc_category} {D: cc_category}
                        (F : C ⟶ D) : UU
    := (iso (term_ob D) (F (term_ob C))) ×

         (∏ (x y: C), iso (F (chosen_prod x y))
                                     (chosen_prod (F x) (F y))) ×

         (∏ (x y : C), iso (F (chosen_exp x y)) (chosen_exp (F x) (F y))).

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

  Theorem gluing_cc_along_cc_is_cc :
    ∏ (C : cc_category) (R : cc_category) (T : C ⟶ R),
           is_cc_functor T ->
           cc_structure (comma_category T (functor_identity R)).
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
        exact (term_iso X).
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



            epose (make_Terminal _ (cc_func_of_term_is_term X)).
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
          rewrite X0, X1.
          intros.
          clear comma_condition.
          rename comma_condition0 into comma_condition.
          Fail eapply (total2_paths2 (a1 := (TerminalArrow _ a_R,, TerminalArrow _ a_C)) (a2 := (TerminalArrow _ a_R,, TerminalArrow _ a_C)) (b1 := comma_condition) (b2 := match
                                                                                                                                                                             TerminalArrowUnique
                                                                                                                                                                               (make_Terminal (T (term_ob C)) (cc_func_of_term_is_term X)) a_R
                                                                                                                                                                               (TerminalArrow
                                                                                                                                                                                  (make_Terminal (T (term_ob C)) (cc_func_of_term_is_term X)) a_R) in
                                                                                                                                                                             (_ = y) return (int_a · # T (TerminalArrow _ a_C) = y)
                                                                                                                                                                           with
                                                                                                                                                                           | idpath _ =>
                                                                                                                                                                               TerminalArrowUnique
                                                                                                                                                                                 (make_Terminal (T (term_ob C)) (cc_func_of_term_is_term X)) a_R
                                                                                                                                                                                 (int_a · # T (TerminalArrow _ a_C))
                                                                                                                                                                           end)).

          Fail eapply (total2_paths2 (a1 := {| pr1 := syn; pr2 := sem |}) (a2:={|
                                                                                 pr1 := TerminalArrow (has_terminal R) a_R;
                                                                                 pr2 := TerminalArrow (has_terminal C) a_C |}) (b1 := comma_condition) (b2 := match
                                                                                                                                                               TerminalArrowUnique
                                                                                                                                                                 (make_Terminal (T (term_ob C)) (cc_func_of_term_is_term X)) a_R
                                                                                                                                                                 (TerminalArrow
                                                                                                                                                                    (make_Terminal (T (term_ob C)) (cc_func_of_term_is_term X)) a_R) in
                                                                                                                                                               (_ = y) return (int_a · # T (TerminalArrow (has_terminal C) a_C) = y)
                                                                                                                                                             with
                                                                                                                                                             | idpath _ =>
                                                                                                                                                                 TerminalArrowUnique
                                                                                                                                                                   (make_Terminal (T (term_ob C)) (cc_func_of_term_is_term X)) a_R
                                                                                                                                                                   (int_a · # T (TerminalArrow (has_terminal C) a_C))
                                                                                                                                                             end) _ _).
          eapply PartA.pair_path2 ; simpl.
          unfold transportf.
          unfold constr1.
          simpl.
          admit.
        }
      }
    }
    unshelve econstructor.
    {

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

             rewrite <-pi1R.
              pose (pi2^R := pr2 (pr2 (pr1 prods_C))).
             unfold has_prods.
             simpl.

             simpl.
             unfold inv_from_iso.
             unfold invmap.
            }



          }


        }
      }
      {
        admit.
      }
    }
    {admit.}
    all: admit.
  Admitted.
