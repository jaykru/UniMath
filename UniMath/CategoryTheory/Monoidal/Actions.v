(**
  Generalisation of the concept of actions, over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.

Local Open Scope cat.

Section A.

Context (Mon_V : monoidal_precat).

Let V := monoidal_precat_precat Mon_V.
Let I := monoidal_precat_unit Mon_V.
Let tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α' := monoidal_precat_associator Mon_V.
Let λ' := monoidal_precat_left_unitor Mon_V.
Let ρ' := monoidal_precat_right_unitor Mon_V.

Section Actions_Definition.

(* A ⊙ I --> A *)

Section Actions_Natural_Transformations.

Context {A : precategory} (odot : functor (precategory_binproduct A V) A).

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (# odot (f #, g)) (at level 31).

Definition odot_I_functor : functor A A := functor_fix_snd_arg _ _ _ odot I.

Definition action_right_unitor : UU := nat_iso odot_I_functor (functor_identity A).

Definition odot_x_odot_y_functor : (A ⊠ V) ⊠ V ⟶ A :=
  functor_composite (pair_functor odot (functor_identity _)) odot.

Definition odot_x_otimes_y_functor : (A ⊠ V) ⊠ V ⟶ A :=
  functor_composite (precategory_binproduct_unassoc _ _ _)
                    (functor_composite (pair_functor (functor_identity _) tensor) odot).

Definition action_convertor : UU := nat_iso odot_x_odot_y_functor odot_x_otimes_y_functor.

Definition action_triangle_eq (ϱ : action_right_unitor) (χ : action_convertor) := ∏ (a : A), ∏ (x : V),
  (pr1 ϱ a) #⊙ (id x) = (pr1 χ ((a, I), x)) · (id a) #⊙ (pr1 λ' x).

Definition action_pentagon_eq (χ : action_convertor) := ∏ (a : A), ∏ (x y z : V),
  (pr1 χ ((a ⊙ x, y), z)) · (pr1 χ ((a, x), y ⊗ z)) =
  (pr1 χ ((a, x), y)) #⊙ (id z) · (pr1 χ ((a, x ⊗ y), z)) ·
                                  (id a) #⊙ (pr1 α' ((x, y), z)).

End Actions_Natural_Transformations.

(* Action over a monoidal category. *)
Definition action : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor odot), ∑ (χ : action_convertor odot), (action_triangle_eq odot ϱ χ) × (action_pentagon_eq odot χ).

Definition action_struct : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor odot), ∑ (χ : action_convertor odot), unit.

End Actions_Definition.

(* The canonical tensorial action on a monoidal category. *)
Definition tensorial_action : action.
Proof.
  exists V.
  exists tensor.
  exists ρ'.
  exists α'.
  exact (monoidal_precat_eq Mon_V).
Defined.

(* The action induced by a strong monoidal functor U. *)
Section Strong_Monoidal_Functor_Action.

Context (Mon_A : monoidal_precat).

Let A := monoidal_precat_precat Mon_A.
Let I_A := monoidal_precat_unit Mon_A.
Let tensor_A := monoidal_precat_tensor Mon_A.
Notation "X ⊗_A Y" := (tensor_A (X , Y)) (at level 31).
Notation "f #⊗_A g" := (#tensor_A (f #, g)) (at level 31).
Let α_A := monoidal_precat_associator Mon_A.
Let λ_A := monoidal_precat_left_unitor Mon_A.
Let ρ_A := monoidal_precat_right_unitor Mon_A.

Context (U : strong_monoidal_functor Mon_V Mon_A).

Definition otimes_U_functor : A ⊠ V ⟶ A := functor_composite (pair_functor (functor_identity _) U) tensor_A.

Definition U_action_ρ_nat_trans : odot_I_functor otimes_U_functor ⟹ functor_identity A.
  refine (nat_trans_comp _ _ _ _  (pr1 ρ_A)).
  unfold odot_I_functor.
  pose (ϵ_inv := inv_from_iso (mk_iso (pr1 (pr2 U)))).
  set (aux := nat_trans_from_functor_fix_snd_morphism_arg _ _ _ tensor_A _ _ ϵ_inv).
  (* aux is "morally" the result, but types do not fully agree, hence we argue more extensionally *)
  use tpair.
  - intro a.
    apply (pr1 aux a).
  - cbn; red.
    intros a a' f.
    cbn.
    rewrite functor_id.
    exact (pr2 aux a a' f).
Defined.

Definition U_action_ρ_is_nat_iso : is_nat_iso U_action_ρ_nat_trans.
Proof.
  intro.
  cbn.
  use is_iso_comp_of_is_isos.
  - use is_iso_tensor_iso.
    + exact (identity_is_iso _ _).
    + use is_iso_inv_from_iso.
  - exact (pr2 ρ_A c).
Qed.

Definition U_action_ρ : action_right_unitor otimes_U_functor := mk_nat_iso _ _ U_action_ρ_nat_trans U_action_ρ_is_nat_iso.

Definition U_action_χ_nat_trans_data : nat_trans_data (odot_x_odot_y_functor otimes_U_functor)
(odot_x_otimes_y_functor otimes_U_functor).
Proof.
  pose (μ := pr1 (pr2 (pr2 (pr1 U)))).
  intro x.
  pose (k := ob1 (ob1 x)); pose (k' := ob2 (ob1 x)); pose (k'' := ob2 x).
  exact (pr1 α_A ((k, U k'), U k'') · id k #⊗_A pr1 μ (k', k'')).
Defined.

Definition U_action_χ_is_nat_trans : is_nat_trans (odot_x_odot_y_functor otimes_U_functor)
  (odot_x_otimes_y_functor otimes_U_functor) U_action_χ_nat_trans_data.
Proof.
  pose (μ := pr1 (pr2 (pr2 (pr1 U)))).
  unfold U_action_χ_nat_trans_data.
  intros x x' g.
  cbn.
  pose (k_1 := ob1 (ob1 x)); pose (k'_1 := ob2 (ob1 x)); pose (k''_1 := ob2 x).
  pose (k_2 := ob1 (ob1 x')); pose (k'_2 := ob2 (ob1 x')); pose (k''_2 := ob2 x').
  pose (f := mor1 (mor1 g)); pose (f' := mor2 (mor1 g)); pose (f'' := mor2 g).
  assert (α_nat_law := pr2 (pr1 α_A) ((k_1, U k'_1), U k''_1)
                                     ((k_2, U k'_2), U k''_2)
                                     ((f #, #U f') #, #U f'')).
  assert (μ_coher : id k_1 #⊗_A (pr1 μ (k'_1, k''_1)) · (f #⊗_A #U (f' #⊗ f'')) =
                    f #⊗_A (#U f' #⊗_A #U f'') · id k_2 #⊗_A (pr1 μ (k'_2, k''_2))).
  { do 2 rewrite <- tensor_comp.
    rewrite id_left; rewrite id_right.
    assert (snd_eq : pr1 μ (k'_1, k''_1) · # U (f' #⊗ f'') =
                     # tensor_A (# U f' #, # U f'') · pr1 μ (k'_2, k''_2)).
    { apply pathsinv0.
      exact (pr2 μ (k'_1, k''_1) (k'_2, k''_2) (f' #, f'')).
    }
    change (# tensor_A (f #, pr1 μ (k'_1, k''_1) · # U (# tensor (f' #, f''))) =
            # tensor_A (f #, # tensor_A (# U f' #, # U f'') · pr1 μ (k'_2, k''_2))).
    rewrite <- snd_eq.
    apply idpath.
  }
  change (# tensor_A (# tensor_A (f #, # U f') #, # U f'') ·
            pr1 (pr1 α_A) ((k_2, U k'_2), U k''_2) =
          pr1 (pr1 α_A) ((k_1, U k'_1), U k''_1) ·
              # tensor_A (f #, # tensor_A (# U f' #, # U f''))) in α_nat_law.
  assert (α_nat_law' := maponpaths (λ p, p · id k_2 #⊗_A (pr1 μ (k'_2, k''_2))) α_nat_law).
  simpl in α_nat_law'.
  repeat rewrite <- assoc in α_nat_law'.
  change (# tensor_A (# tensor_A (f #, # U f') #, # U f'') ·
            (pr1 (pr1 α_A) ((k_2, U k'_2), U k''_2) ·
                 # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))) =
          pr1 (pr1 α_A) ((k_1, U k'_1), U k''_1) ·
              (# tensor_A (f #, # tensor_A (# U f' #, # U f'')) ·
                 # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2)))) in α_nat_law'.
  change (# tensor_A (id k_1 #, pr1 μ (k'_1, k''_1)) ·
            # tensor_A (f #, # U (# tensor (f' #, f''))) =
          # tensor_A (f #, # tensor_A (# U f' #, # U f'')) ·
            # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2))) in μ_coher.
  pose (common := (# tensor_A (f #, # tensor_A (# U f' #, # U f'')) ·
                     # tensor_A (id k_2 #, pr1 μ (k'_2, k''_2)))).
  fold common in μ_coher.
  fold common in α_nat_law'.
  rewrite <- μ_coher in α_nat_law'.
  repeat rewrite assoc in α_nat_law'.
  repeat rewrite assoc.
  exact α_nat_law'.
Qed.

Definition U_action_χ_nat_trans : odot_x_odot_y_functor otimes_U_functor ⟹ odot_x_otimes_y_functor otimes_U_functor :=
  mk_nat_trans _ _ U_action_χ_nat_trans_data U_action_χ_is_nat_trans.

Lemma U_action_χ_is_nat_iso : is_nat_iso U_action_χ_nat_trans.
Proof.
  intro x.
  pose (k := ob1 (ob1 x)); pose (k' := ob2 (ob1 x)); pose (k'' := ob2 x).
  use is_iso_comp_of_is_isos.
  - exact (pr2 α_A ((k, U k'), U k'')).
  - use is_iso_tensor_iso.
    + use identity_is_iso.
    + exact (pr2 (pr2 U) (k', k'')).
Qed.

Definition U_action_χ : action_convertor otimes_U_functor :=
  mk_nat_iso _ _ U_action_χ_nat_trans U_action_χ_is_nat_iso.

Definition U_action_struct : action_struct.
Proof.
  exists A.
  exists otimes_U_functor.
  (* K ⊗ U I_C -- (1_K ⊗ ϵ^{-1} · λ_D K) --> K *)
  exists U_action_ρ.
  exists U_action_χ.
  exact tt.
Defined.

Context
  {U_action_tlaw : action_triangle_eq (A := pr1 U_action_struct)
                                      (pr1 (pr2 U_action_struct))
                                      (pr1 (pr2 (pr2 U_action_struct)))
                                      (pr1 (pr2 (pr2 (pr2 U_action_struct))))}
  {U_action_plaw : action_pentagon_eq (A := pr1 U_action_struct)
                                      (pr1 (pr2 U_action_struct))
                                      (pr1 (pr2 (pr2 (pr2 U_action_struct))))}.

Definition U_action : action.
  exists (pr1 U_action_struct).
  exists (pr1 (pr2 U_action_struct)).
  exists (pr1 (pr2 (pr2 U_action_struct))).
  exists (pr1 (pr2 (pr2 (pr2 U_action_struct)))).
  exists U_action_tlaw.
  exact U_action_plaw.
Defined.

End Strong_Monoidal_Functor_Action.

End A.
