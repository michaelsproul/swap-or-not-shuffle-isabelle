theory AbstractSwapOrNotShuffle
imports
  HOL.List
  "HOL-Library.Permutation"
  "HOL-Algebra.Ring"
begin

(* Swap or not primitive for shuffling a single element *)
definition (in abelian_group)
  swap_or_not  :: "'a \<Rightarrow> ('a \<times> ('a set \<Rightarrow> bool)) list \<Rightarrow> 'a"
where
  "swap_or_not x kfs \<equiv>
    fold
      (\<lambda>(ki, fi) x. let
        x' = ki \<ominus> x in
        if fi {x, x'} then x' else x
      )
      kfs
      x"

lemma (in abelian_group) swap_or_not_nil:
  "swap_or_not x [] = x"
  by (fastforce simp: swap_or_not_def)

lemma (in abelian_group) swap_or_not_rec:
  "swap_or_not x ((ki, fi) # kfs) =
    (if fi {x, ki \<ominus> x} then
      swap_or_not (ki \<ominus> x) kfs
    else
      swap_or_not x kfs)"
  by (fastforce simp: swap_or_not_def)

(* Swap or not shuffle on lists, parameterised by keys (k) and round functions (f) *)
(* The number of rounds is determined by the number of keys and round functions provided *)
definition (in abelian_group)
  swap_or_not_shuffle :: "'a list \<Rightarrow> ('a \<times> ('a set \<Rightarrow> bool)) list \<Rightarrow> 'a list"
where
  "swap_or_not_shuffle xs kfs \<equiv> [swap_or_not x kfs. x \<leftarrow> xs]"

lemma (in abelian_group) swap_or_not_shuffle_rec:
  "swap_or_not_shuffle xs (kfs @ [(k, f)]) =
     map (\<lambda>x. swap_or_not x [(k, f)]) (swap_or_not_shuffle xs kfs)"
  by (fastforce simp: swap_or_not_shuffle_def swap_or_not_def)

(* Mapping a bijection over a permuted list yields another permutation *)
lemma map_perm:
  "\<lbrakk>xs <~~> ys; bij_betw f (set ys) (set ys); distinct xs\<rbrakk>
  \<Longrightarrow> xs <~~> map f ys"
  apply (clarsimp simp: mset_eq_perm[symmetric])
  apply (clarsimp simp: bij_betw_def dest!: mset_set_set[symmetric])
  using image_mset_mset_set mset_eq_setD by fastforce

lemma (in abelian_group) plus_left_cancel:
  "\<lbrakk>a \<oplus> b = a \<oplus> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> b = c"
  by fastforce

lemma (in abelian_group) minus_left_cancel:
  "\<lbrakk>a \<ominus> b = a \<ominus> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> b = c"
  by (metis add.Units_eq add.Units_l_cancel add.inv_closed l_neg local.minus_eq)

lemma (in abelian_group) double_minus_eq:
  "\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> a \<ominus> (a \<ominus> b) = b"
  by (metis (no_types, lifting) abelian_group.minus_add abelian_group.minus_minus
      abelian_group.r_neg1 abelian_group_axioms add.inv_closed local.minus_eq)

(* The swap or not function is a bijection *)
lemma (in abelian_group) swap_or_not_bij:
  "k \<in> carrier G \<Longrightarrow>
   set xs = carrier G \<Longrightarrow>
   bij_betw (\<lambda>x. swap_or_not x [(k, f)]) (set xs) (set xs)"
  apply (clarsimp simp: bij_betw_def)
  apply (rule conjI)
   apply (clarsimp simp: swap_or_not_def Let_def inj_on_def)
   apply safe
      apply (erule (1) minus_left_cancel)
       apply ((fastforce simp: double_minus_eq insert_commute)+)[4]
   apply (fastforce simp: swap_or_not_def Let_def)
  apply (clarsimp simp: swap_or_not_def Let_def image_def)
  apply (frule_tac x="k \<ominus> x" in bspec;
         fastforce simp: double_minus_eq insert_commute)
  done

(* Swap or not shuffle yields a permutation of the original list *)
lemma (in abelian_group) swap_or_not_shuffle_perm:
  "\<lbrakk>distinct xs; set xs = carrier G; set (map fst kfs) \<subseteq> carrier G\<rbrakk>
  \<Longrightarrow> xs <~~> swap_or_not_shuffle xs kfs"
  apply (induct kfs arbitrary: xs rule: List.rev_induct)
   apply (fastforce simp: swap_or_not_shuffle_def swap_or_not_nil)
  apply (rename_tac kf kfs' xs')
  apply (case_tac kf, rename_tac k f)
  apply (clarsimp simp: swap_or_not_shuffle_rec)
  apply (rule map_perm)
    apply fastforce
   apply (erule swap_or_not_bij)
  using perm_set_eq by blast

end