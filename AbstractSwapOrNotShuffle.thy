theory AbstractSwapOrNotShuffle
imports
  HOL.List
  "HOL-Library.Permutation"
  "HOL-Algebra.Ring"
  "HOL-Algebra.Elementary_Groups"
  "HOL-Word.Word"
  "Word_Lib.Word_Syntax"
  "Word_Lib.Word_Lemmas"
  "Word_Lib.Word_Lemmas_64"
  (* "Word_Lib.Word_Lemma_Bucket" *)
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

type_synonym u8 = word8
type_synonym u16 = word16
type_synonym u32 = word32
type_synonym u64 = word64
type_synonym h256 = "u8 list"

definition "SHUFFLE_ROUND_COUNT \<equiv> 90"

(* Opaque definition of our hash function *)
consts
  hash :: "u8 list \<Rightarrow> h256"

(* TODO:
   make little-endian
   remove witness type
*)
definition
  int_to_bytes :: "('a :: len) \<Rightarrow> int \<Rightarrow> h256"
where
  "int_to_bytes _ x \<equiv> word_rsplit (word_of_int x :: 'a word)"

abbreviation "int_to_bytes1 x \<equiv> int_to_bytes (0 :: 8) x"
abbreviation "int_to_bytes4 x \<equiv> int_to_bytes (0 :: 32) x"

definition
  bytes_to_int :: "('a :: len) \<Rightarrow> u8 list \<Rightarrow> int"
where
  "bytes_to_int _ bytes \<equiv> uint (word_rcat bytes :: 'a word)"

abbreviation "bytes32_to_int bytes \<equiv> bytes_to_int (0 :: 32) bytes"

definition
  compute_shuffled_index :: "u64 \<Rightarrow> u64 \<Rightarrow> h256 \<Rightarrow> u64"
where
  "compute_shuffled_index index index_count seed \<equiv>
    fold
      (\<lambda>current_round. \<lambda>index. let
        pivot = bytes32_to_int
                  (take 8 (hash (seed @ int_to_bytes1 current_round)))
                mod uint index_count;
        flip = (word_of_int pivot + index_count - index) mod index_count;
        position = max index flip;
        source = hash (seed @ int_to_bytes1 current_round @ int_to_bytes4 (uint position div 256));
        byte = source ! unat (position mod 256 div 8);
        bit = (byte >> unat (position mod 8)) mod 2
        in
          if bit = 1 then flip else index
      )
      [0..SHUFFLE_ROUND_COUNT]
      index"

(*
  ki: depends on current_round (that's fine), and seed (immutable), and
      index_count which is a bit awkward
  fi: depends on max of two parameters, seed, round
*)

(* flip = ki \<ominus> x *)
(* we're operating in the Abelian group of word64's modulo the index_count *)

definition
  mod_word_group :: "u64 \<Rightarrow> (u64, 'm) ring_scheme"
where
  "mod_word_group n = \<lparr>
    carrier = {0..<n},
    mult = \<lambda>x y. (x * y) mod n,
    one = 1,
    zero = 0,
    add = \<lambda>x y. (x + y) mod n,
    \<dots> = (undefined :: 'm)
  \<rparr>"

lemma mod_magic:
  "n > 0 \<Longrightarrow> y = x mod n \<Longrightarrow> (y :: int) \<in> {0..<n}"
  quickcheck
  oops

lemma word_mod_mod_idem:
  "n > 0 \<Longrightarrow> x mod n mod n = (x :: ('a::len) word) mod n"
  apply (clarsimp simp: word_mod_def)
  apply (subst uint_word_of_int)
  apply (subst uint_mod[symmetric])
  apply (subst uint_idem[where 'a='a])
  apply (subst uint_mod)
  apply (fastforce simp: uint_mod)
  done

(* Validator registry limit *)
abbreviation "vrl \<equiv> 2^40"

lemma pls:
  "\<lbrakk>n > 0; n \<le> vrl; x \<le> vrl; y \<le> vrl\<rbrakk> \<Longrightarrow>
  (x mod n + y) mod n = (x + y mod n) mod (n :: u64)"
  apply (clarsimp simp: word_mod_def)
  apply (subgoal_tac "y = word_of_int (uint y)")
   apply (erule ssubst[where t=y])
   apply (subst plus_word.abs_eq)
   apply (subst uint_word_of_int)
   apply clarsimp
   apply (clarsimp simp: word_add_def)
   apply (subst uint_plus_simple_iff[THEN iffD1, symmetric])
  apply (rule word_plus_mono_right2[where b=vrl])
  apply (clarsimp simp: word_le_def word_less_def, uint_arith, fastforce)
  apply (clarsimp simp: word_le_def word_less_def word_mod_def, uint_arith)
  apply clarsimp
  defer 
sorry

lemma "\<lbrakk>n > 0\<rbrakk>\<Longrightarrow> (x + y) mod n = (x mod n + y mod n) mod (n :: u64)"
  quickcheck

(*
  x = 0, y = 1, z = 2
  n = 2

  (0 + 1) mod 2 = 1
     + 2 (mod 2) = 1

  vs

  (0 + (1 + 2) mod 2) mod 2 = 1
*)

(*
  x mod n = k such that x = cx*n + kx

  x + y = (cx + cy)*n + (kx + ky)

  know kx < n and ky < n, so kx + ky is _at most_ (2n - 2)

  x + y mod n = (kx + ky) mod n
*)
oops

lemma add_mod_distrib_int:
  "\<lbrakk>n > 0; n \<le> vrl; x < n; y < n; z < n\<rbrakk> \<Longrightarrow>
  ((x + y) mod n + z) mod n = (x + (y + z) mod n) mod (n :: int)"
  by (fastforce simp: add.commute add.left_commute mod_add_right_eq)

lemma word_mod_add_right_eq:
  "\<lbrakk>n > 0; x < vrl; y < vrl\<rbrakk> \<Longrightarrow> (x + y mod n) mod n = (x + y) mod (n :: u64)"
  apply (clarsimp simp: word_mod_def word_add_def word_less_def)
  sorry
find_theorems word_of_int uint

find_theorems name: Ring

thm abelian_groupE(3)[simplified abelian_group_def]

find_theorems "abelian_group" 

lemma add_mod_distrib:
  "\<lbrakk>n > 0; n \<le> vrl; x < n; y < n; z < n\<rbrakk> \<Longrightarrow>
  ((x + y) mod n + z) mod n = (x + (y + z) mod n) mod (n :: u64)"
  apply (clarsimp simp: word_add_def)



  apply (clarsimp simp: word_of_int_def)
sorry

locale bounded_n =
  fixes n :: u64
  assumes n_non_zero: "n > 0"
  assumes n_leq_validator_registry_limit: "n \<le> 2^40"

sublocale bounded_n < mod_word_abelian: abelian_group "mod_word_group n"
   apply (clarsimp simp: abelian_group_def)
   apply (insert n_non_zero n_leq_validator_registry_limit)
   apply (rule conjI)
    apply (rule abelian_monoidI)
        apply (fastforce simp: mod_word_group_def word_mod_less_divisor n_non_zero)
       apply (fastforce simp: mod_word_group_def n_non_zero)
      apply (clarsimp simp: mod_word_group_def)
     apply (fastforce elim: add_mod_distrib)
    apply (fastforce simp: mod_word_group_def word_mod_def word_less_def)
   apply (clarsimp simp: mod_word_group_def word_mod_def word_less_def word_le_def add.commute)
  (* FIXME: nasty copy pasta *)
  apply unfold_locales
        apply (simp_all add: mod_word_group_def)
       apply (fastforce simp: mod_word_group_def word_mod_less_divisor n_non_zero)
      apply (fastforce elim: add_mod_distrib)
     apply (fastforce simp: mod_word_group_def word_mod_def word_less_def)+
   apply (fastforce simp: mod_word_group_def word_mod_def word_less_def word_le_def add.commute)
  apply (clarsimp simp: Units_def)
  apply (clarsimp simp: add.commute)
  apply (case_tac "x = 0")
   apply (rule_tac x = "0" in bexI; fastforce simp: word_mod_def)
  apply (rule_tac x = "n - x" in bexI)
   apply (fastforce simp: word_mod_def)
  apply (clarsimp simp: word_minus_def word_less_def word_le_def)
  apply uint_arith
  done

end