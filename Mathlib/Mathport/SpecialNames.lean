/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathlib.Mathport.Rename

namespace Mathlib.Prelude

-- Note: we do not currently auto-align constants.
#align quot Quot
#align quot.mk Quot.mk
#align quot.lift Quot.lift
#align quot.ind Quot.ind

-- Otherwise would be`OutParam` and `OptParam`!
-- Note: we want `auto_param` to *not* align.
#align out_param               outParam
#align opt_param               optParam

#align heq                     HEq

#align psigma                  PSigma
#align punit                   PUnit
#align pprod                   PProd
#align psum                    PSum
#align ulift                   ULift

#align classical.some          Classical.choose
#align classical.some_spec     Classical.choose_spec

#align Exists                  Exists
#align Exists.some             Exists.choose
#align Exists.some_spec        Exists.choose_spec

#align has_coe Coe
#align has_coe.coe Coe.coe

#align has_coe_t CoeTₓ
#align has_coe_t.coe CoeTₓ.coe

#align has_coe_to_fun CoeFun
#align has_coe_to_fun.coe CoeFun.coe

#align has_coe_to_sort CoeSort
#align has_coe_to_sort.coe CoeSort.coe

#align coe_trans coeTransₓ
#align coe_base coeBaseₓ

#align has_le                  LE
#align has_le.le               LE.le
#align has_lt                  LT
#align has_lt.lt               LT.lt
#align gt                      GT.gt
#align ge                      GE.ge

#align has_beq                 BEq
#align has_sizeof              SizeOf

-- This otherwise causes filenames to clash
#align category_theory.Kleisli CategoryTheory.KleisliCat

-- TODO: backport?
#align int.neg_succ_of_nat     Int.negSucc

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.
#align has_zero      Zero
#align has_one       One
#align has_inv       Inv
#align has_add       Add
#align has_sub       Sub
#align has_mul       Mul
#align has_div       Div
#align has_neg       Neg
#align has_mod       Mod
#align has_pow       Pow
#align has_append    Append
#align has_pure      Pure
#align has_bind      Bind
#align has_seq       Seq
#align has_seq_left  SeqLeft
#align has_seq_right SeqRight
#align has_dvd       Dvd
#align has_subset    Subset
#align has_ssubset   SSubset
#align has_union     Union
#align has_inter     Inter
#align has_sdiff     Sdiff
#align has_mem       Membership
#align has_insert    Insert
#align has_singleton Singleton
#align has_sep       Sep
#align has_bracket   Bracket
#align has_repr      Repr
#align has_to_string ToString

#align has_emptyc EmptyCollection
#align has_emptyc.emptyc EmptyCollection.emptyCollection

-- Implementation detail
#align _sorry_placeholder_     _sorry_placeholder_

#align or.intro_right Or.intro_rightₓ
#align and.elim And.elimₓ
#align xor Xor'
#align iff.elim Iff.elimₓ
#align imp_congr imp_congrₓ
#align imp_congr_ctx imp_congr_ctxₓ
#align imp_congr_right imp_congr_rightₓ

#align preorder.to_has_le Preorder.toLE
#align preorder.to_has_lt Preorder.toLT

#align except.map Except.mapₓ
#align except.map_error Except.mapErrorₓ
#align except.bind Except.bindₓ
#align is_lawful_applicative LawfulApplicative
#align is_lawful_monad LawfulMonad

#align eq_true_intro eq_true
#align eq_false_intro eq_false
#align eq_false eq_false_eq
#align eq_true eq_true_eq

#align array Array'
#align mk_array mkArray'

#align nat.to_digits Nat.toDigits'
#align fin.elim0 Fin.elim0ₓ

#align nat.less_than_or_equal Nat.le
#align nat.le Nat.le
#align nat.lt Nat.lt
#align nat.repeat Nat.repeat'

#align nat.le_of_add_le_add_right Nat.le_of_add_le_add_rightₓ
#align nat.mul_lt_mul Nat.mul_lt_mulₓ
#align nat.mul_lt_mul' Nat.mul_lt_mul'ₓ
#align nat.discriminate Nat.discriminateₓ
#align nat.sub_one_sub_lt Nat.sub_one_sub_ltₓ
#align nat.div_eq_sub_div Nat.div_eq_sub_divₓ
#align nat.div_eq_of_eq_mul_left Nat.div_eq_of_eq_mul_leftₓ
#align nat.div_eq_of_eq_mul_right Nat.div_eq_of_eq_mul_rightₓ
#align nat.div_eq_of_lt_le Nat.div_eq_of_lt_leₓ
#align nat.mul_div_cancel' Nat.mul_div_cancel'ₓ
#align nat.div_mul_cancel Nat.div_mul_cancelₓ
#align nat.mul_div_assoc Nat.mul_div_assocₓ
#align nat.dvd_of_mul_dvd_mul_left Nat.dvd_of_mul_dvd_mul_leftₓ
#align nat.dvd_of_mul_dvd_mul_right Nat.dvd_of_mul_dvd_mul_rightₓ

#align int.nonneg Int.NonNeg
#align int.le Int.le
#align int.lt Int.lt

#align list.erase List.erase'
#align list.bag_inter List.bagInter'
#align list.diff List.diff'
#align list.head List.head'
#align list.filter List.filter'
#align list.partition List.partition'
#align list.drop_while List.dropWhile'
#align list.after List.after'
#align list.span List.span'
#align list.index_of List.indexOf'
#align list.remove_all List.removeAll'
#align list.is_prefix_of List.isPrefixOf'
#align list.is_suffix_of List.isSuffixOf'
#align list.lt List.lt

#align subrelation.accessible Subrelation.accessibleₓ
#align inv_image.accessible InvImage.accessibleₓ

#align or.assoc or_assoc
#align or_iff_left_of_imp or_iff_left_of_impₓ
