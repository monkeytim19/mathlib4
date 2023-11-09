/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Small.Defs

#align_import data.fintype.small from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Shrinking a fintype gives a fintype
-/

universe w v
variable {α : Type v} [Fintype α]

noncomputable instance Shrink.instFintype [Small.{w} α] : Fintype (Shrink.{w} α) :=
  Fintype.ofEquiv _ $ equivShrink _

@[simp] lemma Fintype.card_shrink [Small.{w} α] : Fintype.card (Shrink.{w} α) = Fintype.card α :=
  Fintype.card_congr (equivShrink _).symm
