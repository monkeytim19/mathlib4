/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Data.Finset.MulAntidiagonal

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Multiplicative properties of Hahn series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  We prove some facts about multiplying
Hahn series.

## Main Definitions
  * `HahnModule` is a type alias for `HahnSeries`, which we use for defining scalar multiplication
  of `HahnSeries Γ R` on `HahnModule Γ V` for an `R`-module `V`.
  * If `R` is a (commutative) (semi-)ring, then so is `HahnSeries Γ R`.

## To do

* Incorporate OrderedCancelVAdd from Algebra.Order.AddTorsor.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open BigOperators Pointwise

noncomputable section

variable {Γ Γ' R V : Type*}

namespace HahnSeries

variable [PartialOrder Γ] [Zero Γ]

instance [Zero R] [One R] : One (HahnSeries Γ R) :=
  ⟨single 0 1⟩

@[simp]
theorem one_coeff [Zero R] [One R] {a : Γ} :
    (1 : HahnSeries Γ R).coeff a = if a = 0 then 1 else 0 :=
  single_coeff
#align hahn_series.one_coeff HahnSeries.one_coeff

@[simp]
theorem single_zero_one [Zero R] [One R] : single (0 : Γ) (1 : R) = 1 :=
  rfl
#align hahn_series.single_zero_one HahnSeries.single_zero_one

@[simp]
theorem support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : HahnSeries Γ R) = {0} :=
  support_single_of_ne one_ne_zero
#align hahn_series.support_one HahnSeries.support_one

@[simp]
theorem orderTop_one [MulZeroOneClass R] [Nontrivial R] : orderTop (1 : HahnSeries Γ R) = 0 := by
  rw [← single_zero_one, orderTop_single one_ne_zero, WithTop.coe_eq_zero]

@[simp]
theorem order_one [MulZeroOneClass R] : order (1 : HahnSeries Γ R) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (1 : HahnSeries Γ R) 0, order_zero]
  · exact order_single one_ne_zero
#align hahn_series.order_one HahnSeries.order_one

@[simp]
theorem leadingCoeff_one [MulZeroOneClass R] : (1 : HahnSeries Γ R).leadingCoeff = 1 := by
  simp [leadingCoeff_eq]

end HahnSeries

/-- We introduce a type alias for `HahnSeries` in order to work with scalar multiplication by
series. If we wrote a `SMul (HahnSeries Γ R) (HahnSeries Γ V)` instance, then when
`V = HahnSeries Γ R`, we would have two different actions of `HahnSeries Γ R` on `HahnSeries Γ V`.
See `Mathlib.Algebra.Polynomial.Module` for more discussion on this problem. -/
@[nolint unusedArguments]
def HahnModule (Γ R V : Type*) [PartialOrder Γ] [Zero V] [SMul R V] :=
  HahnSeries Γ V

namespace HahnModule

/-- The casting function to the type synonym. -/
def of {Γ : Type*} (R : Type*) {V : Type*} [PartialOrder Γ] [Zero V] [SMul R V] :
    HahnSeries Γ V ≃ HahnModule Γ R V := Equiv.refl _

/-- Recursion principle to reduce a result about the synonym to the original type. -/
@[elab_as_elim]
def rec [PartialOrder Γ] [Zero V] [SMul R V] {motive : HahnModule Γ R V → Sort*}
    (h : ∀ x : HahnSeries Γ V, motive (of R x)) : ∀ x, motive x :=
  fun x => h <| (of R).symm x

@[ext]
theorem ext [PartialOrder Γ] [Zero V] [SMul R V] (x y : HahnModule Γ R V)
    (h : ((of R).symm x).coeff = ((of R).symm y).coeff) : x = y :=
  (of R).symm.injective <| HahnSeries.coeff_inj.1 h

theorem ext_iff [PartialOrder Γ] [Zero V] [SMul R V]
    (x y : HahnModule Γ R V) : ((of R).symm x).coeff = ((of R).symm y).coeff ↔ x = y := by
  simp_all only [HahnSeries.coeff_inj, EmbeddingLike.apply_eq_iff_eq]

section SMul

variable [AddCommMonoid V] [SMul R V]

variable [PartialOrder Γ]

instance instAddCommMonoid : AddCommMonoid (HahnModule Γ R V) :=
  inferInstanceAs <| AddCommMonoid (HahnSeries Γ V)
instance instBaseSMul {V} [Monoid R] [AddMonoid V] [DistribMulAction R V] :
    SMul R (HahnModule Γ R V) :=
  inferInstanceAs <| SMul R (HahnSeries Γ V)

@[simp] theorem of_zero : of R (0 : HahnSeries Γ V) = 0 := rfl
@[simp] theorem of_add (x y : HahnSeries Γ V) : of R (x + y) = of R x + of R y := rfl

@[simp] theorem of_symm_zero : (of R).symm (0 : HahnModule Γ R V) = 0 := rfl
@[simp] theorem of_symm_add (x y : HahnModule Γ R V) :
  (of R).symm (x + y) = (of R).symm x + (of R).symm y := rfl

instance instBaseMod {V} [Semiring R] [AddCommMonoid V] [Module R V] :
    Module R (HahnModule Γ R V) :=
  inferInstanceAs <| Module R (HahnSeries Γ V)

variable [PartialOrder Γ'] [OrderedCancelVAdd Γ Γ']

instance instSMul [Zero R] : SMul (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul x y := {
    coeff := fun a =>
      ∑ ij in vAddAntidiagonal x.isPWO_support y.isPWO_support a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd
    isPWO_support' :=
        haveI h :
          { a : Γ' |
              (∑ ij : Γ × Γ' in vAddAntidiagonal x.isPWO_support y.isPWO_support a,
                  x.coeff ij.fst • y.coeff ij.snd) ≠
                0 } ⊆
            { a : Γ' | (vAddAntidiagonal x.isPWO_support y.isPWO_support a).Nonempty } := by
          intro a ha
          contrapose! ha
          simp [not_nonempty_iff_eq_empty.1 ha]
        isPWO_support_vAddAntidiagonal.mono h }

theorem smul_coeff [Zero R] (x : HahnSeries Γ R) (y : HahnModule Γ' R V) (a : Γ') :
    ((of R).symm <| x • y).coeff a =
      ∑ ij in vAddAntidiagonal x.isPWO_support y.isPWO_support a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd :=
  rfl

end SMul

section SMulZeroClass

variable [PartialOrder Γ] [PartialOrder Γ'] [OrderedCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V]

instance instRSMulZeroClass [PartialOrder Γ] [SMulZeroClass R V] :
    SMulZeroClass R (HahnModule Γ R V) :=
  inferInstanceAs <| SMulZeroClass R (HahnSeries Γ V)

@[simp] theorem of_smul [PartialOrder Γ] [SMulZeroClass R V] (r : R) (x : HahnSeries Γ V) :
  (of R) (r • x) = r • (of R) x := rfl
@[simp] theorem of_symm_smul [PartialOrder Γ] [SMulZeroClass R V] (r : R) (x : HahnModule Γ R V) :
  (of R).symm (r • x) = r • (of R).symm x := rfl

instance instSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul_zero x := by
    ext
    simp [smul_coeff]

theorem smul_coeff_right [SMulZeroClass R V] {x : HahnSeries Γ R} {y : HahnModule Γ' R V} {a : Γ'}
    {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R).symm y).support ⊆ s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij in vAddAntidiagonal x.isPWO_support hs a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  rw [smul_coeff]
  apply sum_subset_zero_on_sdiff (vAddAntidiagonal_mono_right hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_vAddAntidiagonal, HahnSeries.mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2, smul_zero]

theorem smul_coeff_left [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij in vAddAntidiagonal hs ((of R).symm y).isPWO_support a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  rw [smul_coeff]
  apply sum_subset_zero_on_sdiff (vAddAntidiagonal_mono_left hxs) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_vAddAntidiagonal, HahnSeries.mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1, hb.1.2.2⟩, zero_smul]

end SMulZeroClass

section DistribSMul

variable [PartialOrder Γ] [PartialOrder Γ'] [OrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

theorem smul_add [Zero R] [DistribSMul R V] (x : HahnSeries Γ R) (y z : HahnModule Γ' R V) :
    x • (y + z) = x • y + x • z := by
  ext k
  have hwf := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
  rw [smul_coeff_right hwf, of_symm_add]
  · simp_all only [HahnSeries.add_coeff', Pi.add_apply, smul_add, of_symm_add]
    rw [smul_coeff_right hwf (Set.subset_union_right _ _),
      smul_coeff_right hwf (Set.subset_union_left _ _)]
    simp_all [sum_add_distrib]
  · intro b
    simp_all only [Set.isPWO_union, HahnSeries.isPWO_support, and_self, of_symm_add,
      HahnSeries.add_coeff', Pi.add_apply, ne_eq, Set.mem_union, HahnSeries.mem_support]
    contrapose!
    intro h
    rw [h.1, h.2, add_zero]

instance instDistribSMul [MonoidWithZero R] [DistribSMul R V] : DistribSMul (HahnSeries Γ R)
    (HahnModule Γ' R V) where
  smul_add := smul_add

theorem add_smul [AddCommMonoid R] [SMulWithZero R V] {x y : HahnSeries Γ R}
    {z : HahnModule Γ' R V} (h : ∀(r s : R) (u : V), (r + s) • u = r • u + s • u) :
    (x + y) • z = x • z + y • z := by
  ext a
  have hwf := x.isPWO_support.union y.isPWO_support
  rw [smul_coeff_left hwf, HahnSeries.add_coeff', of_symm_add]
  simp_all only [Pi.add_apply, HahnSeries.add_coeff']
  rw [smul_coeff_left hwf (Set.subset_union_right _ _),
    smul_coeff_left hwf (Set.subset_union_left _ _)]
  · simp only [HahnSeries.add_coeff, h, sum_add_distrib]
  · intro b
    simp_all only [Set.isPWO_union, HahnSeries.isPWO_support, and_self, HahnSeries.mem_support,
      HahnSeries.add_coeff, ne_eq, Set.mem_union]
    contrapose!
    intro h
    rw [h.1, h.2, add_zero]

theorem single_smul_coeff_add [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V}
    {a : Γ'} {b : Γ} :
    ((of R).symm (HahnSeries.single b r • x)).coeff (b +ᵥ a) = r • ((of R).symm x).coeff a := by
  by_cases hr : r = 0
  · simp_all only [map_zero, zero_smul, smul_coeff, HahnSeries.support_zero, HahnSeries.zero_coeff,
    sum_const_zero]
  simp only [smul_coeff, ne_eq, hr, not_false_eq_true, HahnSeries.support_single_of_ne]
  by_cases hx : ((of R).symm x).coeff a = 0
  · simp only [hx, smul_zero]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_vAddAntidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro rfl h2 h1
    rw [CancelVAdd.left_cancel a1 a2 a h1] at h2
    exact h2 hx
  trans ∑ ij : Γ × Γ' in {(b, a)},
    (HahnSeries.single b r).coeff ij.fst • ((of R).symm x).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_vAddAntidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, _, h1⟩
      exact ⟨rfl, CancelVAdd.left_cancel a1 a2 a h1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, by exact hx, rfl⟩
  · simp

theorem single_zero_smul_coeff {Γ} [OrderedAddCommMonoid Γ] [OrderedCancelAddAction Γ Γ']
    [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V} {a : Γ'} :
    ((of R).symm ((HahnSeries.single 0 r : HahnSeries Γ R) • x)).coeff a =
      r • ((of R).symm x).coeff a := by
  nth_rw 1 [← zero_vadd Γ a]
  exact single_smul_coeff_add

@[simp]
theorem single_zero_smul_eq_smul (Γ) [OrderedAddCommMonoid Γ] [OrderedCancelAddAction Γ Γ']
    [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V} :
    (HahnSeries.single (0 : Γ) r) • x = r • x := by
  ext
  exact single_zero_smul_coeff

@[simp]
theorem zero_smul' [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V} :
    (0 : HahnSeries Γ R) • x = 0 := by
  ext
  simp [smul_coeff]

@[simp]
theorem one_smul' {Γ} [OrderedAddCommMonoid Γ] [OrderedCancelAddAction Γ Γ'] [MonoidWithZero R]
    [MulActionWithZero R V] {x : HahnModule Γ' R V} : (1 : HahnSeries Γ R) • x = x := by
  ext g
  exact single_zero_smul_coeff.trans (one_smul R (x.coeff g))

theorem support_smul_subset_vAdd_support [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} : ((of R).symm (x • y)).support ⊆
      x.support +ᵥ ((of R).symm y).support := by
  apply Set.Subset.trans (fun x hx => _) (support_vAddAntidiagonal_subset_vAdd
    (hs := x.isPWO_support) (ht := ((of R).symm y).isPWO_support))
  intro x hx
  contrapose! hx
  simp only [Set.mem_setOf_eq, not_nonempty_iff_eq_empty] at hx
  simp [hx, smul_coeff]

theorem smul_coeffTop_orderTop_vAdd_orderTop {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ']
    [OrderedCancelVAdd Γ Γ'] [Zero R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).coeffTop (x.orderTop +ᵥ ((of R).symm y).orderTop) =
      x.leadingCoeff • ((of R).symm y).leadingCoeff := by
  by_cases hx : x = 0; · simp_all [hx]
  by_cases hy : (of R).symm y = 0; · simp_all [hy]
  simp_rw [HahnSeries.orderTop_of_ne hx, HahnSeries.orderTop_of_ne hy,
    HahnSeries.leadingCoeff_of_ne hx, HahnSeries.leadingCoeff_of_ne hy, ← WithTop.coe_vAdd,
    HahnSeries.coeffTop_eq]
  rw [smul_coeff, Finset.vAddAntidiagonal_min_vAdd_min, Finset.sum_singleton]

theorem orderTop_vAdd_le_orderTop_smul {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ']
    [OrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} :
    x.orderTop +ᵥ ((of R).symm y).orderTop ≤ ((of R).symm (x • y)).orderTop := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  have hhy : ((of R).symm y) ≠ 0 := hy
  rw [HahnSeries.orderTop_of_ne hx, HahnSeries.orderTop_of_ne hhy, ← WithTop.coe_vAdd,
      ← Set.IsWF.min_vAdd]
  by_cases hxy : (of R).symm (x • y) = 0
  · rw [hxy, HahnSeries.orderTop_zero]
    exact OrderTop.le_top (α := WithTop Γ') _
  · rw [HahnSeries.orderTop_of_ne hxy, WithTop.coe_le_coe]
    exact Set.IsWF.min_le_min_of_subset support_smul_subset_vAdd_support

theorem orderTop_smul_of_nonzero {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ']
    [OrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} (h : x.leadingCoeff • ((of R).symm y).leadingCoeff ≠ 0) :
    ((of R).symm (x • y)).orderTop = x.orderTop +ᵥ ((of R).symm y).orderTop := by
  refine le_antisymm (HahnSeries.orderTop_le_of_coeffTop_ne_zero ?_) orderTop_vAdd_le_orderTop_smul
  rw [smul_coeffTop_orderTop_vAdd_orderTop]
  exact h

theorem leadingCoeff_smul_of_nonzero {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ']
    [OrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} (h : x.leadingCoeff • ((of R).symm y).leadingCoeff ≠ 0) :
    ((of R).symm (x • y)).leadingCoeff = x.leadingCoeff • ((of R).symm y).leadingCoeff := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : (of R).symm y = 0; · simp_all
  simp [HahnSeries.leadingCoeff, orderTop_smul_of_nonzero h, smul_coeffTop_orderTop_vAdd_orderTop]

theorem smul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Zero R]
    [SMulWithZero R V] (x : HahnSeries Γ R) (y : HahnModule Γ R V) :
    ((of R).symm (x • y)).coeff (x.order + ((of R).symm y).order) =
    x.leadingCoeff • ((of R).symm y).leadingCoeff := by
  by_cases hx : x = (0 : HahnSeries Γ R); · simp [HahnSeries.zero_coeff, hx]
  by_cases hy : (of R).symm y = 0; · simp [hy, smul_coeff]
  rw [HahnSeries.order_of_ne hx, HahnSeries.order_of_ne hy, smul_coeff,
    HahnSeries.leadingCoeff_of_ne hx, HahnSeries.leadingCoeff_of_ne hy]
  erw [Finset.vAddAntidiagonal_min_vAdd_min, Finset.sum_singleton]

end DistribSMul

end HahnModule

variable [OrderedCancelAddCommMonoid Γ]

namespace HahnSeries

instance [NonUnitalNonAssocSemiring R] : Mul (HahnSeries Γ R) where
  mul x y := (HahnModule.of R).symm (x • HahnModule.of R y)

theorem of_symm_smul_of_eq_mul [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    (HahnModule.of R).symm (x • HahnModule.of R y) = x * y := rfl

theorem mul_coeff [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl
#align hahn_series.mul_coeff HahnSeries.mul_coeff

instance [NonUnitalNonAssocSemiring R] : MulZeroClass (HahnSeries Γ R) where
  zero_mul x := by
    ext
    simp [mul_coeff]
  mul_zero x := by
    ext
    simp [mul_coeff]

theorem mul_coeff_left' [NonUnitalNonAssocSemiring R] {x : HahnSeries Γ R}
    {y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal hs y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.smul_coeff_left hs hxs
#align hahn_series.mul_coeff_left' HahnSeries.mul_coeff_left'

theorem mul_coeff_right' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hys : y.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPWO_support hs a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.smul_coeff_right hs hys
#align hahn_series.mul_coeff_right' HahnSeries.mul_coeff_right'

instance [NonUnitalNonAssocSemiring R] : Distrib (HahnSeries Γ R) :=
  { inferInstanceAs (Mul (HahnSeries Γ R)),
    inferInstanceAs (Add (HahnSeries Γ R)) with
    left_distrib := fun x y z => by
      simp only [← smul_eq_mul]
      exact HahnModule.smul_add x y z
    right_distrib := fun x y z => by
      simp only [← smul_eq_mul]
      refine HahnModule.add_smul ?_
      simp only [smul_eq_mul]
      exact add_mul }

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (Distrib (HahnSeries Γ R)),
    inferInstanceAs (MulZeroClass (HahnSeries Γ R)) with }

theorem single_mul_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a := by
  rw [← smul_eq_mul, add_comm, ← smul_eq_mul]
  exact HahnModule.single_smul_coeff_add
#align hahn_series.single_mul_coeff_add HahnSeries.single_mul_coeff_add

theorem mul_single_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases hr : r = 0
  · simp [hr, mul_coeff]
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne, not_false_iff, smul_eq_mul]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_addAntidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro h2 rfl h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij : Γ × Γ in {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_addAntidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, rfl, h1⟩
      exact ⟨add_right_cancel h1, rfl⟩
    · rintro ⟨rfl, rfl⟩
      simp [hx]
  · simp
#align hahn_series.mul_single_coeff_add HahnSeries.mul_single_coeff_add

@[simp]
theorem mul_single_zero_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by rw [← add_zero a, mul_single_coeff_add, add_zero]
#align hahn_series.mul_single_zero_coeff HahnSeries.mul_single_zero_coeff

theorem single_zero_mul_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    ((single 0 r : HahnSeries Γ R) * x).coeff a = r * x.coeff a := by
  rw [← add_zero a, single_mul_coeff_add, add_zero]
#align hahn_series.single_zero_mul_coeff HahnSeries.single_zero_mul_coeff

instance [NonAssocSemiring R] : NonAssocSemiring (HahnSeries Γ R) :=
  { AddMonoidWithOne.unary,
    inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    one_mul := fun x => by
      ext
      exact single_zero_mul_coeff.trans (one_mul _)
    mul_one := fun x => by
      ext
      exact mul_single_zero_coeff.trans (mul_one _) }

@[simp]
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : HahnSeries Γ R} :
    single 0 r * x = r • x := by
  ext
  exact single_zero_mul_coeff
#align hahn_series.single_zero_mul_eq_smul HahnSeries.single_zero_mul_eq_smul

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    support (x * y) ⊆ support x + support y := by
  rw [← smul_eq_mul]
  exact HahnModule.support_smul_subset_vAdd_support
#align hahn_series.support_mul_subset_add_support HahnSeries.support_mul_subset_add_support

theorem mul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x y : HahnSeries Γ R) :
    (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff := by
  simp only [← smul_eq_mul]
  exact HahnModule.smul_coeff_order_add_order x y
#align hahn_series.mul_coeff_order_add_order HahnSeries.mul_coeff_order_add_order

theorem orderTop_mul_of_nonzero {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} (h : x.leadingCoeff * y.leadingCoeff ≠ 0) :
    (x * y).orderTop = x.orderTop + y.orderTop := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_smul_of_nonzero h

theorem orderTop_add_le_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    x.orderTop + y.orderTop ≤ (x * y).orderTop := by
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_vAdd_le_orderTop_smul

theorem order_add_le_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} (hxy : x * y ≠ 0) :
  x.order + y.order ≤ (x * y).order := by
  have hx : x ≠ 0 := by
    by_contra h
    rw [h, zero_mul y] at hxy
    exact hxy rfl
  have hy : y ≠ 0 := by
    by_contra h
    rw [h, mul_zero x] at hxy
    exact hxy rfl
  refine WithTop.coe_le_coe.mp ?_
  rw [WithTop.coe_add, order_eq_orderTop_of_ne hx, order_eq_orderTop_of_ne hy,
    order_eq_orderTop_of_ne hxy]
  exact orderTop_add_le_mul

theorem order_mul_of_nonzero {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R}
    (h : x.leadingCoeff * y.leadingCoeff ≠ 0) : (x * y).order = x.order + y.order := by
  have hx : x.leadingCoeff ≠ 0 := by aesop
  have hy : y.leadingCoeff ≠ 0 := by aesop
  have hxy : (x * y).coeff (x.order + y.order) ≠ 0 :=
    ne_of_eq_of_ne (mul_coeff_order_add_order x y) h
  refine le_antisymm (order_le_of_coeff_ne_zero
    (Eq.mpr (congrArg (fun _a ↦ _a ≠ 0) (mul_coeff_order_add_order x y)) h)) ?_
  rw [order_of_ne <| leadingCoeff_ne_iff.mpr hx, order_of_ne <| leadingCoeff_ne_iff.mpr hy,
    order_of_ne <| ne_zero_of_coeff_ne_zero hxy, ← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset_add_support

theorem leadingCoeff_mul_of_nonzero {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} (h : x.leadingCoeff * y.leadingCoeff ≠ 0) :
    (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff := by
  simp only [leadingCoeff_eq, order_mul_of_nonzero h, mul_coeff_order_add_order]

theorem order_mul_single_of_nonzero_divisor {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] {g : Γ} {r : R} (hr : ∀ (s : R), r * s = 0 → s = 0)
    {x : HahnSeries Γ R} (hx : x ≠ 0) : (((single g) r) * x).order = g + x.order := by
  have hR : ∃ (y : R), y ≠ 0 := Exists.intro (x.coeff (order x)) (coeff_order_ne_zero hx)
  have hrne : r ≠ 0 := by
    by_contra hr'
    let y := Exists.choose hR
    exact (Exists.choose_spec hR) (hr y (mul_eq_zero_of_left hr' y))
  have hrx : ((single g) r).leadingCoeff * x.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_of_single]
    exact fun hrx' => (leadingCoeff_ne_iff.mp hx) (hr x.leadingCoeff hrx')
  rw [order_mul_of_nonzero hrx, order_single hrne]

private theorem mul_assoc' [NonUnitalSemiring R] (x y z : HahnSeries Γ R) :
    x * y * z = x * (y * z) := by
  ext b
  rw [mul_coeff_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset_add_support,
    mul_coeff_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset_add_support]
  simp only [mul_coeff, add_coeff, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
  aesop (add safe Set.add_mem_add) (add simp [add_assoc, mul_assoc])

instance [NonUnitalSemiring R] : NonUnitalSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    mul_assoc := mul_assoc' }

instance [Semiring R] : Semiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with }

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (HahnSeries Γ R) where
  __ : NonUnitalSemiring (HahnSeries Γ R) := inferInstance
  mul_comm x y := by
    ext
    simp_rw [mul_coeff, mul_comm]
    exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ ↦ swap_mem_addAntidiagonal.symm) <| by simp

instance [CommSemiring R] : CommSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalCommSemiring (HahnSeries Γ R)),
    inferInstanceAs (Semiring (HahnSeries Γ R)) with }

theorem orderTop_prod_le_sum {Γ} [LinearOrderedCancelAddCommMonoid Γ]{α : Type*} [CommSemiring R]
    {x : α → HahnSeries Γ R} {s : Finset α} :
    ∑ i ∈ s, (x i).orderTop ≤ (∏ i ∈ s, x i).orderTop := by
  refine cons_induction ?_ (fun a hfa ha ih => ?_) s
  · rw [sum_empty, prod_empty, ← single_zero_one]
    exact LE.le.trans (Preorder.le_refl 0) orderTop_single_le
  · rw [sum_cons, prod_cons]
    exact (add_le_add_left ih (x a).orderTop).trans orderTop_add_le_mul

theorem order_prod_le_sum {Γ} [LinearOrderedCancelAddCommMonoid Γ]{α : Type*} [CommSemiring R]
    {x : α → HahnSeries Γ R} {s : Finset α} (hx : ∀ t : Finset α, ∏ i ∈ t, x i ≠ 0) :
    ∑ i ∈ s, (x i).order ≤ (∏ i ∈ s, x i).order := by
  refine cons_induction ?_ (fun a t ha ih => ?_) s
  · simp only [sum_empty, prod_empty, order_one, le_refl]
  · rw [sum_cons, prod_cons]
    refine (add_le_add_left ih (x a).order).trans (order_add_le_mul ?_)
    rw [← prod_cons ha]
    exact hx _

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (AddGroup (HahnSeries Γ R)) with }

instance [NonUnitalRing R] : NonUnitalRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocRing (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with }

instance [NonAssocRing R] : NonAssocRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocRing (HahnSeries Γ R)),
    inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)) with }

instance [Ring R] : Ring (HahnSeries Γ R) :=
  { inferInstanceAs (Semiring (HahnSeries Γ R)),
    inferInstanceAs (AddCommGroup (HahnSeries Γ R)) with }

instance [NonUnitalCommRing R] : NonUnitalCommRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalCommSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalRing (HahnSeries Γ R)) with }

instance [CommRing R] : CommRing (HahnSeries Γ R) :=
  { inferInstanceAs (CommSemiring (HahnSeries Γ R)),
    inferInstanceAs (Ring (HahnSeries Γ R)) with }

end HahnSeries

namespace HahnModule

variable [PartialOrder Γ'] [OrderedCancelAddAction Γ Γ'] [AddCommMonoid V]

private theorem mul_smul' [Semiring R] [Module R V] (x y : HahnSeries Γ R)
    (z : HahnModule Γ' R V) : (x * y) • z = x • (y • z) := by
  ext b
  rw [smul_coeff_left (x.isPWO_support.add y.isPWO_support)
    HahnSeries.support_mul_subset_add_support, smul_coeff_right
    (y.isPWO_support.vAdd ((of R).symm z).isPWO_support) support_smul_subset_vAdd_support]
  simp only [HahnSeries.mul_coeff, smul_coeff, HahnSeries.add_coeff, sum_smul, smul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l +ᵥ j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe [Set.vAdd_mem_vAdd, Set.add_mem_add]) (add simp [add_vadd, mul_smul])

instance instRModule [Semiring R] [Module R V] : Module R (HahnModule Γ R V) :=
  inferInstanceAs <| Module R (HahnSeries Γ V)

/-- The isomorphism between HahnSeries and HahnModules, as a linear map. -/
@[simps]
def lof (R : Type*) [Semiring R] [Module R V] : HahnSeries Γ V ≃ₗ[R] HahnModule Γ R V where
  toFun := of R
  map_add' := of_add
  map_smul' := of_smul
  invFun := (of R).symm
  left_inv := congrFun rfl
  right_inv := congrFun rfl

instance instModule [Semiring R] [Module R V] : Module (HahnSeries Γ R)
    (HahnModule Γ' R V) := {
  inferInstanceAs (DistribSMul (HahnSeries Γ R) (HahnModule Γ' R V)) with
  mul_smul := fun x y z => mul_smul' x y z
  one_smul := fun x => @one_smul' Γ' R V _ _ Γ _ _ _ _ x
  add_smul := fun _ _ _ => add_smul Module.add_smul
  zero_smul := fun _ => zero_smul'
  }

instance instGroupModule {V} [Ring R] [AddCommGroup V] [Module R V] : Module (HahnSeries Γ R)
    (HahnModule Γ' R V) where
  add_smul _ _ _ := add_smul Module.add_smul
  zero_smul _ := zero_smul'

instance SMulCommClass [CommRing R] [Module R V] :
    SMulCommClass R (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul_comm r x y := by
    rw [← single_zero_smul_eq_smul Γ, ← mul_smul', mul_comm, mul_smul', single_zero_smul_eq_smul Γ]

theorem smul_comm [CommRing R] [Module R V] (r : R) (x : HahnSeries Γ R) (y : HahnModule Γ' R V) :
    r • x • y = x • r • y := by
  rw [@SMulCommClass.smul_comm]

instance [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module R V] [Module S V]
    [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) where
  smul_assoc r s a := by
    ext
    simp

/-!
instance [CommRing R] [Module R V] : IsScalarTower R (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul_assoc r x a := by
    ext
    simp only [of_symm_smul, HahnSeries.smul_coeff, smul_coeff, smul_sum]
-/

instance instNoZeroSMulDivisors {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Zero R] [SMulWithZero R V]
    [NoZeroSMulDivisors R V] : NoZeroSMulDivisors (HahnSeries Γ R) (HahnModule Γ R V) where
  eq_zero_or_eq_zero_of_smul_eq_zero {x y} hxy := by
    contrapose! hxy
    simp_all only [ne_eq]
    rw [← HahnModule.ext_iff, Function.funext_iff, not_forall]
    refine' ⟨x.order + ((of R).symm y).order, _⟩
    rw [smul_coeff_order_add_order x y, of_symm_zero, HahnSeries.zero_coeff, smul_eq_zero]
    simp only [HahnSeries.leadingCoeff_ne_iff.mp hxy.1, false_or]
    exact HahnSeries.leadingCoeff_ne_iff.mp hxy.2 -- defeq abuse?

end HahnModule

namespace HahnSeries

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] :
    NoZeroDivisors (HahnSeries Γ R) where
    eq_zero_or_eq_zero_of_mul_eq_zero {x y} xy := by
      have : NoZeroSMulDivisors (HahnSeries Γ R) (HahnSeries Γ R) :=
        HahnModule.instNoZeroSMulDivisors
      exact eq_zero_or_eq_zero_of_smul_eq_zero xy

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R] :
    IsDomain (HahnSeries Γ R) :=
  NoZeroDivisors.to_isDomain _

@[simp]
theorem order_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R]
    [NoZeroDivisors R] {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).order = x.order + y.order :=
  order_mul_of_nonzero (mul_ne_zero (leadingCoeff_ne_iff.mp hx) (leadingCoeff_ne_iff.mp hy))
#align hahn_series.order_mul HahnSeries.order_mul

@[simp]
theorem order_pow {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Semiring R] [NoZeroDivisors R]
    (x : HahnSeries Γ R) (n : ℕ) : (x ^ n).order = n • x.order := by
  induction' n with h IH
  · simp
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rw [pow_succ, order_mul (pow_ne_zero _ hx) hx, succ_nsmul, IH]
#align hahn_series.order_pow HahnSeries.order_pow

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} :
    single a r * single b s = single (a + b) (r * s) := by
  ext x
  by_cases h : x = a + b
  · rw [h, mul_single_coeff_add]
    simp
  · rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero]
    simp_rw [mem_addAntidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy, eq_of_mem_support_single hz] at h
    exact (h rfl).elim
#align hahn_series.single_mul_single HahnSeries.single_mul_single

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
def C : R →+* HahnSeries Γ R where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]
#align hahn_series.C HahnSeries.C

--@[simp] Porting note (#10618): simp can prove it
theorem C_zero : C (0 : R) = (0 : HahnSeries Γ R) :=
  C.map_zero
#align hahn_series.C_zero HahnSeries.C_zero

--@[simp] Porting note (#10618): simp can prove it
theorem C_one : C (1 : R) = (1 : HahnSeries Γ R) :=
  C.map_one
#align hahn_series.C_one HahnSeries.C_one

theorem C_injective : Function.Injective (C : R → HahnSeries Γ R) := by
  intro r s rs
  rw [HahnSeries.ext_iff, Function.funext_iff] at rs
  have h := rs 0
  rwa [C_apply, single_coeff_same, C_apply, single_coeff_same] at h
#align hahn_series.C_injective HahnSeries.C_injective

theorem C_ne_zero {r : R} (h : r ≠ 0) : (C r : HahnSeries Γ R) ≠ 0 := by
  contrapose! h
  rw [← C_zero] at h
  exact C_injective h
#align hahn_series.C_ne_zero HahnSeries.C_ne_zero

theorem order_C {r : R} : order (C r : HahnSeries Γ R) = 0 := by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h
#align hahn_series.order_C HahnSeries.order_C

end NonAssocSemiring

section Semiring

variable [Semiring R]

theorem C_mul_eq_smul {r : R} {x : HahnSeries Γ R} : C r * x = r • x :=
  single_zero_mul_eq_smul
#align hahn_series.C_mul_eq_smul HahnSeries.C_mul_eq_smul

@[simp]
theorem single_pow (a : Γ) (n : ℕ) (r : R) : single a r ^ n = single (n • a) (r ^ n) := by
  induction' n with n IH
  · ext; simp only [pow_zero, one_coeff, zero_smul, single_zero_one]
  · simp only [pow_succ, IH, single_mul_single, succ_nsmul]

theorem pow_leadingCoeff {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x : HahnSeries Γ R}
    (hx : ¬IsNilpotent x.leadingCoeff) (n : ℕ) : (x ^ n).leadingCoeff = (x.leadingCoeff) ^ n := by
  induction' n with n ihn
  · simp
  · rw [pow_succ, leadingCoeff_mul_of_nonzero, ihn, pow_succ]
    rw [ihn, ← pow_succ]
    by_contra
    simp_all [IsNilpotent]

end Semiring

section Domain

variable {Γ' : Type*} [OrderedCancelAddCommMonoid Γ']

theorem embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
    (hf : ∀ x y, f (x + y) = f x + f y) (x y : HahnSeries Γ R) :
    embDomain f (x * y) = embDomain f x * embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [mul_coeff, embDomain_coeff]
    trans
      ∑ ij in
        (addAntidiagonal x.isPWO_support y.isPWO_support g).map
          (Function.Embedding.prodMap f.toEmbedding f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).coeff ij.2
    · simp
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_addAntidiagonal, embDomain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [embDomain_notin_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, hi, _, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
    obtain ⟨i, _, rfl⟩ := support_embDomain_subset hi
    obtain ⟨j, _, rfl⟩ := support_embDomain_subset hj
    exact ⟨i + j, hf i j⟩
#align hahn_series.emb_domain_mul HahnSeries.embDomain_mul

theorem embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : HahnSeries Γ R) = (1 : HahnSeries Γ' R) :=
  embDomain_single.trans <| hf.symm ▸ rfl
#align hahn_series.emb_domain_one HahnSeries.embDomain_one

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
def embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ R →+* HahnSeries Γ' R where
  toFun := embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _
#align hahn_series.emb_domain_ring_hom HahnSeries.embDomainRingHom

theorem embDomainRingHom_C [NonAssocSemiring R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
    {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : embDomainRingHom f hfi hf (C r) = C r :=
  embDomain_single.trans (by simp)
#align hahn_series.emb_domain_ring_hom_C HahnSeries.embDomainRingHom_C

end Domain

section Algebra

variable [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

instance : Algebra R (HahnSeries Γ A) where
  toRingHom := C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [smul_coeff, single_zero_mul_eq_smul, RingHom.coe_comp, RingHom.toFun_eq_coe, C_apply,
      Function.comp_apply, algebraMap_smul, mul_single_zero_coeff]
    rw [← Algebra.commutes, Algebra.smul_def]

theorem C_eq_algebraMap : C = algebraMap R (HahnSeries Γ R) :=
  rfl
#align hahn_series.C_eq_algebra_map HahnSeries.C_eq_algebraMap

theorem algebraMap_apply {r : R} : algebraMap R (HahnSeries Γ A) r = C (algebraMap R A r) :=
  rfl
#align hahn_series.algebra_map_apply HahnSeries.algebraMap_apply

instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R (HahnSeries Γ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne, SetLike.ext_iff, not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine ⟨single a 1, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff, Function.funext_iff, not_forall]
      refine ⟨a, ?_⟩
      rw [single_coeff_same, algebraMap_apply, C_apply, single_coeff_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type*} [OrderedCancelAddCommMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps!]
def embDomainAlgHom (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ A →ₐ[R] HahnSeries Γ' A :=
  { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }
#align hahn_series.emb_domain_alg_hom HahnSeries.embDomainAlgHom

end Domain

end Algebra

end HahnSeries
