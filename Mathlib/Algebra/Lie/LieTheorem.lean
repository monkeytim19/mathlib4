/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Weights.Linear

/-!
# Lie's theorem for Solvable Lie algebras.

This file proves Lie's theorem, the statement that Lie modules of solvable Lie algebras over
algebraically closed fields of characteristic 0 have a common eigenvector for the action of all
elements of the Lie algebra. This result is named `LieModule.exists_forall_lie_eq_smul_of_Solvable`.
-/

open LieAlgebra

-- let k be a field of characteristic zero
variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
-- Let L be a Lie algebra over k
variable {L : Type*} [LieRing L] [LieAlgebra k L]
-- and let V be a finite-dimensional k-representation of L
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [LieRingModule L V] [LieModule k L V] [Nontrivial V]

open FiniteDimensional

/- We define the Submodules generated by repeatedly applying a linear map `f: V →ₗ[F] V`
to a vector `v`-/

namespace LinearMap.End

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (v : V) (f : Module.End F V)
/-- The Submodule generated by `v`, `f v`, `f f v`, ... , `f^[n-1] v`.-/
abbrev iteratedRange (n : ℕ) : Submodule F V :=
  Submodule.span F {v' : V | ∃ a < n, v' = (f^a) v}

lemma iteratedRange_zero_eq_bot : iteratedRange v f 0 = ⊥ := by
  rw [Submodule.span_eq_bot]
  intro x ⟨a, ha, _⟩
  contradiction

lemma iteratedRange_mono {a b : ℕ} (h : a ≤ b) : iteratedRange v f a ≤ iteratedRange v f b :=
  Submodule.span_mono (fun _ ⟨c, hc, hw⟩ ↦ ⟨c, lt_of_lt_of_le hc h, hw⟩)

lemma map_iteratedRange_le (n : ℕ) :
    Submodule.map f (iteratedRange v f n) ≤ iteratedRange v f (n + 1) := by
  rw [Submodule.map_span]
  apply Submodule.span_mono
  intro w ⟨z, ⟨m, hm, hz⟩, hw⟩
  use m + 1, Nat.add_lt_add_right hm 1
  rw [← hw, hz, ← LinearMap.mul_apply, ← pow_succ']

/-- The monotone map sending `n : ℕ` to the `iteratedRange` up to `n`.-/
def iteratedRange_map : ℕ →o Submodule F V where
  toFun := iteratedRange v f
  monotone' _ _ := iteratedRange_mono v f

/-- The union of `iteratedRange` for all `n : ℕ`.-/
abbrev iSup_iteratedRange : Submodule F V := ⨆ k : ℕ, iteratedRange_map v f k

lemma iSup_eq_iteratedRange : ∃ N : ℕ, iSup_iteratedRange v f = iteratedRange v f N := by
  apply Submodule.FG.stabilizes_of_iSup_eq (IsNoetherian.noetherian (iSup_iteratedRange v f))
    (iteratedRange_map v f)
  rfl

lemma map_iteratedRange_iSup_le_iSup:
    Submodule.map f (iSup_iteratedRange v f) ≤ iSup_iteratedRange v f := by
  rcases iSup_eq_iteratedRange v f with ⟨N, hN⟩
  nth_rewrite 1 [hN]
  apply le_trans' $ le_iSup (iteratedRange v f) (N + 1)
  exact map_iteratedRange_le v f N

end LinearMap.End

open LinearMap.End

-- the lie action of `L` on `V`
local notation "π" => LieModule.toEnd k L V

section

variable (A : LieIdeal k L) (χ : Module.Dual k A)

abbrev T (w : A) : Module.End k V := (π w)  - χ w • 1

/-- The common eigenvectors of `V` with respect to the action of all elements in
the Lie Ideal `A`.-/
def altWeightSpace : Submodule k V where
  carrier := {v | ∀ a : A, ⁅a.val, v⁆ = (χ a) • v}
  add_mem' := by
    intro _ _ hb hc _
    rw [lie_add, hc, hb, ← smul_add]
  zero_mem' _ := by rw [lie_zero, smul_zero]
  smul_mem' := by
    intro _ _ hx _
    rw [lie_smul, hx, smul_comm]

variable (z : L) (w : A) {v : V}

lemma T_apply_succ (hv : v ∈ altWeightSpace A χ) (n : ℕ) :
    Submodule.map (T A χ w) (iteratedRange v (π z) (n + 1)) ≤ iteratedRange v (π z) n := by
  rw [Submodule.map_span, Submodule.span_le]
  revert w
  induction n
  · intro w x ⟨v', ⟨m, hm, hv'⟩, hx⟩
    rw [Nat.lt_one_iff.mp hm, pow_zero, LinearMap.one_apply] at hv'
    rw [hv', T, LinearMap.sub_apply, LieModule.toEnd_apply_apply, LinearMap.smul_apply,
      LinearMap.one_apply, hv w, sub_self] at hx
    rw [← hx]; exact Submodule.zero_mem _
  · next n hn =>
    intro w x ⟨v', ⟨m, hm, hv'⟩, hx⟩
    rcases (eq_or_lt_of_le (Nat.le_of_lt_succ hm)) with (rfl | hm')
    · rw [← hx, hv', T, LinearMap.sub_apply]
      rw [pow_succ', LinearMap.mul_apply]
      rw [LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply, LinearMap.smul_apply,
        LinearMap.one_apply, SetLike.mem_coe, leibniz_lie, add_sub_assoc]
      apply Submodule.add_mem
      · let wz : A := ⟨⁅w, z⁆, lie_mem_left k L A w.val z w.prop⟩
        have : ⁅⁅w.val, z⁆, (π z ^ n) v⁆ =
            (T A χ wz) ((π z ^ n) v) + χ wz • ((π z ^ n) v) := by
          simp
        rw [this]
        apply Submodule.add_mem
        · exact iteratedRange_mono v _ (Nat.le_succ n)
            (hn wz ⟨(π z ^ n) v, ⟨n, Nat.lt_succ_self n, rfl⟩, rfl⟩)
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩)
      · have : ⁅w.val, (π z ^ n) v⁆ = (T A χ w) ((π z ^ n) v) + χ w • ((π z ^ n) v) := by simp
        rw [this, lie_add, lie_smul, add_sub_assoc, sub_self, add_zero]
        exact map_iteratedRange_le _ _ _ ⟨(T A χ w) ((π z ^ n) v),
          ⟨hn w ⟨(π z ^ n) v, ⟨n, Nat.lt_succ_self n, rfl⟩, rfl⟩, rfl⟩⟩
    · exact iteratedRange_mono v _ (Nat.le_succ n) (hn w ⟨v', ⟨m, hm', hv'⟩, hx⟩)

lemma T_map_iSup_iteratedRange (hv : v ∈ altWeightSpace A χ) (x : V)
    (hx : x ∈ iSup_iteratedRange v (π z)) : (T A χ w) x ∈ iSup_iteratedRange v (π z) := by
  obtain ⟨n, hn⟩ := iSup_eq_iteratedRange v (π z)
  rw [hn] at hx
  suffices h :
    Submodule.map (T A χ w) (iteratedRange v (π z) (n + 1)) ≤ iteratedRange v (π z) n from
    Submodule.mem_iSup_of_mem n (h ⟨x, iteratedRange_mono v _ (Nat.le_succ n) hx, rfl⟩)
  exact T_apply_succ A χ z w hv n

theorem iSup_iteratedRange_A_stable (hv : v ∈ altWeightSpace A χ) (x : V)
    (hx : x ∈ iSup_iteratedRange v (π z)) : (π w) x ∈ (iSup_iteratedRange v (π z)):= by
  have hx' : (π w) x = (T A χ w) x + χ w • x := by simp
  rw [hx']
  exact Submodule.add_mem _ (T_map_iSup_iteratedRange A χ z w hv x hx)
    (Submodule.smul_mem (iSup_iteratedRange v (π z)) _ hx)

lemma T_map_iteratedRange_nilpotent (hv : v ∈ altWeightSpace A χ) (N: ℕ) :
    ∀ x ∈ (iteratedRange_map v (π z)) N, (T A χ w ^ N) x = 0 := by
  induction' N with N ih
  · simp only [iteratedRange_map, Nat.zero_eq, OrderHom.coe_mk, iteratedRange_zero_eq_bot,
      Submodule.mem_bot, pow_zero, LinearMap.one_apply, imp_self, forall_const]
  · intro x hx
    rw [pow_succ, LinearMap.mul_apply]
    apply ih
    apply T_apply_succ A χ z w hv N
    use x, hx

theorem T_res_nilpotent (hv : v ∈ altWeightSpace A χ) :
    IsNilpotent ((T A χ w).restrict (T_map_iSup_iteratedRange A χ z w hv)) := by
  rw [Module.Finite.Module.End.isNilpotent_iff_of_finite]
  rintro ⟨x, hx⟩
  rw [Submodule.mem_iSup_of_chain] at hx
  rcases hx with ⟨N, hN⟩
  use N
  rw [LinearMap.pow_restrict, Subtype.ext_iff, LinearMap.restrict_apply, ZeroMemClass.coe_zero]
  exact T_map_iteratedRange_nilpotent A χ z w hv N x hN

lemma trace_T_res_zero (hv : v ∈ altWeightSpace A χ) :
    LinearMap.trace k (iSup_iteratedRange v (π z))
      ((T A χ w).restrict (T_map_iSup_iteratedRange A χ z w hv)) = 0 := by
  apply IsNilpotent.eq_zero
  exact LinearMap.isNilpotent_trace_of_isNilpotent (T_res_nilpotent A χ z w hv)

lemma πaz_map_iSup_iteratedRange (a : A) (hv : v ∈ altWeightSpace A χ) (x : V)
    (hx : x ∈ iSup_iteratedRange v (π z)) : π ⁅a, z⁆ x ∈ iSup_iteratedRange v (π z):= by
  apply iSup_iteratedRange_A_stable A χ z ⟨⁅a, z⁆, lie_mem_left k L A a z a.prop⟩ hv
  assumption

lemma trace_πaz (a : A) (hv : v ∈ altWeightSpace A χ):
    LinearMap.trace k (iSup_iteratedRange v (π z))
      ((π ⁅a, z⁆).restrict (πaz_map_iSup_iteratedRange A χ z a hv))
    = χ ⟨⁅a, z⁆, lie_mem_left k L A a z a.prop⟩ • (finrank k (iSup_iteratedRange v (π z))) := by
  rw [← LinearMap.trace_id, ← LinearMap.map_smul, ← sub_eq_zero, ← LinearMap.map_sub]
  apply trace_T_res_zero A χ z ⟨⁅a, z⁆, lie_mem_left k L A a z a.prop⟩ hv

theorem trace_πaz_zero (a : A) (hv : v ∈ altWeightSpace A χ):
    LinearMap.trace k (iSup_iteratedRange v (π z))
      ((π ⁅a, z⁆).restrict (πaz_map_iSup_iteratedRange A χ z a hv))
    = 0 := by
  have hzU : ∀ x ∈ iSup_iteratedRange v (π z), (π z) x ∈ iSup_iteratedRange v (π z) :=
    fun _ hx ↦ (map_iteratedRange_iSup_le_iSup v (π z)) (Submodule.mem_map_of_mem hx)
  have hres : (π ⁅a, z⁆).restrict (πaz_map_iSup_iteratedRange A χ z a hv) =
    ⁅(π a).restrict (iSup_iteratedRange_A_stable A χ z a hv), (π z).restrict hzU⁆ := by
    ext ⟨x, hx⟩
    simp
  rw [hres, LieRing.of_associative_ring_bracket, map_sub, LinearMap.trace_mul_comm, sub_self]

lemma chi_az_zero (a : A) (hv : v ∈ altWeightSpace A χ) (hv' : v ≠ 0):
    χ ⟨⁅a, z⁆, lie_mem_left k L A a z a.prop⟩ = 0 := by
  have h := trace_πaz A χ z a hv
  rw [trace_πaz_zero A χ z a hv] at h
  suffices h' : finrank k ↥(iSup_iteratedRange v (π z)) ≠ 0 by
    aesop
  have hvU : v ∈ iSup_iteratedRange v (π z) := by
    apply Submodule.mem_iSup_of_mem 1
    apply Submodule.subset_span
    use 0, zero_lt_one
    rw [pow_zero, LinearMap.one_apply]
  have iSup_iteratedRange_nontrivial : Nontrivial (iSup_iteratedRange v (π z)) :=
    ⟨⟨v,hvU⟩,0, by simp only [ne_eq, Submodule.mk_eq_zero, hv', not_false_eq_true]⟩
  apply Nat.ne_of_lt'
  apply FiniteDimensional.finrank_pos

theorem altWeightSpace_lie_stable (hv : v ∈ altWeightSpace A χ):  ⁅z, v⁆ ∈ altWeightSpace A χ := by
  rcases eq_or_ne v 0 with (rfl | hv')
  · simp only [lie_zero, Submodule.zero_mem]
  · intro a
    have hzwv : ⁅⁅a.val, z⁆, v⁆ = χ ⟨⁅a, z⁆, lie_mem_left k L A a z a.prop⟩ • v :=
      hv ⟨⁅a, z⁆, lie_mem_left k L A a z a.prop⟩
    rw [leibniz_lie, hv a, hzwv, chi_az_zero A χ z a hv hv']
    simp only [zero_smul, lie_smul, zero_add]
end

instance : IsCoatomic (Submodule k V) :=
  isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

lemma exists_coatom (n : ℕ) (hV : finrank k V = n + 1) (X : Submodule k V) (hX : X ≠ ⊤) :
    ∃ W : Submodule k V, X ≤ W ∧ finrank k W = n ∧ IsCoatom W := by
  obtain (h1 | ⟨W, hW1, hW2⟩) := eq_top_or_exists_le_coatom X; contradiction
  use W, hW2
  have hW1' := isSimpleModule_iff_isCoatom.mpr hW1
  apply isSimpleModule_iff_finrank_eq_one.mp at hW1'
  have := W.finrank_quotient_add_finrank
  rw [hV, hW1', add_comm 1 _] at this
  apply add_right_cancel at this
  constructor <;> assumption

lemma derivedSeries_eq_top (n : ℕ) (h : derivedSeries k L 1 = ⊤) : derivedSeries k L n = ⊤ := by
  rw [derivedSeries_def]
  induction' n with n ih
  · simp only [Nat.zero_eq, derivedSeriesOfIdeal_zero]
  · rw [derivedSeriesOfIdeal_succ, ih]
    assumption


variable (k) (L) in
theorem derivedSeries_ne_top_of_solvable [IsSolvable k L] [Nontrivial L] :
    derivedSeries k L 1 ≠ ⊤ := by
  by_contra!
  rcases LieAlgebra.IsSolvable.solvable (R := k) (L := L) with ⟨n, hn⟩
  apply derivedSeries_eq_top n at this
  aesop

theorem exists_lieIdeal_of_derivedSeries_le (A : Submodule k L) (h : derivedSeries k L 1 ≤ A) :
    ∃ A' : LieIdeal k L, A = A' := ⟨{
      carrier := A
      add_mem' := A.add_mem'
      zero_mem' := A.zero_mem'
      smul_mem' := A.smul_mem'
      lie_mem := by
        intro x m hm
        simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
          LieIdeal.coe_to_lieSubalgebra_to_submodule, SetLike.mem_coe] at *
        apply h
        apply LieSubmodule.lie_mem_lie
        trivial
        trivial
    }, rfl⟩

theorem derivedSubalgebra_ne_top [LieAlgebra.IsSolvable k L] [Nontrivial L] :
    (lieIdealSubalgebra k L (LieAlgebra.derivedSeries k L 1)).toSubmodule ≠ ⊤ := by
    have h := derivedSeries_ne_top_of_solvable k L
    simp_all only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, ne_eq,
      LieIdeal.coe_to_lieSubalgebra_to_submodule, LieSubmodule.coeSubmodule_eq_top_iff,
      not_false_eq_true]

section
-- we introduce linear projections from a direct sum to its summands
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}

noncomputable def pr1_aux (hcodis : Codisjoint A B) (v : V) : V :=
    (Submodule.exists_add_eq_of_codisjoint hcodis v).choose

lemma pr1_aux_mem (hcodis : Codisjoint A B) (v : V) : pr1_aux hcodis v ∈ A :=
      (Submodule.exists_add_eq_of_codisjoint hcodis v).choose_spec.1

noncomputable def pr2_aux (hcodis : Codisjoint A B) (v : V) : V :=
    (Submodule.exists_add_eq_of_codisjoint hcodis v).choose_spec.2.choose

lemma pr2_aux_mem (hcodis : Codisjoint A B) (v : V) : pr2_aux hcodis v ∈ B :=
      (Submodule.exists_add_eq_of_codisjoint hcodis v).choose_spec.2.choose_spec.1

lemma pr1_pr2_add' (hcodis : Codisjoint A B) (v : V) : pr1_aux hcodis v + pr2_aux hcodis v = v :=
      (Submodule.exists_add_eq_of_codisjoint hcodis v).choose_spec.2.choose_spec.2

lemma id_sub_pr2' (hcodis : Codisjoint A B) (v : V) :
    v - (pr2_aux hcodis v) = (pr1_aux hcodis v) := by
  nth_rw 1 [← pr1_pr2_add' hcodis v]
  simp only [add_sub_cancel_right]

lemma id_sub_pr1' (hcodis : Codisjoint A B) (v : V) :
    v - (pr1_aux hcodis v) = (pr2_aux hcodis v) := by
  nth_rw 1 [← pr1_pr2_add' hcodis v]
  simp only [add_sub_cancel_left]

noncomputable def pr1 (hcodis : Codisjoint A B) (hdis : Disjoint A B) : V →ₗ[R] A where
  toFun := fun v ↦ ⟨pr1_aux hcodis v, pr1_aux_mem hcodis v⟩
  map_add' := by
    intro x y
    simp only [AddSubmonoid.mk_add_mk, Subtype.mk.injEq]
    have : pr1_aux hcodis (x + y) - (pr1_aux hcodis x) - (pr1_aux hcodis y) ∈ A ⊓ B := by
      constructor
      · apply Submodule.sub_mem
        apply Submodule.sub_mem <;> apply pr1_aux_mem
        apply pr1_aux_mem
      · have : pr1_aux hcodis (x + y) - (pr1_aux hcodis x) - (pr1_aux hcodis y) =
            (pr2_aux hcodis x) + (pr2_aux hcodis y) - (pr2_aux hcodis (x + y)) := by
          rw [← id_sub_pr2', ← id_sub_pr2', ← id_sub_pr2']
          abel
        rw [this]
        apply Submodule.sub_mem
        apply Submodule.add_mem <;> apply pr2_aux_mem
        apply pr2_aux_mem
    rw [disjoint_iff.mp hdis, Submodule.mem_bot] at this
    rw [sub_eq_zero, sub_eq_iff_eq_add, add_comm (pr1_aux hcodis y)] at this
    assumption
  map_smul' := by
    intro c x
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq]
    have : pr1_aux hcodis (c • x) - c • (pr1_aux hcodis x) ∈ A ⊓ B := by
      constructor
      · apply Submodule.sub_mem
        apply pr1_aux_mem
        apply Submodule.smul_mem
        apply pr1_aux_mem
      · have : pr1_aux hcodis (c • x) - c • pr1_aux hcodis x  =
            c • pr2_aux hcodis x - pr2_aux hcodis (c • x) := by
          rw [← id_sub_pr2', ← id_sub_pr2', smul_sub]
          abel
        rw [this]
        apply Submodule.sub_mem
        apply Submodule.smul_mem
        apply pr2_aux_mem
        apply pr2_aux_mem
    rwa [disjoint_iff.mp hdis, Submodule.mem_bot, sub_eq_zero] at this


theorem pr1_val (hcodis : Codisjoint A B) (hdis : Disjoint A B) (v : V) :
    (pr1 hcodis hdis v).val = pr1_aux hcodis v := rfl

noncomputable def pr2 (hcodis : Codisjoint A B) (hdis : Disjoint A B) : V →ₗ[R] B where
  toFun := fun v ↦ ⟨pr2_aux hcodis v, pr2_aux_mem hcodis v⟩
  map_add' := by
    intro x y
    simp only [AddSubmonoid.mk_add_mk, Subtype.mk.injEq]
    rw [← id_sub_pr1' hcodis, ← id_sub_pr1' hcodis, ← id_sub_pr1' hcodis]
    rw [← pr1_val, (pr1 hcodis hdis).map_add]
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
    rw [pr1_val, pr1_val]
    abel
  map_smul' := by
    intro x y
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq]
    rw [← id_sub_pr1', ← id_sub_pr1', ← pr1_val, (pr1 hcodis hdis).map_smul]
    simp only [SetLike.val_smul]
    rw [pr1_val, smul_sub]

end

noncomputable def kequivB (z : L) (hz : z ≠ 0): k ≃ₗ[k] Submodule.span k {z} where
  toFun := fun d ↦ ⟨d • z, Submodule.smul_mem _ d (Submodule.mem_span_singleton_self z)⟩
  map_add' := by
    intro c d
    rw [AddSubmonoid.mk_add_mk, Subtype.mk.injEq]
    exact add_smul c d z
  map_smul' := by
    intro c d
    rw [smul_eq_mul, RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq]
    exact mul_smul c d z
  invFun := fun ⟨z', hz'⟩ ↦ (Submodule.mem_span_singleton.mp hz').choose
  left_inv := by
    intro c
    simp only
    have h : (Submodule.mem_span_singleton.mp
        (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z))).choose • z = c • z :=
      (Submodule.mem_span_singleton.mp
          (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z))).choose_spec
    rw [← sub_eq_zero, ← sub_smul] at *
    rwa [smul_eq_zero_iff_left hz] at h
  right_inv := by
    intro ⟨z', hz'⟩
    simp only [Subtype.mk.injEq]
    apply (Submodule.mem_span_singleton.mp hz').choose_spec

theorem extend_weight (A : LieIdeal k L) (z : L) (hz : z ∉ A)
    (hcodis : A.toSubmodule ⊔ (Submodule.span k {z}) = ⊤)
    (hdis : A.toSubmodule ⊓ (Submodule.span k {z}) = ⊥) (χ' : Module.Dual k A) (v : V)
    (hv : v ≠ 0) (hvA' : ∀ (x : A), ⁅x, v⁆ = χ' x • v) :
  ∃ (χ : Module.Dual k L) (v : V), v ≠ 0 ∧ ∀ (x : L), ⁅x, v⁆ = χ x • v := by
  let πz_res : altWeightSpace (V := V) A χ' →ₗ[k] altWeightSpace (V := V) A χ' :=
      (π z).restrict (p := altWeightSpace A χ') (q := altWeightSpace A χ')
      (fun _ hx ↦ altWeightSpace_lie_stable A χ' z hx)
  have altWeightSpace_nontrivial : Nontrivial (altWeightSpace (V := V) A χ') :=
    ⟨⟨v, hvA'⟩, ⟨0, Subtype.coe_ne_coe.mp hv⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue  πz_res
  obtain ⟨⟨v', hv'⟩, hv''⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hc
  rw [← codisjoint_iff] at hcodis
  rw [← disjoint_iff] at hdis
  have hz' : z ≠ 0 := by
    intro h
    rw [h] at hz
    apply hz
    apply Submodule.zero_mem

  use (χ'.comp (pr1 hcodis hdis)) + c • ((kequivB z hz').symm.comp (pr2 hcodis hdis)), v'
  constructor
  · have := hv''.right
    rw [ne_eq]
    intro h
    apply this
    apply (Submodule.mk_eq_zero _ _).mpr h
  · intro x
    nth_rw 1 [← pr1_pr2_add' hcodis x, add_lie]
    have pr1lie : ⁅pr1_aux hcodis x, v'⁆ = ⁅(pr1 hcodis hdis x).val, v'⁆ := rfl
    have pr2lie : ⁅pr2_aux hcodis x, v'⁆ = ⁅(pr2 hcodis hdis x).val, v'⁆ := rfl
    rw [pr1lie, pr2lie, hv' ((pr1 hcodis hdis) x), LinearMap.add_apply, LinearMap.comp_apply]
    rw [add_smul]
    simp only [LieIdeal.coe_to_lieSubalgebra_to_submodule, LinearMap.smul_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, smul_eq_mul, add_right_inj]
    rcases Submodule.mem_span_singleton.mp (((pr2 hcodis hdis) x).prop) with ⟨d, hd⟩
    rw [← hd, smul_lie]
    have : ⁅z, v'⁆ = πz_res ⟨v', hv'⟩ := rfl
    rw [this, Module.End.HasEigenvector.apply_eq_smul hv'', mul_comm, mul_smul]
    simp only [SetLike.mk_smul_mk]
    have : (pr2 hcodis hdis) x = d • ⟨z, Submodule.mem_span_singleton_self z⟩ := by
      simp only [SetLike.mk_smul_mk, hd]
    rw [this]
    rw [SetLike.mk_smul_mk]
    rw [← LinearEquiv.invFun_eq_symm]
    have : ⟨d • z, _⟩  =  (kequivB z hz').toFun d := rfl
    rw [this, (kequivB z hz').left_inv]


theorem LieIdeal.incl_injective (I : LieIdeal k L) : Function.Injective I.incl := by
  suffices h : Function.Injective ⇑(I.incl.toLinearMap) from h
  rw [I.incl_coe]
  simp only [LieIdeal.coe_to_lieSubalgebra_to_submodule]
  rw [Submodule.coeSubtype]
  exact Subtype.val_injective

theorem LieModule.exists_forall_lie_eq_smul_finrank :
    ∀ (L : Type*) [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] [IsSolvable k L]
      [LieRingModule L V] [LieModule k L V],
      ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  intro L _ _ _ _ _ _
  obtain _inst|_inst := subsingleton_or_nontrivial L
  · rcases (exists_ne (0 : V)) with ⟨v, hv⟩
    use 0, v, hv
    intro x
    simp only [Subsingleton.elim x 0, zero_lie, map_zero, zero_smul]
  obtain H|⟨A, hcoatomA, hAL⟩ := eq_top_or_exists_le_coatom (derivedSeries k L 1 : Submodule k L)
  · exact (derivedSubalgebra_ne_top H).elim
  obtain ⟨z, hz⟩ : ∃ (z : L), z ∉ A := by
    by_contra! h
    apply hcoatomA.1
    rw [eq_top_iff]
    exact fun ⦃x⦄ _ => h x
  set B := Submodule.span k {z} with hBdef
  have htopdecomp : A ⊔ B = ⊤ := by
    apply hcoatomA.2
    rw [left_lt_sup]
    contrapose! hz with h
    exact h <| Submodule.mem_span_singleton_self z
  have hAinterB : A ⊓ B = ⊥ := by
    rw [hBdef, ← le_bot_iff]
    rintro x ⟨(ha : x ∈ A), (hb : x ∈ Submodule.span k _)⟩
    obtain ⟨c, rfl⟩ : ∃ c, c • z = x := by rwa [Submodule.mem_span_singleton] at hb
    apply A.smul_mem c⁻¹ at ha
    rcases eq_or_ne c 0 with (rfl | hc) <;> simp_all
  obtain ⟨A, rfl⟩ : ∃ A' : LieIdeal k L, A = A'.toSubmodule :=
    exists_lieIdeal_of_derivedSeries_le _ hAL
  have hAsolv : LieAlgebra.IsSolvable k A := A.incl_injective.lieAlgebra_isSolvable
  obtain ⟨χ', v, hv, hvA⟩ := LieModule.exists_forall_lie_eq_smul_finrank A
  apply extend_weight A z hz htopdecomp hAinterB χ' v hv hvA
termination_by L _ _ _ => finrank k L
decreasing_by
  simp_wf
  rw [← finrank_top k L]
  apply Submodule.finrank_lt_finrank_of_lt
  rw [← covBy_top_iff] at hcoatomA
  exact hcoatomA.1

-- If `L` is solvable, we can find a non-zero eigenvector
theorem LieModule.exists_forall_lie_eq_smul_of_Solvable [IsSolvable k L] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  let imL := (LieModule.toEnd k L V).range
  have hdim : FiniteDimensional k imL := Submodule.finiteDimensional_of_le (le_top)
  suffices h : ∃ χ : Module.Dual k imL, ∃ v : V, v ≠ 0 ∧ ∀ x : imL, ⁅x, v⁆ = χ x • v by
    rcases h with ⟨χ', v, hv, hχ'⟩
    let toEndo : L →ₗ[k] imL := LinearMap.codRestrict imL.toSubmodule (LieModule.toEnd k L V)
        (fun x ↦ LinearMap.mem_range.mpr ⟨x, rfl⟩ : ∀ x : L, LieModule.toEnd k L V x ∈ imL)
    use χ'.comp toEndo, v, hv
    intro x
    have : ⁅x, v⁆ = ⁅toEndo x, v⁆ := rfl
    rw [LinearMap.comp_apply, this, hχ' (toEndo x)]
  have hsolv : IsSolvable k imL := LieHom.isSolvable_range (LieModule.toEnd k L V)
  apply LieModule.exists_forall_lie_eq_smul_finrank (L := imL)