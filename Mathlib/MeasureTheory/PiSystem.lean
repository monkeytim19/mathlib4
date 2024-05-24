/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Martin Zinkevich, Rémy Degenne
-/
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Defs

#align_import measure_theory.pi_system from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Induction principles for measurable sets, related to π-systems and λ-systems.

## Main statements

* The main theorem of this file is Dynkin's π-λ theorem, which appears
  here as an induction principle `induction_on_inter`. Suppose `s` is a
  collection of subsets of `α` such that the intersection of two members
  of `s` belongs to `s` whenever it is nonempty. Let `m` be the σ-algebra
  generated by `s`. In order to check that a predicate `C` holds on every
  member of `m`, it suffices to check that `C` holds on the members of `s` and
  that `C` is preserved by complementation and *disjoint* countable
  unions.

* The proof of this theorem relies on the notion of `IsPiSystem`, i.e., a collection of sets
  which is closed under binary non-empty intersections. Note that this is a small variation around
  the usual notion in the literature, which often requires that a π-system is non-empty, and closed
  also under disjoint intersections. This variation turns out to be convenient for the
  formalization.

* The proof of Dynkin's π-λ theorem also requires the notion of `DynkinSystem`, i.e., a collection
  of sets which contains the empty set, is closed under complementation and under countable union
  of pairwise disjoint sets. The disjointness condition is the only difference with `σ`-algebras.

* `generatePiSystem g` gives the minimal π-system containing `g`.
  This can be considered a Galois insertion into both measurable spaces and sets.

* `generateFrom_generatePiSystem_eq` proves that if you start from a collection of sets `g`,
  take the generated π-system, and then the generated σ-algebra, you get the same result as
  the σ-algebra generated from `g`. This is useful because there are connections between
  independent sets that are π-systems and the generated independent spaces.

* `mem_generatePiSystem_iUnion_elim` and `mem_generatePiSystem_iUnion_elim'` show that any
  element of the π-system generated from the union of a set of π-systems can be
  represented as the intersection of a finite number of elements from these sets.

* `piiUnionInter` defines a new π-system from a family of π-systems `π : ι → Set (Set α)` and a
  set of indices `S : Set ι`. `piiUnionInter π S` is the set of sets that can be written
  as `⋂ x ∈ t, f x` for some finset `t ∈ S` and sets `f x ∈ π x`.

## Implementation details

* `IsPiSystem` is a predicate, not a type. Thus, we don't explicitly define the galois
  insertion, nor do we define a complete lattice. In theory, we could define a complete
  lattice and galois insertion on the subtype corresponding to `IsPiSystem`.
-/


open MeasurableSpace Set

open scoped Classical
open MeasureTheory

/-- A π-system is a collection of subsets of `α` that is closed under binary intersection of
  non-disjoint sets. Usually it is also required that the collection is nonempty, but we don't do
  that here. -/
def IsPiSystem {α} (C : Set (Set α)) : Prop :=
  ∀ᵉ (s ∈ C) (t ∈ C), (s ∩ t : Set α).Nonempty → s ∩ t ∈ C
#align is_pi_system IsPiSystem

namespace MeasurableSpace

theorem isPiSystem_measurableSet {α : Type*} [MeasurableSpace α] :
    IsPiSystem { s : Set α | MeasurableSet s } := fun _ hs _ ht _ => hs.inter ht
#align measurable_space.is_pi_system_measurable_set MeasurableSpace.isPiSystem_measurableSet

end MeasurableSpace

theorem IsPiSystem.singleton {α} (S : Set α) : IsPiSystem ({S} : Set (Set α)) := by
  intro s h_s t h_t _
  rw [Set.mem_singleton_iff.1 h_s, Set.mem_singleton_iff.1 h_t, Set.inter_self,
    Set.mem_singleton_iff]
#align is_pi_system.singleton IsPiSystem.singleton

theorem IsPiSystem.insert_empty {α} {S : Set (Set α)} (h_pi : IsPiSystem S) :
    IsPiSystem (insert ∅ S) := by
  intro s hs t ht hst
  cases' hs with hs hs
  · simp [hs]
  · cases' ht with ht ht
    · simp [ht]
    · exact Set.mem_insert_of_mem _ (h_pi s hs t ht hst)
#align is_pi_system.insert_empty IsPiSystem.insert_empty

theorem IsPiSystem.insert_univ {α} {S : Set (Set α)} (h_pi : IsPiSystem S) :
    IsPiSystem (insert Set.univ S) := by
  intro s hs t ht hst
  cases' hs with hs hs
  · cases' ht with ht ht <;> simp [hs, ht]
  · cases' ht with ht ht
    · simp [hs, ht]
    · exact Set.mem_insert_of_mem _ (h_pi s hs t ht hst)
#align is_pi_system.insert_univ IsPiSystem.insert_univ

theorem IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiSystem S) (f : α → β) :
    IsPiSystem { s : Set α | ∃ t ∈ S, f ⁻¹' t = s } := by
  rintro _ ⟨s, hs_mem, rfl⟩ _ ⟨t, ht_mem, rfl⟩ hst
  rw [← Set.preimage_inter] at hst ⊢
  exact ⟨s ∩ t, h_pi s hs_mem t ht_mem (nonempty_of_nonempty_preimage hst), rfl⟩
#align is_pi_system.comap IsPiSystem.comap

theorem isPiSystem_iUnion_of_directed_le {α ι} (p : ι → Set (Set α))
    (hp_pi : ∀ n, IsPiSystem (p n)) (hp_directed : Directed (· ≤ ·) p) :
    IsPiSystem (⋃ n, p n) := by
  intro t1 ht1 t2 ht2 h
  rw [Set.mem_iUnion] at ht1 ht2 ⊢
  cases' ht1 with n ht1
  cases' ht2 with m ht2
  obtain ⟨k, hpnk, hpmk⟩ : ∃ k, p n ≤ p k ∧ p m ≤ p k := hp_directed n m
  exact ⟨k, hp_pi k t1 (hpnk ht1) t2 (hpmk ht2) h⟩
#align is_pi_system_Union_of_directed_le isPiSystem_iUnion_of_directed_le

theorem isPiSystem_iUnion_of_monotone {α ι} [SemilatticeSup ι] (p : ι → Set (Set α))
    (hp_pi : ∀ n, IsPiSystem (p n)) (hp_mono : Monotone p) : IsPiSystem (⋃ n, p n) :=
  isPiSystem_iUnion_of_directed_le p hp_pi (Monotone.directed_le hp_mono)
#align is_pi_system_Union_of_monotone isPiSystem_iUnion_of_monotone

section Order

variable {α : Type*} {ι ι' : Sort*} [LinearOrder α]

theorem isPiSystem_image_Iio (s : Set α) : IsPiSystem (Iio '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
  exact ⟨a ⊓ b, inf_ind a b ha hb, Iio_inter_Iio.symm⟩
#align is_pi_system_image_Iio isPiSystem_image_Iio

theorem isPiSystem_Iio : IsPiSystem (range Iio : Set (Set α)) :=
  @image_univ α _ Iio ▸ isPiSystem_image_Iio univ
#align is_pi_system_Iio isPiSystem_Iio

theorem isPiSystem_image_Ioi (s : Set α) : IsPiSystem (Ioi '' s) :=
  @isPiSystem_image_Iio αᵒᵈ _ s
#align is_pi_system_image_Ioi isPiSystem_image_Ioi

theorem isPiSystem_Ioi : IsPiSystem (range Ioi : Set (Set α)) :=
  @image_univ α _ Ioi ▸ isPiSystem_image_Ioi univ
#align is_pi_system_Ioi isPiSystem_Ioi

theorem isPiSystem_image_Iic (s : Set α) : IsPiSystem (Iic '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
  exact ⟨a ⊓ b, inf_ind a b ha hb, Iic_inter_Iic.symm⟩

theorem isPiSystem_Iic : IsPiSystem (range Iic : Set (Set α)) :=
  @image_univ α _ Iic ▸ isPiSystem_image_Iic univ
#align is_pi_system_Iic isPiSystem_Iic

theorem isPiSystem_image_Ici (s : Set α) : IsPiSystem (Ici '' s) :=
  @isPiSystem_image_Iic αᵒᵈ _ s

theorem isPiSystem_Ici : IsPiSystem (range Ici : Set (Set α)) :=
  @image_univ α _ Ici ▸ isPiSystem_image_Ici univ
#align is_pi_system_Ici isPiSystem_Ici

theorem isPiSystem_Ixx_mem {Ixx : α → α → Set α} {p : α → α → Prop}
    (Hne : ∀ {a b}, (Ixx a b).Nonempty → p a b)
    (Hi : ∀ {a₁ b₁ a₂ b₂}, Ixx a₁ b₁ ∩ Ixx a₂ b₂ = Ixx (max a₁ a₂) (min b₁ b₂)) (s t : Set α) :
    IsPiSystem { S | ∃ᵉ (l ∈ s) (u ∈ t), p l u ∧ Ixx l u = S } := by
  rintro _ ⟨l₁, hls₁, u₁, hut₁, _, rfl⟩ _ ⟨l₂, hls₂, u₂, hut₂, _, rfl⟩
  simp only [Hi]
  exact fun H => ⟨l₁ ⊔ l₂, sup_ind l₁ l₂ hls₁ hls₂, u₁ ⊓ u₂, inf_ind u₁ u₂ hut₁ hut₂, Hne H, rfl⟩
#align is_pi_system_Ixx_mem isPiSystem_Ixx_mem

theorem isPiSystem_Ixx {Ixx : α → α → Set α} {p : α → α → Prop}
    (Hne : ∀ {a b}, (Ixx a b).Nonempty → p a b)
    (Hi : ∀ {a₁ b₁ a₂ b₂}, Ixx a₁ b₁ ∩ Ixx a₂ b₂ = Ixx (max a₁ a₂) (min b₁ b₂)) (f : ι → α)
    (g : ι' → α) : @IsPiSystem α { S | ∃ i j, p (f i) (g j) ∧ Ixx (f i) (g j) = S } := by
  simpa only [exists_range_iff] using isPiSystem_Ixx_mem (@Hne) (@Hi) (range f) (range g)
#align is_pi_system_Ixx isPiSystem_Ixx

theorem isPiSystem_Ioo_mem (s t : Set α) :
    IsPiSystem { S | ∃ᵉ (l ∈ s) (u ∈ t), l < u ∧ Ioo l u = S } :=
  isPiSystem_Ixx_mem (Ixx := Ioo) (fun ⟨_, hax, hxb⟩ => hax.trans hxb) Ioo_inter_Ioo s t
#align is_pi_system_Ioo_mem isPiSystem_Ioo_mem

theorem isPiSystem_Ioo (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ l u, f l < g u ∧ Ioo (f l) (g u) = S } :=
  isPiSystem_Ixx (Ixx := Ioo) (fun ⟨_, hax, hxb⟩ => hax.trans hxb) Ioo_inter_Ioo f g
#align is_pi_system_Ioo isPiSystem_Ioo

theorem isPiSystem_Ioc_mem (s t : Set α) :
    IsPiSystem { S | ∃ᵉ (l ∈ s) (u ∈ t), l < u ∧ Ioc l u = S } :=
  isPiSystem_Ixx_mem (Ixx := Ioc) (fun ⟨_, hax, hxb⟩ => hax.trans_le hxb) Ioc_inter_Ioc s t
#align is_pi_system_Ioc_mem isPiSystem_Ioc_mem

theorem isPiSystem_Ioc (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ i j, f i < g j ∧ Ioc (f i) (g j) = S } :=
  isPiSystem_Ixx (Ixx := Ioc) (fun ⟨_, hax, hxb⟩ => hax.trans_le hxb) Ioc_inter_Ioc f g
#align is_pi_system_Ioc isPiSystem_Ioc

theorem isPiSystem_Ico_mem (s t : Set α) :
    IsPiSystem { S | ∃ᵉ (l ∈ s) (u ∈ t), l < u ∧ Ico l u = S } :=
  isPiSystem_Ixx_mem (Ixx := Ico) (fun ⟨_, hax, hxb⟩ => hax.trans_lt hxb) Ico_inter_Ico s t
#align is_pi_system_Ico_mem isPiSystem_Ico_mem

theorem isPiSystem_Ico (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ i j, f i < g j ∧ Ico (f i) (g j) = S } :=
  isPiSystem_Ixx (Ixx := Ico) (fun ⟨_, hax, hxb⟩ => hax.trans_lt hxb) Ico_inter_Ico f g
#align is_pi_system_Ico isPiSystem_Ico

theorem isPiSystem_Icc_mem (s t : Set α) :
    IsPiSystem { S | ∃ᵉ (l ∈ s) (u ∈ t), l ≤ u ∧ Icc l u = S } :=
  isPiSystem_Ixx_mem (Ixx := Icc) nonempty_Icc.1 (by exact Icc_inter_Icc) s t
#align is_pi_system_Icc_mem isPiSystem_Icc_mem

theorem isPiSystem_Icc (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ i j, f i ≤ g j ∧ Icc (f i) (g j) = S } :=
  isPiSystem_Ixx (Ixx := Icc) nonempty_Icc.1 (by exact Icc_inter_Icc) f g
#align is_pi_system_Icc isPiSystem_Icc

end Order

/-- Given a collection `S` of subsets of `α`, then `generatePiSystem S` is the smallest
π-system containing `S`. -/
inductive generatePiSystem {α} (S : Set (Set α)) : Set (Set α)
  | base {s : Set α} (h_s : s ∈ S) : generatePiSystem S s
  | inter {s t : Set α} (h_s : generatePiSystem S s) (h_t : generatePiSystem S t)
    (h_nonempty : (s ∩ t).Nonempty) : generatePiSystem S (s ∩ t)
#align generate_pi_system generatePiSystem

theorem isPiSystem_generatePiSystem {α} (S : Set (Set α)) : IsPiSystem (generatePiSystem S) :=
  fun _ h_s _ h_t h_nonempty => generatePiSystem.inter h_s h_t h_nonempty
#align is_pi_system_generate_pi_system isPiSystem_generatePiSystem

theorem subset_generatePiSystem_self {α} (S : Set (Set α)) : S ⊆ generatePiSystem S := fun _ =>
  generatePiSystem.base
#align subset_generate_pi_system_self subset_generatePiSystem_self

theorem generatePiSystem_subset_self {α} {S : Set (Set α)} (h_S : IsPiSystem S) :
    generatePiSystem S ⊆ S := fun x h => by
  induction' h with _ h_s s u _ _ h_nonempty h_s h_u
  · exact h_s
  · exact h_S _ h_s _ h_u h_nonempty
#align generate_pi_system_subset_self generatePiSystem_subset_self

theorem generatePiSystem_eq {α} {S : Set (Set α)} (h_pi : IsPiSystem S) : generatePiSystem S = S :=
  Set.Subset.antisymm (generatePiSystem_subset_self h_pi) (subset_generatePiSystem_self S)
#align generate_pi_system_eq generatePiSystem_eq

theorem generatePiSystem_mono {α} {S T : Set (Set α)} (hST : S ⊆ T) :
    generatePiSystem S ⊆ generatePiSystem T := fun t ht => by
  induction' ht with s h_s s u _ _ h_nonempty h_s h_u
  · exact generatePiSystem.base (Set.mem_of_subset_of_mem hST h_s)
  · exact isPiSystem_generatePiSystem T _ h_s _ h_u h_nonempty
#align generate_pi_system_mono generatePiSystem_mono

theorem generatePiSystem_measurableSet {α} [M : MeasurableSpace α] {S : Set (Set α)}
    (h_meas_S : ∀ s ∈ S, MeasurableSet s) (t : Set α) (h_in_pi : t ∈ generatePiSystem S) :
    MeasurableSet t := by
  induction' h_in_pi with s h_s s u _ _ _ h_s h_u
  · apply h_meas_S _ h_s
  · apply MeasurableSet.inter h_s h_u
#align generate_pi_system_measurable_set generatePiSystem_measurableSet

theorem generateFrom_measurableSet_of_generatePiSystem {α} {g : Set (Set α)} (t : Set α)
    (ht : t ∈ generatePiSystem g) : MeasurableSet[generateFrom g] t :=
  @generatePiSystem_measurableSet α (generateFrom g) g
    (fun _ h_s_in_g => measurableSet_generateFrom h_s_in_g) t ht
#align generate_from_measurable_set_of_generate_pi_system generateFrom_measurableSet_of_generatePiSystem

theorem generateFrom_generatePiSystem_eq {α} {g : Set (Set α)} :
    generateFrom (generatePiSystem g) = generateFrom g := by
  apply le_antisymm <;> apply generateFrom_le
  · exact fun t h_t => generateFrom_measurableSet_of_generatePiSystem t h_t
  · exact fun t h_t => measurableSet_generateFrom (generatePiSystem.base h_t)
#align generate_from_generate_pi_system_eq generateFrom_generatePiSystem_eq

/-- Every element of the π-system generated by the union of a family of π-systems
is a finite intersection of elements from the π-systems.
For an indexed union version, see `mem_generatePiSystem_iUnion_elim'`. -/
theorem mem_generatePiSystem_iUnion_elim {α β} {g : β → Set (Set α)} (h_pi : ∀ b, IsPiSystem (g b))
    (t : Set α) (h_t : t ∈ generatePiSystem (⋃ b, g b)) :
    ∃ (T : Finset β) (f : β → Set α), (t = ⋂ b ∈ T, f b) ∧ ∀ b ∈ T, f b ∈ g b := by
  induction' h_t with s h_s s t' h_gen_s h_gen_t' h_nonempty h_s h_t'
  · rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩
    refine ⟨{b}, fun _ => s, _⟩
    simpa using h_s_in_t'
  · rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩⟩⟩
    use T_s ∪ T_t', fun b : β =>
      if b ∈ T_s then if b ∈ T_t' then f_s b ∩ f_t' b else f_s b
      else if b ∈ T_t' then f_t' b else (∅ : Set α)
    constructor
    · ext a
      simp_rw [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union, or_imp]
      rw [← forall_and]
      constructor <;> intro h1 b <;> by_cases hbs : b ∈ T_s <;> by_cases hbt : b ∈ T_t' <;>
          specialize h1 b <;>
        simp only [hbs, hbt, if_true, if_false, true_imp_iff, and_self_iff, false_imp_iff,
          and_true_iff, true_and_iff] at h1 ⊢
      all_goals exact h1
    intro b h_b
    split_ifs with hbs hbt hbt
    · refine h_pi b (f_s b) (h_s b hbs) (f_t' b) (h_t' b hbt) (Set.Nonempty.mono _ h_nonempty)
      exact Set.inter_subset_inter (Set.biInter_subset_of_mem hbs) (Set.biInter_subset_of_mem hbt)
    · exact h_s b hbs
    · exact h_t' b hbt
    · rw [Finset.mem_union] at h_b
      apply False.elim (h_b.elim hbs hbt)
#align mem_generate_pi_system_Union_elim mem_generatePiSystem_iUnion_elim

/-- Every element of the π-system generated by an indexed union of a family of π-systems
is a finite intersection of elements from the π-systems.
For a total union version, see `mem_generatePiSystem_iUnion_elim`. -/
theorem mem_generatePiSystem_iUnion_elim' {α β} {g : β → Set (Set α)} {s : Set β}
    (h_pi : ∀ b ∈ s, IsPiSystem (g b)) (t : Set α) (h_t : t ∈ generatePiSystem (⋃ b ∈ s, g b)) :
    ∃ (T : Finset β) (f : β → Set α), ↑T ⊆ s ∧ (t = ⋂ b ∈ T, f b) ∧ ∀ b ∈ T, f b ∈ g b := by
  have : t ∈ generatePiSystem (⋃ b : Subtype s, (g ∘ Subtype.val) b) := by
    suffices h1 : ⋃ b : Subtype s, (g ∘ Subtype.val) b = ⋃ b ∈ s, g b by rwa [h1]
    ext x
    simp only [exists_prop, Set.mem_iUnion, Function.comp_apply, Subtype.exists, Subtype.coe_mk]
    rfl
  rcases @mem_generatePiSystem_iUnion_elim α (Subtype s) (g ∘ Subtype.val)
      (fun b => h_pi b.val b.property) t this with
    ⟨T, ⟨f, ⟨rfl, h_t'⟩⟩⟩
  refine
    ⟨T.image (fun x : s => (x : β)),
      Function.extend (fun x : s => (x : β)) f fun _ : β => (∅ : Set α), by simp, _, _⟩
  · ext a
    constructor <;>
      · simp (config := { proj := false }) only
          [Set.mem_iInter, Subtype.forall, Finset.set_biInter_finset_image]
        intro h1 b h_b h_b_in_T
        have h2 := h1 b h_b h_b_in_T
        revert h2
        rw [Subtype.val_injective.extend_apply]
        apply id
  · intros b h_b
    simp_rw [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      at h_b
    cases' h_b with h_b_w h_b_h
    have h_b_alt : b = (Subtype.mk b h_b_w).val := rfl
    rw [h_b_alt, Subtype.val_injective.extend_apply]
    apply h_t'
    apply h_b_h
#align mem_generate_pi_system_Union_elim' mem_generatePiSystem_iUnion_elim'

section UnionInter

variable {α ι : Type*}

/-! ### π-system generated by finite intersections of sets of a π-system family -/


/-- From a set of indices `S : Set ι` and a family of sets of sets `π : ι → Set (Set α)`,
define the set of sets that can be written as `⋂ x ∈ t, f x` for some finset `t ⊆ S` and sets
`f x ∈ π x`. If `π` is a family of π-systems, then it is a π-system. -/
def piiUnionInter (π : ι → Set (Set α)) (S : Set ι) : Set (Set α) :=
  { s : Set α |
    ∃ (t : Finset ι) (_ : ↑t ⊆ S) (f : ι → Set α) (_ : ∀ x, x ∈ t → f x ∈ π x), s = ⋂ x ∈ t, f x }
#align pi_Union_Inter piiUnionInter

theorem piiUnionInter_singleton (π : ι → Set (Set α)) (i : ι) :
    piiUnionInter π {i} = π i ∪ {univ} := by
  ext1 s
  simp only [piiUnionInter, exists_prop, mem_union]
  refine ⟨_, fun h => _⟩
  · rintro ⟨t, hti, f, hfπ, rfl⟩
    simp only [subset_singleton_iff, Finset.mem_coe] at hti
    by_cases hi : i ∈ t
    · have ht_eq_i : t = {i} := by
        ext1 x
        rw [Finset.mem_singleton]
        exact ⟨fun h => hti x h, fun h => h.symm ▸ hi⟩
      simp only [ht_eq_i, Finset.mem_singleton, iInter_iInter_eq_left]
      exact Or.inl (hfπ i hi)
    · have ht_empty : t = ∅ := by
        ext1 x
        simp only [Finset.not_mem_empty, iff_false_iff]
        exact fun hx => hi (hti x hx ▸ hx)
      -- Porting note: `Finset.not_mem_empty` required
      simp [ht_empty, Finset.not_mem_empty, iInter_false, iInter_univ, Set.mem_singleton univ,
        or_true_iff]
  · cases' h with hs hs
    · refine ⟨{i}, _, fun _ => s, ⟨fun x hx => _, _⟩⟩
      · rw [Finset.coe_singleton]
      · rw [Finset.mem_singleton] at hx
        rwa [hx]
      · simp only [Finset.mem_singleton, iInter_iInter_eq_left]
    · refine ⟨∅, _⟩
      simpa only [Finset.coe_empty, subset_singleton_iff, mem_empty_iff_false, IsEmpty.forall_iff,
        imp_true_iff, Finset.not_mem_empty, iInter_false, iInter_univ, true_and_iff,
        exists_const] using hs
#align pi_Union_Inter_singleton piiUnionInter_singleton

theorem piiUnionInter_singleton_left (s : ι → Set α) (S : Set ι) :
    piiUnionInter (fun i => ({s i} : Set (Set α))) S =
      { s' : Set α | ∃ (t : Finset ι) (_ : ↑t ⊆ S), s' = ⋂ i ∈ t, s i } := by
  ext1 s'
  simp_rw [piiUnionInter, Set.mem_singleton_iff, exists_prop, Set.mem_setOf_eq]
  refine ⟨fun h => _, fun ⟨t, htS, h_eq⟩ => ⟨t, htS, s, fun _ _ => rfl, h_eq⟩⟩
  obtain ⟨t, htS, f, hft_eq, rfl⟩ := h
  refine ⟨t, htS, _⟩
  congr! 3
  apply hft_eq
  assumption
#align pi_Union_Inter_singleton_left piiUnionInter_singleton_left

theorem generateFrom_piiUnionInter_singleton_left (s : ι → Set α) (S : Set ι) :
    generateFrom (piiUnionInter (fun k => {s k}) S) = generateFrom { t | ∃ k ∈ S, s k = t } := by
  refine le_antisymm (generateFrom_le _) (generateFrom_mono _)
  · rintro _ ⟨I, hI, f, hf, rfl⟩
    refine Finset.measurableSet_biInter _ fun m hm => measurableSet_generateFrom _
    exact ⟨m, hI hm, (hf m hm).symm⟩
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨{k}, fun m hm => _, s, fun i _ => _, _⟩
    · rw [Finset.mem_coe, Finset.mem_singleton] at hm
      rwa [hm]
    · exact Set.mem_singleton _
    · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
#align generate_from_pi_Union_Inter_singleton_left generateFrom_piiUnionInter_singleton_left

/-- If `π` is a family of π-systems, then `piiUnionInter π S` is a π-system. -/
theorem isPiSystem_piiUnionInter (π : ι → Set (Set α)) (hpi : ∀ x, IsPiSystem (π x)) (S : Set ι) :
    IsPiSystem (piiUnionInter π S) := by
  rintro t1 ⟨p1, hp1S, f1, hf1m, ht1_eq⟩ t2 ⟨p2, hp2S, f2, hf2m, ht2_eq⟩ h_nonempty
  simp_rw [piiUnionInter, Set.mem_setOf_eq]
  let g n := ite (n ∈ p1) (f1 n) Set.univ ∩ ite (n ∈ p2) (f2 n) Set.univ
  have hp_union_ss : ↑(p1 ∪ p2) ⊆ S := by
    simp only [hp1S, hp2S, Finset.coe_union, union_subset_iff, and_self_iff]
  use p1 ∪ p2, hp_union_ss, g
  have h_inter_eq : t1 ∩ t2 = ⋂ i ∈ p1 ∪ p2, g i := by
    rw [ht1_eq, ht2_eq]
    simp_rw [← Set.inf_eq_inter]
    ext1 x
    simp only [g, inf_eq_inter, mem_inter_iff, mem_iInter, Finset.mem_union]
    refine ⟨fun h i _ => _, fun h => ⟨fun i hi1 => _, fun i hi2 => _⟩⟩
    · split_ifs with h_1 h_2 h_2
      exacts [⟨h.1 i h_1, h.2 i h_2⟩, ⟨h.1 i h_1, Set.mem_univ _⟩, ⟨Set.mem_univ _, h.2 i h_2⟩,
        ⟨Set.mem_univ _, Set.mem_univ _⟩]
    · specialize h i (Or.inl hi1)
      rw [if_pos hi1] at h
      exact h.1
    · specialize h i (Or.inr hi2)
      rw [if_pos hi2] at h
      exact h.2
  refine ⟨fun n hn => _, h_inter_eq⟩
  simp only [g]
  split_ifs with hn1 hn2 h
  · refine hpi n (f1 n) (hf1m n hn1) (f2 n) (hf2m n hn2) (Set.nonempty_iff_ne_empty.2 fun h => _)
    rw [h_inter_eq] at h_nonempty
    suffices h_empty : ⋂ i ∈ p1 ∪ p2, g i = ∅ from
      (Set.not_nonempty_iff_eq_empty.mpr h_empty) h_nonempty
    refine le_antisymm (Set.iInter_subset_of_subset n _) (Set.empty_subset _)
    refine Set.iInter_subset_of_subset hn _
    simp_rw [g, if_pos hn1, if_pos hn2]
    exact h.subset
  · simp [hf1m n hn1]
  · simp [hf2m n h]
  · exact absurd hn (by simp [hn1, h])
#align is_pi_system_pi_Union_Inter isPiSystem_piiUnionInter

theorem piiUnionInter_mono_left {π π' : ι → Set (Set α)} (h_le : ∀ i, π i ⊆ π' i) (S : Set ι) :
    piiUnionInter π S ⊆ piiUnionInter π' S := fun _ ⟨t, ht_mem, ft, hft_mem_pi, h_eq⟩ =>
  ⟨t, ht_mem, ft, fun x hxt => h_le x (hft_mem_pi x hxt), h_eq⟩
#align pi_Union_Inter_mono_left piiUnionInter_mono_left

theorem piiUnionInter_mono_right {π : ι → Set (Set α)} {S T : Set ι} (hST : S ⊆ T) :
    piiUnionInter π S ⊆ piiUnionInter π T := fun _ ⟨t, ht_mem, ft, hft_mem_pi, h_eq⟩ =>
  ⟨t, ht_mem.trans hST, ft, hft_mem_pi, h_eq⟩
#align pi_Union_Inter_mono_right piiUnionInter_mono_right

theorem generateFrom_piiUnionInter_le {m : MeasurableSpace α} (π : ι → Set (Set α))
    (h : ∀ n, generateFrom (π n) ≤ m) (S : Set ι) : generateFrom (piiUnionInter π S) ≤ m := by
  refine generateFrom_le _
  rintro t ⟨ht_p, _, ft, hft_mem_pi, rfl⟩
  refine Finset.measurableSet_biInter _ fun x hx_mem => (h x) _ _
  exact measurableSet_generateFrom (hft_mem_pi x hx_mem)
#align generate_from_pi_Union_Inter_le generateFrom_piiUnionInter_le

theorem subset_piiUnionInter {π : ι → Set (Set α)} {S : Set ι} {i : ι} (his : i ∈ S) :
    π i ⊆ piiUnionInter π S := by
  have h_ss : {i} ⊆ S := by
    intro j hj
    rw [mem_singleton_iff] at hj
    rwa [hj]
  refine Subset.trans _ (piiUnionInter_mono_right h_ss)
  rw [piiUnionInter_singleton]
  exact subset_union_left _ _
#align subset_pi_Union_Inter subset_piiUnionInter

theorem mem_piiUnionInter_of_measurableSet (m : ι → MeasurableSpace α) {S : Set ι} {i : ι}
    (hiS : i ∈ S) (s : Set α) (hs : MeasurableSet[m i] s) :
    s ∈ piiUnionInter (fun n => { s | MeasurableSet[m n] s }) S :=
  subset_piiUnionInter hiS hs
#align mem_pi_Union_Inter_of_measurable_set mem_piiUnionInter_of_measurableSet

theorem le_generateFrom_piiUnionInter {π : ι → Set (Set α)} (S : Set ι) {x : ι} (hxS : x ∈ S) :
    generateFrom (π x) ≤ generateFrom (piiUnionInter π S) :=
  generateFrom_mono (subset_piiUnionInter hxS)
#align le_generate_from_pi_Union_Inter le_generateFrom_piiUnionInter

theorem measurableSet_iSup_of_mem_piiUnionInter (m : ι → MeasurableSpace α) (S : Set ι) (t : Set α)
    (ht : t ∈ piiUnionInter (fun n => { s | MeasurableSet[m n] s }) S) :
    MeasurableSet[⨆ i ∈ S, m i] t := by
  rcases ht with ⟨pt, hpt, ft, ht_m, rfl⟩
  refine pt.measurableSet_biInter fun i hi => _
  suffices h_le : m i ≤ ⨆ i ∈ S, m i from h_le (ft i) (ht_m i hi)
  have hi' : i ∈ S := hpt hi
  exact le_iSup₂ (f := fun i (_ : i ∈ S) => m i) i hi'
#align measurable_set_supr_of_mem_pi_Union_Inter measurableSet_iSup_of_mem_piiUnionInter

theorem generateFrom_piiUnionInter_measurableSet (m : ι → MeasurableSpace α) (S : Set ι) :
    generateFrom (piiUnionInter (fun n => { s | MeasurableSet[m n] s }) S) = ⨆ i ∈ S, m i := by
  refine le_antisymm _ _
  · rw [← @generateFrom_measurableSet α (⨆ i ∈ S, m i)]
    exact generateFrom_mono (measurableSet_iSup_of_mem_piiUnionInter m S)
  · refine iSup₂_le fun i hi => _
    rw [← @generateFrom_measurableSet α (m i)]
    exact generateFrom_mono (mem_piiUnionInter_of_measurableSet m hi)
#align generate_from_pi_Union_Inter_measurable_set generateFrom_piiUnionInter_measurableSet

end UnionInter

namespace MeasurableSpace

variable {α : Type*}

/-! ## Dynkin systems and Π-λ theorem -/


/-- A Dynkin system is a collection of subsets of a type `α` that contains the empty set,
  is closed under complementation and under countable union of pairwise disjoint sets.
  The disjointness condition is the only difference with `σ`-algebras.

  The main purpose of Dynkin systems is to provide a powerful induction rule for σ-algebras
  generated by a collection of sets which is stable under intersection.

  A Dynkin system is also known as a "λ-system" or a "d-system".
-/
structure DynkinSystem (α : Type*) where
  /-- Predicate saying that a given set is contained in the Dynkin system. -/
  Has : Set α → Prop
  /-- A Dynkin system contains the empty set. -/
  has_empty : Has ∅
  /-- A Dynkin system is closed under complementation. -/
  has_compl : ∀ {a}, Has a → Has aᶜ
  /-- A Dynkin system is closed under countable union of pairwise disjoint sets. Use a more general
  `MeasurableSpace.DynkinSystem.has_iUnion` instead. -/
  has_iUnion_nat : ∀ {f : ℕ → Set α}, Pairwise (Disjoint on f) → (∀ i, Has (f i)) → Has (⋃ i, f i)
#align measurable_space.dynkin_system MeasurableSpace.DynkinSystem

namespace DynkinSystem

@[ext]
theorem ext : ∀ {d₁ d₂ : DynkinSystem α}, (∀ s : Set α, d₁.Has s ↔ d₂.Has s) → d₁ = d₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h => by
    have : s₁ = s₂ := funext fun x => propext <| h x
    subst this
    rfl
#align measurable_space.dynkin_system.ext MeasurableSpace.DynkinSystem.ext

variable (d : DynkinSystem α)

theorem has_compl_iff {a} : d.Has aᶜ ↔ d.Has a :=
  ⟨fun h => by simpa using d.has_compl h, fun h => d.has_compl h⟩
#align measurable_space.dynkin_system.has_compl_iff MeasurableSpace.DynkinSystem.has_compl_iff

theorem has_univ : d.Has univ := by simpa using d.has_compl d.has_empty
#align measurable_space.dynkin_system.has_univ MeasurableSpace.DynkinSystem.has_univ

theorem has_iUnion {β} [Countable β] {f : β → Set α} (hd : Pairwise (Disjoint on f))
    (h : ∀ i, d.Has (f i)) : d.Has (⋃ i, f i) := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  exact
    d.has_iUnion_nat (Encodable.iUnion_decode₂_disjoint_on hd) fun n =>
      Encodable.iUnion_decode₂_cases d.has_empty h
#align measurable_space.dynkin_system.has_Union MeasurableSpace.DynkinSystem.has_iUnion

theorem has_union {s₁ s₂ : Set α} (h₁ : d.Has s₁) (h₂ : d.Has s₂) (h : Disjoint s₁ s₂) :
    d.Has (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]
  exact d.has_iUnion (pairwise_disjoint_on_bool.2 h) (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align measurable_space.dynkin_system.has_union MeasurableSpace.DynkinSystem.has_union

theorem has_diff {s₁ s₂ : Set α} (h₁ : d.Has s₁) (h₂ : d.Has s₂) (h : s₂ ⊆ s₁) :
    d.Has (s₁ \ s₂) := by
  apply d.has_compl_iff.1
  simp only [diff_eq, compl_inter, compl_compl]
  exact d.has_union (d.has_compl h₁) h₂ (disjoint_compl_left.mono_right h)
#align measurable_space.dynkin_system.has_diff MeasurableSpace.DynkinSystem.has_diff

instance instLEDynkinSystem : LE (DynkinSystem α) where le m₁ m₂ := m₁.Has ≤ m₂.Has

theorem le_def {α} {a b : DynkinSystem α} : a ≤ b ↔ a.Has ≤ b.Has :=
  Iff.rfl
#align measurable_space.dynkin_system.le_def MeasurableSpace.DynkinSystem.le_def

instance : PartialOrder (DynkinSystem α) :=
  { DynkinSystem.instLEDynkinSystem with
    le_refl := fun a b => le_rfl
    le_trans := fun a b c hab hbc => le_def.mpr (le_trans hab hbc)
    le_antisymm := fun a b h₁ h₂ => ext fun s => ⟨h₁ s, h₂ s⟩ }

/-- Every measurable space (σ-algebra) forms a Dynkin system -/
def ofMeasurableSpace (m : MeasurableSpace α) : DynkinSystem α where
  Has := m.MeasurableSet'
  has_empty := m.measurableSet_empty
  has_compl {a} := m.measurableSet_compl a
  has_iUnion_nat {f} _ hf := m.measurableSet_iUnion f hf
#align measurable_space.dynkin_system.of_measurable_space MeasurableSpace.DynkinSystem.ofMeasurableSpace

theorem ofMeasurableSpace_le_ofMeasurableSpace_iff {m₁ m₂ : MeasurableSpace α} :
    ofMeasurableSpace m₁ ≤ ofMeasurableSpace m₂ ↔ m₁ ≤ m₂ :=
  Iff.rfl
#align measurable_space.dynkin_system.of_measurable_space_le_of_measurable_space_iff MeasurableSpace.DynkinSystem.ofMeasurableSpace_le_ofMeasurableSpace_iff

/-- The least Dynkin system containing a collection of basic sets.
  This inductive type gives the underlying collection of sets. -/
inductive GenerateHas (s : Set (Set α)) : Set α → Prop
  | basic : ∀ t ∈ s, GenerateHas s t
  | empty : GenerateHas s ∅
  | compl : ∀ {a}, GenerateHas s a → GenerateHas s aᶜ
  | iUnion : ∀ {f : ℕ → Set α},
    Pairwise (Disjoint on f) → (∀ i, GenerateHas s (f i)) → GenerateHas s (⋃ i, f i)
#align measurable_space.dynkin_system.generate_has MeasurableSpace.DynkinSystem.GenerateHas

theorem generateHas_compl {C : Set (Set α)} {s : Set α} : GenerateHas C sᶜ ↔ GenerateHas C s := by
  refine ⟨_, GenerateHas.compl⟩
  intro h
  convert GenerateHas.compl h
  simp
#align measurable_space.dynkin_system.generate_has_compl MeasurableSpace.DynkinSystem.generateHas_compl

/-- The least Dynkin system containing a collection of basic sets. -/
def generate (s : Set (Set α)) : DynkinSystem α where
  Has := GenerateHas s
  has_empty := GenerateHas.empty
  has_compl {_} := GenerateHas.compl
  has_iUnion_nat {_} := GenerateHas.iUnion
#align measurable_space.dynkin_system.generate MeasurableSpace.DynkinSystem.generate

theorem generateHas_def {C : Set (Set α)} : (generate C).Has = GenerateHas C :=
  rfl
#align measurable_space.dynkin_system.generate_has_def MeasurableSpace.DynkinSystem.generateHas_def

instance : Inhabited (DynkinSystem α) :=
  ⟨generate univ⟩

/-- If a Dynkin system is closed under binary intersection, then it forms a `σ`-algebra. -/
def toMeasurableSpace (h_inter : ∀ s₁ s₂, d.Has s₁ → d.Has s₂ → d.Has (s₁ ∩ s₂)) :
    MeasurableSpace α where
  MeasurableSet' := d.Has
  measurableSet_empty := d.has_empty
  measurableSet_compl s h := d.has_compl h
  measurableSet_iUnion f hf := by
    rw [← iUnion_disjointed]
    exact
      d.has_iUnion (disjoint_disjointed _) fun n =>
        disjointedRec (fun (t : Set α) i h => h_inter _ _ h <| d.has_compl <| hf i) (hf n)
#align measurable_space.dynkin_system.to_measurable_space MeasurableSpace.DynkinSystem.toMeasurableSpace

theorem ofMeasurableSpace_toMeasurableSpace
    (h_inter : ∀ s₁ s₂, d.Has s₁ → d.Has s₂ → d.Has (s₁ ∩ s₂)) :
    ofMeasurableSpace (d.toMeasurableSpace h_inter) = d :=
  ext fun _ => Iff.rfl
#align measurable_space.dynkin_system.of_measurable_space_to_measurable_space MeasurableSpace.DynkinSystem.ofMeasurableSpace_toMeasurableSpace

/-- If `s` is in a Dynkin system `d`, we can form the new Dynkin system `{s ∩ t | t ∈ d}`. -/
def restrictOn {s : Set α} (h : d.Has s) : DynkinSystem α where
  -- Porting note(#12129): additional beta reduction needed
  Has t := d.Has (t ∩ s)
  has_empty := by simp [d.has_empty]
  has_compl {t} hts := by
    beta_reduce
    have : tᶜ ∩ s = (t ∩ s)ᶜ \ sᶜ := Set.ext fun x => by by_cases h : x ∈ s <;> simp [h]
    rw [this]
    exact
      d.has_diff (d.has_compl hts) (d.has_compl h)
        (compl_subset_compl.mpr <| inter_subset_right _ _)
  has_iUnion_nat {f} hd hf := by
    simp only []
    rw [iUnion_inter]
    refine d.has_iUnion_nat _ hf
    exact hd.mono fun i j => Disjoint.mono (inter_subset_left _ _) (inter_subset_left _ _)
#align measurable_space.dynkin_system.restrict_on MeasurableSpace.DynkinSystem.restrictOn

theorem generate_le {s : Set (Set α)} (h : ∀ t ∈ s, d.Has t) : generate s ≤ d := fun _ ht =>
  ht.recOn h d.has_empty (fun {_} _ h => d.has_compl h) fun {_} hd _ hf => d.has_iUnion hd hf
#align measurable_space.dynkin_system.generate_le MeasurableSpace.DynkinSystem.generate_le

theorem generate_has_subset_generate_measurable {C : Set (Set α)} {s : Set α}
    (hs : (generate C).Has s) : MeasurableSet[generateFrom C] s :=
  generate_le (ofMeasurableSpace (generateFrom C)) (fun _ => measurableSet_generateFrom) s hs
#align measurable_space.dynkin_system.generate_has_subset_generate_measurable MeasurableSpace.DynkinSystem.generate_has_subset_generate_measurable

theorem generate_inter {s : Set (Set α)} (hs : IsPiSystem s) {t₁ t₂ : Set α}
    (ht₁ : (generate s).Has t₁) (ht₂ : (generate s).Has t₂) : (generate s).Has (t₁ ∩ t₂) :=
  have : generate s ≤ (generate s).restrictOn ht₂ :=
    generate_le _ fun s₁ hs₁ =>
      have : (generate s).Has s₁ := GenerateHas.basic s₁ hs₁
      have : generate s ≤ (generate s).restrictOn this :=
        generate_le _ fun s₂ hs₂ =>
          show (generate s).Has (s₂ ∩ s₁) from
            (s₂ ∩ s₁).eq_empty_or_nonempty.elim (fun h => h.symm ▸ GenerateHas.empty) fun h =>
              GenerateHas.basic _ <| hs _ hs₂ _ hs₁ h
      have : (generate s).Has (t₂ ∩ s₁) := this _ ht₂
      show (generate s).Has (s₁ ∩ t₂) by rwa [inter_comm]
  this _ ht₁
#align measurable_space.dynkin_system.generate_inter MeasurableSpace.DynkinSystem.generate_inter

/-- **Dynkin's π-λ theorem**:
  Given a collection of sets closed under binary intersections, then the Dynkin system it
  generates is equal to the σ-algebra it generates.
  This result is known as the π-λ theorem.
  A collection of sets closed under binary intersection is called a π-system (often requiring
  additionally that it is non-empty, but we drop this condition in the formalization).
-/
theorem generateFrom_eq {s : Set (Set α)} (hs : IsPiSystem s) :
    generateFrom s = (generate s).toMeasurableSpace fun t₁ t₂ => generate_inter hs :=
  le_antisymm (generateFrom_le fun t ht => GenerateHas.basic t ht)
    (ofMeasurableSpace_le_ofMeasurableSpace_iff.mp <| by
      rw [ofMeasurableSpace_toMeasurableSpace]
      exact generate_le _ fun t ht => measurableSet_generateFrom ht)
#align measurable_space.dynkin_system.generate_from_eq MeasurableSpace.DynkinSystem.generateFrom_eq

end DynkinSystem

theorem induction_on_inter {C : Set α → Prop} {s : Set (Set α)} [m : MeasurableSpace α]
    (h_eq : m = generateFrom s) (h_inter : IsPiSystem s) (h_empty : C ∅) (h_basic : ∀ t ∈ s, C t)
    (h_compl : ∀ t, MeasurableSet t → C t → C tᶜ)
    (h_union :
      ∀ f : ℕ → Set α,
        Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) → (∀ i, C (f i)) → C (⋃ i, f i)) :
    ∀ ⦃t⦄, MeasurableSet t → C t :=
  have eq : MeasurableSet = DynkinSystem.GenerateHas s := by
    rw [h_eq, DynkinSystem.generateFrom_eq h_inter]
    rfl
  fun t ht =>
  have : DynkinSystem.GenerateHas s t := by rwa [eq] at ht
  this.recOn h_basic h_empty
    (fun {t} ht =>
      h_compl t <| by
        rw [eq]
        exact ht)
    fun {f} hf ht =>
    h_union f hf fun i => by
      rw [eq]
      exact ht _
#align measurable_space.induction_on_inter MeasurableSpace.induction_on_inter

end MeasurableSpace
