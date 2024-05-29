/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Partition.Equipartition

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations show
that the graph is (isomorphic to) the Turán graph for the given parameters.

The reverse direction proceeds as in Turán's original proof, via induction on the vertex count.
If we know that `turanGraph n r` is Turán-maximal, consider any `r + 1`-cliquefree graph on
`n + r` vertices; we can assume without loss of generality that it is Turán-maximal. Maximality
implies there is an `r`-clique `K`, so the graph's edges split into three sets:
* Edges entirely within `K`, which number at most `r.choose 2`
* Edges entirely outside `K` and hence in the `n`-vertex subgraph induced by `Kᶜ`,
  which by the inductive hypothesis number at most `(turanGraph n r).edgeFinset.card`
* Edges spanning `K` and `Kᶜ`; no vertex in `Kᶜ` can connect to all of `K`, so this set of edges
  numbers at most `(r - 1) * n`
These bounds add up to exactly `(turanGraph (n + r) r).edgeFinset.card`, completing the induction.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `isTuranMaximalIsoTuranGraph`: the forward direction, an isomorphism between `G` satisfying
  `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj]
  {n r : ℕ}

section Defs

/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

variable {G H}

lemma IsTuranMaximal.le_iff_eq (hG : G.IsTuranMaximal r) (hH : H.CliqueFree (r + 1)) :
    G ≤ H ↔ G = H := by
  classical exact ⟨fun hGH ↦ edgeFinset_inj.1 <| eq_of_subset_of_card_le
    (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 _ hH), le_of_eq⟩

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

instance turanGraph.instDecidableRelAdj : DecidableRel (turanGraph n r).Adj := by
  dsimp only [turanGraph]; infer_instance

@[simp]
lemma turanGraph_zero : turanGraph n 0 = ⊤ := by
  ext a b; simp_rw [turanGraph, top_adj, Nat.mod_zero, not_iff_not, Fin.val_inj]

@[simp]
theorem turanGraph_eq_top : turanGraph n r = ⊤ ↔ r = 0 ∨ n ≤ r := by
  simp_rw [SimpleGraph.ext_iff, Function.funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.trans_le h), Nat.mod_eq_of_lt (b.2.trans_le h), Fin.val_inj]

variable (hr : 0 < r)

theorem turanGraph_cliqueFree : (turanGraph n r).CliqueFree (r + 1) := by
  rw [cliqueFree_iff]
  by_contra h
  rw [not_isEmpty_iff] at h
  obtain ⟨f, ha⟩ := h
  simp only [turanGraph, top_adj] at ha
  obtain ⟨x, y, d, c⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun x ↦
    (⟨(f x).1 % r, Nat.mod_lt _ hr⟩ : Fin r)) (by simp)
  simp only [Fin.mk.injEq] at c
  exact absurd c ((@ha x y).mpr d)

/-- For `n ≤ r` and `0 < r`, `turanGraph n r` is Turán-maximal. -/
theorem isTuranMaximal_turanGraph (h : n ≤ r) : (turanGraph n r).IsTuranMaximal r :=
  ⟨turanGraph_cliqueFree hr, fun _ _ _ ↦
    card_le_card (edgeFinset_mono ((turanGraph_eq_top.mpr (Or.inr h)).symm ▸ le_top))⟩

/-- An `r + 1`-cliquefree Turán-maximal graph is _not_ `r`-cliquefree
if it can accommodate such a clique. -/
theorem not_cliqueFree_of_isTuranMaximal (hn : r ≤ Fintype.card V) (hG : G.IsTuranMaximal r) :
    ¬G.CliqueFree r := by
  rintro h
  obtain ⟨K, _, rfl⟩ := exists_smaller_set (univ : Finset V) r hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
  exact hGab <| le_sup_right.trans_eq ((hG.le_iff_eq <| h.sup_edge _ _).1 le_sup_left).symm <|
    (edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, hab⟩

open Classical in
lemma exists_IsTuranMaximal : ∃ H : SimpleGraph V, H.IsTuranMaximal r := by
  let c := {H : SimpleGraph V | H.CliqueFree (r + 1)}
  have cn : c.toFinset.Nonempty := ⟨⊥, by
    simp only [Set.toFinset_setOf, mem_filter, mem_univ, true_and, c]
    exact cliqueFree_bot (by omega)⟩
  obtain ⟨S, Sm, Sl⟩ := exists_max_image c.toFinset (·.edgeFinset.card) cn
  use S
  rw [Set.mem_toFinset] at Sm
  refine' ⟨Sm, _⟩
  intro I _ cf
  by_cases Im : I ∈ c.toFinset
  · convert Sl I Im
  · rw [Set.mem_toFinset] at Im
    contradiction

end Defs

section EdgeCard

lemma range_castAddEmb_compl_eq_attach_image : ((Set.range (@Fin.castAddEmb n r)).toFinset)ᶜ =
    (range r).attach.image (fun x ↦ ⟨n + x.1, add_lt_add_left (mem_range.mp x.2) n⟩) := by
  ext x
  simp_rw [Set.toFinset_range, mem_compl, mem_image, mem_univ, Fin.castAddEmb_apply, mem_attach,
    true_and, Subtype.exists, mem_range]
  have : (∃ a, Fin.castAdd r a = x) ↔ x < n := by
    constructor <;> intro h
    · rw [← h.choose_spec]; simp
    · use ⟨x.1, h⟩; simp
  simp_rw [Fin.castAdd] at this
  rw [this, not_lt]
  constructor <;> intro h
  · use x - n, (Nat.sub_lt_iff_lt_add h).mpr x.2
    simp only [add_tsub_cancel_of_le h]
  · rw [← h.choose_spec.choose_spec, le_add_iff_nonneg_right]
    exact zero_le _

lemma range_castAddEmb_eq_attach_image : (Set.range (@Fin.castAddEmb n r)).toFinset =
    (range n).attach.image (fun x ↦ ⟨x.1, (mem_range.mp x.2).trans_le (Nat.le_add_right ..)⟩) := by
  ext x
  simp only [Set.toFinset_range, mem_image, mem_univ, Fin.castAddEmb_apply, true_and, mem_attach,
    Subtype.exists, mem_range]
  have : (∃ a, Fin.castAdd r a = x) ↔ x < n := by
    constructor <;> intro h
    · rw [← h.choose_spec]; simp
    · use ⟨x.1, h⟩; simp
  simp_rw [Fin.castAdd] at this
  rw [this]
  constructor <;> intro h
  · use x, h
  · obtain ⟨a, b, c⟩ := h
    simp [← c, b]

open BigOperators in
theorem card_edgeFinset_turanGraph_add (hr : 0 < r) : (turanGraph (n + r) r).edgeFinset.card =
    (r - 1) * n + (turanGraph n r).edgeFinset.card + r.choose 2 := by
  set R := (Set.range (@Fin.castAddEmb n r)).toFinset
  have Rc : R.card = n := by
    simp only [R]
    rw [Set.toFinset_range, card_image_of_injective _ (Fin.castAddEmb r).injective, card_fin]
  rw [(turanGraph (n + r) r).edgeFinset_decompose_card R]
  congr 2
  · rw [crossEdges_edgeFinset_card, range_castAddEmb_compl_eq_attach_image,
      sum_image (by simp [SetCoe.ext_iff])]
    let K := fun y ↦ (R.filter (fun z : Fin (n + r) ↦ z % r ≠ (n + y) % r)).card
    let L := fun y ↦ (R.filter (fun z : Fin (n + r) ↦ z % r = (n + y) % r)).card
    change ∑ x in (range r).attach, K x = _
    rw [sum_attach]
    have feq := fun y ↦ filter_card_add_filter_neg_card_eq_card (s := R)
      (fun z ↦ z % r ≠ (n + y) % r)
    simp_rw [Rc, not_not] at feq
    have Keq : ∀ x ∈ range r, K x = n - L x := fun x _ ↦ by
      conv_rhs => arg 1; rw [← feq x]
      exact (add_tsub_cancel_right _ _).symm
    rw [sum_congr rfl Keq]
    have Lle : ∀ x, L x ≤ n := fun x ↦ Rc.symm ▸ card_filter_le R _
    zify [Lle, hr]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sub_one_mul, sub_right_inj]
    simp_rw [L, R, range_castAddEmb_eq_attach_image, filter_image]
    conv_lhs =>
      enter [2, x]
      rw [card_image_of_injective _ (fun _ _ c ↦ by simpa [Subtype.val_inj] using c),
        filter_attach (fun v ↦ v % r = (n + x) % r), card_map, card_attach, card_filter,
        ← sum_range_reflect]
    rw [← sum_range_reflect]
    have rcoe : ∀ b : ℕ, ∀ x ∈ range b, ↑(b - 1 - x) = (b : ℤ) - 1 - x := fun b x hb ↦ by
      rw [Nat.sub_sub, Int.sub_sub, Int.natCast_sub, Int.natCast_add, Nat.cast_one]
      have := mem_range.mp hb
      omega
    zify
    rw [sum_congr (g := fun x : ℕ ↦
      ∑ y in range n, if (n - 1 - y) % r = ((n : ℤ) + (r - 1 - x)) % r then 1 else 0) rfl
      fun x hx ↦ sum_congr rfl (fun y hy ↦ by rw [rcoe r x hx, rcoe n y hy])]
    simp_rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    conv_lhs =>
      enter [2, x, 2, y]
      rw [show (n : ℤ) - 1 - y - (n + (r - 1 - x)) = x - y - r by omega, Int.Int.emod_sub_cancel]
    simp_rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
    norm_cast; clear! R K L rcoe
    rw [sum_comm, sum_congr (g := fun y ↦ 1) rfl, sum_const, card_range, smul_eq_mul, mul_one]
    · intro y _
      rw [sum_congr (g := fun x ↦ if x = y % r then 1 else 0) rfl
        (fun x hx ↦ by congr; exact Nat.mod_eq_of_lt (mem_range.mp hx)), sum_ite_eq']
      simp only [mem_range.mpr (Nat.mod_lt y hr), ite_true]
  · symm
    apply Iso.card_edgeFinset_eq
    rw [Set.coe_toFinset]
    exact {toEquiv := (@Fin.castAddEmb n r).orderIso, map_rel_iff' := by simp [turanGraph]}
  · convert card_edgeFinset_top_eq_card_choose_two
    · ext x' y'
      obtain ⟨x, hx⟩ := x'
      obtain ⟨y, hy⟩ := y'
      replace hx : n ≤ x := by simpa [R, Fin.castAdd] using hx
      replace hy : n ≤ y := by simpa [R, Fin.castAdd] using hy
      have := (Nat.mod_injOn_Ico n r).eq_iff (mem_Ico.mpr ⟨hx, x.2⟩) (mem_Ico.mpr ⟨hy, y.2⟩)
      simp [turanGraph, this, Fin.val_eq_val]
    · simp only [Fintype.card_compl_set, Fintype.card_fin, Set.toFinset_range, coe_image, coe_univ,
        Set.image_univ, Fintype.card_range, add_tsub_cancel_left, R]
    · infer_instance
    · infer_instance

end EdgeCard

section Forward

variable {s t u : V} (hmax : G.IsTuranMaximal r)

/-- First part of Zykov symmetrisation. If vertex `s` has larger degree than
a non-adjacent other vertex `t`, `G.replaceVertex s t` has more edges than `G`. -/
theorem card_lt_card_replaceVertex1 (hn : ¬G.Adj s t) (hd : G.degree t < G.degree s) :
    G.edgeFinset.card < (G.replaceVertex s t).edgeFinset.card := by
  rw [G.card_edgeFinset_replaceVertex_of_not_adj hn, add_tsub_assoc_of_le hd.le]
  exact Nat.lt_add_of_pos_right <| tsub_pos_iff_lt.mpr hd

/-- Second part of Zykov symmetrisation. A witness to non-transitivity of non-adjacency
where the involved vertices have the same degree can be used to generate
(using `replaceVertex` only) a graph with more edges. -/
theorem card_lt_card_replaceVertex2 (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) (htu : G.Adj t u)
    (hdt : G.degree s = G.degree t) (hdu : G.degree s = G.degree u) :
    G.edgeFinset.card < ((G.replaceVertex s t).replaceVertex s u).edgeFinset.card := by
  have ntu : t ≠ u := G.ne_of_adj htu
  have nst : s ≠ t := fun a => by subst a; contradiction
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, hdt, Nat.add_sub_cancel]
  have de1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset, SimpleGraph.irrefl, ite_self]
    by_cases eq : v = t
    · subst eq
      simpa only [not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have de2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    unfold degree
    rw [← card_singleton t, ← card_sdiff (by simp [htu.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs with hu hv hv
    · simp_all
    · simp_all
    · simp [adj_comm, hsu, hv]
    · simp [adj_comm, hsu, hv]
  have dpos : 0 < G.degree u := by
    rw [G.degree_pos_iff_exists_adj u]
    use t
    exact htu.symm
  have dmp : G.degree u - 1 + 1 = G.degree u := Nat.succ_pred_eq_of_pos dpos
  nth_rw 1 [de1, de2, hdu, ← dmp, add_tsub_assoc_of_le (by simp), add_tsub_cancel_left]
  linarith

variable {G}

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
theorem not_adj_transitive (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) : ¬G.Adj t u := by
  by_cases z : G.degree s = G.degree t ∧ G.degree s = G.degree u <;>
    (contrapose! hmax; unfold IsTuranMaximal; push_neg; intro cf)
  · use (G.replaceVertex s t).replaceVertex s u, inferInstance
    exact ⟨(cf.replaceVertex s t).replaceVertex s u,
      card_lt_card_replaceVertex2 _ hst hsu hmax z.1 z.2⟩
  · rw [Decidable.not_and_iff_or_not_not] at z
    cases' z with st su
    · cases' lt_or_gt_of_ne st with less more
      · use G.replaceVertex t s, inferInstance
        rw [adj_comm] at hst
        exact ⟨cf.replaceVertex t s, G.card_lt_card_replaceVertex1 hst less⟩
      · use G.replaceVertex s t, inferInstance
        exact ⟨cf.replaceVertex s t, G.card_lt_card_replaceVertex1 hst more⟩
    · cases' lt_or_gt_of_ne su with less more
      · use G.replaceVertex u s, inferInstance
        rw [adj_comm] at hsu
        exact ⟨cf.replaceVertex u s, G.card_lt_card_replaceVertex1 hsu less⟩
      · use G.replaceVertex s u, inferInstance
        exact ⟨cf.replaceVertex s u, G.card_lt_card_replaceVertex1 hsu more⟩

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem notAdj_equivalence : Equivalence fun x y => ¬G.Adj x y where
  refl x := by simp
  symm xy := by simp [xy, adj_comm]
  trans xy yz := by
    rw [adj_comm] at xy
    exact G.not_adj_transitive hmax xy yz

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph that exists
because of `notAdj_equivalence`. Said graph is therefore a complete multipartite graph. -/
def notAdjSetoid : Setoid V := ⟨_, (notAdj_equivalence hmax)⟩

instance : DecidableRel (notAdjSetoid hmax).r :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

/-- The finpartition derived from `notAdjSetoid`. -/
def notAdjFinpartition : Finpartition (univ : Finset V) :=
  Finpartition.ofSetoid (notAdjSetoid hmax)

theorem degree_eq_fintype_card_sub_part_card : G.degree s = Fintype.card V -
    ((notAdjFinpartition hmax).part s).card := by
  calc
    G.degree s = (univ.filter (fun b => G.Adj s b)).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter (fun b => ¬G.Adj s b)).card :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert (Finpartition.mem_part_ofSetoid_iff_rel).symm
      simp [notAdjSetoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
theorem notAdj_equipartition : (notAdjFinpartition hmax).IsEquipartition := by
  let fp := notAdjFinpartition hmax
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  have large_eq : large = fp.part w :=
    (fp.existsUnique_mem (a := w) (mem_univ _)).unique
      ⟨hl, hw⟩ ⟨fp.part_mem (mem_univ _), fp.mem_part (mem_univ _)⟩
  have small_eq : small = fp.part v :=
    (fp.existsUnique_mem (a := v) (mem_univ _)).unique
      ⟨hs, hv⟩ ⟨fp.part_mem (mem_univ _), fp.mem_part (mem_univ _)⟩
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro cf
    use G.replaceVertex v w, inferInstance
    refine' ⟨cf.replaceVertex v w, _⟩
    have ha : G.Adj v w := by
      have lsn : large ≠ small := fun _ => by simp_all only [add_lt_iff_neg_left, not_lt_zero']
      contrapose! lsn
      have : _ ∈ fp.part _ ↔ ¬G.Adj v w := Finpartition.mem_part_ofSetoid_iff_rel
      exact fp.eq_of_mem_parts hl hs hw (small_eq ▸ this.mpr lsn)
    rw [G.card_edgeFinset_replaceVertex_of_adj ha]
    have large_le : large.card ≤ Fintype.card V := by
      simpa using card_le_card large.subset_univ
    have small_le : small.card ≤ Fintype.card V := by
      simpa using card_le_card small.subset_univ
    rw [degree_eq_fintype_card_sub_part_card, ← small_eq,
      degree_eq_fintype_card_sub_part_card, ← large_eq,
      Nat.add_sub_assoc (by rw [tsub_le_tsub_iff_left small_le]; linarith),
      tsub_tsub_tsub_cancel_left large_le, Nat.add_sub_assoc (lt_tsub_iff_left.mpr ineq).le]
    linarith [tsub_pos_iff_lt.mpr (lt_tsub_iff_left.mpr ineq)]
  contradiction

theorem notAdj_card_parts_le : (notAdjFinpartition hmax).parts.card ≤ r := by
  let fp := notAdjFinpartition hmax
  by_contra! h
  obtain ⟨z, _, hz⟩ := fp.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree z.card := by
    refine' IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ _, rfl⟩
    norm_cast at hv hw
    contrapose! hn
    have i1 : w ∈ fp.part v := Finpartition.mem_part_ofSetoid_iff_rel.mpr hn
    have i2 : w ∈ fp.part w := fp.mem_part (mem_univ _)
    exact hz.injOn hv hw <|
      fp.eq_of_mem_parts (fp.part_mem (mem_univ _)) (fp.part_mem (mem_univ _)) i1 i2
  have zc : z.card = fp.parts.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe, Fintype.card_eq]
    let q := hz.equiv
    use q, q.symm, q.left_inv, q.right_inv
  rw [zc] at ncf
  exact absurd (CliqueFree.mono (Nat.succ_le_of_lt h) hmax.1) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
The `min` is necessary because `r` may be greater than `n`, in which case `G` is complete but
still `r + 1`-cliquefree for having insufficiently many vertices. -/
theorem notAdj_card_parts : (notAdjFinpartition hmax).parts.card = min (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  apply le_antisymm (le_min fp.card_parts_le_card (notAdj_card_parts_le _))
  by_contra! h
  rw [lt_min_iff] at h
  obtain ⟨x, _, y, _, hn, he⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun a => fp.part a) univ fp.parts h.1 (fun _ _ => fp.part_mem (mem_univ _))
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro
    use G ⊔ edge x y, inferInstance
    have cf : G.CliqueFree r := by
      simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
        forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff]
      intro z zc
      obtain ⟨x', xm, y', ym, hn', he'⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
        (f := fun a => fp.part a) z fp.parts (zc.symm ▸ h.2)
        (fun _ _ => fp.part_mem (mem_univ _))
      unfold Set.Pairwise; push_neg; norm_cast
      use x', xm, y', ym, hn'
      change (notAdjSetoid hmax).r x' y'
      apply Finpartition.mem_part_ofSetoid_iff_rel.mp
      exact he' ▸ fp.mem_part (mem_univ _)
    refine' ⟨cf.sup_edge x y, _⟩
    convert Nat.lt.base G.edgeFinset.card
    convert G.card_edgeFinset_sup_edge _ hn
    change (notAdjSetoid hmax).r x y
    apply Finpartition.mem_part_ofSetoid_iff_rel.mp
    exact he ▸ fp.mem_part (mem_univ _)
  contradiction

/-- **Turán's theorem**, forward direction.
Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
noncomputable def IsTuranMaximal.isoTuranGraph : G ≃g turanGraph (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  obtain ⟨zm, zp⟩ := (notAdj_equipartition hmax).partPreservingEquiv
  use (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  rw [← not_iff_not]
  change _ ↔ (notAdjSetoid hmax).r a b
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change _ ↔ b ∈ fp.part _
  have pe : b ∈ fp.part a ↔ fp.part a = fp.part b := by
    constructor <;> intro h
    · exact fp.eq_of_mem_parts (fp.part_mem (mem_univ _)) (fp.part_mem (mem_univ _)) h
        (fp.mem_part (mem_univ _))
    · rw [h]; exact fp.mem_part (mem_univ _)
  rw [pe, zp ⟨a, mem_univ _⟩ ⟨b, mem_univ _⟩, notAdj_card_parts, not_not, min_comm]
  rcases le_or_lt r (Fintype.card V) with h | h
  · rw [min_eq_left h]; rfl
  · rw [min_eq_right h.le]
    have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ _⟩).2
    have cn0 : Fintype.card V ≠ 0 := by by_contra h; exact absurd (h ▸ lc a) not_lt_zero'
    have rn0 : r ≠ 0 := by linarith
    rw [(Nat.mod_eq_iff_lt cn0).mpr (lc a), (Nat.mod_eq_iff_lt cn0).mpr (lc b),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc a).trans h),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc b).trans h)]
    rfl

end Forward

section Reverse

variable (hr : 0 < r)

open Classical in
lemma induce_compl_edgeFinset_card {m} (H : SimpleGraph (Fin (m + r)))
    (itm : H.IsTuranMaximal r) (K : Finset (Fin (m + r))) (Kc : K.card = r)
    (ih : (turanGraph m r).IsTuranMaximal r) :
    (H.induce Kᶜ).edgeFinset.card ≤ (turanGraph m r).edgeFinset.card := by
  let S := H.induce Kᶜ
  have Sc : Fintype.card ↑((K : Set (Fin (m + r)))ᶜ) = m := by
    rw [Fintype.card_compl_set]
    simp [Kc]
  let S' := S.overFin Sc
  let I := S.overFinIso Sc
  have card_eq : S'.edgeFinset.card = S.edgeFinset.card := by
    apply card_eq_of_equiv; simp only [Set.mem_toFinset]; exact I.mapEdgeSet.symm
  exact card_eq ▸ ih.2 S' ((itm.1.comap (Embedding.induce Kᶜ)).comap I.symm)

open Classical BigOperators in
lemma sum_card_filter_adj_le_sub_mul {m} (H : SimpleGraph (Fin (m + r)))
    (cf : H.CliqueFree (r + 1)) (K : Finset (Fin (m + r))) (Kp : H.IsNClique r K) :
    ∑ b in Kᶜ, card (filter (fun x ↦ H.Adj x b) K) ≤ (r - 1) * m := by
  suffices ∀ b ∈ Kᶜ, ∃ a ∈ K, ¬H.Adj a b by
    have lt : ∀ b ∈ Kᶜ, (K.filter (H.Adj · b)).card ≤ r - 1 := by
      intro b mb
      simp_rw [← Nat.lt_add_one_iff, Nat.sub_add_cancel hr, ← Kp.2]
      conv_rhs => rw [← filter_card_add_filter_neg_card_eq_card (H.Adj · b)]
      rw [Nat.lt_add_right_iff_pos, card_pos]
      obtain ⟨w, wp⟩ := this b mb
      use w; exact mem_filter.mpr wp
    convert sum_le_sum lt
    rw [sum_const, smul_eq_mul, card_compl, Kp.2, Fintype.card_fin, add_tsub_cancel_right,
      mul_comm]
  by_contra! l; obtain ⟨b, _, pp⟩ := l
  simp_rw [adj_comm] at pp
  exact absurd cf (Kp.insert pp).not_cliqueFree

open Classical in
lemma card_edgeFinset_le_card_turanGraph_calc {m} (H : SimpleGraph (Fin (m + r)))
    (itm : H.IsTuranMaximal r) (ncf : ¬H.CliqueFree r)
    (ih : (turanGraph m r).IsTuranMaximal r) :
    card (edgeFinset H) ≤ card (edgeFinset (turanGraph (m + r) r)) := by
  rw [CliqueFree] at ncf; push_neg at ncf; obtain ⟨K, Kp⟩ := ncf
  have Kc : K.card = r := Kp.2
  rw [H.edgeFinset_decompose_card K, crossEdges_edgeFinset_card,
    card_edgeFinset_turanGraph_add hr, add_assoc (_ * _), add_comm _ (r.choose 2), ← add_assoc]
  gcongr
  · exact H.sum_card_filter_adj_le_sub_mul hr itm.1 K Kp
  · convert card_edgeFinset_le_card_choose_two
    · simp [Kc]
    · infer_instance
  · exact H.induce_compl_edgeFinset_card itm K Kc ih

/-- `turanGraph n r` is Turán-maximal *per se* (if `0 < r`). -/
theorem isTuranMaximal_turanGraph' : (turanGraph n r).IsTuranMaximal r := by
  suffices r = 0 ∨ (turanGraph n r).IsTuranMaximal r by
    exact this.resolve_left (by intro a; exact absurd a hr.ne')
  apply Nat.mod.inductionOn (motive := fun n r ↦ r = 0 ∨ (turanGraph n r).IsTuranMaximal r)
  · intro n r ⟨hr, b⟩ ih
    rw [Nat.eq_add_of_sub_eq b rfl]
    replace ih := ih.resolve_left hr.ne'
    apply Or.inr
    refine' ⟨turanGraph_cliqueFree hr, _⟩
    intro H _ cf
    wlog itm : H.IsTuranMaximal r generalizing H
    · obtain ⟨S, Z⟩ := exists_IsTuranMaximal (V := Fin _) hr
      classical exact (Z.2 H cf).trans (this S Z.1 Z)
    have ncf := H.not_cliqueFree_of_isTuranMaximal (r := r) hr (by simp)
    convert card_edgeFinset_le_card_turanGraph_calc hr H (by convert itm) (ncf itm) ih
  · intro n r b
    simp only [not_and, not_le] at b
    cases' r.eq_zero_or_pos with hr hr
    · exact Or.inl hr
    · exact Or.inr <| isTuranMaximal_turanGraph hr (b hr).le

/-- **Turán's theorem**, reverse direction.
Any graph isomorphic to `turanGraph n r` is itself Turán-maximal. -/
theorem isTuranMaximal_of_iso (iso : G ≃g turanGraph n r) : G.IsTuranMaximal r := by
  obtain ⟨p1, p2⟩ := isTuranMaximal_turanGraph' (n := n) hr
  have cV := iso.card_eq
  rw [Fintype.card_fin] at cV
  constructor
  · exact p1.comap iso
  · intro H _ cf
    let tr := H.overFinIso cV
    classical rw [iso.card_edgeFinset_eq, tr.card_edgeFinset_eq]
    convert p2 (H.overFin cV) (cf.comap tr.symm)

end Reverse

/-- **Turán's theorem**. `turanGraph n r` is, up to isomorphism, the unique
`r + 1`-cliquefree Turán-maximal graph on `n` vertices. -/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (Fintype.card V) r) :=
  ⟨fun h ↦ ⟨h.isoTuranGraph⟩, fun h ↦ G.isTuranMaximal_of_iso hr h.some⟩

end SimpleGraph
