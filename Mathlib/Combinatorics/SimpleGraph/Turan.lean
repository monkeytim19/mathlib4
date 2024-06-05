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
complete multipartite with the parts being the equivalence classes. Then basic manipulations
show that the graph is isomorphic to the Turán graph for the given parameters.

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
* `SimpleGraph.IsTuranMaximal.finpartition`: The result of Zykov symmetrisation, a finpartition of
  the vertices such that two vertices are in the same part iff they are non-adjacent.
* `SimpleGraph.IsTuranMaximal.nonempty_iso_TuranGraph`: The forward direction, an isomorphism
  between `G` satisfying `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.

## References

* https://en.wikipedia.org/wiki/Turán%27s_theorem
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
  refine ⟨Sm, ?_⟩
  intro I _ cf
  by_cases Im : I ∈ c.toFinset
  · convert Sl I Im
  · rw [Set.mem_toFinset] at Im
    contradiction

end Defs

section EdgeCard

lemma range_castAddOrderEmb_compl_eq_attach_image :
    ((Set.range (@Fin.castAddOrderEmb n r)).toFinset)ᶜ =
    (range r).attach.image (fun x ↦ ⟨n + x.1, add_lt_add_left (mem_range.mp x.2) n⟩) := by
  ext x
  simp_rw [Set.toFinset_range, mem_compl, mem_image, mem_univ, Fin.castAddOrderEmb_apply,
    mem_attach, true_and, Subtype.exists, mem_range]
  have : (∃ a, Fin.castAdd r a = x) ↔ x < n := by
    constructor <;> intro h
    · rw [← h.choose_spec]; simp
    · use ⟨x.1, h⟩; simp
  rw [this, not_lt]
  constructor <;> intro h
  · use x - n, (Nat.sub_lt_iff_lt_add h).mpr x.2
    simp only [add_tsub_cancel_of_le h]
  · rw [← h.choose_spec.choose_spec, le_add_iff_nonneg_right]
    exact zero_le _

lemma range_castAddOrderEmb_eq_attach_image :
    (Set.range (@Fin.castAddOrderEmb n r)).toFinset =
    (range n).attach.image (fun x ↦ ⟨x.1, (mem_range.mp x.2).trans_le (Nat.le_add_right ..)⟩) := by
  ext x
  simp only [Set.toFinset_range, mem_image, mem_univ, Fin.castAddOrderEmb_apply, true_and,
    mem_attach, Subtype.exists, mem_range]
  have : (∃ a, Fin.castAdd r a = x) ↔ x < n := by
    constructor <;> intro h
    · rw [← h.choose_spec]; simp
    · use ⟨x.1, h⟩; simp
  rw [this]
  constructor <;> intro h
  · use x, h
  · obtain ⟨a, b, c⟩ := h
    simp [← c, b]

open BigOperators in
theorem card_edgeFinset_turanGraph_add (hr : 0 < r) : (turanGraph (n + r) r).edgeFinset.card =
    (r - 1) * n + (turanGraph n r).edgeFinset.card + r.choose 2 := by
  set R := (Set.range (@Fin.castAddOrderEmb n r)).toFinset
  have Rc : R.card = n := by
    simp only [R]
    rw [Set.toFinset_range, card_image_of_injective _ (Fin.castAddOrderEmb r).injective, card_fin]
  rw [(turanGraph (n + r) r).edgeFinset_decompose_card R]
  congr 2
  · rw [crossEdges_edgeFinset_card, range_castAddOrderEmb_compl_eq_attach_image,
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
    simp_rw [L, R, range_castAddOrderEmb_eq_attach_image, filter_image]
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
    exact {toEquiv := (@Fin.castAddOrderEmb n r).orderIso, map_rel_iff' := by simp [turanGraph]}
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

variable {G} {s t u : V} (h : G.IsTuranMaximal r)

namespace IsTuranMaximal

/-- In a Turán-maximal graph, non-adjacent vertices have the same degree. -/
lemma degree_eq_of_not_adj (hn : ¬G.Adj s t) : G.degree s = G.degree t := by
  rw [IsTuranMaximal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_lt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  use G.replaceVertex s t, inferInstance, cf.replaceVertex s t
  have := G.card_edgeFinset_replaceVertex_of_not_adj hn
  omega

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
lemma not_adj_transitive (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) : ¬G.Adj t u := by
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal] at h; contrapose! h; intro cf
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t).replaceVertex s u
  have nst : s ≠ t := fun a ↦ hsu (a ▸ h)
  have ntu : t ≠ u := G.ne_of_adj h
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, dst, Nat.add_sub_cancel]
  have l1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset, SimpleGraph.irrefl, ite_self]
    by_cases eq : v = t
    · simpa only [eq, not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have l2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    rw [degree, degree, ← card_singleton t, ← card_sdiff (by simp [h.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs <;> simp_all [adj_comm]
  have l3 : 0 < G.degree u := by rw [G.degree_pos_iff_exists_adj u]; use t, h.symm
  omega

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem not_adj_equivalence : Equivalence fun x y ↦ ¬G.Adj x y where
  refl x := by simp
  symm xy := by simp [xy, adj_comm]
  trans xy yz := by
    rw [adj_comm] at xy
    exact h.not_adj_transitive xy yz

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `not_adj_equivalence`. -/
def setoid : Setoid V := ⟨_, h.not_adj_equivalence⟩

instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

/-- The finpartition derived from `h.setoid`. -/
def finpartition : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid

lemma not_adj_iff_part_eq : ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t ∈ fp.part s ↔ fp.part s = fp.part t
  refine ⟨fun c ↦ fp.eq_of_mem_parts ?_ ?_ c ?_, fun c ↦ c ▸ fp.mem_part (mem_univ t)⟩ <;>
    simp [fp.part_mem, fp.mem_part]

lemma degree_eq_card_sub_part_card : G.degree s = Fintype.card V - (h.finpartition.part s).card :=
  calc
    _ = (univ.filter fun b ↦ G.Adj s b).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter fun b ↦ ¬G.Adj s b).card :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert Finpartition.mem_part_ofSetoid_iff_rel.symm
      simp [setoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
theorem isEquipartition : h.finpartition.IsEquipartition := by
  set fp := h.finpartition
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  have large_eq := fp.eq_of_mem_parts hl (fp.part_mem (mem_univ w)) hw (fp.mem_part (mem_univ w))
  have small_eq := fp.eq_of_mem_parts hs (fp.part_mem (mem_univ v)) hv (fp.mem_part (mem_univ v))
  apply absurd h
  rw [IsTuranMaximal]; push_neg; intro cf
  use G.replaceVertex v w, inferInstance, cf.replaceVertex v w
  have ha : G.Adj v w := by
    by_contra hn; rw [h.not_adj_iff_part_eq, ← small_eq, ← large_eq] at hn
    rw [hn] at ineq; omega
  rw [G.card_edgeFinset_replaceVertex_of_adj ha,
    degree_eq_card_sub_part_card h, ← small_eq, degree_eq_card_sub_part_card h, ← large_eq]
  have : large.card ≤ Fintype.card V := by simpa using card_le_card large.subset_univ
  omega

lemma card_parts_le : h.finpartition.parts.card ≤ r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree z.card := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ ?_, rfl⟩
    contrapose! hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (h.1.mono (Nat.succ_le_of_lt l)) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
`min` handles the `n < r` case, when `G` is complete but still `r + 1`-cliquefree
for having insufficiently many vertices. -/
theorem card_parts : h.finpartition.parts.card = min (Fintype.card V) r := by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ ↦ fp.part_mem (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal]; push_neg; rintro -
  have cf : G.CliqueFree r := by
    simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
      forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff, Set.Pairwise]
    intro z zc; push_neg; simp_rw [h.not_adj_iff_part_eq]
    exact exists_ne_map_eq_of_card_lt_of_maps_to (zc.symm ▸ l.2) fun a _ ↦ fp.part_mem (mem_univ a)
  use G ⊔ edge x y, inferInstance, cf.sup_edge x y
  convert Nat.lt.base G.edgeFinset.card
  convert G.card_edgeFinset_sup_edge _ hn
  rwa [h.not_adj_iff_part_eq]

/-- **Turán's theorem**, forward direction.
Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
theorem nonempty_iso_turanGraph : Nonempty (G ≃g turanGraph (Fintype.card V) r) := by
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_eq] at this
  rw [← not_iff_not, not_ne_iff, this, card_parts]
  rcases le_or_lt r (Fintype.card V) with c | c
  · rw [min_eq_right c]; rfl
  · have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ x⟩).2
    rw [min_eq_left c.le, Nat.mod_eq_of_lt (lc a), Nat.mod_eq_of_lt (lc b),
      ← Nat.mod_eq_of_lt ((lc a).trans c), ← Nat.mod_eq_of_lt ((lc b).trans c)]; rfl

end IsTuranMaximal

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
  ⟨fun h ↦ h.nonempty_iso_turanGraph, fun h ↦ G.isTuranMaximal_of_iso hr h.some⟩

end SimpleGraph
