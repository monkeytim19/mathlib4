import Mathlib.Algebra.Algebra.Subalgebra.Unitization
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero
--import Mathlib.CFCNonUnital.ContinuousMapZeroMaterial
import Mathlib.Tactic.Peel
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass

open Submodule


variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [TopologicalSpace R] [TopologicalSemiring R]
variable {X : Type*} [TopologicalSpace X] {𝕜 : Type*} [RCLike 𝕜]

-- annoying, things break below without this.
instance : IsScalarTower 𝕜 C(X, 𝕜) C(X, 𝕜) := @IsScalarTower.right _ C(X, 𝕜) _ _ _
instance : SMulCommClass 𝕜 C(X, 𝕜) C(X, 𝕜) := @Algebra.to_smulCommClass _ C(X, 𝕜) _ _ _

def ContinuousMap.evalAlgHom {X : Type*} (R : Type*) [TopologicalSpace X] [CommSemiring R]
    [TopologicalSpace R] [TopologicalSemiring R] (x : X) : C(X, R) →ₐ[R] R where
  toFun := λ f => f x
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  commutes' := fun _ => rfl

@[simps]
def ContinuousMap.evalStarAlgHom {X : Type*} (R : Type*) [TopologicalSpace X] [CommSemiring R]
    [TopologicalSpace R] [TopologicalSemiring R] [StarRing R] [ContinuousStar R] (x : X) :
    C(X, R) →⋆ₐ[R] R where
  toFun := λ f => f x
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  commutes' := fun _ => rfl
  map_star' := fun _ => rfl

open NonUnitalStarAlgebra Submodule in
lemma ContinuousMap.adjoin_id_eq_span_one_union (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      span 𝕜 ({(1 : C(s, 𝕜))} ∪ (adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))})) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, span_union, span_eq_toSubmodule]

open NonUnitalStarAlgebra Submodule Pointwise in
lemma ContinuousMap.adjoin_id_eq_span_one_add (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) + (adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} : Set C(s, 𝕜)) := by
  ext x
  rw [SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, mem_sup]
  simp [Set.mem_add]

open NonUnitalStarAlgebra in
lemma ContinuousMap.mem_ker_evalStarAlgHom_of_mem_nonUnitalStarAlgebraAdjoin_id
    {s : Set 𝕜} (h0 : 0 ∈ s) {f : C(s, 𝕜)} (hf : f ∈ adjoin 𝕜 {.restrict s (.id 𝕜)}) :
    f ∈ RingHom.ker (evalStarAlgHom 𝕜 (⟨0, h0⟩ : s)) := by
  induction hf using NonUnitalStarAlgebra.adjoin_induction' with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f _ g _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f _ g _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [RingHom.mem_ker] at hf ⊢
    rw [map_smul, hf, smul_zero]
  | star f _ hf =>
    rw [RingHom.mem_ker] at hf ⊢
    rw [map_star, hf, star_zero]

open NonUnitalStarAlgebra Submodule in
lemma ContinuousMap.ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) :
    (StarAlgebra.adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} : Set C(s, 𝕜)) ∩
      RingHom.ker (evalStarAlgHom 𝕜 (⟨0, h0⟩ : s)) =
        adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} := by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := mem_ker_evalStarAlgHom_of_mem_nonUnitalStarAlgebraAdjoin_id h0 hf
    rw [RingHom.mem_ker, evalStarAlgHom_apply] at hf₂ this
    rw [add_apply, this, add_zero, smul_apply, one_apply, smul_eq_mul, mul_one] at hf₂
    rwa [hf₂, zero_smul, zero_add]
  · simp only [Set.mem_inter_iff, SetLike.mem_coe]
    refine fun hf ↦ ⟨?_, mem_ker_evalStarAlgHom_of_mem_nonUnitalStarAlgebraAdjoin_id h0 hf⟩
    exact NonUnitalStarAlgebra.adjoin_le_starAlgebra_adjoin _ _ hf

attribute [fun_prop] continuous_algebraMap ContinuousMap.continuous_eval_const

-- the statement should be in terms of non unital subalgebras, but we lack API
-- TODO : this is a bad name
open RingHom Filter Topology in
theorem AlgHom.closure_ker_inter {F S K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace A] [ContinuousSub A] [ContinuousSMul K A]
    [FunLike F A K] [AlgHomClass F K A K] [SetLike S A] [OneMemClass S A] [AddSubgroupClass S A]
    [SMulMemClass S K A] (φ : F) (hφ : Continuous φ) (s : S) :
    closure (s ∩ RingHom.ker φ) = closure s ∩ (ker φ : Set A) := by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt, ClusterPt] at hxs
    have : Tendsto (fun y ↦ y - φ y • 1) (𝓝 x ⊓ 𝓟 s) (𝓝 x) := by
      conv => congr; rfl; rfl; rw [← sub_zero x, ← zero_smul K 1, ← hxφ]
      exact Filter.tendsto_inf_left (Continuous.tendsto (by fun_prop) x)
    refine mem_closure_of_tendsto this <| eventually_inf_principal.mpr ?_
    filter_upwards [] with g hg using
      ⟨sub_mem hg (SMulMemClass.smul_mem _ <| one_mem _), by simp [RingHom.mem_ker]⟩

-- should generalize this
open Polynomial in
lemma ContinuousMap.restrict_id_eq_polynomial_toContinuousMap_X (s : Set 𝕜) :
    restrict s (.id 𝕜) = Polynomial.X.toContinuousMapOn s := by
  ext; simp

open NonUnitalStarAlgebra in
lemma ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s)
    [CompactSpace s] :
    (RingHom.ker (evalStarAlgHom 𝕜 (⟨0, h0⟩ : s)) : Set C(s, 𝕜)) =
      closure (adjoin 𝕜 {(restrict s (.id 𝕜))}) := by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0,
    AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 (X := s) ⟨0, h0⟩) (continuous_eval_const _) _]
  convert (Set.univ_inter _).symm
  rw [restrict_id_eq_polynomial_toContinuousMap_X, ← Polynomial.toContinuousMapOnAlgHom_apply,
    ← polynomialFunctions.starClosure_eq_adjoin_X s]
  congrm(($(polynomialFunctions.starClosure_topologicalClosure s) : Set C(s, 𝕜)))

open ContinuousMapZero

-- should we just use `Fact (0 ∈ s)` to get a `Zero s` instance? Then we wouldn't need these `h0`s.
open NonUnitalStarAlgebra in
lemma ContinuousMapZero.adjoin_id_dense {s : Set 𝕜} [Zero s] (h0 : ((0 : s) : 𝕜) = 0)
    [CompactSpace s] : Dense (adjoin 𝕜 {(.id h0 : C(s, 𝕜)₀)} : Set C(s, 𝕜)₀) := by
  have h0' : 0 ∈ s := h0 ▸ (0 : s).property
  -- should move this out elsewhere
  have : T2Space C(s, 𝕜)₀ := inferInstance -- closedEmbedding_toContinuousMapHom.toEmbedding.t2Space
  rw [dense_iff_closure_eq,
    ← closedEmbedding_toContinuousMap.injective.preimage_image (closure _),
    ← closedEmbedding_toContinuousMap.closure_image_eq, ← coe_toContinuousMapHom,
    ← NonUnitalStarSubalgebra.coe_map, NonUnitalStarAlgHom.map_adjoin_singleton,
    toContinuousMapHom_apply, toContinuousMap_id h0,
    ← ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id s h0']
  apply Set.eq_univ_of_forall fun f ↦ ?_
  simp only [Set.mem_preimage, toContinuousMapHom_apply, SetLike.mem_coe, RingHom.mem_ker,
    ContinuousMap.evalStarAlgHom_apply, ContinuousMap.coe_coe]
  rw [show ⟨0, h0'⟩ = (0 : s) by ext; exact h0.symm, _root_.map_zero f]
