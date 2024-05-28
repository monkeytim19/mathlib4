import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero
import Mathlib.Topology.Algebra.Algebra

open Set Topology TopologicalSpace Function Uniformity

theorem Set.exists_image2_iff {α β γ : Type*} {f : α → β → γ} {s : Set α} {t : Set β}
    {p : γ → Prop}  :
    (∃ z ∈ image2 f s t, p z) ↔ ∃ x ∈ s, ∃ y ∈ t, p (f x y) := by
  simp only [mem_image2, exists_exists_and_exists_and_eq_and]

section MissingHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simps]
def ContinuousMap.inl : C(X, X ⊕ Y) where
  toFun := Sum.inl

@[simps]
def ContinuousMap.inr : C(Y, X ⊕ Y) where
  toFun := Sum.inr

@[simps]
def ContinuousMap.sumElim (f : C(X, Z) × C(Y, Z)) : C(X ⊕ Y, Z) where
  toFun := Sum.elim f.1 f.2

def Homeomorph.sumCompl {s : Set X} [DecidablePred (· ∈ s)] (hs : IsClopen s) :
    s ⊕ (sᶜ : Set X) ≃ₜ X :=
  .homeomorphOfContinuousOpen (Equiv.Set.sumCompl s)
    (by rw [continuous_sum_dom]; exact ⟨continuous_subtype_val, continuous_subtype_val⟩)
    (by
      rw [isOpenMap_sum]
      exact ⟨hs.isOpen.isOpenMap_subtype_val, hs.compl.isOpen.isOpenMap_subtype_val⟩)

variable (X Y Z) in
@[simps]
def ContinuousMap.sumEquiv :
    C(X, Z) × C(Y, Z) ≃ C(X ⊕ Y, Z) where
  toFun := ContinuousMap.sumElim
  invFun f := ⟨f.comp .inl, f.comp .inr⟩
  left_inv f := rfl
  right_inv f := ext <| by rintro (x|y) <;> rfl

-- variable (X Y Z) in
-- def ContinuousMap.sumHomeomorph :
--     C(X, Z) × C(Y, Z) ≃ₜ C(X ⊕ Y, Z) where
--   toEquiv := ContinuousMap.sumEquiv X Y Z
--   continuous_toFun := continuous_compactOpen.mpr fun K hK U hU ↦ by
--     sorry
--   continuous_invFun := sorry

end MissingHomeomorph

section MissingCompactOpen

namespace ContinuousMap

variable {X₁ X₂ Y : Type*} (Z : Type*) {i₁ : X₁ → Y} {i₂ : X₂ → Y}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Y]
    [UniformSpace Z]

-- TODO:
-- 1) make proof cleaner (do we really need bases ? One inequality should be easy at least)
-- 2) generalize to UniformOnFun
-- 3) can we do a purely topological statement ?
lemma foo (hi₁ : ClosedEmbedding i₁) (hi₂ : ClosedEmbedding i₂) (hi : range i₁ ∪ range i₂ = univ) :
    (inferInstance : UniformSpace C(Y, Z)) =
      (.comap (fun f ↦ f.comp ⟨i₁, hi₁.continuous⟩) inferInstance)
      ⊓ (.comap (fun f ↦ f.comp ⟨i₂, hi₂.continuous⟩) inferInstance) := UniformSpace.ext <| by
  rw [@inf_uniformity C(Y, Z) (.comap _ _) (.comap _ _), uniformity_comap, uniformity_comap]
  refine hasBasis_compactConvergenceUniformity.ext
    (hasBasis_compactConvergenceUniformity.comap _ |>.inf <|
      hasBasis_compactConvergenceUniformity.comap _) ?_ ?_
  · rintro ⟨K, U⟩ ⟨hK, hU⟩
    refine ⟨⟨⟨i₁ ⁻¹' K, U⟩, ⟨i₂ ⁻¹' K, U⟩⟩,
      ⟨⟨hi₁.isCompact_preimage hK, hU⟩, ⟨hi₂.isCompact_preimage hK, hU⟩⟩,
      fun ⟨f, g⟩ ⟨hfg₁, hfg₂⟩ y hy ↦ ?_⟩
    have : y ∈ range i₁ ∪ range i₂ := hi.ge trivial
    rcases this with ⟨x₁, rfl⟩ | ⟨x₂, rfl⟩
    · exact hfg₁ x₁ hy
    · exact hfg₂ x₂ hy
  · rintro ⟨⟨K₁, U₁⟩, ⟨K₂, U₂⟩⟩ ⟨⟨hK₁, hU₁⟩, ⟨hK₂, hU₂⟩⟩
    exact ⟨⟨i₁ '' K₁ ∪ i₂ '' K₂, U₁ ∩ U₂⟩,
      ⟨hK₁.image hi₁.continuous |>.union <| hK₂.image hi₂.continuous, Filter.inter_mem hU₁ hU₂⟩,
      fun ⟨f, g⟩ hfg ↦
        ⟨fun x₁ hx₁ ↦ inter_subset_left _ U₂ <| hfg (i₁ x₁) <| .inl <| mem_image_of_mem _ hx₁,
          fun x₂ hx₂ ↦ inter_subset_right U₁ _ <| hfg (i₂ x₂) <| .inr <| mem_image_of_mem _ hx₂⟩⟩

end ContinuousMap

end MissingCompactOpen
namespace ContinuousMapZero

section Uniform

variable {X Y R : Type*} [TopologicalSpace X] [Zero X]
variable [UniformSpace R] [Zero R]

-- TODO: clean a bit
-- This is the only thing still needed from this file
lemma uniformInducing_precomp_toContinuousMap_of_almost_surj [T1Space X] [TopologicalSpace Y]
    {i : Y → X} (hi₁ : ClosedEmbedding i) (hi₂ : range i ∪ {0} = univ) :
    UniformInducing (fun f : C(X, R)₀ ↦ f.toContinuousMap.comp ⟨i, hi₁.continuous⟩) where
  comap_uniformity := by
    have := ContinuousMap.foo R hi₁ (isClosed_singleton (x := 0)).closedEmbedding_subtype_val
      (by simpa using hi₂)
    simp_rw [ContinuousMapZero.instUniformSpace, this, uniformity_comap,
      @inf_uniformity _ (.comap _ _) (.comap _ _), uniformity_comap, Filter.comap_inf,
      Filter.comap_comap]
    refine .symm <| inf_eq_left.mpr <| le_top.trans <| eq_top_iff.mp ?_
    have : ∀ U ∈ 𝓤 (C(({0} : Set X), R)), (0, 0) ∈ U := fun U hU ↦ refl_mem_uniformity hU
    convert Filter.comap_const_of_mem this with ⟨f, g⟩ <;>
    ext ⟨x, rfl⟩ <;>
    [exact map_zero f; exact map_zero g]

end Uniform

section Semiring

variable {X R : Type*} [TopologicalSpace X] [Zero X]
variable [TopologicalSpace R] [CommSemiring R] [TopologicalSemiring R]


instance instContinuousMapSMul : SMul C(X, R) C(X, R)₀ where
  smul f g₀ := ⟨f * g₀, by simp⟩

instance instContinuousMapModule : Module C(X, R) C(X, R)₀ :=
  toContinuousMap_injective.module C(X, R)
    ({ toFun := toContinuousMap, map_add' := fun _ _ ↦ rfl, map_zero' := rfl})
    fun _ _ ↦ rfl

lemma smul_coe (f : C(X, R)) (g₀ : C(X, R)₀) : f • (g₀ : C(X, R)) = ↑(f • g₀) := rfl

@[simp] lemma coe_smul' (g : C(X, R)) (f : C(X, R)₀) : ⇑(g • f) = ⇑g • ⇑f := rfl

lemma closedEmbedding_toContinuousMapHom [T1Space R] [StarRing R] [ContinuousStar R] :
    ClosedEmbedding (toContinuousMapHom (X := X) (R := R)) where
  induced := rfl
  inj f g h := ext fun x ↦ congr($(h) x)
  isClosed_range := by
    convert isClosed_singleton (x := (0 : R)) |>.preimage <|
      ContinuousMap.continuous_eval_const (0 : X)
    ext f
    simp only [Set.mem_range, toContinuousMapHom_apply, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, rfl⟩
      exact map_zero f
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩

@[simps]
def toContinuousMapHomL : C(X, R)₀ →L[C(X, R)] C(X, R) where
  toFun := toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_induced_dom

end Semiring

section Ring

variable {X R : Type*} [TopologicalSpace X] [Zero X]
variable [TopologicalSpace R] [CommRing R] [TopologicalRing R]

@[simps!]
noncomputable def ofContinuousMap : C(X, R) →L[R] C(X, R)₀ where
  toFun f := ⟨f - algebraMap R C(X, R) (f 0), by simp⟩
  map_add' f g := by ext; simp [sub_add_sub_comm]
  map_smul' r f := by ext; simp [mul_sub]
  cont := by
    simp only [continuous_induced_rng, Function.comp]
    exact continuous_id.sub <| ContinuousMap.continuous_const'.comp <|
      ContinuousMap.continuous_eval_const (0 : X)

lemma surjective_ofContinuousMap : Function.Surjective (ofContinuousMap (X := X) (R := R)) :=
  fun f ↦ ⟨f, by ext; simp⟩

-- missing instance!
instance [LocallyCompactSpace X] : TopologicalSemiring C(X, R) := by exact TopologicalSemiring.mk

-- missing `fun_prop` attributes!
attribute [fun_prop] continuous_algebraMap ContinuousMap.continuous_eval_const

lemma ofContinuousMap_of_map_zero (f₀ : C(X, R)₀) :
    ofContinuousMap (X := X) (R := R) f₀ = f₀ := by
  ext; simp

lemma ofContinuousMap_of_map_zero' (f : C(X, R)) (hf : f 0 = 0) :
    ofContinuousMap (X := X) (R := R) f = ⟨f, hf⟩ :=
  ofContinuousMap_of_map_zero ⟨f, hf⟩

@[simp]
lemma StarAlgHom.toFun_eq_coe {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    f.toFun = ⇑f :=
  rfl

open Unitization in
noncomputable def unitizationStarAlgEquiv [StarRing R] [ContinuousStar R] :
    Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R) where
  __ := starLift (toContinuousMapHom (X := X) (R := R))
  invFun := fun f ↦ algebraMap R _ (f 0) + (ContinuousMapZero.ofContinuousMap (X := X) (R := R) f)
  left_inv u := by
    ext1
    · rw [fst_add, fst_inr, add_zero, algebraMap_eq_inl, fst_inl, StarAlgHom.toFun_eq_coe]
      simp
    · ext x
      simp [algebraMap_eq_inl]
  right_inv f := by
    ext x
    simp only [StarAlgHom.toFun_eq_coe, starLift_apply_apply]
    simp [algebraMap_eq_inl]
  map_smul' r u := (starLift (toContinuousMapHom (X := X) (R := R))).map_smul r u

end Ring
