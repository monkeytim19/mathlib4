/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.CFCNonUnital.ContinuousMapZeroMaterial
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus
namespace ContinuousMapZero

variable {X Y M R S : Type*} [Zero X] [Zero Y] [CommSemiring M]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R] [TopologicalSpace S]
  [CommSemiring R] [StarRing R] [TopologicalSemiring R] [ContinuousStar R]
  [CommSemiring S] [StarRing S] [TopologicalSemiring S] [ContinuousStar S]
  [Module M R] [Module M S] [ContinuousConstSMul M R] [ContinuousConstSMul M S]

variable (R) in
@[simps]
def nonUnitalStarAlgHom_precomp (f : C(X, Y)₀) : C(Y, R)₀ →⋆ₙₐ[R] C(X, R)₀ where
  toFun g := g.comp f
  map_zero' := ext fun _ ↦ rfl
  map_add' _ _ := ext <| by simp
  map_mul' _ _ := ext <| by simp
  map_star' _ := ext <| by simp
  map_smul' _ _ := ext <| by simp

@[simp]
lemma smul_apply (m : M) (f : C(X, R)₀) (x : X) : (m • f) x = m • f x := rfl

variable (X) in
@[simps apply]
def nonUnitalStarAlgHom_postcomp (φ : R →⋆ₙₐ[M] S) (hφ : Continuous φ) :
    C(X, R)₀ →⋆ₙₐ[M] C(X, S)₀ where
  toFun := .comp ⟨⟨φ, hφ⟩, by simp⟩
  map_zero' := ext <| by simp
  map_add' _ _ := ext <| by simp
  map_mul' _ _ := ext <| by simp
  map_star' _ := ext <| by simp [map_star]
  map_smul' r f := ext <| by simp

end ContinuousMapZero

namespace QuasispectrumRestricts

local notation "σₙ" => quasispectrum
open ContinuousMapZero Set

/-- The homeomorphism `spectrum S a ≃ₜ spectrum R a` induced by `SpectrumRestricts a f`. -/
def homeomorph {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] [IsScalarTower S A A] [SMulCommClass S A A]
    {a : A} {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    σₙ S a ≃ₜ σₙ R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
  left_inv x := Subtype.ext <| h.rightInvOn x.2
  right_inv x := Subtype.ext <| h.left_inv x
  continuous_toFun := continuous_induced_rng.mpr <| f.continuous.comp continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr <|
    continuous_algebraMap R S |>.comp continuous_induced_dom

universe u v w

open ContinuousMapZero
/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
def nonUnitalStarAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [Field S]
    [StarRing S] [TopologicalSpace S] [TopologicalRing S] [ContinuousStar S] [NonUnitalRing A]
    [StarRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A) {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (nonUnitalStarAlgHom_postcomp (σₙ S a) (StarAlgHom.ofId R S) (algebraMapCLM R S).continuous).comp <|
      nonUnitalStarAlgHom_precomp R
        ⟨⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x ∈ σₙ S a) => h.subset_preimage hx⟩, Subtype.ext h.map_zero⟩

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
variable [Field S] [StarRing S] [MetricSpace S] [TopologicalRing S] [ContinuousStar S]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]
variable [SMulCommClass S A A] [NonUnitalContinuousFunctionalCalculus S q]
variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
variable [CompleteSpace R]

lemma closedEmbedding_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A}
    (hφ : ClosedEmbedding φ) {f : C(S, R)} (h : QuasispectrumRestricts a f)
    (halg : UniformEmbedding (algebraMap R S)) [h_cpct : CompactSpace (σₙ S a)] :
    ClosedEmbedding (h.nonUnitalStarAlgHom φ) := by
  have := h.compactSpace
  have : CompleteSpace C(σₙ R a, R)₀ := sorry -- PR#12992
  have : T0Space C(σₙ S a, S)₀ := sorry -- PR#12992
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
  refine hφ.comp <| UniformEmbedding.toClosedEmbedding <| .comp
    (ContinuousMapZero.uniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.uniformEmbedding)

lemma nonUnitalStarAlgHom_id {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A} {f : C(S, R)}
    (h : QuasispectrumRestricts a f) (h_id : φ (.id rfl) = a) :
    h.nonUnitalStarAlgHom φ (.id rfl) = a := by
  simp only [QuasispectrumRestricts.nonUnitalStarAlgHom_apply]
  convert h_id
  ext x
  exact h.rightInvOn x.2

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Given a `ContinuousFunctionalCalculus S q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R p`. -/
protected theorem cfc (f : C(S, R)) (halg : UniformEmbedding (algebraMap R S))
    (h : ∀ a, p a ↔ q a ∧ QuasispectrumRestricts a f) (h_cpct : ∀ a, q a → CompactSpace (σₙ S a)) :
    NonUnitalContinuousFunctionalCalculus R p where
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.nonUnitalStarAlgHom (cfcₙHom ((h a).mp ha).1 (R := S)),
      ?hom_closedEmbedding, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_closedEmbedding =>
      exact ((h a).mp ha).2.closedEmbedding_nonUnitalStarAlgHom (cfcₙHom_closedEmbedding ((h a).mp ha).1)
        halg (h_cpct := h_cpct a ((h a).mp ha).1)
    case hom_id => exact ((h a).mp ha).2.nonUnitalStarAlgHom_id <| cfcₙHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      intro g
      rw [nonUnitalStarAlgHom_apply]
      simp only [← @quasispectrum.preimage_algebraMap (R := R) S, cfcₙHom_map_quasispectrum]
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have := congr_arg f hy
        simp only [nonUnitalStarAlgHom_postcomp_apply, NonUnitalStarAlgHom.coe_coe,
          Function.comp_apply, comp_apply, coe_mk, ContinuousMap.coe_mk, StarAlgHom.ofId_apply]
          at this
        rw [((h a).mp ha).2.left_inv _, ((h a).mp ha).2.left_inv _] at this
        exact ⟨_, this⟩
      · rintro ⟨y, rfl⟩
        rw [Set.mem_preimage]
        refine' ⟨⟨algebraMap R S y, quasispectrum.algebraMap_mem S y.prop⟩, _⟩
        simp only [nonUnitalStarAlgHom_postcomp_apply, NonUnitalStarAlgHom.coe_coe,
          Function.comp_apply, comp_apply, coe_mk, ContinuousMap.coe_mk, StarAlgHom.ofId_apply]
        congr
        exact Subtype.ext (((h a).mp ha).2.left_inv y)
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcₙHom_predicate _ _, ?_⟩
      refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
      rw [nonUnitalStarAlgHom_apply,
        cfcₙHom_map_quasispectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [NonUnitalContinuousFunctionalCalculus R p]
variable [UniqueNonUnitalContinuousFunctionalCalculus R A]

lemma cfcₙHom_eq_restrict (f : C(S, R)) (halg : UniformEmbedding (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : QuasispectrumRestricts a f) [CompactSpace (σₙ S a)] :
    cfcₙHom hpa = h.nonUnitalStarAlgHom (cfcₙHom hqa) := by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact h.closedEmbedding_nonUnitalStarAlgHom (cfcₙHom_closedEmbedding hqa) halg |>.continuous
  · exact h.nonUnitalStarAlgHom_id (cfcₙHom_id hqa)

lemma cfc_eq_restrict (f : C(S, R)) (halg : UniformEmbedding (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : QuasispectrumRestricts a f) [CompactSpace (σₙ S a)] (g : R → R) :
    cfcₙ g a = cfcₙ (fun x ↦ algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · obtain ⟨hg, hg0⟩ := hg
    rw [cfcₙ_apply g a, cfcₙHom_eq_restrict f halg hpa hqa h, nonUnitalStarAlgHom_apply,
      cfcₙHom_eq_cfcₙ_extend 0]
    apply cfcₙ_congr fun x hx ↦ ?_
    lift x to σₙ S a using hx
    simp [Function.comp, Subtype.val_injective.extend_apply]
  · simp only [not_and_or] at hg
    obtain (hg | hg) := hg
    · have : ¬ ContinuousOn (fun x ↦ algebraMap R S (g (f x)) : S → S) (σₙ S a) := by
        refine fun hg' ↦ hg ?_
        rw [halg.embedding.continuousOn_iff]
        simpa [halg.embedding.continuousOn_iff, Function.comp, h.left_inv _] using
          hg'.comp halg.embedding.continuous.continuousOn
          (fun _ : R ↦ quasispectrum.algebraMap_mem S)
      rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn a this]
    · rw [cfcₙ_apply_of_not_map_zero a hg, cfcₙ_apply_of_not_map_zero a (by simpa [h.map_zero])]

end QuasispectrumRestricts
