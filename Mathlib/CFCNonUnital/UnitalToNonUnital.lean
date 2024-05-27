import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus
import Mathlib.CFCNonUnital.ContinuousMapZeroMaterial

section Generic

open ContinuousMapZero Set

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R] [CompleteSpace R]
variable [TopologicalRing R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
variable [Algebra R A] [ContinuousFunctionalCalculus R p]
variable [h_cpct : ∀ a : A, CompactSpace (spectrum R a)]

lemma ContinuousFunctionalCalculus.toNonUnital : NonUnitalContinuousFunctionalCalculus R p where
  exists_cfc_of_predicate a ha := by
    -- Should this be a lemma ?
    have h_cpct' : CompactSpace (quasispectrum R a) := by
      specialize h_cpct a
      simp_rw [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
      exact h_cpct.union isCompact_singleton
    let e := ContinuousMapZero.toContinuousMapHom (X := quasispectrum R a) (R := R)
    let f : C(spectrum R a, quasispectrum R a) :=
      ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
    let ψ := ContinuousMap.compStarAlgHom' R R f
    let ψ' := (cfcHom ha (R := R) : C(spectrum R a, R) →⋆ₙₐ[R] A).comp <|
      (ψ : C(quasispectrum R a, R) →⋆ₙₐ[R] C(spectrum R a, R)).comp e
    refine ⟨ψ', ?closedEmbedding, ?map_id, ?map_spectrum, ?predicate⟩
    case closedEmbedding =>
      refine (cfcHom_closedEmbedding ha).comp <|
        (UniformInducing.uniformEmbedding ?_).toClosedEmbedding
      have : ClosedEmbedding f := Continuous.closedEmbedding f.continuous <| inclusion_injective <|
        spectrum_subset_quasispectrum R a
      refine uniformInducing_precomp_toContinuousMap_of_almost_surj this ?_
      simp only [← Subtype.val_injective.image_injective.eq_iff, image_union, image_singleton,
        ← range_comp, image_univ, f, ContinuousMap.coe_mk, val_comp_inclusion, Subtype.range_coe,
        quasispectrum.coe_zero, quasispectrum_eq_spectrum_union_zero]
    case map_id => exact cfcHom_id ha
    case map_spectrum =>
      intro f
      simp only [ψ']
      rw [quasispectrum_eq_spectrum_union_zero]
      simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
        NonUnitalStarAlgHom.coe_coe]
      rw [cfcHom_map_spectrum ha]
      ext x
      constructor
      · rintro (⟨x, rfl⟩ | rfl)
        · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩, rfl⟩
        · exact ⟨0, map_zero f⟩
      · rintro ⟨x, rfl⟩
        have hx := x.2
        simp_rw [quasispectrum_eq_spectrum_union_zero R a] at hx
        obtain (hx | hx) := hx
        · exact Or.inl ⟨⟨x.1, hx⟩, rfl⟩
        · apply Or.inr
          simp only [Set.mem_singleton_iff] at hx ⊢
          rw [show x = 0 from Subtype.val_injective hx, map_zero]
    case predicate => exact fun f ↦ cfcHom_predicate ha _

end Generic
