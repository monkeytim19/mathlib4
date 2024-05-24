/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.CFCNonUnital.NonUnitalInstance
import Mathlib.CFCNonUnital.UnitizationL1Norm
section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜]

open NonUnitalStarAlgebra in
theorem RCLike.uniqueNonUnitalContinuousFunctionalCalculus_of_compactSpace_quasispectrum
    [TopologicalSpace A] [T2Space A] [NonUnitalRing A] [StarRing A] [Module 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [h : ∀ a : A, CompactSpace (quasispectrum 𝕜 a)] :
    UniqueNonUnitalContinuousFunctionalCalculus 𝕜 A where
  eq_of_continuous_of_map_id s hs _inst h0 φ ψ hφ hψ h := by
    rw [DFunLike.ext'_iff, ← Set.eqOn_univ, ← (ContinuousMapZero.adjoin_id_dense h0).closure_eq]
    refine Set.EqOn.closure (fun f hf ↦ ?_) hφ hψ
    rw [← NonUnitalStarAlgHom.mem_equalizer]
    apply adjoin_le ?_ hf
    rw [Set.singleton_subset_iff]
    exact h
  compactSpace_quasispectrum := h

instance RCLike.instUniqueNonUnitalContinuousFunctionalCalculus [NonUnitalNormedRing A]
    [StarRing A] [CompleteSpace A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] :
    UniqueNonUnitalContinuousFunctionalCalculus 𝕜 A :=
  RCLike.uniqueNonUnitalContinuousFunctionalCalculus_of_compactSpace_quasispectrum

end RCLike

section NNReal
open NNReal

variable {X : Type*} [TopologicalSpace X] [Zero X]

namespace ContinuousMapZero

instance {R : Type*} [TopologicalSpace R] [CommSemiring R] [StarRing R] [TopologicalSemiring R]
    [ContinuousStar R] [TrivialStar R] : TrivialStar C(X, R)₀ where
  star_trivial _ := DFunLike.ext _ _ fun _ ↦ star_trivial _


/-- This map sends `f : C(X, ℝ)` to `Real.toNNReal ∘ f`, bundled as a continuous map `C(X, ℝ≥0)`. -/
@[pp_dot]
noncomputable def toNNReal (f : C(X, ℝ)₀) : C(X, ℝ≥0)₀ := ⟨.realToNNReal |>.comp f, by simp⟩

@[simp]
lemma toNNReal_apply (f : C(X, ℝ)₀) (x : X) : f.toNNReal x = Real.toNNReal (f x) := rfl

@[fun_prop]
lemma continuous_toNNReal : Continuous (toNNReal (X := X)) := by
  rw [continuous_induced_rng]
  exact ContinuousMap.continuous_comp _ |>.comp continuous_induced_dom

@[simp]
lemma toContinuousMap_toNNReal (f : C(X, ℝ)₀) : (f : C(X, ℝ)).toNNReal = f.toNNReal := rfl


lemma toContinuousMap_injective' {Y : Type*} [TopologicalSpace Y] [Zero Y] :
    Function.Injective ((↑) : C(X, Y)₀ → C(X, Y)) := by
  intro f g h
  ext x
  exact congr($(h) x)

@[simp]
lemma toNNReal_smul (r : ℝ≥0) (f : C(X, ℝ)₀) : (r • f).toNNReal = r • f.toNNReal := by
  ext x
  by_cases h : 0 ≤ f x
  · simpa [max_eq_left h, NNReal.smul_def] using mul_nonneg r.coe_nonneg h
  · push_neg at h
    simpa [max_eq_right h.le, NNReal.smul_def]
      using mul_nonpos_of_nonneg_of_nonpos r.coe_nonneg h.le

@[simp]
lemma toNNReal_neg_smul (r : ℝ≥0) (f : C(X, ℝ)₀) : (-(r • f)).toNNReal = r • (-f).toNNReal := by
  rw [NNReal.smul_def, ← smul_neg, ← NNReal.smul_def, toNNReal_smul]


--@[simp]
--lemma toNNReal_algebraMap (r : ℝ≥0) :
    --(algebraMap ℝ C(X, ℝ) r).toNNReal = algebraMap ℝ≥0 C(X, ℝ≥0) r := by
  --ext; simp

--@[simp]
--lemma toNNReal_neg_algebraMap (r : ℝ≥0) : (- algebraMap ℝ C(X, ℝ) r).toNNReal = 0 := by
  --ext; simp

--@[simp]
--lemma toNNReal_one : (1 : C(X, ℝ)).toNNReal = 1 := toNNReal_algebraMap 1

--@[simp]
--lemma toNNReal_neg_one : (-1 : C(X, ℝ)).toNNReal = 0 := toNNReal_neg_algebraMap 1

end ContinuousMapZero

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalRing A]

namespace NonUnitalStarAlgHom

open ContinuousMapZero

set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 300000
/-- Given a non-unital star `ℝ≥0`-algebra homomorphism `φ` from `C(X, ℝ≥0)₀` into a non-unital
`ℝ`-algebra `A`, this is the unique extension of `φ` from `C(X, ℝ)₀` to `A` as a non-unital
star `ℝ`-algebra homomorphism. -/
@[simps]
noncomputable def realContinuousMapZeroOfNNReal (φ : C(X, ℝ≥0)₀ →⋆ₙₐ[ℝ≥0] A) :
    C(X, ℝ)₀ →⋆ₙₐ[ℝ] A where
  toFun f := φ f.toNNReal - φ (-f).toNNReal
  map_zero' := by simp
  map_mul' f g := by
    have := (f : C(X, ℝ)).toNNReal_mul_add_neg_mul_add_mul_neg_eq g
    simp_rw [← toContinuousMapHom_apply, ← map_mul, ← map_neg, toContinuousMapHom_apply,
      toContinuousMap_toNNReal, ← toContinuousMapHom_apply, ← map_mul, ← map_add,
      toContinuousMapHom_apply] at this
    have := congr(φ $(toContinuousMap_injective' this))
    simp only [map_add, map_mul, sub_mul, mul_sub] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    convert this using 1
    abel
  map_add' f g := by
    have := (f : C(X, ℝ)).toNNReal_add_add_neg_add_neg_eq g
    simp_rw [← toContinuousMapHom_apply, ← map_add, ← map_neg, toContinuousMapHom_apply,
      toContinuousMap_toNNReal, ← toContinuousMapHom_apply, ← map_add,
      toContinuousMapHom_apply] at this
    have := congr(φ $(toContinuousMap_injective' this))
    simp only [map_add, map_mul, sub_mul, mul_sub] at this ⊢
    rw [← sub_eq_zero] at this ⊢
    convert this using 1
    abel
  map_smul' r f := by
    simp only [MonoidHom.id_apply]
    by_cases hr : 0 ≤ r
    · lift r to ℝ≥0 using hr
      simp [← NNReal.smul_def, smul_sub]
    · rw [not_le, ← neg_pos] at hr
      rw [← neg_smul]
      nth_rw 1 [← neg_neg r]
      nth_rw 3 [← neg_neg r]
      lift -r to ℝ≥0 using hr.le with r
      simp only [neg_smul, ← smul_def, toNNReal_neg_smul, map_smul, toNNReal_smul, smul_sub,
        sub_neg_eq_add]
      rw [sub_eq_add_neg, add_comm]
  map_star' f := by simp only [star_trivial, star_sub, ← map_star]

@[simp]
lemma ContinuousMapZero.coe_neg {X R : Type*} [TopologicalSpace X] [Zero X]
    [TopologicalSpace R] [CommRing R] [TopologicalRing R] (f : C(X, R)₀) : ⇑(-f) = -⇑f :=
  rfl

instance : ContinuousNeg C(X, ℝ)₀ where
  continuous_neg := by
    rw [continuous_induced_rng]
    exact continuous_neg.comp continuous_induced_dom

@[fun_prop]
lemma continuous_realContinuousMapZeroOfNNReal (φ : C(X, ℝ≥0)₀ →⋆ₙₐ[ℝ≥0] A)
    (hφ : Continuous φ) : Continuous φ.realContinuousMapZeroOfNNReal := by
  simp [realContinuousMapZeroOfNNReal]
  fun_prop

@[simp high]
lemma realContinuousMapZeroOfNNReal_apply_comp_toReal (φ : C(X, ℝ≥0)₀ →⋆ₙₐ[ℝ≥0] A)
    (f : C(X, ℝ≥0)₀) :
    φ.realContinuousMapZeroOfNNReal ((ContinuousMapZero.mk ⟨toReal, continuous_coe⟩ rfl).comp f) = φ f := by
  simp only [realContinuousMapZeroOfNNReal_apply]
  convert_to φ f - φ 0 = φ f using 2
  on_goal -1 => rw [map_zero, sub_zero]
  all_goals
    congr
    ext x
    simp



lemma realContinuousMapZeroOfNNReal_injective :
    Function.Injective (realContinuousMapZeroOfNNReal (X := X) (A := A)) := by
  intro φ ψ h
  ext f
  simpa using congr($(h) ((ContinuousMapZero.mk ⟨toReal, continuous_coe⟩ rfl).comp f))

end NonUnitalStarAlgHom

open ContinuousMapZero

@[simps]
def ContinuousMapZero.nonUnitalStarAlgHomPrecomp {X Y : Type*} (R : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [Zero X] [Zero Y] [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] (f : C(X, Y)₀) :
    C(Y, R)₀ →⋆ₙₐ[R] C(X, R)₀ where
  toFun g := g.comp f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl


instance NNReal.instUniqueNonUnitalContinuousFunctionalCalculus
    [UniqueNonUnitalContinuousFunctionalCalculus ℝ A] :
    UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A where
  compactSpace_quasispectrum a := by
    have : CompactSpace (quasispectrum ℝ a) :=
      UniqueNonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum a
    rw [← isCompact_iff_compactSpace] at *
    rw [← quasispectrum.preimage_algebraMap ℝ]
    exact closedEmbedding_subtype_val isClosed_nonneg |>.isCompact_preimage <| by assumption
  eq_of_continuous_of_map_id s hs _inst h0 φ ψ hφ hψ h := by
    let s' : Set ℝ := (↑) '' s
    let e : s ≃ₜ s' :=
      { toFun := Subtype.map (↑) (by simp [s'])
        invFun := Subtype.map Real.toNNReal (by simp [s'])
        left_inv := fun _ ↦ by ext; simp
        right_inv := fun x ↦ by
          ext
          obtain ⟨y, -, hy⟩ := x.2
          simpa using hy ▸ NNReal.coe_nonneg y
        continuous_toFun := continuous_coe.subtype_map (by simp [s'])
        continuous_invFun := continuous_real_toNNReal.subtype_map (by simp [s']) }
    let _inst₁ : Zero s' := ⟨0, ⟨0, h0 ▸ Subtype.property (0 : s), coe_zero⟩⟩
    have h0' : ((0 : s') : ℝ) = 0 := rfl
    have e0 : e 0 = 0 := by ext; simp [e, h0, h0']
    have e0' : e.symm 0 = 0 := by
      simpa only [Homeomorph.symm_apply_apply] using congr(e.symm $(e0)).symm
    have (ξ : C(s, ℝ≥0)₀ →⋆ₙₐ[ℝ≥0] A) (hξ : Continuous ξ) :
        (let ξ' := ξ.realContinuousMapZeroOfNNReal.comp <| ContinuousMapZero.nonUnitalStarAlgHomPrecomp ℝ ⟨e, e0⟩;
        Continuous ξ' ∧ ξ' (ContinuousMapZero.id h0') = ξ (ContinuousMapZero.id h0)) := by
      intro ξ'
      refine ⟨ξ.continuous_realContinuousMapZeroOfNNReal hξ |>.comp <|
        ?_, ?_⟩
      · rw [continuous_induced_rng]
        exact ContinuousMap.continuous_comp_left _ |>.comp continuous_induced_dom
      · exact ξ.realContinuousMapZeroOfNNReal_apply_comp_toReal (.id h0)
    obtain ⟨hφ', hφ_id⟩ := this φ hφ
    obtain ⟨hψ', hψ_id⟩ := this ψ hψ
    have hs' : CompactSpace s' := e.compactSpace
    have h' := UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id s' h0' _ _ hφ' hψ'
      (hφ_id ▸ hψ_id ▸ h)
    have h'' := congr($(h').comp <| ContinuousMapZero.nonUnitalStarAlgHomPrecomp ℝ ⟨(e.symm : C(s', s)), e0'⟩)
    have : (ContinuousMapZero.nonUnitalStarAlgHomPrecomp ℝ ⟨(e : C(s, s')), e0⟩).comp
        (ContinuousMapZero.nonUnitalStarAlgHomPrecomp ℝ ⟨(e.symm : C(s', s)), e0'⟩) =
        NonUnitalStarAlgHom.id _ _ := by
      ext; simp
    simp only [NonUnitalStarAlgHom.comp_assoc, this, NonUnitalStarAlgHom.comp_id] at h''
    exact NonUnitalStarAlgHom.realContinuousMapZeroOfNNReal_injective h''

end NNReal
