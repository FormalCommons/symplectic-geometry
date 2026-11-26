/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.ChernClass
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.LinearSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass

import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Line
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.Submodule
import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.EulerClass
import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.ComplexLinear
import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
import TauCeti.LinearAlgebra.Matrix.Rank.Closed
import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
import SymplecticGeometry.Geometry.Manifold.Projectivization.ChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality

/-!
# The degree of a smooth projective hypersurface

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d` and positive dimension `n`,
with inclusion `ι = X.embedding`, and let `h` be the hyperplane class of `ℂℙⁿ⁺¹`. This file proves
`⟨(ι^* h) ^ n, [X]⟩ = d`, the fundamental class being that of the complex orientation of `X`
(`SymplecticGeometry.complexManifoldEvalFundamentalClass`).

The class `(ι^* h) ^ n` is the top Chern class of `ι^* 𝒪(1)^{⊕n}`, by the Whitney sum formula
for `𝒪(1)^{⊕n}` (`Projectivization.totalChernClass_twistPiCore`) and naturality, hence its Euler
class (`SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass`). Pairing the Euler class
with `[X]` adds up, over the zeros of a section with finitely many zeros, its index at each
(`SymplecticGeometry.complexManifoldEvalFundamentalClass_complexEulerClass_eq_sum_sectionIndex`,
a form of Tau Ceti's
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`). The
section is the one given by a tuple `ℓ` of `n` linear forms on `ℂⁿ⁺²`, whose zeros are the points
of `X` on the line `{ℓ = 0}`; it is chosen by Tau Ceti's theorem on generic sections
(`ContMDiffSection.mem_residual_setOf_regular_and_finite_zero_affineFamily`), whose residual set
of parameters, being dense, meets the nonempty open set of surjective tuples. For such a tuple:

* each zero is transverse, and there the derivative of the section is a complex isomorphism
  (`exists_continuousLinearEquiv_hasFDerivAt_trivializationAt_linearSection`),
  so its index is `1`
  (`SymplecticGeometry.sectionIndex_eq_one_of_complexLinear`);
* the line `{ℓ = 0}` is transverse to `X`, so it meets `X` in `d` points
  (`SymplecticGeometry.SmoothProjectiveHypersurface.card_inter_line`).

## Main results

The following are in the namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

* `complexEulerClass_twistPiCore_pullback`: the Euler class of `ι^* 𝒪(1)^{⊕(r+1)}` is
  `(ι^* h) ^ (r + 1)`.
* `exists_surjective_linearSection_regular`: some surjective `ℓ : ℂⁿ⁺² → ℂⁿ` gives a section
  of `ι^* 𝒪(1)^{⊕n}` that is transverse to zero, with finitely many zeros.
* `card_setOfPred_linearSection_eq_zero`: for surjective `ℓ` whose section is transverse to zero,
  that section has exactly `d` zeros.
* `evalFundamentalClass_hyperplaneClass_pow`: `⟨(ι^* h) ^ n, [X]⟩ = d` for `n ≠ 0`, written for a
  hypersurface of dimension `n + 1`. The case `n = 0`, where the pairing is read as a count of
  points, is `SmoothProjectiveHypersurface.card_eq`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.3 and Exercise 4.4.6.
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2 and Chapter 1, §1.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 and §14 (the Euler class as a sum of indices of a section, and the top
  Chern class as the Euler class).
-/

public section

open Bundle Module Projectivization SymplecticGeometry.Bundle TauCeti
open scoped LinearAlgebra.Projectivization Manifold VectorBundle.ComplexToReal

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- **The Euler class of `ι^* 𝒪(1)^{⊕(r+1)}`.** On a smooth projective hypersurface `X`, the Euler
class of the pull-back of `𝒪(1) ⊗ ℂ^{r+1}` by the inclusion, read in integral cohomology, is
`(ι^* h) ^ (r + 1)`. -/
theorem complexEulerClass_twistPiCore_pullback (r : ℕ) :
    ((TopCat.of X).uliftIntegralCohomologyIso (2 * r + 2)).hom
        (complexEulerClass (Fin (r + 1) → ℂ)
          (X.embedding *ᵖ (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 (Fin (r + 1))).Fiber)
          (finrank_fin_fun ℂ)) =
      ((TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass ^ (r + 1)) (r + 1) := by
  rw [← chernClass_finrank_eq_complexEulerClass, ← totalChernClass_apply]
  refine (congrArg (· (r + 1)) (totalChernClass_pullback (G := Fin (r + 1) → ℂ)
    (E := (twistPiCore (𝕜 := ℂ) (n := n + 1) 1 (Fin (r + 1))).Fiber)
    X.embedding.toContinuousMap)).trans ?_
  dsimp only
  rw [totalChernClass_twistPiCore, one_smul, map_pow, map_add, map_one,
    evenIntegralCohomologyMap_hyperplaneClass]
  -- The component of degree `r + 1` of `(1 + ι^* h) ^ (r + 1)` is that of `(ι^* h) ^ (r + 1)`.
  rw [TopCat.one_add_evenIntegralCohomologyOf_pow_apply, Nat.choose_self, Nat.cast_one, one_smul]

open scoped TauCeti.ComplexManifold in
/-- **A generic tuple of linear forms.** Some surjective `ℓ : ℂⁿ⁺² → ℂⁿ` gives a section of
`ι^* 𝒪(1)^{⊕n}` whose linearization, over the underlying real manifold of `X`, is surjective at
each of its zeros, and which has finitely many zeros. -/
theorem exists_surjective_linearSection_regular :
    ∃ ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ, Function.Surjective ℓ ∧
      (∀ z, X.linearSection ℓ z = 0 → Function.Surjective
        (sectionLinearization 𝓘(ℝ, Fin n → ℂ) (F := Fin n → ℂ) id
          (X.linearSection ℓ) z)) ∧ {x | X.linearSection ℓ x = 0}.Finite := by
  -- The real family of the forms `x_j c e_k`, for `c ∈ {1, i}`, whose sections span every fibre.
  set f : Fin (n + 2) × Fin n × Fin 2 → (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ := fun p ↦
    (LinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) p.1).smulRight
      (Pi.single p.2.1 (Complex.basisOneI p.2.2))
  set ℓ : (Fin (n + 2) × Fin n × Fin 2 → ℝ) → (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ :=
    fun a ↦ ∑ p, a p • f p
  have hℓ (a) (v : Fin (n + 2) → ℂ) (k : Fin n) : ℓ a v k =
      ∑ p, a p • (v p.1 * Pi.single (M := fun _ ↦ ℂ) p.2.1 (Complex.basisOneI p.2.2) k) := by
    simp [ℓ, f, LinearMap.sum_apply, Finset.sum_apply]
  have hres := ContMDiffSection.mem_residual_setOf_regular_and_finite_zero_affineFamily 0
    (fun p ↦ X.linearSection (f p)) X.span_range_linearSection_smulRight rfl
  have haff (a) : ContMDiffSection.affineFamily 0 (fun p ↦ X.linearSection (f p)) a =
      X.linearSection (ℓ a) := by
    ext x
    rw [ContMDiffSection.affineFamily_apply]
    simp only [ℓ, map_sum, map_smul, ContMDiffSection.coe_zero, Pi.zero_apply, zero_add]
    simp only [ContMDiffSection.coe_sum, Finset.sum_apply, ContMDiffSection.coe_smul, Pi.smul_apply]
  -- The parameters giving a surjective tuple of forms form a nonempty open set.
  have hU : IsOpen {a | Function.Surjective (ℓ a)} := by
    have hc : Continuous fun a ↦ LinearMap.toMatrix' (ℓ a) :=
      continuous_matrix fun k j ↦ by
        simp only [LinearMap.toMatrix'_apply, hℓ]
        fun_prop
    convert Matrix.isOpen_setOfPred_mulVec_surjective.preimage hc using 1
    ext a
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show (LinearMap.toMatrix' (ℓ a)).mulVec = ℓ a from funext (LinearMap.toMatrix'_mulVec _)]
  have hU₀ : {a | Function.Surjective (ℓ a)}.Nonempty := by
    -- The forms `x_0, …, x_{n-1}`.
    refine ⟨fun p ↦ if p.1 = Fin.castLE (n := n) (m := n + 2) (by omega) p.2.1 ∧ p.2.2 = 0
      then 1 else 0, ?_⟩
    rw [Set.mem_ofPred_eq]
    convert LinearMap.funLeft_surjective_of_injective ℂ ℂ _
      (Fin.castLE_injective (m := n) (n := n + 2) (by omega)) using 2
    ext v k
    simp [hℓ, Fintype.sum_prod_type, Pi.single_apply, eq_comm]
  obtain ⟨a, haU, hareg, hafin⟩ := (dense_of_mem_residual hres).inter_open_nonempty _ hU hU₀
  refine ⟨ℓ a, haU, fun z hz ↦ ?_, by simpa only [haff] using hafin⟩
  have := isRegularSectionParameter_iff.1 hareg z (by simpa only [haff] using hz)
  simp only [haff] at this
  exact this

/-- **A transverse section given by linear forms has `d` zeros.** Let `ℓ : ℂⁿ⁺² → ℂⁿ` be
surjective, and suppose that the section of `ι^* 𝒪(1)^{⊕n}` that it gives has, over the
underlying real manifold of `X`, a surjective linearization at each of its zeros. Then that
section has exactly `d` zeros: they are the points of `X` on the line `{ℓ = 0}`, which is
transverse to `X`. -/
theorem card_setOfPred_linearSection_eq_zero {ℓ : (Fin (n + 2) → ℂ) →ₗ[ℂ] Fin n → ℂ}
    (hℓ : Function.Surjective ℓ)
    (htr : ∀ z, X.linearSection ℓ z = 0 → Function.Surjective
      (sectionLinearization 𝓘(ℝ, Fin n → ℂ) (F := Fin n → ℂ) id
        (X.linearSection ℓ) z)) :
    Nat.card {x : X | X.linearSection ℓ x = 0} = d := by
  -- The line `{ℓ = 0}` is the image of an injective `L : ℂ² → ℂⁿ⁺²` with range `ker ℓ`.
  have hk : finrank ℂ (LinearMap.ker ℓ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [LinearMap.range_eq_top.2 hℓ, finrank_top] at h
    simp only [finrank_fin_fun] at h
    omega
  obtain ⟨L, hL, hrange⟩ :=
    (LinearMap.ker ℓ).exists_linearMap_injective_range_eq (F := Fin 2 → ℂ) (by simp [hk])
  have hmem (p : ℙ ℂ (Fin (n + 2) → ℂ)) :
      p ∈ Set.range (Projectivization.map L hL) ↔ ℓ p.rep = 0 := by
    rw [mem_range_map_iff, hrange, LinearMap.mem_ker]
  have hset : Subtype.val '' {x : X | X.linearSection ℓ x = 0} =
      X.carrier ∩ Set.range (Projectivization.map L hL) := by
    rw [← Subtype.image_preimage_coe]
    congr 1
    ext x
    rw [Set.mem_ofPred_eq, linearSection_eq_zero_iff, Set.mem_preimage, hmem]
  rw [← Nat.card_image_of_injective Subtype.val_injective, hset]
  refine X.card_inter_line hL fun p hp ↦ ?_
  have hz : X.linearSection ℓ ⟨_, hp⟩ = 0 :=
    (X.linearSection_eq_zero_iff ℓ _).2 ((hmem _).1 ⟨p, rfl⟩)
  exact (X.exists_sum_mul_eval_pderiv_ne_zero_iff hL hrange (z := ⟨_, hp⟩) rfl).1
    ((X.surjective_sectionLinearization_linearSection_iff hℓ hz).1 (htr _ hz))

/-- **The degree of a hypersurface as a characteristic number.** For a smooth hypersurface
`X ⊆ ℂℙⁿ⁺²` of degree `d` and dimension `n + 1`, oriented by its complex structure
(`complexManifoldHomologicalOrientation`), the class
`(ι^* h) ^ (n + 1) ∈ H^{2n+2}(X; ℤ)` evaluated on the fundamental class of `X` is `d`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem evalFundamentalClass_hyperplaneClass_pow (X : SmoothProjectiveHypersurface (n + 1) d) :
    complexManifoldEvalFundamentalClass (Fin (n + 1) → ℂ) X (Module.finrank_fin_fun ℂ)
      (((TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass ^ (n + 1)) (n + 1)) = d := by
  obtain ⟨ℓ, hℓ, hreg, hfin⟩ := X.exists_surjective_linearSection_regular
  have hs : Continuous fun x ↦ TotalSpace.mk' (Fin (n + 1) → ℂ) x (X.linearSection ℓ x) :=
    (X.linearSection ℓ).contMDiff.continuous
  -- The pairing is that of the Euler class of `ι^* 𝒪(1)^{⊕(n+1)}`, the sum of the local indices
  -- of the section given by `ℓ`.
  rw [← X.complexEulerClass_twistPiCore_pullback n,
    complexManifoldEvalFundamentalClass_complexEulerClass_eq_sum_sectionIndex _ _ hs hfin]
  calc _ = ∑ _z ∈ hfin.toFinset, (1 : ℤ) := Finset.sum_congr rfl ?_
    _ = d := by
      rw [Finset.sum_const, nsmul_one, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq,
        X.card_setOfPred_linearSection_eq_zero hℓ hreg]
  -- Each zero is transverse, with a complex-linear derivative, so its index is `1`.
  intro z hz
  have hz0 : X.linearSection ℓ z = 0 := hfin.mem_toFinset.1 hz
  obtain ⟨A, hA⟩ := X.exists_continuousLinearEquiv_hasFDerivAt_trivializationAt_linearSection hℓ
    hz0 ((X.surjective_sectionLinearization_linearSection_iff hℓ hz0).1 (hreg z hz0))
  exact sectionIndex_eq_one_of_complexLinear (Module.finrank_fin_fun ℂ) hs hz0 _
    (mem_baseSet_trivializationAt _ _ z) A hA

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
