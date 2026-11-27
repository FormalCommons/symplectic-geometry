/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import SymplecticGeometry.Geometry.Symplectic.Moser.Field
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.Flow.TimeDependent.RestPoint
import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import TauCeti.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Topology.Sets.Opens.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Family
import SymplecticGeometry.Geometry.Symplectic.Manifold.Flat
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm

/-!
# The relative Moser theorem with prescribed first derivative

Consider closed two-forms `σ₀`, `σ₁` on a boundaryless Hausdorff second-countable manifold `M`, and
let `f : Q → M` be an embedding. Suppose that at every point `f q` the two forms coincide as forms
on the whole tangent space `T_{f q} M`, and that `σ₀` is nondegenerate there. Then
`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along` gives open sets `U₀`, `U₁`
containing `f(Q)` and a diffeomorphism `φ : U₀ → U₁` with `φ^* σ₁ = σ₀`, which fixes every point
of `f(Q)` and whose differential at each of them is the identity of `T_{f q} M`
([McDuffSalamon2017], Lemma 3.2.1, with the first-order conclusion of
[McDuffSalamon2019Errata], p. 109; [CannasdaSilva2001Lectures], Theorem 7.4). The source `Q` need
not be compact, and the image `f(Q)` need not be closed.

The proof is Moser's argument along a flow that is only partially defined.

1. Tau Ceti's relative Poincaré lemma
   (`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`, in the form of
   `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub`) gives, on a tube `W`
   around `f(Q)`, a primitive `β` of `σ₁ - σ₀` that vanishes along `f(Q)`. Since `σ₁ - σ₀`
   vanishes at the points of `f(Q)` as a form on the ambient tangent spaces, the coordinate
   expressions of `β` also have zero derivative there.
2. The tube is chosen inside the open set of points at which every form `σ₀ + s (σ₁ - σ₀)` with
   `s ∈ [0, 1]` is nondegenerate
   (`TauCeti.SmoothTwoForm.isOpen_setOfPred_forall_mem_Icc_nondegenerate`).
   This set contains `f(Q)`, where all these forms equal `σ₀`.
3. On `W`, the slices of `σ₀ + c(t) (σ₁ - σ₀)`, `c = Real.smoothTransition`, are symplectic, and
   the field `X_t = (σ_t♭)⁻¹ (-c'(t) β)` (`SymplecticGeometry.moserField`, without cutoff) is
   smooth in `(t, x)`. It solves Moser's equation
   `∂_t σ_t + L_{X_t} σ_t = 0`, vanishes along `f(Q)`, and has zero first jet there
   (`TauCeti.SmoothTwoForm.IsNondegenerate.hasFDerivAt_mpullbackWithin_interiorEquiv_symm`).
4. The time-one map of `X` is a partial diffeomorphism of `W`
   (`TauCeti.timeDependentFlowPartialDiffeomorph`) whose source contains `f(Q)`. On its source it
   pulls `σ₁` back to `σ₀` by Moser's principle along trajectories, it fixes `f(Q)`, and its
   differential there is the identity. Read in `M`, it is a diffeomorphism between its source and
   its target.

The proof adapts Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq` and
`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along` from a compactly supported cut-off
flow to the local flow. Step 3 follows the construction of the Moser field in Tau
Ceti's `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_eq` and
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact`. Step 4, and the reading of the
time-one map in `M`, follow Tau Ceti's
`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_apply_eq`.

## Main results

* `TauCeti.SmoothTwoForm.exists_partialDiffeomorph_eq_timeDependentFlowOf_moserField`: Moser's
  argument along the local flow, with the partial diffeomorphism given as the time-one map of the
  Moser field `SymplecticGeometry.moserField`, so that later arguments can read off its
  properties, such as equivariance.
* `TauCeti.SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub`: Moser's
  argument along the local flow, for a primitive `β` of `σ₁ - σ₀` on a manifold on which the
  whole segment from `σ₀` to `σ₁` is nondegenerate.
* `TauCeti.SmoothEmbedding.exists_smoothForm_relative_primitive_sub_of_eq_along`: steps 1 and 2,
  a tube around `f(Q)` on which the segment is nondegenerate, with a primitive of `σ₁ - σ₀` that
  vanishes with its first jet along `f(Q)`.
* `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along`: the relative Moser theorem with
  prescribed first derivative, for an embedding with a source that need not be compact and an
  image that need not be closed.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures]
-/

public section

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace SmoothTwoForm

omit [T2Space M] in
/-- The Moser field of the path `σ₀ + c(t) (σ₁ - σ₀)`, `c = Real.smoothTransition`, for a primitive
`β` of `σ₁ - σ₀`, on a manifold on which every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is
nondegenerate: for a one-form `α` on `ℝ × M` with slices `c'(t) β`, the field
`X_t = (σ_t♭)⁻¹(-c'(t) β)` of `SymplecticGeometry.moserField` is jointly smooth, solves Moser's
equation, vanishes where `β` does, and has zero first jet where `β` has. -/
private theorem exists_moserField {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    {β : SmoothForm I M ℝ 1} (hβ : mextDeriv β.val = (σ₁ - σ₀).val)
    (hnd : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1,
      (∀ t, SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α =
        deriv Real.smoothTransition t • β) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞ (fun p : ℝ × M ↦ (⟨p.2, SymplecticGeometry.moserField
        (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1 p.1 p.2⟩ :
          TangentBundle I M)) ∧
      (∀ x, β.val x = 0 → ∀ t, SymplecticGeometry.moserField
        (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1 t x = 0) ∧
      (∀ x, β.val x = 0 →
        HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
          (extChartAt I x x) → ∀ t,
        HasFDerivAt (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
          (SymplecticGeometry.moserField
            (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1 t) (range I))
          (0 : E →L[ℝ] E) (extChartAt I x x)) ∧
      ∀ t, mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E)))
          (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff).val) +
        mlieDerivForm (SymplecticGeometry.moserField
            (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1 t)
          (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff).val) = 0 := by
  set c : ℝ → ℝ := Real.smoothTransition
  have hc' : ContDiff ℝ ∞ (deriv c) :=
    (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2
  -- The path `σ₀ + c(t) (σ₁ - σ₀)` and the one-forms `-c'(t) β`, as forms on `ℝ × M`.
  set σ := SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff
  set α := SmoothForm.lineMapFamily (0 : SmoothForm I M ℝ 1) β hc'.neg
  have hαt (t : ℝ) : SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α =
      (-deriv c t) • β := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, zero_add, sub_zero]
  have hcl : (σ₁ - σ₀).IsClosed := by
    rw [SmoothForm.isClosed_def, ← hβ]
    exact SmoothForm.mextDeriv_mextDeriv β
  -- Since `c(t) ∈ [0, 1]`, every slice `σ_t` is symplectic.
  have hσ (t : ℝ) : IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily]
    exact ⟨h₀.add (hcl.smul _), isNondegenerate_def.2 fun x ↦
      hnd x _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  -- The Moser field `X_t = (σ_t♭)⁻¹ (-c'(t) β)`, as the inverse of the interior product.
  set α' := SmoothForm.lineMapFamily (0 : SmoothForm I M ℝ 1) β hc'
  have hα't (t : ℝ) : SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α' =
      deriv c t • β := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, zero_add, sub_zero]
  have hX : SymplecticGeometry.moserField σ α' 1 = fun t x ↦
      (hσ t).isNondegenerate.interiorEquiv.symm
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) x := by
    funext t x
    rw [SymplecticGeometry.moserField_def, IsNondegenerate.interiorEquiv_symm_apply, hα't, hαt,
      Pi.one_apply, one_smul, map_smul, map_smul]
    congr 1
    ext v
    simp
  refine ⟨α', hα't, ?_⟩
  rw [hX]
  refine ⟨?_, fun x hx t ↦ ?_, fun x hx hjet t ↦ ?_, fun t ↦ ?_⟩
  · exact contMDiff_interiorEquiv_symm_mpullback_prodMk σ (fun t ↦ (hσ t).isNondegenerate) α
  · rw [IsNondegenerate.interiorEquiv_symm_apply_eq_zero_iff, hαt]
    simp [hx]
  · refine (hσ t).isNondegenerate.hasFDerivAt_mpullbackWithin_interiorEquiv_symm ?_ ?_
    · rw [hαt, SmoothBundleForm.smul_apply, hx, smul_zero]
    · rw [hαt, SmoothForm.smul_toRoughForm, RoughForm.inChartAt_smul]
      simpa using hjet.const_smul (-deriv c t)
  -- Moser's equation: the rate `∂_t σ_t + L_{X_t} σ_t = c'(t) dβ - c'(t) dβ` vanishes.
  funext y
  have hvel : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) y = deriv c t • (σ₁ - σ₀).val y := by
    rw [SmoothForm.mpullback_prodMk_mlieDerivForm_lineMapFamily, SmoothBundleForm.smul_apply]
  have h := (hσ t).mlieDerivForm_interiorEquiv_symm
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)
  have hd : mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      α).val = (-deriv c t) • (σ₁ - σ₀).val := by
    rw [hαt, SmoothForm.smul_toRoughForm, mextDeriv_smul, hβ]
  rw [hd, SmoothForm.coe_mpullback] at h
  rw [Pi.add_apply, hvel, h, Pi.smul_apply, Pi.zero_apply, neg_smul, add_neg_cancel]

/-- **Moser's argument along the local flow, as the time-one map of the Moser field.** Let `σ₀`
be closed, `β` a primitive of `σ₁ - σ₀`, and let every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, be
nondegenerate. Let `σ` be the path `σ₀ + c(t) (σ₁ - σ₀)` on `ℝ × M`, `c = Real.smoothTransition`.
Then there are a one-form `α` on `ℝ × M` with slices `c'(t) β`, whose Moser field
`X_t = (σ_t♭)⁻¹(-c'(t) β)` (`SymplecticGeometry.moserField σ α 1`) is jointly smooth, and a
partial diffeomorphism `Φ` whose source is the set of points whose trajectory of `X` from time `0`
reaches time `1`, which is the time-one map of `X` there, and which has the properties of
`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub`. -/
theorem exists_partialDiffeomorph_eq_timeDependentFlowOf_moserField
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1}
    (hβ : mextDeriv β.val = (σ₁ - σ₀).val)
    (hnd : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1,
      (∀ t, SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α =
        deriv Real.smoothTransition t • β) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞ (fun p : ℝ × M ↦ (⟨p.2, SymplecticGeometry.moserField
        (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1 p.1 p.2⟩ :
          TangentBundle I M)) ∧
      ∃ Φ : PartialDiffeomorph I I M M ∞,
        (∀ x, x ∈ Φ.source ↔ ((0, 1), x) ∈ timeDependentFlowDomain (SymplecticGeometry.moserField
          (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1)) ∧
        (∀ x, Φ x = timeDependentFlowOf (SymplecticGeometry.moserField
          (SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff) α 1) 0 1 x) ∧
        (∀ x, β.val x = 0 → x ∈ Φ.source ∧ Φ x = x ∧
          (HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
            (extChartAt I x x) → mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x))) ∧
        ∀ x ∈ Φ.source, mpullback I I Φ σ₁.val x = σ₀.val x := by
  obtain ⟨α, hα, hX, hX0, hXjet, hL⟩ := exists_moserField h₀ hβ hnd
  set σ := SmoothForm.lineMapFamily σ₀ σ₁ Real.smoothTransition.contDiff
  set X := SymplecticGeometry.moserField σ α 1
  -- The time-one map of the Moser flow, defined where the trajectory reaches time one.
  let Φ := timeDependentFlowPartialDiffeomorph (n := ⊤) le_top hX 0 1
  have hΦ : ⇑Φ = timeDependentFlowOf X 0 1 :=
    funext (timeDependentFlowPartialDiffeomorph_apply le_top hX 0 1)
  refine ⟨α, hα, hX, Φ, fun x ↦ mem_timeDependentFlowPartialDiffeomorph_source_iff le_top hX,
    fun x ↦ by rw [hΦ], fun x hx ↦ ⟨(mem_timeDependentFlowPartialDiffeomorph_source_iff le_top hX).2
    (mem_timeDependentFlowDomain_of_forall_eq_zero (hX0 x hx) 0 1), ?_, fun hjet ↦ ?_⟩,
    fun x hx ↦ ?_⟩
  · rw [hΦ]
    exact timeDependentFlowOf_eq_self_of_forall_eq_zero (hX.of_le (by simp)) (hX0 x hx) 0 1
  · rw [hΦ]
    exact mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero (hX.of_le (by simp)) (hX0 x hx)
      fun u _ ↦ (hXjet x hx hjet u).fderiv
  · -- Along trajectories, Moser's principle carries `σ_{c(1)} = σ₁` back to `σ_{c(0)} = σ₀`.
    have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem (hX.of_le (by simp))
      (σ.contMDiff.of_le (by simp)) hL
      ((mem_timeDependentFlowPartialDiffeomorph_source_iff le_top hX).1 hx)
    rw [SmoothForm.coe_mpullback_prodMk_lineMapFamily,
      SmoothForm.coe_mpullback_prodMk_lineMapFamily, Real.smoothTransition.one,
      Real.smoothTransition.zero, one_smul, zero_smul, add_zero, add_sub_cancel] at h
    rw [hΦ]
    exact h

/-- **Moser's argument along the local flow.** Let `σ₀` be closed, `β` a primitive of `σ₁ - σ₀`,
and let every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, be nondegenerate. Then there is a partial
diffeomorphism `Φ` whose source contains and whose map fixes every point at which `β` vanishes,
with identity differential at those points where `β` also has zero first jet, and with
`(Φ^* σ₁)ₓ = (σ₀)ₓ` at every point `x` of its source. -/
theorem exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1}
    (hβ : mextDeriv β.val = (σ₁ - σ₀).val)
    (hnd : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Φ : PartialDiffeomorph I I M M ∞,
      (∀ x, β.val x = 0 → x ∈ Φ.source ∧ Φ x = x ∧
        (HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
          (extChartAt I x x) → mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x))) ∧
      ∀ x ∈ Φ.source, mpullback I I Φ σ₁.val x = σ₀.val x := by
  obtain ⟨-, -, -, Φ, -, -, hΦ⟩ :=
    exists_partialDiffeomorph_eq_timeDependentFlowOf_moserField h₀ hβ hnd
  exact ⟨Φ, hΦ⟩

end SmoothTwoForm

namespace SmoothEmbedding

variable [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]

open TopologicalSpace SmoothTwoForm in
/-- Steps 1 and 2 of the relative Moser theorem. Let `σ₀`, `σ₁` be closed two-forms that agree at
every point `f q` as forms on the whole tangent space `T_{f q} M`, with `σ₀` nondegenerate there.
Then there is an open `W` containing `f(Q)` on which every form `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`,
is nondegenerate, and a one-form `β` on `W` with `dβ = σ₁ - σ₀` there, which vanishes at every
point `f q` and whose coordinate expression in the chart at `f q` has zero derivative there. -/
theorem exists_smoothForm_relative_primitive_sub_of_eq_along (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (W : Opens M) (_ : (W : Set M) ⊆
        {x | ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate})
      (hfW : range f ⊆ W) (β : SmoothForm I W ℝ 1),
      mextDeriv β.val =
        (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ₁ -
          SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal σ₀).val ∧
      (∀ q, β.val ⟨f q, hfW (mem_range_self q)⟩ = 0) ∧
      ∀ q, HasFDerivAt (RoughForm.inChartAt β.val ⟨f q, hfW (mem_range_self q)⟩)
        (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
        (extChartAt I (⟨f q, hfW (mem_range_self q)⟩ : W) ⟨f q, hfW (mem_range_self q)⟩) := by
  -- Along `f(Q)`, every form of the segment from `σ₀` to `σ₁` is `σ₀`.
  have hfO : range f ⊆
      {x | ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate} := by
    rintro _ ⟨q, rfl⟩ s -
    refine nondegenerate_bilinFormAt_add_smul_sub_of_eq ?_ (hnd q) s
    rw [SmoothBundleForm.sub_apply, heq q, sub_self]
  have hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀ :=
    (SmoothForm.mpullback_eq_iff _).2 (funext fun q ↦ by
      rw [SmoothForm.coe_mpullback, mpullback_apply_congr (heq q)])
  obtain ⟨W, hWO, hfW, β, hdβ, hβ0, hβ1⟩ := f.exists_smoothForm_relative_primitive_sub h₀ h₁
    hf (isOpen_setOfPred_forall_mem_Icc_nondegenerate σ₀ σ₁) hfO
  exact ⟨W, hWO, hfW, β, hdβ, hβ0, fun q ↦ hβ1 q (heq q)⟩

open TopologicalSpace SmoothTwoForm in
/-- Steps 1 to 3 of the relative Moser theorem: on a tube `W` around `f(Q)`, a partial
diffeomorphism `Φ` of `W` whose source contains `f(Q)`, which fixes `f(Q)` with identity
differential there, and which pulls `σ₁` back to `σ₀` at every point of its source. -/
private theorem exists_partialDiffeomorph_opens_of_eq_along (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (W : Opens M) (Φ : PartialDiffeomorph I I W W ∞),
      (∀ q, ∃ h : f q ∈ W, ⟨f q, h⟩ ∈ Φ.source ∧ Φ ⟨f q, h⟩ = ⟨f q, h⟩ ∧
        mfderiv I I Φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : W))) ∧
      ∀ x ∈ Φ.source,
        mpullback I I Φ (mpullback I I (Subtype.val : W → M) σ₁.val) x = σ₀.val x := by
  -- A primitive of `σ₁ - σ₀` on a tube `W` around `f(Q)` on which the segment is nondegenerate,
  -- vanishing with its first jet along `f(Q)`.
  obtain ⟨W, hWO, hfW, βW, hdβW, hβW0, hβW1⟩ :=
    f.exists_smoothForm_relative_primitive_sub_of_eq_along h₀ h₁ hnd heq
  -- Moser's argument on `W`, with the restricted forms.
  obtain ⟨Φ, hΦf, hΦ⟩ := exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub
    (h₀.mpullback _ _) hdβW
    (fun x s hs ↦ by
      rw [← map_sub, ← map_smul, ← map_add]
      exact (nondegenerate_bilinFormAt_mpullback_subtype_val_iff x).2 (hWO x.property s hs))
  refine ⟨W, Φ, fun q ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨hq, hfix, hjet⟩ := hΦf ⟨f q, hfW (mem_range_self q)⟩ (hβW0 q)
    exact ⟨hfW (mem_range_self q), hq, hfix, hjet (hβW1 q)⟩
  · rw [← SmoothForm.coe_mpullback _ contMDiff_subtypeVal, hΦ x hx,
      SmoothForm.coe_mpullback_subtype_val_apply]

open TopologicalSpace in
/-- **The relative Moser theorem with prescribed first derivative.** Consider closed two-forms
`σ₀`, `σ₁` on a boundaryless Hausdorff second-countable manifold `M`, and let `f : Q → M` be a
smooth embedding. Suppose that at every point `f q` the forms `σ₁` and `σ₀` agree on the whole
tangent space `T_{f q} M`, and that `σ₀` is nondegenerate there. Then there are open sets `U₀`,
`U₁` of `M` containing `f(Q)` and a diffeomorphism `φ : U₀ → U₁` which pulls the restriction of
`σ₁` to `U₁` back to the restriction of `σ₀` to `U₀`, fixes every point `f q`, and has the
identity of `T_{f q} M` as its differential there.

This generalizes Tau Ceti's `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`: the
source `Q` need not be compact, and the image `f(Q)` need not be closed in `M`.

Milestone: *Relative Moser theorem with prescribed first derivative*. -/
theorem exists_diffeomorph_opens_of_eq_along (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (U₀ U₁ : Opens M) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q ∧
        mfderiv I I φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : U₀))) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal σ₀ := by
  obtain ⟨W, Φ, hΦf, hΦ⟩ := exists_partialDiffeomorph_opens_of_eq_along f h₀ h₁ hnd heq
  rcases isEmpty_or_nonempty W with hW | hW
  · -- If the tube is empty, so is `Q`, and the empty opens will do.
    have : IsEmpty Q := ⟨fun q ↦ hW.false ⟨f q, (hΦf q).1⟩⟩
    exact ⟨⊥, ⊥, Diffeomorph.ofIsEmpty, isEmptyElim, Subsingleton.elim _ _⟩
  -- Read `Φ` in `M`, as a diffeomorphism between the source and the target of its lift.
  refine ⟨_, _, (Φ.liftOpens hW hW).toDiffeomorphSourceTarget, fun q ↦ ?_,
    Φ.mpullback_toDiffeomorphSourceTarget_liftOpens hW hW hΦ⟩
  obtain ⟨_, hq, hfix, hjet⟩ := hΦf q
  exact Φ.exists_toDiffeomorphSourceTarget_liftOpens_eq_and_mfderiv_eq_id hW hq hfix hjet

end SmoothEmbedding

end TauCeti

end
