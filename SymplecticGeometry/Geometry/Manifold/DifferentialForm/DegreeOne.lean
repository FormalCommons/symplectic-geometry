/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Trivialization
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# One-forms: proportionality and values on smooth vector fields

If the kernel of a one-form `α` at `x` lies in that of `β`, and `α_x(v) = 1`, then
`β_x = β_x(v) α_x` (`TauCeti.RoughForm.apply_eq_smul_of_ker_le`). This holds for rough forms,
with no smoothness asked. Its proof adapts that of Tau Ceti's
`TauCeti.SmoothForm.apply_eq_smul_of_kerDistribution_le`, which is stated for smooth forms only.

Let `α` be a smooth one-form with values in a real normed space `F`, and `x ↦ (b x, V x)` a
`C^n` map from a manifold into the tangent bundle, for some `n ≤ ∞`. Then `x ↦ α_{b x}(V x)`
is a `C^n` `F`-valued function (`TauCeti.SmoothForm.contMDiff_apply_fin_one`, and
`TauCeti.SmoothForm.contMDiffAt_apply_fin_one` at a point). It extends Tau Ceti's
`TauCeti.SmoothForm.contMDiffAt_apply_vectorField`, for real forms on vector fields, to any `F`
and any base map `b`. Through Tau Ceti's `TauCeti.SmoothForm.degreeOneEquiv`, `α` is a smooth
section of the bundle of continuous linear maps from the tangent bundle to `F`; pulled back along
`b`, it is applied to `V` by `ContMDiffAt.clm_bundle_apply`. This is the degree-one analogue of
Tau Ceti's `TauCeti.SmoothBundleForm.contMDiffAt_eval₂`. Two cases follow:

* `TauCeti.SmoothForm.contMDiff_apply_contMDiffSection`: `α` on a smooth vector field.
* `TauCeti.SmoothForm.contMDiff_apply_prodMk_zero_prodMk`: on a product `M × N` whose second
  factor is modelled on `E'`, and for a fixed `y : N`, the map `(q, v) ↦ α_{(q, y)} (0, v)` on
  `M × E'`. The vectors `(0, v)` at `(q, y)` pair the zero section of `M` with the inclusion of
  the tangent space at `y` (`TangentBundle.contMDiff_totalSpaceMk`), through Mathlib's
  `contMDiff_equivTangentBundleProd_symm`.

Two smooth bundle-valued one-forms are equal once they agree on each single tangent vector
(`TauCeti.SmoothBundleForm.ext_fin_one`). This is the degree-one analogue of Tau Ceti's
`TauCeti.SmoothBundleForm.ext_eval₂`, and follows from `ContinuousAlternatingMap.ext_fin_one`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- If the kernel of the one-form `α` at `x` lies in that of `β`, then `β` is proportional to `α`
at `x`: if `α_x(v) = 1`, then `β_x = β_x(v) α_x`. -/
theorem apply_eq_smul_of_ker_le {α β : RoughForm I M ℝ 1} {x : M} {v : TangentSpace I x}
    (hker : α.ker x ≤ β.ker x) (hv : α x ![v] = 1) : β x = β x ![v] • α x := by
  ext w
  -- `w - α(w) v` lies in `ker α ⊆ ker β`.
  have hw : α x ![w - α x ![w] • v] = 0 := by
    rw [← eval_apply, map_sub, map_smul, eval_apply, eval_apply, hv, smul_eq_mul, mul_one,
      sub_self]
  have h := mem_ker.1 (hker (mem_ker.2 hw))
  rw [← eval_apply, map_sub, map_smul, eval_apply, eval_apply, smul_eq_mul, sub_eq_zero] at h
  rw [ContinuousAlternatingMap.smul_apply, h, smul_eq_mul, mul_comm]

end TauCeti.RoughForm

namespace TauCeti.SmoothBundleForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- Two smooth bundle-valued one-forms are equal when they agree on every tangent vector. -/
theorem ext_fin_one {φ ψ : SmoothBundleForm I F V 1}
    (h : ∀ x v, φ.val x ![v] = ψ.val x ![v]) : φ = ψ :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext_fin_one (h x)

end TauCeti.SmoothBundleForm

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Eval

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]

/-- Let `α` be a smooth `F`-valued one-form on `M`, and `x ↦ (b x, V x)` a map into the tangent
bundle of `M` that is `C^n` at `x₀`, for some `n ≤ ∞`. Then `x ↦ α_{b x}(V x)` is `C^n` at
`x₀`. -/
theorem contMDiffAt_apply_fin_one {n : WithTop ℕ∞} [ENat.LEInfty n] (α : SmoothForm I M F 1)
    {b : X → M} {V : ∀ x, TangentSpace I (b x)} {x₀ : X}
    (hV : ContMDiffAt IX I.tangent n (fun x ↦ TotalSpace.mk' E (b x) (V x)) x₀) :
    ContMDiffAt IX 𝓘(ℝ, F) n (fun x ↦ α.val (b x) ![V x]) x₀ := by
  have hb : ContMDiffAt IX I n b x₀ :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp x₀ hV
  have h : ContMDiffAt IX (I.prod 𝓘(ℝ, F)) n (fun x ↦
      TotalSpace.mk' F (E := Trivial M F) (b x) (degreeOneEquiv α (b x) (V x))) x₀ :=
    ((((degreeOneEquiv α).contMDiff (b x₀)).of_le ENat.LEInfty.out).comp x₀ hb).clm_bundle_apply
      hV
  exact (contMDiffAt_totalSpace_iff.mp h).2.congr_of_eventuallyEq
    (.of_forall fun x ↦ (degreeOneEquiv_apply_apply_vec α _ _).symm)

/-- Let `α` be a smooth `F`-valued one-form on `M`, and `x ↦ (b x, V x)` a `C^n` map into the
tangent bundle of `M`, for some `n ≤ ∞`. Then `x ↦ α_{b x}(V x)` is `C^n`. -/
theorem contMDiff_apply_fin_one {n : WithTop ℕ∞} [ENat.LEInfty n] (α : SmoothForm I M F 1)
    {b : X → M} {V : ∀ x, TangentSpace I (b x)}
    (hV : ContMDiff IX I.tangent n fun x ↦ TotalSpace.mk' E (b x) (V x)) :
    ContMDiff IX 𝓘(ℝ, F) n fun x ↦ α.val (b x) ![V x] := fun x ↦
  contMDiffAt_apply_fin_one α (hV x)

end Eval

/-- The value `α(X)` of a smooth `F`-valued one-form on a smooth vector field is a smooth
`F`-valued function. -/
theorem contMDiff_apply_contMDiffSection (α : SmoothForm I M F 1)
    (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    ContMDiff I 𝓘(ℝ, F) ∞ fun x ↦ α.val x ![X x] :=
  contMDiff_apply_fin_one (b := id) α X.contMDiff

/-- Let `α` be a smooth `F`-valued one-form on a product `M × N` whose second factor is modelled
on `E'`, and fix `y : N`. The value of `α` at `(q, y)` on the tangent vector `(0, v)`, with `v`
in the model space `E'` of the tangent space of `N` at `y`, is a smooth function of
`(q, v) : M × E'`. -/
theorem contMDiff_apply_prodMk_zero_prodMk {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J 1 N] (α : SmoothForm (I.prod J) (M × N) F 1) (y : N) :
    ContMDiff (I.prod 𝓘(ℝ, E')) 𝓘(ℝ, F) ∞
      fun p : M × E' ↦ α.val (p.1, y) ![((0 : E), p.2)] :=
  -- The vector `(0, v)` at `(q, y)` is the pair of the zero vector at `q` and `v` at `y`.
  contMDiff_apply_fin_one (b := fun p : M × E' ↦ (p.1, y)) (V := fun p ↦ ((0 : E), p.2)) α <|
    contMDiff_equivTangentBundleProd_symm.comp
      (((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_fst).prodMk
        ((TangentBundle.contMDiff_totalSpaceMk y).comp contMDiff_snd))

end TauCeti.SmoothForm

end
