/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import SymplecticGeometry.Geometry.Manifold.Algebra.SMul
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Pulling forms back along local diffeomorphisms

For a `C^n` partial diffeomorphism `ψ` with `n ≠ 0`, pulling a form back along `ψ` and then
along `ψ.symm` returns it at each point of the target of `ψ`
(`PartialDiffeomorph.mpullback_symm_mpullback_apply`): by the chain rule, since `ψ ∘ ψ.symm`
is the identity near such a point. The proof is the pointwise form of the proof of Tau Ceti's
`TauCeti.mpullback_symm_mpullback` for diffeomorphisms, and adapts the last step of the proof of
Tau Ceti's `IsLocalDiffeomorphAt.exists_partialDiffeomorph_mpullback_eq`. Applied to `ψ.symm`,
it gives the other order, along `ψ.symm` and then along `ψ`, at each point of the source of `ψ`
(`PartialDiffeomorph.mpullback_mpullback_symm_apply`).

If a local diffeomorphism `f` at `x` pulls a form `ω` back to `η` at a point `Λ y`, where
`Λ = hf.localInverse` and `y` lies in the source of `Λ`, then `Λ` pulls `η` back to `ω` at `y`
(`IsLocalDiffeomorphAt.mpullback_localInverse_apply_eq`). Tau Ceti's
`IsLocalDiffeomorphAt.exists_partialDiffeomorph_mpullback_eq` only gives some partial
diffeomorphism, a restriction of `Λ`; the pointwise form keeps `Λ` itself, so that it is still
known to invert `f`. Near `Λ y`, `f` agrees with `Λ.symm`
(`IsLocalDiffeomorphAt.eqOn_localInverse_symm`), so this is
`PartialDiffeomorph.mpullback_mpullback_symm_apply` for `Λ`.

A `C^n` local diffeomorphism `f` with `2 ≤ n` also pulls a pair with `ι_Y dα = α` back to such a
pair, for the pulled-back field and form
(`IsLocalDiffeomorph.interior_mextDeriv_mpullback_of_interior_mextDeriv`). The proof combines Tau
Ceti's `TauCeti.mpullback_mextDeriv_at` and `TauCeti.mpullback_interior`; that the differential of
`f` sends the pulled-back field to `Y` is `IsLocalDiffeomorphAt.mfderiv_apply_mpullback`, from
`SymplecticGeometry.Geometry.Manifold.VectorField.Pullback`.

At a single point `x` where `f` is a local diffeomorphism, the same tools transfer pointwise
identities between a form `ω` at `f x` and its pullback at `x`: `dφ = ψ`
(`IsLocalDiffeomorphAt.mextDeriv_apply_eq_iff`), `ι_Z ω = ψ` for fields related by the
differential (`IsLocalDiffeomorphAt.interior_apply_eq_iff`), nondegeneracy of a two-form
(`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv`, which needs only
an invertible differential at `x`; for an immersion at `x` between manifolds of one finite
dimension, which has one, the direction from `f x` to `x` is
`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_of_isImmersionAt`; for the action of an
element of a group acting by smooth maps, on a
two-form invariant under it, this is `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_smul_iff`),
and, for a two-form closed at `f x`, the
identity `L_Z ω = ψ` (`IsLocalDiffeomorphAt.mlieDerivForm_apply_eq_iff`, through the
pointwise Cartan formula `TauCeti.mlieDerivForm_eq_mextDeriv_interior_apply`). They are the
pointwise forms, for a map that is a local diffeomorphism only near `x`, of Tau Ceti's
`IsLocalDiffeomorph.isClosed_mpullback_iff` and `IsLocalDiffeomorph.isNondegenerate_mpullback_iff`.

The group action also carries such an identity along an orbit: if a map `f` that commutes with
`z ↦ g • z`, and is differentiable at `y`, pulls a form `ω` back to `η` at `y`, both forms being
invariant under `g`, then it does so at `g • y` (`TauCeti.mpullback_apply_smul_eq_of_apply_eq`),
since the differential of `z ↦ g • z` at `y` is onto. Such an `f` is differentiable at `g • y`
too (`MDifferentiableAt.at_smul_of_map_smul`, from
`SymplecticGeometry.Geometry.Manifold.Algebra.SMul`).

For `f : M → M'` and a form `α` on `M`, `TauCeti.RoughForm.pushforwardAt I I' f α x z` is `α x`
read through the inverse of the differential of `f` at `x`, as an alternating map on the tangent
space at `z` (meant for `z = f x`). When that differential is invertible, a form on `M'` whose
value at `f x` is this one pulls back to `α x`
(`TauCeti.mpullback_apply_eq_of_apply_eq_pushforwardAt`). Reading a form through an inverse of a
differential is what Tau Ceti's `TauCeti.RoughForm.descendedForm` does through a right inverse.

Two such pushforwards glue pointwise: for `f₁ : M → M''` injective on `s₁` and an injective
`f₂ : M' → M''`, `TauCeti.RoughForm.glue I'' f₁ s₁ f₂ α₁ α₂` is the pushforward of `α₁` on
`f₁ '' s₁` and that of `α₂` at the other points of the range of `f₂`. It pulls back to `α₁` and
`α₂` there (`TauCeti.RoughForm.mpullback_glue_apply_of_mem`,
`TauCeti.RoughForm.mpullback_glue_apply_of_notMem`), and it is `C^m` when `α₁` and `α₂` are,
`f₁` and `f₂` are `C^n` local diffeomorphisms with `m + 1 ≤ n` whose images cover `M''`, and
its pull-back by `f₂` is `α₂` near each point off `f₁ '' s₁`
(`TauCeti.RoughForm.isSmoothForm_glue`), by Tau Ceti's
`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`.

Let `g : M → M'` be a local diffeomorphism pulling a form `σ` back to `τ`, and `Λ` a
diffeomorphism of `M` preserving `τ`. A diffeomorphism `Ψ` of `M'` with `Ψ ∘ g = g ∘ Λ` that
fixes every point outside a closed subset of the range of `g` preserves `σ`
(`TauCeti.SmoothForm.mem_diffeomorphStabilizer_of_semiconj`). At a point `g w` this is
`g^* Ψ^* σ = Λ^* g^* σ = τ = g^* σ`, by Tau Ceti's
`TauCeti.SmoothForm.mpullback_mpullback_of_comp_eq`, and the differential of `g` at `w` is onto;
elsewhere `Ψ` is the identity near the point.

The same two cases carry an exactness identity from a chart to the manifold
(`TauCeti.SmoothForm.exists_mpullback_sub_eq_mextDerivₗ_of_partialDiffeomorph`). Let `e` be a
partial diffeomorphism into `M'`, `C ⊆ W ⊆ e.source` with `C` compact and `W` open, and `Φ` a
diffeomorphism of `M'` that fixes every point off `e '' C`. If `(Φ ∘ e)^* θ - e^* θ = dk` on `W`
for a function `k` that vanishes on `W` outside `C`, then `k ∘ e⁻¹` on `e '' W`, extended by zero
(`PartialDiffeomorph.contMDiff_indicator_image_comp_symm`), is a smooth `K` with
`Φ^* θ - θ = dK`. At a point of `e '' W` both sides pull back along `e` to the hypothesis
(`IsLocalDiffeomorphAt.mextDeriv_apply_eq_iff`); off `e '' C`, `Φ` is the identity and `K` is `0`
near the point. Seidel uses this to see that the Dehn twist along an exact Lagrangian sphere is
an exact symplectomorphism.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], the paragraph
  before Proposition 1.11 (arXiv version 2)
-/

public section

open Set Filter
open scoped Manifold Topology

open TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {n : WithTop ℕ∞} {f : M → M'} {x : M}

/-- For a `C^n` partial diffeomorphism `ψ` with `n ≠ 0`, pulling a form `ω` back along `ψ` and
then along `ψ.symm` gives `ω` back at every point of the target of `ψ`. -/
theorem PartialDiffeomorph.mpullback_symm_mpullback_apply (ψ : PartialDiffeomorph I I' M M' n)
    (hn : n ≠ 0) (ω : RoughForm I' M' F k) {y : M'} (hy : y ∈ ψ.target) :
    mpullback I' I ψ.symm (mpullback I I' ψ ω) y = ω y := by
  have hid : ψ ∘ ψ.symm =ᶠ[𝓝 y] id :=
    eventually_of_mem (ψ.open_target.mem_nhds hy) fun z hz ↦ ψ.right_inv hz
  rw [← mpullback_comp_at (ψ.symm.mdifferentiableAt hn hy)
    (ψ.mdifferentiableAt hn (ψ.map_target hy)), hid.mpullback_eq, mpullback_id]

/-- For a `C^n` partial diffeomorphism `ψ` with `n ≠ 0`, pulling a form `ω` back along `ψ.symm`
and then along `ψ` gives `ω` back at every point of the source of `ψ`. -/
theorem PartialDiffeomorph.mpullback_mpullback_symm_apply (ψ : PartialDiffeomorph I I' M M' n)
    (hn : n ≠ 0) (ω : RoughForm I M F k) {x : M} (hx : x ∈ ψ.source) :
    mpullback I I' ψ (mpullback I' I ψ.symm ω) x = ω x :=
  ψ.symm.mpullback_symm_mpullback_apply hn ω hx

namespace TauCeti

variable (I I') in
/-- The value at `z` of the pushforward of a form `α` along `f : M → M'` from the point `x`:
`α x` read through the inverse of the differential of `f` at `x`, with the tangent space at `z`
identified with the one at `f x`. It is meant for `z = f x` and an invertible differential. -/
noncomputable def RoughForm.pushforwardAt (f : M → M') (α : RoughForm I M F k) (x : M) (z : M') :
    TangentSpace I' z [⋀^Fin k]→L[ℝ] F :=
  (α x).compContinuousLinearMap
    ((mfderiv I I' f x).inverse.comp (tangentSpaceCast I' z (f x) : TangentSpace I' z →L[ℝ] _))

theorem RoughForm.pushforwardAt_def (f : M → M') (α : RoughForm I M F k) (x : M) (z : M') :
    pushforwardAt I I' f α x z = (α x).compContinuousLinearMap
      ((mfderiv I I' f x).inverse.comp (tangentSpaceCast I' z (f x) : TangentSpace I' z →L[ℝ] _)) :=
  (rfl)

/-- If the differential of `f` at `x` is invertible, a form `β` whose value at `f x` is the
pushforward of `α` from `x` pulls back along `f` to `α` at `x`. -/
theorem mpullback_apply_eq_of_apply_eq_pushforwardAt {α : RoughForm I M F k}
    {β : RoughForm I' M' F k} (hf : (mfderiv I I' f x).IsInvertible)
    (hβ : β (f x) = RoughForm.pushforwardAt I I' f α x (f x)) :
    mpullback I I' f β x = α x := by
  ext v
  rw [mpullback_apply, hβ, RoughForm.pushforwardAt_def]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, tangentSpaceCast_self,
    hf.inverse_apply_self]

section Glue

variable {E'' H'' M'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  [TopologicalSpace M''] [ChartedSpace H'' M''] {I'' : ModelWithCorners ℝ E'' H''}
  {f₁ : M → M''} {s₁ : Set M} {f₂ : M' → M''} {α₁ : RoughForm I M F k}
  {α₂ : RoughForm I' M' F k} {y : M'}

open Classical in
variable (I'') in
/-- The form on `M''` glued pointwise from a form `α₁` on `M` and a form `α₂` on `M'` along
`f₁ : M → M''` and `f₂ : M' → M''`: at a point `f₁ x` with `x ∈ s₁` it is the pushforward of `α₁`
from `x`, at the other points `f₂ y` the pushforward of `α₂` from `y`, and `0` off both images.
It is meant for `f₁` injective on `s₁` and `f₂` injective (`glue_apply_of_mem`,
`glue_apply_of_notMem`). -/
noncomputable def RoughForm.glue (f₁ : M → M'') (s₁ : Set M) (f₂ : M' → M'')
    (α₁ : RoughForm I M F k) (α₂ : RoughForm I' M' F k) : RoughForm I'' M'' F k := fun z ↦
  if hz : ∃ x ∈ s₁, f₁ x = z then pushforwardAt I I'' f₁ α₁ hz.choose z
  else if hz' : ∃ y, f₂ y = z then pushforwardAt I' I'' f₂ α₂ hz'.choose z
  else 0

open Classical in
variable (I'') in
theorem RoughForm.glue_def (f₁ : M → M'') (s₁ : Set M) (f₂ : M' → M'')
    (α₁ : RoughForm I M F k) (α₂ : RoughForm I' M' F k) (z : M'') :
    glue I'' f₁ s₁ f₂ α₁ α₂ z =
      if hz : ∃ x ∈ s₁, f₁ x = z then pushforwardAt I I'' f₁ α₁ hz.choose z
      else if hz' : ∃ y, f₂ y = z then pushforwardAt I' I'' f₂ α₂ hz'.choose z
      else 0 :=
  (rfl)

/-- At `f₁ x` with `x ∈ s₁`, where `f₁` is injective on `s₁`, the glued form is the pushforward
of `α₁` from `x`. -/
theorem RoughForm.glue_apply_of_mem (hf₁ : InjOn f₁ s₁) (hx : x ∈ s₁) :
    glue I'' f₁ s₁ f₂ α₁ α₂ (f₁ x) = pushforwardAt I I'' f₁ α₁ x (f₁ x) := by
  have hz : ∃ x' ∈ s₁, f₁ x' = f₁ x := ⟨x, hx, rfl⟩
  rw [glue_def, dite_eq_left hz, hf₁ hz.choose_spec.1 hx hz.choose_spec.2]

/-- At `f₂ y` off `f₁ '' s₁`, where `f₂` is injective, the glued form is the pushforward of `α₂`
from `y`. -/
theorem RoughForm.glue_apply_of_notMem (hf₂ : Function.Injective f₂) (hy : f₂ y ∉ f₁ '' s₁) :
    glue I'' f₁ s₁ f₂ α₁ α₂ (f₂ y) = pushforwardAt I' I'' f₂ α₂ y (f₂ y) := by
  have hz : ¬∃ x ∈ s₁, f₁ x = f₂ y := fun ⟨x, hx, hxy⟩ ↦ hy ⟨x, hx, hxy⟩
  have hz' : ∃ y', f₂ y' = f₂ y := ⟨y, rfl⟩
  rw [glue_def, dite_eq_right hz, dite_eq_left hz', hf₂ hz'.choose_spec]

/-- If `f₁` is injective on `s₁` and its differential at `x ∈ s₁` is invertible, the glued form
pulls back along `f₁` to `α₁` at `x`. -/
theorem RoughForm.mpullback_glue_apply_of_mem (hf₁ : InjOn f₁ s₁) (hx : x ∈ s₁)
    (hd : (mfderiv I I'' f₁ x).IsInvertible) :
    mpullback I I'' f₁ (glue I'' f₁ s₁ f₂ α₁ α₂) x = α₁ x :=
  mpullback_apply_eq_of_apply_eq_pushforwardAt hd (glue_apply_of_mem hf₁ hx)

/-- If `f₂` is injective, `f₂ y` is off `f₁ '' s₁` and the differential of `f₂` at `y` is
invertible, the glued form pulls back along `f₂` to `α₂` at `y`. -/
theorem RoughForm.mpullback_glue_apply_of_notMem (hf₂ : Function.Injective f₂)
    (hy : f₂ y ∉ f₁ '' s₁) (hd : (mfderiv I' I'' f₂ y).IsInvertible) :
    mpullback I' I'' f₂ (glue I'' f₁ s₁ f₂ α₁ α₂) y = α₂ y :=
  mpullback_apply_eq_of_apply_eq_pushforwardAt hd (glue_apply_of_notMem hf₂ hy)

/-- Let `m + 1 ≤ n`, let `f₁` be a `C^n` local diffeomorphism on an open set `s₁`, injective
there, and let `α₁` and `α₂` be `C^m` forms. If every point off `f₁ '' s₁` is `f₂ y` for a point
`y` at which `f₂` is a `C^n` local diffeomorphism and near which the glued form pulls back along
`f₂` to `α₂`, then the glued form is `C^m`. -/
theorem RoughForm.isSmoothForm_glue [IsManifold I 1 M] [IsManifold I' 1 M']
    [IsManifold I'' 1 M''] {m : WithTop ℕ∞} (hmn : m + 1 ≤ n) (hs₁ : IsOpen s₁)
    (hf₁ : InjOn f₁ s₁) (hd₁ : IsLocalDiffeomorphOn I I'' n f₁ s₁) (hα₁ : IsSmoothForm I m α₁)
    (hα₂ : IsSmoothForm I' m α₂)
    (h₂ : ∀ z ∉ f₁ '' s₁, ∃ y, f₂ y = z ∧ IsLocalDiffeomorphAt I' I'' n f₂ y ∧
      ∀ᶠ r in 𝓝 y, mpullback I' I'' f₂ (glue I'' f₁ s₁ f₂ α₁ α₂) r = α₂ r) :
    IsSmoothForm I'' m (glue I'' f₁ s₁ f₂ α₁ α₂) := by
  have hn : n ≠ 0 := by rintro rfl; simp at hmn
  rw [isSmoothForm_def]
  intro z
  by_cases hz : z ∈ f₁ '' s₁
  · obtain ⟨x, hx, rfl⟩ := hz
    refine ((hd₁ ⟨x, hx⟩).contMDiffAt_mpullback_form_iff hmn).1
      ((hα₁.contMDiff x).congr_of_eventuallyEq ?_)
    filter_upwards [hs₁.mem_nhds hx] with r hr
    rw [mpullback_glue_apply_of_mem hf₁ hr ((hd₁ ⟨r, hr⟩).isInvertible_mfderiv hn)]
  · obtain ⟨y, rfl, hy, hc⟩ := h₂ z hz
    refine (hy.contMDiffAt_mpullback_form_iff hmn).1
      ((hα₂.contMDiff y).congr_of_eventuallyEq ?_)
    filter_upwards [hc] with r hr
    rw [hr]

end Glue

namespace SmoothTwoForm

/-- Let the differential of `f` at `x` be invertible, and let `f` pull the two-form `ω` back to
`η` at `x`. Then `ω` is nondegenerate at `f x` exactly when `η` is nondegenerate at `x`. The
point `x` may lie on the boundary of `M`, where `f` need not be a local diffeomorphism. -/
theorem nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv [IsManifold I 1 M]
    [IsManifold I' 1 M'] (hdf : (mfderiv I I' f x).IsInvertible)
    {ω : SmoothForm I' M' ℝ 2} {η : SmoothForm I M ℝ 2} (h : mpullback I I' f ω.val x = η.val x) :
    (ω.bilinFormAt (f x)).Nondegenerate ↔ (η.bilinFormAt x).Nondegenerate := by
  obtain ⟨e, he⟩ := hdf
  have hη : η.bilinFormAt x =
      LinearMap.BilinForm.congr e.symm.toLinearEquiv (ω.bilinFormAt (f x)) := by
    refine LinearMap.ext₂ fun v w ↦ ?_
    rw [LinearMap.BilinForm.congr_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      ContinuousLinearEquiv.symm_symm, SmoothForm.bilinFormAt_apply,
      SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply,
      ← h, mpullback_apply_pair]
    simp [← he]
  rw [hη, LinearMap.BilinForm.nondegenerate_congr_iff]

open scoped ContDiff in
/-- Let `f : M → M'` be smooth and a `C^n` immersion at `x`, with `n ≠ 0`, where the models of
`M` and `M'` have the same finite dimension. If the two-form `σ` on `M'` is nondegenerate at
`f x`, then its pull-back along `f` is nondegenerate at `x`. -/
theorem nondegenerate_bilinFormAt_mpullback_of_isImmersionAt [FiniteDimensional ℝ E']
    [IsManifold I 1 M] [IsManifold I' 1 M'] (hf : ContMDiff I I' ∞ f)
    (hfx : Manifold.IsImmersionAt I I' n f x) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {σ : SmoothForm I' M' ℝ 2}
    (hσ : (σ.bilinFormAt (f x)).Nondegenerate) :
    ((SmoothForm.mpullback f hf σ).bilinFormAt x).Nondegenerate :=
  (nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
    ((isInvertible_mfderiv_iff_injective hdim).2 (hfx.mfderiv_injective hn))
    (by rw [SmoothForm.coe_mpullback])).1 hσ

open scoped ContDiff in
/-- Let a group `G` act on `M` by smooth maps, and let the two-form `σ` on `M` be invariant
under `y ↦ k • y`. Then `σ` is nondegenerate at `k • y` exactly when it is nondegenerate at `y`. -/
theorem nondegenerate_bilinFormAt_smul_iff [IsManifold I 1 M] {G : Type*} [Group G]
    [MulAction G M] [ContMDiffConstSMul I ∞ G M] {σ : SmoothForm I M ℝ 2} (k : G)
    (hσ : SmoothForm.mpullback (k • ·) (ContMDiffConstSMul.contMDiff_const_smul k) σ = σ)
    (y : M) :
    (σ.bilinFormAt (k • y)).Nondegenerate ↔ (σ.bilinFormAt y).Nondegenerate := by
  have hk : (mfderiv I I (k • ·) y).IsInvertible := by
    rw [← Diffeomorph.coe_constSmul (I := I) (n := ∞) k]
    exact (Diffeomorph.constSmul I ∞ k).isInvertible_mfderiv (by simp)
  refine nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv hk ?_
  have h := congrArg Subtype.val hσ
  rw [SmoothForm.coe_mpullback] at h
  exact congrFun h y

end SmoothTwoForm

/-- Let a group `G` act on `M` and on `M'` by `C¹` maps, and let `f : M → M'` commute with
`z ↦ g • z`, and be differentiable at `y`. Let the forms `α` on `M'` and `β` on `M` be invariant
under `z ↦ g • z`. If `f` pulls `α` back to `β` at `y`, then it pulls `α` back to `β` at
`g • y`. -/
theorem mpullback_apply_smul_eq_of_apply_eq [IsManifold I 1 M] {G : Type*} [Group G]
    [MulAction G M] [ContMDiffConstSMul I 1 G M] [MulAction G M'] [ContMDiffConstSMul I' 1 G M']
    (g : G) (hfg : ∀ z, f (g • z) = g • f z) {α : RoughForm I' M' F k} {β : RoughForm I M F k}
    (hα : mpullback I' I' (g • ·) α = α) (hβ : mpullback I I (g • ·) β = β) {y : M}
    (hf : MDifferentiableAt I I' f y) (h : mpullback I I' f α y = β y) :
    mpullback I I' f α (g • y) = β (g • y) := by
  have hgM : MDifferentiableAt I I (g • ·) y :=
    ContMDiffConstSMul.mdifferentiable_const_smul (I := I) (n := 1) one_ne_zero g y
  have hgM' : MDifferentiableAt I' I' (g • ·) (f y) :=
    ContMDiffConstSMul.mdifferentiable_const_smul (I := I') (n := 1) one_ne_zero g (f y)
  have hsurj : Function.Surjective (mfderiv I I (g • ·) y) := by
    rw [← Diffeomorph.coe_constSmul (I := I) (n := 1) g]
    exact (((Diffeomorph.constSmul I 1 g).isLocalDiffeomorph y).isInvertible_mfderiv
      one_ne_zero).surjective
  refine (mpullback_apply_eq_mpullback_apply_iff hsurj).1 ?_
  -- Both sides at `y`: `(f ∘ (g • ·))^* α = ((g • ·) ∘ f)^* α = f^* α = β = (g • ·)^* β`.
  rw [hβ, ← mpullback_comp_at hgM (hf.at_smul_of_map_smul g hfg),
    show f ∘ (g • ·) = (g • ·) ∘ f from funext hfg, mpullback_comp_at hf hgM', hα, h]

end TauCeti

namespace IsLocalDiffeomorphAt

/-- Let `f` be a `C^n` local diffeomorphism at `x`, `n ≠ 0`, with local inverse `Λ`, and let `y`
be in the source of `Λ`. If `f` pulls `ω` back to `η` at `Λ y`, then `Λ` pulls `η` back to `ω`
at `y`. -/
theorem mpullback_localInverse_apply_eq (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0)
    {ω : RoughForm I' M' F k} {η : RoughForm I M F k} {y : M'} (hy : y ∈ hf.localInverse.source)
    (hfω : mpullback I I' f ω (hf.localInverse y) = η (hf.localInverse y)) :
    mpullback I' I hf.localInverse η y = ω y := by
  have hf' : f =ᶠ[𝓝 (hf.localInverse y)] hf.localInverse.symm :=
    eventually_of_mem (hf.localInverse.open_target.mem_nhds (hf.localInverse.map_source hy))
      hf.eqOn_localInverse_symm
  rw [← hf.localInverse.mpullback_mpullback_symm_apply hn ω hy]
  exact mpullback_apply_congr (hfω.symm.trans (hf'.mpullback_eq ω))

/-- Let `f` be a `C^n` local diffeomorphism at `x`, `n ≠ 0`, whose differential at `x` sends
`X x` to `Z (f x)`. Then `ι_Z ω` agrees with `ψ` at `f x` exactly when `ι_X (f^* ω)` agrees with
`f^* ψ` at `x`. -/
theorem interior_apply_eq_iff (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0)
    {X : (x : M) → TangentSpace I x} {Z : (y : M') → TangentSpace I' y}
    (hXZ : mfderiv I I' f x (X x) = Z (f x)) {ω : RoughForm I' M' F (k + 1)}
    {ψ : RoughForm I' M' F k} :
    ω.interior Z (f x) = ψ (f x) ↔
      (mpullback I I' f ω).interior X x = mpullback I I' f ψ x := by
  rw [← mpullback_interior_at f X Z ω hXZ,
    mpullback_apply_eq_mpullback_apply_iff (hf.isInvertible_mfderiv hn).surjective]

section

variable [IsManifold I 2 M] [IsManifold I' 2 M']

/-- Let `f` be a `C^n` local diffeomorphism at `x`, `2 ≤ n`, and `φ` a form that is `C¹` at
`f x`. Then `dφ` agrees with `ψ` at `f x` exactly when `d(f^* φ)` agrees with `f^* ψ` at `x`. -/
theorem mextDeriv_apply_eq_iff (hf : IsLocalDiffeomorphAt I I' n f x) (hn : 2 ≤ n)
    {φ : RoughForm I' M' F k}
    (hφ : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ Bundle.TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (φ y)) (f x))
    {ψ : RoughForm I' M' F (k + 1)} :
    mextDeriv φ (f x) = ψ (f x) ↔
      mextDeriv (mpullback I I' f φ) x = mpullback I I' f ψ x := by
  rw [← mpullback_mextDeriv_at (hf.contMDiffAt.of_le hn) hφ,
    mpullback_apply_eq_mpullback_apply_iff
      (hf.isInvertible_mfderiv (lt_of_lt_of_le (by simp) hn).ne').surjective]

end

open scoped ContDiff in
/-- Let `f` be a smooth local diffeomorphism at `x` that pulls the two-form `σ` back to `η` near
`x`, and whose differential sends the field `X`, `C¹` at `x`, to the field `Z`, `C¹` at `f x`,
near `x`. If `σ` is closed at `f x`, then `L_Z σ` agrees with a two-form `ψ` at `f x` exactly
when `L_X η` agrees with `f^* ψ` at `x`. -/
theorem mlieDerivForm_apply_eq_iff [IsManifold I ∞ M] [IsManifold I' ∞ M']
    (hf : IsLocalDiffeomorphAt I I' ∞ f x) {σ : SmoothTwoForm I' M'} {η : SmoothTwoForm I M}
    (hση : ∀ᶠ y in 𝓝 x, mpullback I I' f σ.val y = η.val y)
    {X : (x : M) → TangentSpace I x} {Z : (y : M') → TangentSpace I' y}
    (hX : ContMDiffAt I I.tangent 1 (T% X) x) (hZ : ContMDiffAt I' I'.tangent 1 (T% Z) (f x))
    (hXZ : ∀ᶠ y in 𝓝 x, mfderiv I I' f y (X y) = Z (f y))
    (hdσ : mextDeriv σ.val (f x) = 0) {ψ : RoughForm I' M' ℝ 2} :
    mlieDerivForm Z σ.val (f x) = ψ (f x) ↔ mlieDerivForm X η.val x = mpullback I I' f ψ x := by
  have hdη : mextDeriv η.val x = 0 := by
    have := (hf.mextDeriv_apply_eq_iff (by simp) ((σ.contMDiff (f x)).of_le (by simp))
      (ψ := 0)).1 hdσ
    rwa [mpullback_zero, mextDeriv_congr_of_eventuallyEq hση] at this
  have hι : ∀ᶠ y in 𝓝 x, mpullback I I' f (RoughForm.interior Z σ.val) y =
      RoughForm.interior X η.val y := by
    filter_upwards [hση, hXZ] with y h₁ h₂
    ext v
    rw [mpullback_interior_at f X Z σ.val h₂, RoughForm.interior_apply, RoughForm.interior_apply,
      h₁]
  have hιφ := RoughForm.contMDiffAt_interior hZ ((σ.contMDiff (f x)).of_le (by simp))
  rw [mlieDerivForm_eq_mextDeriv_interior_apply (σ.mdifferentiableAt (f x))
      (hZ.mdifferentiableAt (by simp)) hdσ,
    mlieDerivForm_eq_mextDeriv_interior_apply (η.mdifferentiableAt x)
      (hX.mdifferentiableAt (by simp)) hdη,
    hf.mextDeriv_apply_eq_iff (by simp) hιφ,
    mextDeriv_congr_of_eventuallyEq hι]

end IsLocalDiffeomorphAt

namespace IsLocalDiffeomorph

variable [IsManifold I 2 M] [IsManifold I' 2 M']

/-- Let `f : M → M'` be a `C^n` local diffeomorphism with `2 ≤ n`. If the field `Y` on `M'`
satisfies `ι_Y dα = α` for a smooth form `α`, then the pulled-back field `f^* Y` satisfies
`ι_{f^* Y} d(f^* α) = f^* α`. -/
theorem interior_mextDeriv_mpullback_of_interior_mextDeriv (hf : IsLocalDiffeomorph I I' n f)
    (hn : 2 ≤ n) {Y : (y : M') → TangentSpace I' y} {α : SmoothForm I' M' F k}
    (hYα : (mextDeriv α.val).interior Y = α.val) :
    (mextDeriv (mpullback I I' f α.val)).interior (VectorField.mpullback I I' f Y) =
      mpullback I I' f α.val := by
  have hd : mextDeriv (mpullback I I' f α.val) = mpullback I I' f (mextDeriv α.val) :=
    funext fun x ↦ (mpullback_mextDeriv_at ((hf x).contMDiffAt.of_le hn)
      ((α.contMDiff (f x)).of_le (by simp))).symm
  have hY (x : M) := (hf x).mfderiv_apply_mpullback (lt_of_lt_of_le (by simp) hn).ne' Y
  rw [hd, ← mpullback_interior _ _ _ _ hY, hYα]

end IsLocalDiffeomorph

namespace TauCeti.SmoothForm

open scoped ContDiff

/-- **Transplants of symmetries.** Let `g : M → M'` be a smooth local diffeomorphism pulling `σ`
back to `τ`, and `Λ` a diffeomorphism of `M` preserving `τ`. A diffeomorphism `Ψ` of `M'` with
`Ψ ∘ g = g ∘ Λ` that fixes every point outside a closed set `C` contained in the range of `g`
preserves `σ`. -/
theorem mem_diffeomorphStabilizer_of_semiconj [IsManifold I 1 M] [IsManifold I' 1 M']
    {g : M → M'} (hg : IsLocalDiffeomorph I I' ∞ g) {τ : SmoothForm I M F k}
    {σ : SmoothForm I' M' F k} (hgσ : mpullback g hg.contMDiff σ = τ) {Λ : M ≃ₘ⟮I, I⟯ M}
    (hΛ : Λ ∈ diffeomorphStabilizer τ) {Ψ : M' ≃ₘ⟮I', I'⟯ M'} (h : Function.Semiconj g Λ Ψ)
    {C : Set M'} (hC : _root_.IsClosed C) (hCg : C ⊆ range g) (hΨ : ∀ x ∉ C, Ψ x = x) :
    Ψ ∈ diffeomorphStabilizer σ := by
  rw [mem_diffeomorphStabilizer_iff_forall]
  intro x
  by_cases hx : x ∈ range g
  · -- On the range of `g`, compare the pullbacks along `g`, whose differential is onto.
    obtain ⟨w, rfl⟩ := hx
    have hgΨ : mpullback g hg.contMDiff (mpullback Ψ Ψ.contMDiff σ) =
        mpullback g hg.contMDiff σ := by
      rw [mpullback_mpullback_of_comp_eq _ _ Λ.contMDiff hg.contMDiff h.comp_eq.symm, hgσ,
        mem_diffeomorphStabilizer.1 hΛ]
    exact (mpullback_apply_eq_mpullback_apply_iff
      (hg.isInvertible_mfderiv (by simp) w).surjective).1
      (by simpa only [coe_mpullback] using congrFun (congrArg Subtype.val hgΨ) w)
  · -- Off the range of `g`, `Ψ` is the identity near `x`, outside the closed set `C`.
    have hx' : x ∉ C := fun hx' ↦ hx (hCg hx')
    have hid : (Ψ : M' → M') =ᶠ[𝓝 x] id :=
      Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hx') hΨ
    rw [hid.mpullback_eq, TauCeti.mpullback_id]

/-- **Carrying an exactness identity from a chart.** Let `e` be a smooth partial diffeomorphism
from `M` to a Hausdorff manifold `M'`, and `C ⊆ W ⊆ e.source` with `C` compact and `W` open. Let
`Φ` be a diffeomorphism of `M'` that fixes every point outside `e '' C`, `θ` a one-form on `M'`,
and `k` a function on `M` that is smooth on `W` and vanishes on `W` outside `C`, such that
`(Φ ∘ e)^* θ - e^* θ = dk` at each point of `W`. Then `Φ^* θ - θ = dK` for a smooth function `K`
on `M'` that vanishes outside `e '' C` and agrees with `k ∘ e⁻¹` on `e '' W`. -/
theorem exists_mpullback_sub_eq_mextDerivₗ_of_partialDiffeomorph [IsManifold I ∞ M]
    [IsManifold I' ∞ M'] [T2Space M'] (e : PartialDiffeomorph I I' M M' ∞) {C W : Set M}
    (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W) (hWe : W ⊆ e.source)
    {Φ : M' ≃ₘ⟮I', I'⟯ M'} (hΦ : ∀ x ∉ e '' C, Φ x = x) {θ : SmoothForm I' M' ℝ 1} {k : M → ℝ}
    (hk : ContMDiffOn I 𝓘(ℝ) ∞ k W) (hk0 : ∀ z ∈ W, z ∉ C → k z = 0)
    (hθk : ∀ z ∈ W, TauCeti.mpullback I I' (Φ ∘ e) θ.val z - TauCeti.mpullback I I' e θ.val z =
      mextDeriv (RoughForm.ofFunction I k) z) :
    ∃ K : C^∞⟮I', M'; ℝ⟯, (∀ x ∉ e '' C, K x = 0) ∧ (∀ z ∈ W, K (e z) = k z) ∧
      mpullback Φ Φ.contMDiff θ - θ = mextDerivₗ I' 0 (ofFunction K) := by
  have hCc : _root_.IsClosed (e '' C) :=
    (e.isCompact_image_of_subset_source hC (hCW.trans hWe)).isClosed
  -- `K` is `k ∘ e⁻¹` on `e '' W`, extended by `0`.
  set K₀ : M' → ℝ := (e '' W).indicator fun y ↦ k (e.symm y) with hK₀
  have hK₀e : ∀ z ∈ W, K₀ (e z) = k z := fun z hz ↦ by
    rw [hK₀, indicator_of_mem (mem_image_of_mem _ hz), PartialDiffeomorph.symm_toPartialEquiv,
      e.left_inv (hWe hz)]
  have hK₀C : ∀ x ∉ e '' C, K₀ x = 0 := fun x hx ↦ by
    by_cases hxW : x ∈ e '' W
    · obtain ⟨z, hz, rfl⟩ := hxW
      rw [hK₀e z hz, hk0 z hz fun hzC ↦ hx (mem_image_of_mem _ hzC)]
    · exact indicator_of_notMem hxW _
  have hK₀s : ContMDiff I' 𝓘(ℝ) ∞ K₀ :=
    e.contMDiff_indicator_image_comp_symm hk hCc hW hCW hWe hk0
  set K : C^∞⟮I', M'; ℝ⟯ := ⟨K₀, hK₀s⟩
  have hKK : ⇑K = K₀ := ContMDiffMap.coeFn_mk K₀ hK₀s
  refine ⟨K, hKK ▸ hK₀C, hKK ▸ hK₀e, Subtype.ext (funext fun x ↦ ?_)⟩
  simp only [mextDerivₗ_apply, coe_ofFunction, hKK, Submodule.coe_sub, Pi.sub_apply,
    coe_mpullback]
  by_cases hx : x ∈ e '' W
  · -- On `e '' W`, compare the pullbacks along `e`, whose differential is invertible.
    obtain ⟨z, hz, rfl⟩ := hx
    refine (((e.isLocalDiffeomorphAt I I' ∞ (hWe hz)).mextDeriv_apply_eq_iff (by simp)
      (φ := RoughForm.ofFunction I' K₀) (ψ := TauCeti.mpullback I' I' Φ θ.val - θ.val)
      (contMDiffAt_ofFunction_iff.2 ((hK₀s _).of_le (by simp)))).2 ?_).symm
    rw [mpullback_ofFunction, mpullback_sub, Pi.sub_apply,
      ← mpullback_comp_at (e.mdifferentiableAt (by simp) (hWe hz))
        (Φ.contMDiff.mdifferentiable (by simp) _), hθk z hz]
    -- Near `z`, `K₀ ∘ e` is `k`.
    exact mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (c := 0) <|
      eventually_of_mem (hW.mem_nhds hz) fun y hy ↦ by simp [hK₀e y hy]
  · -- Off `e '' C`, `Φ` is the identity and `K₀` vanishes near `x`.
    have hnhds := hCc.isOpen_compl.mem_nhds fun h ↦ hx (image_mono hCW h)
    have hid : (Φ : M' → M') =ᶠ[𝓝 x] id := eventually_of_mem hnhds hΦ
    rw [hid.mpullback_eq, TauCeti.mpullback_id, sub_self,
      mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (g := 0) (c := 0)
        (eventually_of_mem hnhds fun y hy ↦ by simp [hK₀C y hy]),
      mextDeriv_ofFunction_zero, Pi.zero_apply]

end TauCeti.SmoothForm

end
