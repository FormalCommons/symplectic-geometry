/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullback of forms: values, `d`, cut-offs, smoothness, negation, exactness, constant maps, slices

At a point `x`, the pullback of a form `φ` along `f` is the value of `φ` at `f x` composed with
the differential of `f` at `x` (`TauCeti.mpullback_apply_eq_compContinuousLinearMap`). The
statement is on the tangent spaces, so that Mathlib's bound
`ContinuousAlternatingMap.norm_compContinuousLinearMap_le` applies with their norms, such as
Riemannian ones. Tau Ceti's `TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM` states the
same equality on the model spaces.
So two maps with the same value and the same differential at `x` pull every form back to the
same value at `x` (`TauCeti.mpullback_apply_eq_of_mfderiv_eq`). With Tau Ceti's locality and
naturality of the exterior derivative, it gives `dθ` at `x` for a smooth form `θ` that agrees
near `x` with a pullback (`TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`).
On a basis `c` of the tangent space at `x`, the pullback takes the value of `φ (f x)` on the
image of `c` under the differential, when that is given as a linear equivalence
(`TauCeti.mpullback_apply_basis_map`). On three vectors `![u, v, w]`, the pullback of a three-form
is the form on their images under the differential (`TauCeti.mpullback_apply_triple`), as Tau
Ceti's `TauCeti.mpullback_apply_pair` says for two-forms.
With naturality alone, when `f` maps `s` into `t`, a form that is exact on a neighbourhood of `t`
pulls back to one that is exact on a neighbourhood of `s`
(`TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`).

For a two-form, the value of `f^* φ` at `g x` on two vectors in the image of `dg` is, by the chain
rule, the value of `φ` on their images under `du`, wherever `f ∘ g = u` near `x`
(`TauCeti.SmoothForm.eval₂_mpullback_mfderiv_of_comp_eventuallyEq`). Tau Ceti's
`TauCeti.Geometry.Contact.Symplectization.Annihilator` proves a case of it, for the pullback of
`dλ` along a map of the cotangent bundle, in a private lemma.

If `f : M → M` preserves a function `ρ`, and the pullback of `φ` along `f` agrees with `φ` where
`ρ` does not vanish, then `f` pulls `ρ • φ` back to itself
(`TauCeti.mpullback_fun_smul_eq_self`): a form cut off by an invariant function is invariant as
soon as it is so on the support of the cut-off.

Let `g : M → M'` be `C^n` on an open set `u`, and `f : M → ℝ` a `C^m` function with
`tsupport f ⊆ u`, where `m + 1 ≤ n`. Then for a `C^m` form `φ` on `M'`, the form `f • g^* φ` on
`M` is `C^m`, although `g` need not be smooth off `u`
(`TauCeti.isSmoothForm_fun_smul_mpullback`, a step of the proof of Tau Ceti's
`TauCeti.isSmoothForm_sum_finsupport_smul_mpullback` stated on its own, at any order).

Pulling a form back commutes with negation (`TauCeti.mpullback_neg`), as Tau Ceti's
`TauCeti.mpullback_sub` says for subtraction. So a diffeomorphism preserves `-σ` exactly when it
preserves `σ` (`TauCeti.SmoothForm.diffeomorphStabilizer_neg`).

By Tau Ceti's naturality `TauCeti.mpullback_mextDeriv_ofFunction_apply`, and
`TauCeti.mextDeriv_ofFunction_sub_apply` of `DifferentialForm/ExtDeriv.lean`, if `α = β + dg` at
`x` and at `f x` for a self-map `f` differentiable at `x`, and `g` is differentiable at both
points, then `f^* α - α` and `f^* β - β` differ at `x` by the exact form
`d(g ∘ f - g)` (`TauCeti.mpullback_apply_sub_eq_of_eq_add_mextDeriv`).

Pulling a smooth form of positive degree back along a constant map gives the zero form
(`TauCeti.SmoothForm.mpullback_const`, the smooth case of Tau Ceti's
`TauCeti.mpullback_const`). So the slice
`x ↦ (x, p)` of the pullback of such a form along the projection `M × M' → M'` is zero
(`TauCeti.SmoothForm.mpullback_prodMk_left_mpullback_snd`). In the same way the slice
`y ↦ (b, y)` of the pullback of such a form along the projection `M × M' → M` is zero
(`TauCeti.SmoothForm.mpullback_prodMk_mpullback_fst`), so adding such a pullback to a form on
`M × M'` leaves its slice `y ↦ (b, y)` unchanged
(`TauCeti.SmoothForm.mpullback_prodMk_add_mpullback_fst`).

For a map `f : M × M₂ → M'`, the slice `z ↦ f (s, z)` is `f` composed with the inclusion
`z ↦ (s, z)`, whose differential is `w ↦ (0, w)`
(`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right`). By the chain
rule `TauCeti.mpullback_comp_at`, the pullback along the slice at `z` is the pullback along `f` at
`(s, z)` on the vectors `(0, m i)` (`TauCeti.mpullback_comp_prodMk_apply`). When both factors are
normed spaces with their own models, `𝓘(ℝ, E₁ × E₂)` is not syntactically the product model, so
`TauCeti.mpullback_comp_prodMk_apply_modelSpace` states the same identity for that model.

By Tau Ceti's `TauCeti.mpullback_comp_add_right`, if a map `u` of a normed space is invariant
under translation by `c`, so is the pullback along `u` of every form
(`TauCeti.mpullback_add_of_forall_add_eq`).

## Main results

* `TauCeti.mpullback_apply_eq_compContinuousLinearMap`: the pullback at `x` is
  `(φ (f x)).compContinuousLinearMap (mfderiv I I' f x)`.
* `TauCeti.mpullback_apply_triple`: the pullback of a three-form at `x` on `![u, v, w]` is the
  form at `f x` on the images of `u`, `v`, `w` under the differential.
* `TauCeti.mpullback_apply_eq_of_mfderiv_eq`: the pullback at `x` depends only on the value and
  the differential of the map at `x`.
* `Filter.EventuallyEq.mpullback_apply_eq_self`, and its smooth case
  `TauCeti.SmoothForm.mpullback_apply_eq_self_of_eventuallyEq_id`: pulling back along a map that
  is the identity near `x` does not change the value of a form at `x`.
* `TauCeti.SmoothForm.mpullback_eq_self_of_eq_id`: pulling a smooth form back along a smooth
  map equal to the identity gives the form back.
* `TauCeti.mpullback_apply_basis_map`: the pullback at `x` on a basis `c` is `φ (f x)` on the
  image of `c` under the differential, when that is a linear equivalence.
* `TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`: if a smooth form agrees near `x` with
  `f^* α`, its exterior derivative at `x` is `dα` at `f x` composed with `mfderiv f x`.
* `TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`: a form exact near `t` pulls
  back along a map from `s` into `t` to a form exact near `s`.
* `TauCeti.SmoothForm.eval₂_mpullback_mfderiv_of_comp_eventuallyEq`: if `f ∘ g = u` near `x`,
  the value of `f^* φ` at `g x` on the images of two vectors under `dg` is the value of `φ` at
  `u x` on their images under `du`.
* `TauCeti.mpullback_fun_smul_eq_self`: a form multiplied by a function `ρ` is invariant under a
  map that preserves `ρ`, if the form is so where `ρ` does not vanish.
* `TauCeti.isSmoothForm_fun_smul_mpullback`: a `C^m` function times the pullback of a `C^m` form
  along a map that is `C^(m+1)` on an open set containing the function's support is a `C^m` form.
* `TauCeti.mpullback_neg`: the pullback of `-φ` is minus the pullback of `φ`.
* `TauCeti.SmoothForm.mpullback_eq_iff`: an equation `f^* φ = ψ` of smooth forms is the same
  equation of their underlying rough forms; `TauCeti.SmoothForm.mpullback_eq_mpullback_iff` does
  the same for an equation `f^* φ = g^* ψ` of two pullbacks.
* `TauCeti.SmoothForm.diffeomorphStabilizer_neg`: a diffeomorphism preserves `-σ` exactly when
  it preserves `σ`.
* `TauCeti.mpullback_apply_sub_eq_of_eq_add_mextDeriv`: if `α = β + dg` at `x` and at `f x`,
  then `(f^* α - α) x = (f^* β - β) x + d(g ∘ f - g) x`.
* `TauCeti.SmoothForm.mpullback_const`: the pullback of a smooth `(k + 1)`-form along a constant
  map is `0`.
* `TauCeti.SmoothForm.mpullback_prodMk_left_mpullback_snd`: the slice `x ↦ (x, p)` of the
  pullback of a smooth `(k + 1)`-form along `Prod.snd` is `0`.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_fst`: the slice `y ↦ (b, y)` of the pullback
  of a smooth `(k + 1)`-form along `Prod.fst` is `0`.
* `TauCeti.SmoothForm.mpullback_prodMk_add_mpullback_fst`: adding the pullback of a smooth
  `(k + 1)`-form along `Prod.fst` to a smooth form on `M × M'` does not change its slice
  `y ↦ (b, y)`.
* `TauCeti.mpullback_comp_prodMk_apply`: the pullback along a slice `z ↦ f (s, z)` of a map on a
  product, as the pullback along `f` on the vectors `(0, m i)`.
* `TauCeti.mpullback_comp_prodMk_apply_modelSpace`: the same, for a map on a product of normed
  spaces with the model `𝓘(ℝ, E₁ × E₂)`.
* `TauCeti.mpullback_add_of_forall_add_eq`: the pullback along a map invariant under a translation
  is invariant under it.
* `TauCeti.SmoothForm.mpullback_comp_comp_eq_of_mpullback_eq`: if `a^* (i^* σ) = j^* τ`, then
  `(i ∘ a ∘ g)^* σ = (j ∘ g)^* τ` for every smooth `g`.
* `TauCeti.SmoothForm.contDiff_apply_mfderiv`: along a smooth map `γ` from a normed space, a
  smooth form evaluated on the images under `dγ` of fixed vectors is a smooth function, with
  `TauCeti.SmoothForm.contDiff_apply_one_mfderiv` and
  `TauCeti.SmoothForm.differentiable_apply_one_mfderiv` for one-forms.
-/

public section

open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- At a point `x`, the pullback of `φ` along `f` is `φ (f x)` composed with the differential of
`f` at `x`, as an alternating map on the tangent space at `x`. -/
theorem mpullback_apply_eq_compContinuousLinearMap (f : M → M') (φ : RoughForm I' M' F k)
    (x : M) :
    mpullback I I' f φ x = (φ (f x)).compContinuousLinearMap (mfderiv I I' f x) :=
  ContinuousAlternatingMap.ext fun v ↦ mpullback_apply f φ x v

/-- The pullback of a three-form at `x`, evaluated on three tangent vectors, is the form at `f x`
evaluated on their images under the differential of `f` at `x`; Tau Ceti's
`TauCeti.mpullback_apply_pair` is the same statement for two-forms. -/
theorem mpullback_apply_triple (f : M → M') (φ : RoughForm I' M' F 3) (x : M)
    (u v w : TangentSpace I x) :
    mpullback I I' f φ x ![u, v, w] =
      φ (f x) ![mfderiv I I' f x u, mfderiv I I' f x v, mfderiv I I' f x w] := by
  rw [mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Two maps with the same value and the same differential at `x` pull a form back to the same
value at `x`. -/
theorem mpullback_apply_eq_of_mfderiv_eq {f g : M → M'} {x : M} (h : f x = g x)
    (hd : mfderiv I I' f x = mfderiv I I' g x) (φ : RoughForm I' M' F k) :
    mpullback I I' f φ x = mpullback I I' g φ x := by
  rw [mpullback_apply_eq_compContinuousLinearMap, mpullback_apply_eq_compContinuousLinearMap, hd,
    h]

/-- A map that is the identity near `x` pulls every form back to a form with the same value at
`x`. -/
theorem _root_.Filter.EventuallyEq.mpullback_apply_eq_self {f : M → M} {x : M}
    (h : f =ᶠ[𝓝 x] id) (φ : RoughForm I M F k) : mpullback I I f φ x = φ x := by
  rw [h.mpullback_eq, mpullback_id]

/-- The pullback `f^* φ` at `x`, evaluated on a basis `c` of the tangent space at `x`, is `φ` at
`f x` evaluated on the image of `c` under a linear equivalence `e` whose underlying map is the
differential of `f` at `x`. -/
theorem mpullback_apply_basis_map {f : M → M'} {x : M}
    {e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x)}
    (he : (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x)
    (φ : RoughForm I' M' F k) (c : Module.Basis (Fin k) ℝ (TangentSpace I x)) :
    mpullback I I' f φ x c = φ (f x) (c.map e.toLinearEquiv) := by
  rw [mpullback_apply]
  congr 1
  funext i
  simp [← he]

/-- If a smooth form `θ` on `M` agrees near `x` with the pullback `f^* α` of a smooth form `α` on
`M'` along a map `f` that is `C²` at `x`, then the exterior derivative `dθ` at `x` is `dα` at `f x`
composed with the differential of `f` at `x`. -/
theorem mextDerivₗ_apply_eq_of_eventuallyEq_mpullback [IsManifold I 2 M] [IsManifold I' 2 M']
    {f : M → M'} {x : M} (hf : ContMDiffAt I I' 2 f x) {θ : SmoothForm I M F k}
    {α : SmoothForm I' M' F k} (hθ : ∀ᶠ y in 𝓝 x, θ.val y = mpullback I I' f α.val y) :
    (mextDerivₗ I k θ).val x =
      ((mextDerivₗ I' k α).val (f x)).compContinuousLinearMap (mfderiv I I' f x) := by
  rw [mextDerivₗ_apply, mextDerivₗ_apply, mextDeriv_congr_of_eventuallyEq hθ,
    ← mpullback_mextDeriv_at hf ((α.contMDiff _).of_le (by simp)),
    mpullback_apply_eq_compContinuousLinearMap]

/-- Let `f : M → M` preserve `ρ : M → ℝ`, and let the pullback of a form `φ` along `f` agree with
`φ` wherever `ρ` does not vanish. Then the pullback of `ρ • φ` along `f` is `ρ • φ`. -/
theorem mpullback_fun_smul_eq_self {f : M → M} {ρ : M → ℝ} {φ : RoughForm I M F k}
    (hρ : ∀ x, ρ (f x) = ρ x) (hφ : ∀ x, ρ x ≠ 0 → mpullback I I f φ x = φ x) :
    mpullback I I f (fun x ↦ ρ x • φ x) = fun x ↦ ρ x • φ x := by
  rw [mpullback_fun_smul]
  funext x
  rw [hρ]
  by_cases hx : ρ x = 0
  · simp [hx]
  · rw [hφ x hx]

/-- Let `f` be a `C^m` function on `M` whose topological support lies in an open set `u`, and
let `g : M → M'` be `C^n` at every point of `u`, with `m + 1 ≤ n`. Then for every `C^m` form `φ`
on `M'`, the form `f • g^* φ`, which vanishes off the support of `f`, is a `C^m` form on `M`. -/
theorem isSmoothForm_fun_smul_mpullback [IsManifold I 1 M] [IsManifold I' 1 M']
    {m n : WithTop ℕ∞} {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) m f) {u : Set M} (hu : IsOpen u)
    (hfu : tsupport f ⊆ u) {g : M → M'} (hg : ∀ x ∈ u, ContMDiffAt I I' n g x) (hmn : m + 1 ≤ n)
    {φ : RoughForm I' M' F k} (hφ : IsSmoothForm I' m φ) :
    IsSmoothForm I m (fun x ↦ f x • mpullback (F := F) I I' g φ x) := by
  rw [isSmoothForm_def]
  exact ContMDiffOn.smul_section_of_tsupport hf.contMDiffOn hu hfu fun x hx ↦
    ((hφ.contMDiff (g x)).mpullback_form (hg x hx) hmn).contMDiffWithinAt

/-- Pullback commutes with negation. -/
@[simp]
theorem mpullback_neg (f : M → M') (φ : RoughForm I' M' F k) :
    mpullback I I' f (-φ) = -mpullback I I' f φ := by
  funext x
  ext v
  simp [mpullback_apply]

/-- Let `f : M → M` be differentiable at `x`, and `g : M → F` at `x` and at `f x`, and let the
one-forms `α` and `β` satisfy `α = β + dg` at `x` and at `f x`. Then at `x`,
`f^* α - α = (f^* β - β) + d(g ∘ f - g)`. -/
theorem mpullback_apply_sub_eq_of_eq_add_mextDeriv {f : M → M} {g : M → F} {x : M}
    (hf : MDifferentiableAt I I f x) (hgx : MDifferentiableAt I 𝓘(ℝ, F) g x)
    (hgfx : MDifferentiableAt I 𝓘(ℝ, F) g (f x)) {α β : RoughForm I M F 1}
    (hx : α x = β x + mextDeriv (RoughForm.ofFunction I g) x)
    (hfx : α (f x) = β (f x) + mextDeriv (RoughForm.ofFunction I g) (f x)) :
    mpullback I I f α x - α x =
      mpullback I I f β x - β x + mextDeriv (RoughForm.ofFunction I (g ∘ f - g)) x := by
  rw [mpullback_apply_congr (η := β + mextDeriv (RoughForm.ofFunction I g)) hfx, hx,
    mpullback_add, Pi.add_apply, mpullback_mextDeriv_ofFunction_apply hf hgfx,
    mextDeriv_ofFunction_sub_apply (hgfx.comp x hf) hgx]
  abel

/-- Let `f : M × M₂ → M'` be differentiable at `(s, z)`. The pullback of `φ` along the slice
`z ↦ f (s, z)`, at `z` on vectors `m i`, is the pullback of `φ` along `f`, at `(s, z)` on the
vectors `(0, m i)`. -/
theorem mpullback_comp_prodMk_apply {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} {f : M × M₂ → M'} {s : M} {z : M₂}
    (hf : MDifferentiableAt (I.prod I₂) I' f (s, z)) (φ : RoughForm I' M' F k)
    (m : Fin k → TangentSpace I₂ z) :
    mpullback I₂ I' (fun z ↦ f (s, z)) φ z m =
      mpullback (I.prod I₂) I' f φ (s, z) fun i ↦ ((0 : E), m i) := by
  -- The slice is `f ∘ Prod.mk s` by definition.
  refine (DFunLike.congr_fun (mpullback_comp_at (f := Prod.mk s) (g := f)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) hf φ) m).trans ?_
  rw [mpullback_apply]
  exact congrArg _ (funext fun i ↦ mfderiv_prodMk_right_apply (m i))

/-- Let `f : E₁ × E₂ → M'`, on a product of normed spaces, be differentiable at `(s, z)` for the
model `𝓘(ℝ, E₁ × E₂)`. The pullback of `φ` along the slice `z ↦ f (s, z)`, at `z` on vectors
`m i`, is the pullback of `φ` along `f`, at `(s, z)` on the vectors `(0, m i)`. -/
theorem mpullback_comp_prodMk_apply_modelSpace {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {f : E₁ × E₂ → M'} {s : E₁}
    {z : E₂} (hf : MDifferentiableAt 𝓘(ℝ, E₁ × E₂) I' f (s, z)) (φ : RoughForm I' M' F k)
    (m : Fin k → E₂) :
    mpullback 𝓘(ℝ, E₂) I' (fun z ↦ f (s, z)) φ z m =
      mpullback 𝓘(ℝ, E₁ × E₂) I' f φ (s, z) fun i ↦ ((0 : E₁), m i) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hf ⊢
  exact mpullback_comp_prodMk_apply hf φ m

/-- If a differentiable map `u` of a normed space satisfies `u (w + c) = u w` for every `w`, the
pullback `u^* φ` of any form is invariant under translation by `c`. -/
theorem mpullback_add_of_forall_add_eq {u : E' → M} (hu : MDifferentiable 𝓘(ℝ, E') I u) {c : E'}
    (hc : ∀ w, u (w + c) = u w) (φ : RoughForm I M F k) (y : E') :
    mpullback 𝓘(ℝ, E') I u φ (y + c) = mpullback 𝓘(ℝ, E') I u φ y := by
  have h := mpullback_comp_add_right (hu (y + c)) φ
  rw [funext hc] at h
  exact h.symm

namespace SmoothForm

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The smooth pullback of `φ` along `f` is the smooth form `ψ` exactly when the rough pullback
of the rough form underlying `φ` is the rough form underlying `ψ`. -/
theorem mpullback_eq_iff {f : M → M'} (hf : ContMDiff I I' ∞ f) {φ : SmoothForm I' M' F k}
    {ψ : SmoothForm I M F k} :
    mpullback f hf φ = ψ ↔ TauCeti.mpullback (F := F) I I' f φ.val = ψ.val := by
  rw [← coe_mpullback _ hf, Subtype.ext_iff]

omit [IsManifold I 1 M] in
/-- **Chain rule for the value of a pulled-back two-form.** Let `f` be smooth, `g`
differentiable at `x`, and `f ∘ g` equal to `u` near `x`. Then the pullback of `φ` along `f`,
evaluated at `g x` on the images of `v` and `w` under the differential of `g` at `x`, is `φ`
evaluated at `u x` on the images of `v` and `w` under the differential of `u` at `x`. -/
theorem eval₂_mpullback_mfderiv_of_comp_eventuallyEq {E'' H'' M'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H''] [TopologicalSpace M'']
    [ChartedSpace H'' M''] {I'' : ModelWithCorners ℝ E'' H''} [IsManifold I'' 1 M'']
    {f : M' → M''} (hf : ContMDiff I' I'' ∞ f) (φ : SmoothForm I'' M'' F 2) {g : M → M'}
    {u : M → M''} {x : M} (hg : MDifferentiableAt I I' g x) (hu : f ∘ g =ᶠ[𝓝 x] u)
    (v w : TangentSpace I x) :
    (mpullback f hf φ).eval₂ (g x) (mfderiv I I' g x v) (mfderiv I I' g x w) =
      φ.eval₂ (u x) (mfderiv I I'' u x v) (mfderiv I I'' u x w) := by
  have hf' : MDifferentiableAt I' I'' f (g x) := (hf (g x)).mdifferentiableAt (by simp)
  rw [eval₂_mpullback, ← mfderiv_comp_apply x hf' hg, ← mfderiv_comp_apply x hf' hg,
    hu.mfderiv_eq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact eval₂_tangentSpaceCast φ hu.eq_of_nhds.symm _ _

/-- A smooth map that is the identity near `x` pulls a smooth form `θ` back to a form with the
same value as `θ` at `x`. -/
theorem mpullback_apply_eq_self_of_eventuallyEq_id {f : M → M} (hf : ContMDiff I I ∞ f) {x : M}
    (h : f =ᶠ[𝓝 x] id) (θ : SmoothForm I M F k) : (mpullback f hf θ).val x = θ.val x := by
  rw [coe_mpullback, h.mpullback_apply_eq_self]

/-- Pulling a smooth form back along a smooth map equal to the identity gives the form back. -/
theorem mpullback_eq_self_of_eq_id {f : M → M} (hf : ContMDiff I I ∞ f) (h : f = id)
    (θ : SmoothForm I M F k) : mpullback f hf θ = θ := by
  rw [mpullback_congr _ contMDiff_id h, mpullback_id, LinearMap.id_apply]

/-- The smooth pullbacks of `φ` along `f` and of `ψ` along `g` agree exactly when the rough
pullbacks of the underlying rough forms agree. -/
theorem mpullback_eq_mpullback_iff {E'' H'' M'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] [TopologicalSpace M''] [ChartedSpace H'' M'']
    {I'' : ModelWithCorners ℝ E'' H''} [IsManifold I'' 1 M''] {f : M → M'}
    (hf : ContMDiff I I' ∞ f) {g : M → M''} (hg : ContMDiff I I'' ∞ g)
    {φ : SmoothForm I' M' F k} {ψ : SmoothForm I'' M'' F k} :
    mpullback f hf φ = mpullback g hg ψ ↔
      TauCeti.mpullback (F := F) I I' f φ.val = TauCeti.mpullback I I'' g ψ.val := by
  rw [mpullback_eq_iff, coe_mpullback]

/-- A diffeomorphism preserves `-σ` exactly when it preserves `σ`. -/
@[simp]
theorem diffeomorphStabilizer_neg (σ : SmoothForm I M F k) :
    diffeomorphStabilizer (-σ) = diffeomorphStabilizer σ := by
  ext φ
  simp only [mem_diffeomorphStabilizer, map_neg, neg_inj]

/-- The pullback of a smooth form of positive degree along a constant map is zero. -/
@[simp]
theorem mpullback_const (c : M') (hc : ContMDiff I I' ∞ fun _ : M ↦ c)
    (φ : SmoothForm I' M' F (k + 1)) : mpullback (fun _ : M ↦ c) hc φ = 0 := by
  rw [mpullback_eq_iff, TauCeti.mpullback_const k.succ_ne_zero, ZeroMemClass.coe_zero]

/-- The slice `x ↦ (x, p)` of the pullback of a smooth `(k + 1)`-form `β` on `M'` along the
projection `M × M' → M'` is zero, since the projection is constant on the slice. -/
@[simp]
theorem mpullback_prodMk_left_mpullback_snd (p : M') (β : SmoothForm I' M' F (k + 1)) :
    mpullback (fun x : M ↦ (x, p)) (contMDiff_id.prodMk contMDiff_const)
      (mpullback Prod.snd contMDiff_snd β : SmoothForm (I.prod I') (M × M') F (k + 1)) = 0 := by
  simp [mpullback_mpullback, Function.comp_def]

/-- The slice `y ↦ (b, y)` of the pullback of a smooth `(k + 1)`-form `γ` on `M` along the
projection `M × M' → M` is zero, since the projection is constant on the slice. -/
@[simp]
theorem mpullback_prodMk_mpullback_fst (b : M) (γ : SmoothForm I M F (k + 1)) :
    mpullback (Prod.mk b : M' → M × M') (contMDiff_const.prodMk contMDiff_id)
      (mpullback Prod.fst contMDiff_fst γ : SmoothForm (I.prod I') (M × M') F (k + 1)) = 0 := by
  simp [mpullback_mpullback, Function.comp_def]

/-- Adding the pullback of a smooth `(k + 1)`-form `γ` on `M` along the projection `M × M' → M`
to a smooth form `τ` on `M × M'` does not change the slice `y ↦ (b, y)` of `τ`. -/
theorem mpullback_prodMk_add_mpullback_fst (b : M) (τ : SmoothForm (I.prod I') (M × M') F (k + 1))
    (γ : SmoothForm I M F (k + 1)) :
    TauCeti.mpullback (F := F) I' (I.prod I') (Prod.mk b)
        (τ + mpullback Prod.fst contMDiff_fst γ).val =
      TauCeti.mpullback I' (I.prod I') (Prod.mk b) τ.val := by
  have h := congrArg Subtype.val (mpullback_prodMk_mpullback_fst (I' := I') (M' := M') b γ)
  rw [coe_mpullback, ZeroMemClass.coe_zero] at h
  rw [Submodule.coe_add, TauCeti.mpullback_add, h, add_zero]

/-- Let `γ : E → M'` be a smooth map from a normed space. Evaluating a smooth `k`-form `η` at
`γ y` on the images under `dγ_y` of fixed vectors `v i` gives a smooth function of `y`. -/
theorem contDiff_apply_mfderiv (η : SmoothForm I' M' F k) {γ : E → M'}
    (hγ : ContMDiff 𝓘(ℝ, E) I' ∞ γ) (v : Fin k → E) :
    ContDiff ℝ ∞ fun y ↦ η.val (γ y) fun i ↦ mfderiv 𝓘(ℝ, E) I' γ y (v i) := by
  have h := isSmoothForm_modelSpace_iff.1 (mpullback γ hγ η).isSmoothForm
  convert (ContinuousAlternatingMap.apply ℝ E F v).contDiff.comp h using 1
  funext y
  exact (mpullback_apply γ hγ η y v).symm

/-- Let `γ : E → M'` be a smooth map from a normed space. Evaluating a smooth one-form `η` at
`γ y` on `dγ_y w`, for a fixed vector `w`, gives a smooth function of `y`. -/
theorem contDiff_apply_one_mfderiv (η : SmoothForm I' M' F 1) {γ : E → M'}
    (hγ : ContMDiff 𝓘(ℝ, E) I' ∞ γ) (w : E) :
    ContDiff ℝ ∞ fun y ↦ η.val (γ y) ![mfderiv 𝓘(ℝ, E) I' γ y w] := by
  convert contDiff_apply_mfderiv η hγ ![w] using 2 with y
  -- `w` is a vector of `E` rather than of a tangent space, so the lemmas are applied by `exact`.
  exact (mpullback_apply_one γ hγ η y w).symm.trans (mpullback_apply γ hγ η y ![w])

/-- Let `γ : E → M'` be a smooth map from a normed space. Evaluating a smooth one-form `η` at
`γ y` on `dγ_y w`, for a fixed vector `w`, gives a differentiable function of `y`. -/
theorem differentiable_apply_one_mfderiv (η : SmoothForm I' M' F 1) {γ : E → M'}
    (hγ : ContMDiff 𝓘(ℝ, E) I' ∞ γ) (w : E) :
    Differentiable ℝ fun y ↦ η.val (γ y) ![mfderiv 𝓘(ℝ, E) I' γ y w] :=
  (contDiff_apply_one_mfderiv η hγ w).differentiable (by simp)

end SmoothForm

namespace SmoothForm

variable [IsManifold I 2 M] [IsManifold I' 2 M']

/-- Let `f` map `s` into `t`. If `dγ` is `τ` on a neighbourhood of `t`, then `d (f^* γ)` is
`f^* τ` on a neighbourhood of `s`: a form exact near `t` pulls back to a form exact near `s`. -/
theorem exists_mem_nhdsSet_mextDerivₗ_mpullback_eq {f : M → M'} (hf : ContMDiff I I' ∞ f)
    {s : Set M} {t : Set M'} (hst : Set.MapsTo f s t) {γ : SmoothForm I' M' F k}
    {τ : SmoothForm I' M' F (k + 1)} {V : Set M'} (hV : V ∈ 𝓝ˢ t)
    (hγ : ∀ y ∈ V, (mextDerivₗ I' k γ).val y = τ.val y) :
    ∃ V' ∈ 𝓝ˢ s, ∀ x ∈ V', (mextDerivₗ I k (mpullback f hf γ)).val x = (mpullback f hf τ).val x :=
  ⟨f ⁻¹' V, hf.continuous.tendsto_nhdsSet hst hV, fun _ hx ↦ by
    rw [mextDerivₗ_mpullback, coe_mpullback, coe_mpullback]
    exact mpullback_apply_congr (hγ _ hx)⟩

end SmoothForm

namespace SmoothForm

/-- If `a` pulls `i^* σ` back to `j^* τ`, then for every smooth `g`, `i ∘ a ∘ g` pulls `σ` back
to `(j ∘ g)^* τ`. -/
theorem mpullback_comp_comp_eq_of_mpullback_eq {EN HN N EN' HN' N' EX HX X : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN] [TopologicalSpace N]
    [ChartedSpace HN N] {IN : ModelWithCorners ℝ EN HN} [IsManifold IN 1 N]
    [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN'] [TopologicalSpace N']
    [ChartedSpace HN' N'] {IN' : ModelWithCorners ℝ EN' HN'} [IsManifold IN' 1 N']
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX] [TopologicalSpace X]
    [ChartedSpace HX X] {IX : ModelWithCorners ℝ EX HX} [IsManifold IX 1 X]
    [IsManifold I 1 M] [IsManifold I' 1 M'] {a : N → N'} {i : N' → M'} {j : N → M}
    {ha : ContMDiff IN IN' ∞ a} {hi : ContMDiff IN' I' ∞ i} {hj : ContMDiff IN I ∞ j}
    {σ : SmoothForm I' M' F k} {τ : SmoothForm I M F k}
    (h : mpullback a ha (mpullback i hi σ) = mpullback j hj τ) {g : X → N}
    (hg : ContMDiff IX IN ∞ g) :
    mpullback (i ∘ a ∘ g) (hi.comp (ha.comp hg)) σ = mpullback (j ∘ g) (hj.comp hg) τ := by
  rw [mpullback_congr _ ((hi.comp ha).comp hg) (Function.comp_assoc i a g).symm]
  simpa only [mpullback_mpullback] using congrArg (mpullback g hg) h

end SmoothForm

end TauCeti
