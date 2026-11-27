/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
public import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.ContMDiff.Subtype.Cutoff
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Product
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic

/-!
# Moser's principle along local flows, and slices of families of forms

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional manifold `M`
without boundary, with time-dependent flow `φ_{s,t}` (`TauCeti.timeDependentFlowOf`), and let `α`
be a form on `ℝ × M` with slices `α_u = ι_u^* α`. Tau Ceti proves that if the rate
`ι_u^* L_{∂_t} α + L_{X_u} α_u` equals `g_u • α_u` everywhere, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • (α_s)ₓ`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`),
and also the form of this identity that needs the rate only along the trajectory of `x`, for `u`
between `s` and `t` (the variant of that theorem ending in `…_smul_of_forall_mem_uIcc`), which
Gray's argument uses.

This file treats the constant family `(u, y) ↦ β_y` of a form `β` on `M`, whose slices
are all `β` (`TauCeti.SmoothForm.mpullback_prodMk_mpullback_snd`). If `L_{X_u} β = g_u • β`
for every time `u`, with `g` continuous, then
`(φ_{s,t}^* β)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • βₓ` wherever the flow is defined: this is Tau
Ceti's `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`
for the constant family. Contact Hamiltonian flows use it.

The file also records how time derivatives of slices behave under pullback along
`id × f : ℝ × M → ℝ × N`, for a smooth `f : M → N`. The slice of `(id × f)^* α` at time `t` is
`f^* α_t` (Tau Ceti's `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap`), and the slice at
time `t` of its time derivative (`TauCeti.SmoothForm.timeDeriv`) is the pullback along `f` of
the slice of `∂_t α`: both are the velocity of `u ↦ f^* α_u`, by Tau Ceti's
`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`.

Finally, the file contracts forms on `ℝ × M` with the time field `∂_t = (1, 0)`, the smooth
section `SymplecticGeometry.timeField` of the tangent bundle. The contraction `ι_{∂_t} σ` of a
smooth form (`TauCeti.SmoothForm.timeInterior`) is the library's bundled interior product
`TauCeti.SmoothForm.interiorProduct` with it, which is linear in `σ`. For closed `σ`,
Cartan's formula `TauCeti.mlieDerivForm_eq_mextDeriv_interior` makes its exterior derivative
the time derivative of `σ`. Since `id × f` sends `∂_t` to `∂_t`, the contraction commutes with
pullback along `id × f`, and it vanishes on forms pulled back from `M` along the projection.

Last, the restriction of a form on `ℝ × M` to `J × M`, for an open set `J` of times, has the
same time derivative at each time of `J`. It is read on `ℝ × M` through a map `ℝ → J` which is
the identity near that time (Tau Ceti's `TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`),
and Tau Ceti's `TauCeti.hasDerivAt_mpullback_prodMk_comp` computes the derivative there. The
proof adapts that of Tau Ceti's `TauCeti.mpullback_prodMk_mlieDerivForm_mpullback_prodMap`,
which goes the other way, from a form on `J × M` to its pullback to `ℝ × M` through a map
`ℝ → J`.

## Main results

* `TauCeti.mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq`: a smooth
  form with `L_{X_u} β = g_u • β` satisfies `(φ_{s,t}^* β)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • βₓ`
  wherever the flow is defined.
* `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap'`: the slices of the time
  derivative, for a reparametrization `c` of time,
  `ι_t^* ∂_t ((c × f)^* α) = c'(t) f^* ι_{c t}^* ∂_t α`; the case `c = id` is Tau Ceti's
  `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap`.
* `TauCeti.SmoothForm.timeInterior`: the contraction `ι_{∂_t} σ` with the time field.
* `TauCeti.SmoothForm.mextDerivₗ_timeInterior`: `d (ι_{∂_t} σ) = ∂_t σ` for closed `σ`.
* `TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior`: its slices,
  `ι_t^* L_{∂_t} σ = d (ι_t^* ι_{∂_t} σ)` for closed `σ`.
* `TauCeti.SmoothForm.mpullback_prodMap_timeInterior`:
  `(id × f)^* ι_{∂_t} σ = ι_{∂_t} (id × f)^* σ`.
* `TauCeti.SmoothForm.timeInterior_mpullback_snd`: the contraction with `∂_t` of a form pulled
  back along the projection `ℝ × M → M` is zero.
* `TauCeti.mpullback_prodMk_mlieDerivForm_mpullback_prodMap_subtypeVal`: the restriction of a
  form to `J × M` has the time derivative of the form at the times of `J`.

## References

* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability, whose proof integrates this rescaling).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 22 (the
  derivative of pullbacks of a time-dependent family of forms along a time-dependent flow).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 14.35
  (Cartan's formula, for the contraction with the time field).
-/

public section

noncomputable section

open Set Bundle

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {X : ℝ → (x : M) → TangentSpace I x} {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k}

/-- **Local time-dependent flows rescale eigenforms of the Lie derivatives.** Let `X` be a
jointly `C²` time-dependent vector field and `β` a smooth form with `L_{X_u} β = g_u • β` for
every time `u`, where `g : ℝ × M → ℝ` is continuous. Wherever the time-dependent flow `φ` of `X`
from `(s, x)` is defined up to time `t`, it satisfies
`(φ_{s,t}^* β)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • βₓ`. The suspension of `X` need not be
complete. -/
theorem mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {β : SmoothForm I M F k} {g : ℝ × M → ℝ} (hg : Continuous g)
    (hβ : ∀ u, mlieDerivForm (X u) β.val = fun y ↦ g (u, y) • β.val y)
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback I I (timeDependentFlowOf X s t) β.val x =
      Real.exp (∫ u in s..t, g (u, timeDependentFlowOf X s u x)) • β.val x := by
  -- The constant family `p ↦ β (p.2)` on `ℝ × M`, whose slices are all `β`.
  set α := SmoothForm.mpullback (Prod.snd : ℝ × M → M)
    (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (Prod.snd : ℝ × M → M)) β
  have hslice (u : ℝ) : mpullback (F := F) (k := k) I (𝓘(ℝ, ℝ).prod I)
      (Prod.mk u : M → ℝ × M) α.val = β.val := by
    rw [← SmoothForm.coe_mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id),
      SmoothForm.mpullback_prodMk_mpullback_snd]
  have hL (u : ℝ) : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.val) +
      mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u : M → ℝ × M) α.val) =
      fun y ↦ g (u, y) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u : M → ℝ × M) α.val y := by
    funext y
    -- The slices of the constant family do not move, so their time derivative vanishes.
    have hd := hasDerivAt_mpullback_prodMk u y (α.mdifferentiable (u, y))
    simp only [hslice] at hd
    rw [Pi.add_apply, hd.unique (hasDerivAt_const u _), hslice, hβ u]
    -- The zero derivative is taken in the model space of forms, the sum in the fibre at `y`.
    exact zero_add _
  simpa only [hslice] using
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem hX
      ordConnected_univ hg.continuousOn (α.contMDiff.of_le (by simp)) (fun u _ ↦ hL u)
      (mem_univ s) (mem_univ t) h

end TauCeti

namespace TauCeti.SmoothForm

variable {E H M E' H' N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The contraction with the time field -/

/-- The contraction `ι_{∂_t} σ` of a smooth form `σ` on `ℝ × M` with the time field
`∂_t = (1, 0)`, as a smooth form of one degree less: the interior product
`TauCeti.SmoothForm.interiorProduct` with the section `SymplecticGeometry.timeField`. -/
def timeInterior (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k :=
  interiorProduct SymplecticGeometry.timeField σ

/-- `ι_{∂_t} σ` is the interior product of `σ` with the time field. -/
theorem timeInterior_def (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    σ.timeInterior = interiorProduct SymplecticGeometry.timeField σ :=
  (rfl)

/-- The underlying form of `ι_{∂_t} σ` is the contraction of `σ` with `∂_t = (1, 0)`. -/
@[simp]
theorem coe_timeInterior (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    σ.timeInterior.val = RoughForm.interior (I := 𝓘(ℝ, ℝ).prod I) (F := F) (k := k)
      (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val := by
  rw [timeInterior_def, coe_interiorProduct, SymplecticGeometry.coe_timeField]

/-- The contraction with the time field is additive. -/
@[simp]
theorem timeInterior_add (σ τ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (σ + τ).timeInterior = σ.timeInterior + τ.timeInterior :=
  map_add _ σ τ

/-- The contraction with the time field commutes with multiplication by a constant. -/
@[simp]
theorem timeInterior_smul (c : ℝ) (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (c • σ).timeInterior = c • σ.timeInterior :=
  map_smul _ c σ

/-- The contraction of the zero form with the time field is zero. -/
@[simp]
theorem timeInterior_zero :
    (0 : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)).timeInterior = 0 :=
  map_zero _

/-- The contraction with the time field commutes with negation. -/
@[simp]
theorem timeInterior_neg (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (-σ).timeInterior = -σ.timeInterior :=
  map_neg _ σ

/-- The contraction with the time field commutes with subtraction. -/
@[simp]
theorem timeInterior_sub (σ τ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (σ - τ).timeInterior = σ.timeInterior - τ.timeInterior :=
  map_sub _ σ τ

/-- **Cartan's formula for the time field.** For a closed form `σ` on `ℝ × M`, the exterior
derivative of `ι_{∂_t} σ` is the time derivative `∂_t σ = L_{∂_t} σ`. -/
theorem mextDerivₗ_timeInterior {σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    (hσ : σ.IsClosed) :
    mextDerivₗ (𝓘(ℝ, ℝ).prod I) k σ.timeInterior = σ.timeDeriv := by
  refine Subtype.ext ?_
  rw [mextDerivₗ_apply, coe_timeDeriv, coe_timeInterior]
  exact (mlieDerivForm_eq_mextDeriv_interior
    (SymplecticGeometry.contMDiff_timeField.mdifferentiable (by simp)) hσ).symm

/-- For a closed form `σ` on `ℝ × M`, the slice at time `t` of the time derivative
`L_{∂_t} σ` is the exterior derivative of the slice of `ι_{∂_t} σ`:
`ι_t^* L_{∂_t} σ = d (ι_t^* ι_{∂_t} σ)`. -/
theorem mpullback_prodMk_mlieDerivForm_eq_mextDeriv_timeInterior
    {σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)} (hσ : σ.IsClosed) (t : ℝ) :
    TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) =
      mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        σ.timeInterior).val := by
  have h := congrArg Subtype.val (congrArg (mpullback (Prod.mk t)
    (contMDiff_const.prodMk contMDiff_id)) (mextDerivₗ_timeInterior hσ).symm)
  simpa [← mextDerivₗ_mpullback] using h

/-- The contraction with the time field commutes with pullback along `id × f`, which sends the
time field `∂_t` of `ℝ × M` to that of `ℝ × N`: `(id × f)^* ι_{∂_t} σ = ι_{∂_t} (id × f)^* σ`. -/
theorem mpullback_prodMap_timeInterior (f : M → N) (hf : ContMDiff I J ∞ f)
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F (k + 1)) :
    mpullback (Prod.map id f) (contMDiff_id.prodMap hf) σ.timeInterior =
      (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) σ).timeInterior := by
  refine Subtype.ext ?_
  rw [coe_mpullback, coe_timeInterior, coe_timeInterior, coe_mpullback]
  refine mpullback_interior (F := F) _ _ _ _ fun p ↦ ?_
  rw [mfderiv_prodMap mdifferentiableAt_id (hf.mdifferentiableAt (by simp)), mfderiv_id]
  exact Prod.ext rfl (mfderiv I J f p.2).map_zero

/-- A form pulled back from `M` along the projection `ℝ × M → M` has zero contraction with the
time field, since the projection kills `∂_t`. -/
@[simp]
theorem timeInterior_mpullback_snd (β : SmoothForm I M F (k + 1)) :
    (mpullback (Prod.snd : ℝ × M → M) contMDiff_snd β).timeInterior = 0 := by
  refine Subtype.ext ?_
  rw [coe_timeInterior, coe_mpullback, interior_mpullback_snd_eq_zero, ZeroMemClass.coe_zero]

/-! ### Time derivatives of pullbacks along `c × f` -/

variable [I.Boundaryless] [J.Boundaryless]

/-- The time derivative of a family reparametrized in time: for a smooth `c : ℝ → ℝ`, the slice at
time `t` of `∂_t ((c × f)^* α)` is `c'(t)` times the pullback along `f` of the slice of `∂_t α` at
time `c t`. -/
theorem mpullback_prodMk_timeDeriv_mpullback_prodMap' {c : ℝ → ℝ}
    (hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ c) (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map c f) (hc.prodMap hf) α).timeDeriv =
      deriv c t • mpullback f hf
        (mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv) := by
  apply Subtype.ext
  funext x
  -- Both sides at `x` are the velocity at `t` of `u ↦ (f^* α_{c(u)})ₓ`.
  have h₁ := hasDerivAt_mpullback_prodMk_timeDeriv
    (mpullback (Prod.map c f) (hc.prodMap hf) α) t x
  have h₃ : HasDerivAt
      (fun u ↦ @id (E' [⋀^Fin k]→L[ℝ] F)
        ((mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val (f x)))
      (@id (E' [⋀^Fin k]→L[ℝ] F)
        ((mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id)
          α.timeDeriv).val (f x))) (c t) :=
    α.hasDerivAt_mpullback_prodMk_timeDeriv (c t) (f x)
  have hct : HasDerivAt c (deriv c t) t :=
    ((contMDiff_iff_contDiff.1 hc).differentiable (by simp) t).hasDerivAt
  have h₂ := ((ContinuousAlternatingMap.compContinuousLinearMapCLM
    (mfderiv I J f x : E →L[ℝ] E') :
      (E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F)).hasFDerivAt.comp_hasDerivAt t
        (h₃.scomp t hct)
  have hx (γ : SmoothForm J N F k) : (mpullback f hf γ).val x =
      ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := F)
        (mfderiv I J f x : E →L[ℝ] E') (γ.val (f x)) := by
    rw [coe_mpullback, TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM]
  have hs (u : ℝ) := congrArg (fun γ ↦ γ.val x) (mpullback_prodMk_mpullback_prodMap' hc f hf α u)
  simp only [hs, hx, Submodule.coe_smul, Pi.smul_apply] at h₁ h₂ ⊢
  refine h₁.unique ?_
  convert h₂ using 1
  · rw [map_smul, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    -- The two functions differ only by `Function.comp` and `id`, which unfold.
    exact Iff.rfl

end TauCeti.SmoothForm

/-! ### Restriction to an open set of times -/

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Time derivatives of a restricted family.** For an open set `J` of times, the restriction
`(val × id)^* β` of a smooth form `β` on `ℝ × M` to `J × M` has, at each time `t ∈ J`, the time
derivative of `β`: `ι_t^* L_{∂_t} ((val × id)^* β) = ι_t^* L_{∂_t} β`. -/
theorem mpullback_prodMk_mlieDerivForm_mpullback_prodMap_subtypeVal
    {J : TopologicalSpace.Opens ℝ} (β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) (t : J) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E)))
        (SmoothForm.mpullback (Prod.map Subtype.val id)
          (contMDiff_subtypeVal.prodMap contMDiff_id) β).val) =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk (t : ℝ))
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) β.val) := by
  funext x
  -- Read the times of `J` through a map `g : ℝ → J` which is the identity near `t`.
  obtain ⟨g, hg, hgid⟩ := J.exists_contMDiff_eventuallyEq_id (convex_singleton (t : ℝ))
    isCompact_singleton (singleton_nonempty _) (singleton_subset_iff.mpr t.property)
  have hu := hgid _ rfl
  have hgt : g t = t := Subtype.ext hu.self_of_nhds
  have h := hasDerivAt_mpullback_prodMk_comp (hg.of_le (by simp)) hu x
    ((SmoothForm.mpullback (Prod.map Subtype.val id)
      (contMDiff_subtypeVal.prodMap contMDiff_id) β).mdifferentiableAt _)
  rw [hgt] at h
  refine h.unique ((hasDerivAt_mpullback_prodMk (t : ℝ) x
    (β.mdifferentiableAt _)).congr_of_eventuallyEq ?_)
  -- Near `t`, the slices of the restriction at the times `g v` are the slices of `β` at `v`.
  filter_upwards [hu] with v hv
  have hs := congrArg (fun γ ↦ γ.val x)
    (SmoothForm.mpullback_prodMk_mpullback_prodMap_id β contMDiff_subtypeVal (g v))
  simp only [SmoothForm.coe_mpullback, hv, id] at hs
  rw [SmoothForm.coe_mpullback]
  -- `hs` reads the forms in the tangent spaces of `M`, the goal in the model `E`.
  exact hs

end TauCeti

end
