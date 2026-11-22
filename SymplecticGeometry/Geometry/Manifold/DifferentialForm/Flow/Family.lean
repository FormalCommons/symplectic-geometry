/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Analysis.ODE.ScalarLinear
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
and that if the rate vanishes only at the points `φ_{s,u} x` for `u` between `s` and `t`, then
`(φ_{s,t}^* α_t)ₓ = (α_s)ₓ`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`).

This file combines the two: the rescaling identity
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ` holds as soon as the rate at `φ_{s,u} x` is
`c u • α_u` at that point, for every `u` between `s` and `t`, with a coefficient `c` continuous in
time, and `α` is `C¹` only along the trajectory. This is the form in which Gray's argument uses
the identity when the contact structures are given only by local defining forms.

The proof is that of Tau Ceti's
`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`, with
the derivative read only along the trajectory through
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk` and the interval between `s`
and `t` in place of the whole domain of the flow, as in Tau Ceti's
`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`.

The file then treats the constant family `(u, y) ↦ β_y` of a form `β` on `M`, whose slices
are all `β` (`TauCeti.SmoothForm.mpullback_prodMk_mpullback_snd`). If `L_{X_u} β = g_u • β`
for every time `u`, with `g` continuous, then
`(φ_{s,t}^* β)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • βₓ` wherever the flow is defined: this is Tau
Ceti's `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`
for the constant family. Contact Hamiltonian flows use it.

When `β` is closed and its contractions `ι_{X_u} β` are all closed, Cartan's formula gives
`L_{X_u} β = 0`, so the case `g = 0` shows that the local time-dependent flow preserves `β`
wherever it is defined, with no completeness. This is the local form of Tau Ceti's
`TauCeti.mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero`, and gives the
preservation of a symplectic form by local time-dependent Hamiltonian flows.

The file also records how slices behave under pullback along `id × f : ℝ × M → ℝ × N`, for a
smooth `f : M → N`. The slice of `(id × f)^* α` at time `t` is `f^* α_t`, and the slice at time
`t` of its time derivative (`TauCeti.SmoothForm.timeDeriv`) is the pullback along `f` of the
slice of `∂_t α`: both are the velocity of `u ↦ f^* α_u`, by Tau Ceti's
`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`. The same lemma computes the velocity
of the reparametrized segment `α₀ + c(t) (α₁ - α₀)` of forms
(`TauCeti.SmoothForm.lineMapFamily`): its slice at time `t` is `c'(t) (α₁ - α₀)`. The
computation is the one in the private `moserRate_eq_zero` of Tau Ceti's
`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`.

Finally, the file contracts forms on `ℝ × M` with the time field `∂_t = (1, 0)`. The field is
smooth by the argument that Tau Ceti writes inline in the definition of
`TauCeti.SmoothForm.timeDeriv`, through `TauCeti.contMDiff_const_prod_field`, so the contraction
`ι_{∂_t} σ` of a smooth form is smooth (`TauCeti.SmoothForm.timeInterior`). For closed `σ`,
Cartan's formula `TauCeti.mlieDerivForm_eq_mextDeriv_interior` makes its exterior derivative
the time derivative of `σ`. Since `id × f` sends `∂_t` to `∂_t`, the contraction commutes with
pullback along `id × f`, and it vanishes on forms pulled back from `M` along the projection.

## Main results

* `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_…_smul_of_forall_mem_uIcc_of_mem`
  (in full, `…_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem`): if the rate is
  `c u • α_u` along the trajectory of `x` between `s` and `t`, then
  `(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ`.
* `TauCeti.mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq`: a smooth
  form with `L_{X_u} β = g_u • β` satisfies `(φ_{s,t}^* β)ₓ = exp (∫ₛᵗ g (u, φ_{s,u} x) du) • βₓ`
  wherever the flow is defined.
* `TauCeti.mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero`: a closed smooth
  form whose contractions with every `X u` are closed satisfies `(φ_{s,t}^* β)ₓ = βₓ` wherever
  the flow is defined.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap'`: `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`
  for a reparametrization `c` of time, with its cases `c = id`,
  `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap`, and `f = id`,
  `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap_id_right`.
* `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap`: the same for the time
  derivative, `ι_t^* ∂_t ((id × f)^* α) = f^* ι_t^* ∂_t α`, and
  `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap'` for a reparametrization `c`
  of time, `ι_t^* ∂_t ((c × f)^* α) = c'(t) f^* ι_{c t}^* ∂_t α`.
* `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily`: the velocity of the segment
  `α₀ + c(t) (α₁ - α₀)` at time `t` is `c'(t) (α₁ - α₀)`.
* `TauCeti.SmoothForm.timeInterior`: the contraction `ι_{∂_t} σ` with the time field.
* `TauCeti.SmoothForm.mextDerivₗ_timeInterior`: `d (ι_{∂_t} σ) = ∂_t σ` for closed `σ`.
* `TauCeti.SmoothForm.mpullback_prodMap_timeInterior`:
  `(id × f)^* ι_{∂_t} σ = ι_{∂_t} (id × f)^* σ`.

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

/-- **Moser's principle along a trajectory**, rescaling case. Let `X` be a jointly `C²`
time-dependent vector field with time-dependent flow `φ`, defined at `x` from time `s` to time `t`,
and let `α` be a form on `ℝ × M` with slices `α_u = ι_u^* α`, which is `C¹` at `(u, φ_{s,u} x)`
for every time `u` between `s` and `t`. If, for each such `u`, the rate
`ι_u^* L_{∂_t} α + L_{X_u} α_u` at the point `φ_{s,u} x` is `c u • (α_u)_{φ_{s,u} x}`, for a
function `c` of time continuous between `s` and `t`, then
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ c u du) • (α_s)ₓ`. Nothing is assumed away from the trajectory
of `x`. -/
theorem
mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc_of_mem
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : ∀ u ∈ uIcc s t, ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin k]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin k]→L[ℝ] F) p (α p))
      (u, timeDependentFlowOf X s u x))
    {c : ℝ → ℝ} (hc : ContinuousOn c (uIcc s t))
    (hL : ∀ u ∈ uIcc s t, (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
        mlieDerivForm (X u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α))
          (timeDependentFlowOf X s u x) =
        c u • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α (timeDependentFlowOf X s u x)) :
    mpullback I I (timeDependentFlowOf X s t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α) x =
      Real.exp (∫ u in s..t, c u) • mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
  -- The flow from `(s, x)` is defined at all times between `s` and `t`.
  have hJ : uIcc s t ⊆ {u | ((s, u), x) ∈ timeDependentFlowDomain X} :=
    (ordConnected_setOf_mem_timeDependentFlowDomain s x).uIcc_subset
      (mem_timeDependentFlowDomain_self_of_mem h) h
  -- The pullbacks at `x`, as alternating maps on the model space.
  set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦
    mpullback I I (timeDependentFlowOf X s u) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α) x
  -- Between `s` and `t` they satisfy the scalar linear equation `P' = c • P`.
  have hP (u : ℝ) (hu : u ∈ uIcc s t) : HasDerivWithinAt P (c u • P u) (uIcc s t) u := by
    refine ((hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hX (hJ hu)
      (hα u hu)).congr_deriv ?_).hasDerivWithinAt
    rw [mpullback_apply_eq_compContinuousLinearMapCLM, hL u hu, _root_.map_smul,
      ← mpullback_apply_eq_compContinuousLinearMapCLM]
    -- The two sides differ only in the unfolding of `P` and in whether the scalar action is that
    -- of forms on the fibre `T_x M` or on the model space `E`.
    rfl
  have hP0 : P s = mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α x := by
    have hid : timeDependentFlowOf X s s = id := funext (timeDependentFlowOf_self X s)
    exact (congrArg (fun f ↦ mpullback I I f (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) α) x)
      hid).trans (congrFun (mpullback_id _) x)
  rw [← hP0]
  exact eq_exp_integral_smul_of_hasDerivWithinAt_smul (V := E [⋀^Fin k]→L[ℝ] F) ordConnected_uIcc
    hc hP left_mem_uIcc right_mem_uIcc

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
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem hX hg
      (α.contMDiff.of_le (by simp)) hL h

/-- **Local time-dependent flows preserve closed forms with closed contractions.** Let `X` be a
jointly `C²` time-dependent vector field and `β` a closed smooth form whose contraction
`ι_{X_t} β` is closed for every time `t`. Wherever the time-dependent flow `φ` of `X` from
`(s, x)` is defined up to time `t`, it satisfies `(φ_{s,t}^* β)ₓ = βₓ`. The suspension of `X`
need not be complete. -/
theorem mpullback_timeDependentFlowOf_apply_of_mextDeriv_interior_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {β : SmoothForm I M F (k + 1)} (hβ : β.IsClosed)
    (hXβ : ∀ t, mextDeriv (RoughForm.interior (X t) β.val) = 0)
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    mpullback I I (timeDependentFlowOf X s t) β.val x = β.val x := by
  -- By Cartan's formula, `β` is an eigenform of every `L_{X_u}`, with eigenvalue `0`.
  have hL (u : ℝ) : mlieDerivForm (X u) β.val = fun y ↦ (0 : ℝ) • β.val y := by
    have hXu : MDifferentiable I I.tangent (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) :=
      (hX.comp ((contMDiff_const (c := u)).prodMk contMDiff_id)).mdifferentiable two_ne_zero
    rw [mlieDerivForm_eq_mextDeriv_interior β.mdifferentiable hXu
      ((SmoothForm.isClosed_def β).1 hβ), hXβ u]
    funext y
    exact (zero_smul ℝ _).symm
  simpa using mpullback_timeDependentFlowOf_apply_eq_exp_integral_smul_of_mlieDerivForm_eq hX
    (g := fun _ ↦ 0) continuous_const hL h

end TauCeti

/-! ### Slices of pullbacks along `id × f` -/

namespace TauCeti.SmoothForm

variable {E H M E' H' N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × N` along `c × f`, for a smooth
reparametrization `c : ℝ → ℝ` of time, is the pullback along `f` of the slice of `α` at time
`c t`: `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`. -/
theorem mpullback_prodMk_mpullback_prodMap' {c : ℝ → ℝ} (hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ c)
    (f : M → N) (hf : ContMDiff I J ∞ f) (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map c f) (hc.prodMap hf) α) =
      mpullback f hf (mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) α) := by
  rw [← LinearMap.comp_apply, ← mpullback_comp, ← LinearMap.comp_apply, ← mpullback_comp]
  have h : Prod.map c f ∘ Prod.mk t = Prod.mk (c t) ∘ f := by
    ext x <;> simp
  simp only [h]

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × N` along `id × f` is the pullback
along `f` of the slice of `α` at time `t`: `ι_t^* (id × f)^* α = f^* ι_t^* α`. -/
theorem mpullback_prodMk_mpullback_prodMap (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α) =
      mpullback f hf (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  mpullback_prodMk_mpullback_prodMap' contMDiff_id f hf α t

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × M` along `c × id`, for a smooth
`c : ℝ → ℝ`, is the slice of `α` at time `c t`. -/
theorem mpullback_prodMk_mpullback_prodMap_id_right {c : ℝ → ℝ}
    (hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ c) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map c id) (hc.prodMap contMDiff_id) α) =
      mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) α := by
  rw [mpullback_prodMk_mpullback_prodMap' hc id contMDiff_id]
  exact LinearMap.congr_fun SmoothForm.mpullback_id _

/-! ### The contraction with the time field -/

omit [IsManifold I ∞ M] in
/-- The time field `∂_t = (1, 0)` on `ℝ × M` is a smooth section of the tangent bundle. -/
theorem _root_.TauCeti.contMDiff_timeField [IsManifold I 1 M] :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent ∞
      (fun p : ℝ × M ↦ (⟨p, ((1 : ℝ), (0 : E))⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
  contMDiff_const_prod_field 1 (X := 0)
    ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd)

/-- The contraction `ι_{∂_t} σ` of a smooth form `σ` on `ℝ × M` with the time field
`∂_t = (1, 0)`, as a smooth form of one degree less. -/
def timeInterior (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k :=
  ⟨RoughForm.interior (I := 𝓘(ℝ, ℝ).prod I) (F := F) (k := k)
    (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val,
    (σ.isSmoothForm.interior contMDiff_timeField).mem_smoothBundleForms⟩

/-- The underlying form of `ι_{∂_t} σ` is the contraction of `σ` with `∂_t = (1, 0)`. -/
@[simp]
theorem coe_timeInterior (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    σ.timeInterior.val = RoughForm.interior (I := 𝓘(ℝ, ℝ).prod I) (F := F) (k := k)
      (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val :=
  (rfl)

/-- The contraction with the time field is additive. -/
@[simp]
theorem timeInterior_add (σ τ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (σ + τ).timeInterior = σ.timeInterior + τ.timeInterior :=
  -- The underlying forms of the contractions are those of `coe_timeInterior`, and the sums are
  -- the sums of the underlying rough forms.
  Subtype.ext (RoughForm.interior_add _ _ _)

/-- The contraction with the time field commutes with multiplication by a constant. -/
@[simp]
theorem timeInterior_smul (c : ℝ) (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (c • σ).timeInterior = c • σ.timeInterior :=
  -- As in `timeInterior_add`, with multiples in place of sums.
  Subtype.ext (RoughForm.interior_smul _ _ _)

/-- The contraction of the zero form with the time field is zero. -/
@[simp]
theorem timeInterior_zero :
    (0 : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)).timeInterior = 0 := by
  simpa using timeInterior_smul (0 : ℝ) (0 : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1))

/-- The contraction with the time field commutes with negation. -/
@[simp]
theorem timeInterior_neg (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (-σ).timeInterior = -σ.timeInterior := by
  rw [eq_neg_iff_add_eq_zero, ← timeInterior_add, neg_add_cancel, timeInterior_zero]

/-- The contraction with the time field commutes with subtraction. -/
@[simp]
theorem timeInterior_sub (σ τ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)) :
    (σ - τ).timeInterior = σ.timeInterior - τ.timeInterior := by
  simp [sub_eq_add_neg]

/-- **Cartan's formula for the time field.** For a closed form `σ` on `ℝ × M`, the exterior
derivative of `ι_{∂_t} σ` is the time derivative `∂_t σ = L_{∂_t} σ`. -/
theorem mextDerivₗ_timeInterior {σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    (hσ : σ.IsClosed) :
    mextDerivₗ (𝓘(ℝ, ℝ).prod I) k σ.timeInterior = σ.timeDeriv := by
  refine Subtype.ext ?_
  rw [mextDerivₗ_apply, coe_timeDeriv, coe_timeInterior]
  exact (mlieDerivForm_eq_mextDeriv_interior (contMDiff_timeField.mdifferentiable (by simp))
    hσ).symm

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

/-- The time derivative commutes with pullback along `id × f`, slice by slice: the slice at time
`t` of `∂_t ((id × f)^* α)` is the pullback along `f` of the slice of `∂_t α` at time `t`. -/
theorem mpullback_prodMk_timeDeriv_mpullback_prodMap (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α).timeDeriv =
      mpullback f hf
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv) := by
  simpa using mpullback_prodMk_timeDeriv_mpullback_prodMap' contMDiff_id f hf α t

/-! ### The velocity of a reparametrized segment -/

/-- **The velocity of a reparametrized segment of forms.** The slice at time `t` of the time
derivative of `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc`, the family `α₀ + c(t) (α₁ - α₀)`, is
`c'(t) (α₁ - α₀)`. -/
theorem mpullback_prodMk_timeDeriv_lineMapFamily (α₀ α₁ : SmoothForm I M F k) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (lineMapFamily α₀ α₁ hc).timeDeriv = deriv c t • (α₁ - α₀) := by
  apply Subtype.ext
  funext x
  have h := (lineMapFamily α₀ α₁ hc).hasDerivAt_mpullback_prodMk_timeDeriv t x
  simp only [mpullback_prodMk_lineMapFamily] at h
  refine h.unique ?_
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply]
  have hct : HasDerivAt c (deriv c t) t :=
    ((hc.of_le (by simp) : ContDiff ℝ 1 c).differentiable one_ne_zero t).hasDerivAt
  exact (hct.smul_const _).const_add _

end TauCeti.SmoothForm

end
