/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The second derivative of a map between fields of bilinear forms that preserves them

Let `g` and `h` be fields of symmetric nondegenerate bilinear forms on finite-dimensional real
normed spaces `E` and `F` (no positivity is assumed), and let `τ : E → F` be `C²` on an open set
`U`, with `h (τ y) (Dτ(y) u) (Dτ(y) v) = g y u v` for `y ∈ U`: `τ` carries `g` to `h`. If
`Dτ(w)` is surjective at a point `w ∈ U`, the second derivative of `τ` at `w` is determined by the
first:

`D²τ(w)(u, v) = Dτ(w) (Γ_g(w)(u, v)) - Γ_h(τ w)(Dτ(w) u, Dτ(w) v)`,

where `Γ_g` and `Γ_h` are the Christoffel symbols of the second kind of `g` and `h`, Tau Ceti's
`TauCeti.Manifold.christoffelSecondKind`.

Differentiating the identity that `τ` preserves the forms and using the metric compatibility of
both Christoffel maps (`TauCeti.Manifold.fderiv_apply_eq_christoffelSecondKind_add`) shows that
the difference `B(u, v)` of the two sides is symmetric in `u, v` and that
`h(B(z, u), Dτ v) + h(B(z, v), Dτ u) = 0`. The Koszul combination of three such identities gives
`h(B(u, v), Dτ z) = 0` for all `z`, so `B = 0` by surjectivity of `Dτ(w)` and nondegeneracy
of `h`. Surjectivity cannot be dropped: for an isometric embedding of a curve into the plane the
difference is the second fundamental form, normal to the image of `Dτ`.

The argument follows Tau Ceti's `TauCeti.smul_fderiv_fderiv_apply_eq_of_inner_fderiv`, which
proves the case of a conformal map between inner product spaces, and the uniqueness proof
`TauCeti.Manifold.eq_christoffelSecondKind_of_fderiv_apply_eq`.

## Main results

* `SymplecticGeometry.fderiv_fderiv_apply_eq_sub_christoffelSecondKind`: the formula above.
* `SymplecticGeometry.fderiv_fderiv_eq_sub_christoffelSecondKind`: the same formula as an
  equality of continuous bilinear maps, which writes `D²τ(w)` as a function of `w`, `τ w` and
  `Dτ(w)`.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press (1983),
  Chapter 3: the Koszul formula and the Levi-Civita connection of a nondegenerate metric.
-/

public section

open Filter ContinuousLinearMap TauCeti TauCeti.Manifold
open scoped Topology

namespace SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {g : E → E →L[ℝ] E →L[ℝ] ℝ} {h : F → F →L[ℝ] F →L[ℝ] ℝ} {τ : E → F} {U : Set E} {w : E}

/-- **The Koszul formula for a map that preserves fields of bilinear forms.** Let `g` and `h` be
fields of bilinear forms on `E` and `F`, and let `τ : E → F` be `C²` on an open set `U`, with
`h (τ y) (Dτ(y) u) (Dτ(y) v) = g y u v` for `y ∈ U`. At a point `w ∈ U` where `Dτ(w)` is
surjective, `g w` is nondegenerate, and `h` is differentiable at `τ w`, symmetric near `τ w` and
nondegenerate at `τ w`,
`D²τ(w)(u, v) = Dτ(w) (Γ_g(w)(u, v)) - Γ_h(τ w)(Dτ(w) u, Dτ(w) v)`. -/
theorem fderiv_fderiv_apply_eq_sub_christoffelSecondKind (hU : IsOpen U)
    (hτ : ContDiffOn ℝ 2 τ U)
    (hiso : ∀ y ∈ U, ∀ u v, h (τ y) (fderiv ℝ τ y u) (fderiv ℝ τ y v) = g y u v)
    (hw : w ∈ U) (hsurj : Function.Surjective (fderiv ℝ τ w))
    (hgnd : (g w).toBilinForm.Nondegenerate) (hh : DifferentiableAt ℝ h (τ w))
    (hhsymm : ∀ᶠ y in 𝓝 (τ w), (h y).toBilinForm.IsSymm)
    (hhnd : (h (τ w)).toBilinForm.Nondegenerate) (u v : E) :
    fderiv ℝ (fderiv ℝ τ) w u v =
      fderiv ℝ τ w (christoffelSecondKind g w u v) -
        christoffelSecondKind h (τ w) (fderiv ℝ τ w u) (fderiv ℝ τ w v) := by
  have hτw : ContDiffAt ℝ 2 τ w := hτ.contDiffAt (hU.mem_nhds hw)
  have hτd : DifferentiableAt ℝ τ w := hτw.differentiableAt (by norm_num)
  have hDτ (a : E) :
      HasFDerivAt (fun y ↦ fderiv ℝ τ y a) ((fderiv ℝ (fderiv ℝ τ) w).flip a) w :=
    hτw.hasFDerivAt_fderiv_apply le_rfl a
  have hhτ : DifferentiableAt ℝ (fun y ↦ h (τ y)) w := hh.comp w hτd
  -- Near `w`, the form `g` is the pullback of `h` by `τ`.
  have hiso' (a b : E) : (fun y ↦ g y a b) =ᶠ[𝓝 w]
      fun y ↦ h (τ y) (fderiv ℝ τ y a) (fderiv ℝ τ y b) :=
    eventually_of_mem (hU.mem_nhds hw) fun y hy ↦ (hiso y hy a b).symm
  have hg : DifferentiableAt ℝ g w := differentiableAt_clm_apply₂.2 fun a b ↦
    ((hhτ.clm_apply (hDτ a).differentiableAt).clm_apply
      (hDτ b).differentiableAt).congr_of_eventuallyEq (hiso' a b)
  have hgsymm : ∀ᶠ y in 𝓝 w, (g y).toBilinForm.IsSymm := by
    filter_upwards [hU.mem_nhds hw, hτd.continuousAt.tendsto.eventually hhsymm] with y hy hsy
    refine isSymm_toBilinForm_iff.2 fun a b ↦ ?_
    rw [← hiso y hy, ← hiso y hy, isSymm_toBilinForm_iff.1 hsy]
  have hHs : ∀ a b, h (τ w) a b = h (τ w) b a := isSymm_toBilinForm_iff.1 hhsymm.self_of_nhds
  have hAs : ∀ a b, fderiv ℝ (fderiv ℝ τ) w a b = fderiv ℝ (fderiv ℝ τ) w b a :=
    hτw.isSymmSndFDerivAt (by simp)
  have hgH (a b : E) : g w a b = h (τ w) (fderiv ℝ τ w a) (fderiv ℝ τ w b) :=
    (hiso w hw a b).symm
  -- The derivative of the identity `h (τ y) (Dτ(y) a) (Dτ(y) b) = g y a b` in the direction `z`.
  have hder (z a b : E) :
      fderiv ℝ h (τ w) (fderiv ℝ τ w z) (fderiv ℝ τ w a) (fderiv ℝ τ w b) +
          h (τ w) (fderiv ℝ (fderiv ℝ τ) w z a) (fderiv ℝ τ w b) +
          h (τ w) (fderiv ℝ τ w a) (fderiv ℝ (fderiv ℝ τ) w z b) =
        fderiv ℝ g w z a b := by
    rw [← fderiv_clm_apply_const_apply₂ hg, (hiso' a b).fderiv_eq,
      fderiv_bilin_apply hhτ (hDτ a).differentiableAt (hDτ b).differentiableAt,
      fderiv_fun_comp w hh hτd, (hDτ a).fderiv, (hDτ b).fderiv]
    simp
  set L := fderiv ℝ τ w
  set A := fderiv ℝ (fderiv ℝ τ) w
  set H := h (τ w)
  -- The difference of the two sides of the formula, and its two properties.
  set B : E → E → F := fun a b ↦
    A a b + christoffelSecondKind h (τ w) (L a) (L b) - L (christoffelSecondKind g w a b)
    with hB
  have hBs (a b : E) : B a b = B b a := by
    simp only [hB, hAs a b, christoffelSecondKind_comm hhsymm (L a),
      christoffelSecondKind_comm hgsymm a b]
  have hBskew (z a b : E) : H (B z a) (L b) + H (B z b) (L a) = 0 := by
    have e := hder z a b
    rw [fderiv_apply_eq_christoffelSecondKind_add hhsymm hhnd,
      fderiv_apply_eq_christoffelSecondKind_add hgsymm hgnd, hgH, hgH] at e
    have s₁ := hHs (L a) (christoffelSecondKind h (τ w) (L z) (L b))
    have s₂ := hHs (L a) (A z b)
    have s₃ := hHs (L a) (L (christoffelSecondKind g w z b))
    simp only [hB, map_add, map_sub, add_apply, sub_apply]
    linarith
  -- The Koszul combination: `B u v` is `H`-orthogonal to the image of `L`.
  have horth (z : E) : H (B u v) (L z) = 0 := by
    have e₁ := hBskew u v z
    have e₂ := hBskew v u z
    have e₃ := hBskew z u v
    rw [hBs u z] at e₁
    rw [hBs v z, hBs v u] at e₂
    linarith
  have hB0 : B u v = 0 := by
    refine H.separatingLeft_toBilinForm_iff_injective.1 hhnd.1 ?_
    ext y
    obtain ⟨z, rfl⟩ := hsurj y
    simpa using horth z
  rw [eq_sub_iff_add_eq, ← sub_eq_zero]
  exact hB0

/-- **The Koszul formula for a map that preserves fields of bilinear forms**, as an equality of
continuous bilinear maps: under the hypotheses of
`fderiv_fderiv_apply_eq_sub_christoffelSecondKind`, the second derivative `D²τ(w)` is
`Dτ(w) ∘ Γ_g(w) - Γ_h(τ w) ∘ (Dτ(w) × Dτ(w))`. -/
theorem fderiv_fderiv_eq_sub_christoffelSecondKind (hU : IsOpen U)
    (hτ : ContDiffOn ℝ 2 τ U)
    (hiso : ∀ y ∈ U, ∀ u v, h (τ y) (fderiv ℝ τ y u) (fderiv ℝ τ y v) = g y u v)
    (hw : w ∈ U) (hsurj : Function.Surjective (fderiv ℝ τ w))
    (hgnd : (g w).toBilinForm.Nondegenerate) (hh : DifferentiableAt ℝ h (τ w))
    (hhsymm : ∀ᶠ y in 𝓝 (τ w), (h y).toBilinForm.IsSymm)
    (hhnd : (h (τ w)).toBilinForm.Nondegenerate) :
    fderiv ℝ (fderiv ℝ τ) w =
      compL ℝ E E F (fderiv ℝ τ w) ∘L christoffelSecondKind g w -
        (christoffelSecondKind h (τ w)).bilinearComp (fderiv ℝ τ w) (fderiv ℝ τ w) := by
  ext u v
  simp [fderiv_fderiv_apply_eq_sub_christoffelSecondKind hU hτ hiso hw hsurj hgnd hh hhsymm
    hhnd u v]

end SymplecticGeometry

end
