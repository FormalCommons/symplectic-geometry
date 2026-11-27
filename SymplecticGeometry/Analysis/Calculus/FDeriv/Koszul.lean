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

Since `g w` is nondegenerate and `τ` carries `g` to `h`, `Dτ(w)` is injective, hence a linear
equivalence. Pulling `D²τ(w)(u, v) + Γ_h(τ w)(Dτ(w) u, Dτ(w) v)` back along it gives a symmetric
bilinear map `A` on `E`. Differentiating the identity that `τ` preserves the forms, and using
the metric compatibility of `Γ_h` (`TauCeti.Manifold.fderiv_apply_eq_christoffelSecondKind_add`),
shows that `A` is compatible with `Dg(w)`, so `A = Γ_g(w)` by Tau Ceti's uniqueness lemma
`TauCeti.Manifold.eq_christoffelSecondKind_of_fderiv_apply_eq`. Surjectivity cannot be dropped:
for an isometric embedding of a curve into the plane the two sides differ by the second
fundamental form, normal to the image of `Dτ`.

The argument follows Tau Ceti's `TauCeti.smul_fderiv_fderiv_apply_eq_of_inner_fderiv`, which
proves the case of a conformal map between inner product spaces.

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
surjective, `g w` is nondegenerate, and `h` is differentiable at `τ w` and symmetric near `τ w`,
`D²τ(w)(u, v) = Dτ(w) (Γ_g(w)(u, v)) - Γ_h(τ w)(Dτ(w) u, Dτ(w) v)`. -/
theorem fderiv_fderiv_apply_eq_sub_christoffelSecondKind (hU : IsOpen U)
    (hτ : ContDiffOn ℝ 2 τ U)
    (hiso : ∀ y ∈ U, ∀ u v, h (τ y) (fderiv ℝ τ y u) (fderiv ℝ τ y v) = g y u v)
    (hw : w ∈ U) (hsurj : Function.Surjective (fderiv ℝ τ w))
    (hgnd : (g w).toBilinForm.Nondegenerate) (hh : DifferentiableAt ℝ h (τ w))
    (hhsymm : ∀ᶠ y in 𝓝 (τ w), (h y).toBilinForm.IsSymm) (u v : E) :
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
  set D := fderiv ℝ (fderiv ℝ τ) w
  -- `L` is injective since `g w` is nondegenerate, hence a linear equivalence.
  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun a ha ↦
      (g w).separatingLeft_toBilinForm_iff_injective.1 hgnd.1 (?_ : g w a = g w 0)
    ext b
    simp [hgH, ha]
  have hbij : Function.Bijective (L : E →ₗ[ℝ] F) := ⟨hLinj, hsurj⟩
  -- `h (τ w)` is nondegenerate, since `L` is onto and carries `g w` to it.
  have hhnd : (h (τ w)).toBilinForm.Nondegenerate := by
    refine .ofSeparatingLeft <|
      (h (τ w)).separatingLeft_toBilinForm_iff_injective.2 fun p q hpq ↦ ?_
    obtain ⟨a, rfl⟩ := hsurj p
    obtain ⟨b, rfl⟩ := hsurj q
    refine congrArg L ((g w).separatingLeft_toBilinForm_iff_injective.1 hgnd.1 ?_)
    ext c
    simp only [hgH, hpq]
  let e : E ≃L[ℝ] F := (LinearEquiv.ofBijective (L : E →ₗ[ℝ] F) hbij).toContinuousLinearEquiv
  -- The candidate for `Γ_g(w)`, pulled back from `D²τ(w) + Γ_h(τ w) ∘ (L × L)` by `L`.
  set A : E →L[ℝ] E →L[ℝ] E := compL ℝ E F E (e.symm : F →L[ℝ] E) ∘L
    (D + (christoffelSecondKind h (τ w)).bilinearComp L L)
  have he (x : E) : e x = L x := LinearEquiv.ofBijective_apply _ (hf := hbij) x
  have hLA (a b : E) : L (A a b) = D a b + christoffelSecondKind h (τ w) (L a) (L b) := by
    rw [← he]
    simp [A]
  have key : A = christoffelSecondKind g w := by
    refine eq_christoffelSecondKind_of_fderiv_apply_eq
      (isSymm_toBilinForm_iff.2 fun a b ↦ by rw [hgH, hgH, hHs]) hgnd
      (fun a b ↦ hLinj ?_) fun z a b ↦ ?_
    · rw [hLA, hLA, hAs, christoffelSecondKind_comm hhsymm]
    · rw [← hder, fderiv_apply_eq_christoffelSecondKind_add hhsymm hhnd, hgH, hgH, hLA, hLA]
      simp only [map_add, add_apply]
      ring
  rw [← key, hLA]
  abel

/-- **The Koszul formula for a map that preserves fields of bilinear forms**, as an equality of
continuous bilinear maps: under the hypotheses of
`fderiv_fderiv_apply_eq_sub_christoffelSecondKind`, the second derivative `D²τ(w)` is
`Dτ(w) ∘ Γ_g(w) - Γ_h(τ w) ∘ (Dτ(w) × Dτ(w))`. -/
theorem fderiv_fderiv_eq_sub_christoffelSecondKind (hU : IsOpen U)
    (hτ : ContDiffOn ℝ 2 τ U)
    (hiso : ∀ y ∈ U, ∀ u v, h (τ y) (fderiv ℝ τ y u) (fderiv ℝ τ y v) = g y u v)
    (hw : w ∈ U) (hsurj : Function.Surjective (fderiv ℝ τ w))
    (hgnd : (g w).toBilinForm.Nondegenerate) (hh : DifferentiableAt ℝ h (τ w))
    (hhsymm : ∀ᶠ y in 𝓝 (τ w), (h y).toBilinForm.IsSymm) :
    fderiv ℝ (fderiv ℝ τ) w =
      compL ℝ E E F (fderiv ℝ τ w) ∘L christoffelSecondKind g w -
        (christoffelSecondKind h (τ w)).bilinearComp (fderiv ℝ τ w) (fderiv ℝ τ w) := by
  ext u v
  simp [fderiv_fderiv_apply_eq_sub_christoffelSecondKind hU hτ hiso hw hsurj hgnd hh hhsymm u v]

end SymplecticGeometry

end
