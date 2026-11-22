/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Hermitian
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smoothness of Hermitian products within a set

For a smooth `i`-invariant real metric `g` on a complex vector bundle `V`, Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.contMDiff_hermitianPairing` says that the Hermitian product
`g.complexInnerProductSpace hI` of two smooth maps into the total space is smooth. This file gives
its version within a set at a point,
`Bundle.ContMDiffRiemannianMetric.contMDiffWithinAt_hermitianPairing`, with the same proof: the
product is `g(v, w) + i g(i v, w)`. The version on a set,
`Bundle.ContMDiffRiemannianMetric.contMDiffOn_hermitianPairing`, follows from it.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω}
  {XM HM M : Type*} [NormedAddCommGroup XM] [NormedSpace ℝ XM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ XM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

/-- The Hermitian product of two maps into the total space over a common base map is `C^n`
within a set at a point where both maps are. -/
theorem contMDiffWithinAt_hermitianPairing (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {b : M → B} {v w : ∀ m, V (b m)} {s : Set M} {x : M}
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F V)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F V)) s x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffWithinAt IM 𝓘(ℝ, ℂ) n (fun m ↦ Inner.inner ℂ (v m) (w m)) s x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hre := hv.inner_bundle hw
  have him := ((contMDiffWithinAt_const (c := Complex.I)).smul_totalSpace hv).inner_bundle hw
  have hh := (Complex.ofRealCLM.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hre).add
    (him.smul (contMDiffWithinAt_const (I' := 𝓘(ℝ, ℂ)) (c := Complex.I)))
  have hreal (x : B) (v w : V x) : Inner.inner ℝ v w = g.inner x v w := g.inner_eq x v w
  have heq (m : M) : Inner.inner ℂ (v m) (w m) =
      Complex.ofRealCLM (Inner.inner ℝ (v m) (w m)) +
        Inner.inner ℝ (Complex.I • v m) (w m) • Complex.I := by
    rw [complexInnerProductSpace_inner]
    simp [hreal, Complex.real_smul, mul_comm]
  exact hh.congr (fun m _ ↦ heq m) (heq x)

/-- The Hermitian product of two maps into the total space over a common base map is `C^n` on a
set where both maps are. -/
theorem contMDiffOn_hermitianPairing (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {b : M → B} {v w : ∀ m, V (b m)} {s : Set M}
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, v m⟩ : TotalSpace F V)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, w m⟩ : TotalSpace F V)) s) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiffOn IM 𝓘(ℝ, ℂ) n (fun m ↦ Inner.inner ℂ (v m) (w m)) s :=
  fun x hx ↦ g.contMDiffWithinAt_hermitianPairing hI (hv x hx) (hw x hx)

end Bundle.ContMDiffRiemannianMetric
