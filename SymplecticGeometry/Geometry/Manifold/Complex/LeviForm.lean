/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
import SymplecticGeometry.Analysis.Complex.Pseudoconvex
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The Levi form on a complex manifold: its diagonal, and positivity near a point

For a real function `f` on a complex manifold that is `C²` at `x`, strong `q`-pseudoconvexity at
`x` (Tau Ceti's `TauCeti.IsManifoldStronglyPseudoconvexAt`) holds at all points near `x`, and so
does strict plurisubharmonicity:

* `TauCeti.IsManifoldStronglyPseudoconvexAt.eventually`,
* `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.eventually`.

In the preferred chart at `x` this is `TauCeti.IsStronglyPseudoconvexAt.eventually`, and Tau
Ceti's `isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas` lets that one chart serve all
nearby points.

It also records two facts about the real part of the Levi form on the diagonal:

* `TauCeti.re_manifoldLeviForm_scalar_comp_apply_self`: for a composition `φ ∘ f` with a real
  function `φ`, in terms of `df(v)` and `df(i v)`, from Tau Ceti's
  `TauCeti.manifoldLeviForm_scalar_comp_apply`;
* `TauCeti.eventually_forall_re_manifoldLeviForm_add_mul_pos`: if it is positive on the nonzero
  `v` with `df(v) = df(i v) = 0`, it becomes positive on all nonzero `v` once a large multiple of
  `df(v)² + df(i v)²` is added. This is Tau Ceti's Finsler lemma
  `IsCompact.eventually_exists_pos_forall_mul_norm_sq_le_mul_add` for one pair of forms.

On a complex normed space `E` seen as a manifold modelled on itself,
`TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_isStrictlyPlurisubharmonicAt` says that strict
plurisubharmonicity is that of the Levi form on `E`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- On a complex normed space `E`, seen as a complex manifold modelled on itself, strict
plurisubharmonicity of `u : E → ℝ` at `z` is strict plurisubharmonicity in the sense of complex
vector spaces: positive definiteness of the Levi form `leviForm u z`. -/
@[simp]
theorem isManifoldStrictlyPlurisubharmonicAt_iff_isStrictlyPlurisubharmonicAt
    {u : E → ℝ} {z : E} :
    IsManifoldStrictlyPlurisubharmonicAt E u z ↔ IsStrictlyPlurisubharmonicAt u z := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff, isStrictlyPlurisubharmonicAt_iff]
  simp only [manifoldLeviForm_eq_leviForm]

end ModelSpace

section Diagonal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- **The real part of the Levi form of `φ ∘ f` on the diagonal.** For `f` of class `C²` at `x`
and `φ : ℝ → ℝ` of class `C²` at `f x`, the real part of the Levi form of `φ ∘ f` at `x` on `(v, v)`
is `φ'(f x)` times that of `f`, plus `φ''(f x) / 4` times `df(v)² + df(i v)²`. -/
theorem re_manifoldLeviForm_scalar_comp_apply_self {φ : ℝ → ℝ} {f : M → ℝ} {x : M}
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (v : E) :
    (manifoldLeviForm E (φ ∘ f) x v v).re = deriv φ (f x) * (manifoldLeviForm E f x v v).re +
      iteratedDeriv 2 φ (f x) / 4 * (mvfderiv 𝓘(ℝ, E) f x v ^ 2 +
        mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) ^ 2) := by
  -- Tau Ceti's lemma applies `StrongDual.extendRCLike` to `mvfderiv`, a covector on
  -- `TangentSpace 𝓘(ℝ, E) x`; `key` states its value on `E` so that `rw` can use it.
  have key (u : E) :
      (StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) f x) : StrongDual ℂ E) u =
        ↑(mvfderiv 𝓘(ℝ, E) f x u) - Complex.I * ↑(mvfderiv 𝓘(ℝ, E) f x (Complex.I • u)) :=
    StrongDual.extendRCLike_apply _ u
  rw [manifoldLeviForm_scalar_comp_apply hφ hf v v, key]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **The Levi form plus a large multiple of the squared differential.** If the real part of the
Levi form of `f` at `x` is positive on the nonzero vectors `v` with `df(v) = df(i v) = 0`, then
for every large enough `c`, the real part of the Levi form plus `c (df(v)² + df(i v)²)` is
positive on every nonzero `v`. -/
theorem eventually_forall_re_manifoldLeviForm_add_mul_pos [FiniteDimensional ℂ E] {f : M → ℝ}
    {x : M} (hL : ∀ v : E, mvfderiv 𝓘(ℝ, E) f x v = 0 →
      mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) = 0 → v ≠ 0 → 0 < (manifoldLeviForm E f x v v).re) :
    ∀ᶠ c in atTop, ∀ v : E, v ≠ 0 → 0 < (manifoldLeviForm E f x v v).re +
      c * (mvfderiv 𝓘(ℝ, E) f x v ^ 2 + mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) ^ 2) := by
  have : FiniteDimensional ℝ E := .complexToReal E
  let B := fderiv ℝ (fderiv ℝ (f ∘ (chartAt E x).symm)) (chartAt E x x)
  let D : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f x
  let J : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hJ (v : E) : J v = Complex.I • v := by simp [J]
  -- Finsler's lemma, for the forms `a = df ⊗ df + (df ∘ J) ⊗ (df ∘ J)` and `b`, whose diagonal
  -- is the real part of the Levi form.
  let a : E →L[ℝ] E →L[ℝ] ℝ := D.smulRight D + (D.comp J).smulRight (D.comp J)
  let b : E →L[ℝ] E →L[ℝ] ℝ := (4 : ℝ)⁻¹ • (B + B.bilinearComp J J)
  -- `D` is `mvfderiv` with `TangentSpace 𝓘(ℝ, E) x` and `TangentSpace 𝓘(ℝ) (f x)` read as `E`
  -- and `ℝ`, which they are by definition.
  have hD (v : E) : D v = mvfderiv 𝓘(ℝ, E) f x v := rfl
  have ha (v : E) :
      a v v = mvfderiv 𝓘(ℝ, E) f x v ^ 2 + mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) ^ 2 := by
    simp only [a, _root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, hJ, smul_eq_mul, hD]
    ring
  have hb (v : E) : b v v = (manifoldLeviForm E f x v v).re := by
    simp only [b, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.bilinearComp_apply, hJ, smul_eq_mul, manifoldLeviForm_def,
      re_leviForm_apply]
    ring
  filter_upwards [isCompact_singleton.eventually_exists_pos_forall_mul_norm_sq_le_mul_add
    (K := {()}) (a := fun _ ↦ a) (b := fun _ ↦ b) continuousOn_const continuousOn_const
    (fun _ _ v ↦ by rw [ha]; positivity) fun _ _ v hv h ↦ by
      rw [ha] at h
      rw [hb]
      have h1 : mvfderiv 𝓘(ℝ, E) f x v = 0 := by nlinarith
      have h2 : mvfderiv 𝓘(ℝ, E) f x (Complex.I • v) = 0 := by nlinarith
      exact hL v h1 h2 hv] with t ⟨c, hc, h⟩ v hv
  have h := h () rfl v
  rw [ha, hb] at h
  have : 0 < c * ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv; positivity
  linarith

end Diagonal

section Eventually

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 2 M]
  {f : M → ℝ} {x : M}

/-- **Strong `q`-pseudoconvexity is an open condition** on a complex manifold. If `f` is real
`C²` at `x` and strongly `q`-pseudoconvex at `x`, then it is strongly `q`-pseudoconvex at every
point near `x`. -/
theorem IsManifoldStronglyPseudoconvexAt.eventually {q : ℕ}
    (h : IsManifoldStronglyPseudoconvexAt E q f x) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    ∀ᶠ y in 𝓝 x, IsManifoldStronglyPseudoconvexAt E q f y := by
  have : IsManifold 𝓘(ℝ, E) 2 M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) 2 M)
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, E)) (n := 2) x
  have hx := mem_chart_source E x
  -- Read `f` in the preferred chart at `x`, and use the openness on the model space.
  have h' := ((isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas he hx hf).1 h).eventually
    hf.contDiffAt_comp_chartAt_symm
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf,
    (chartAt E x).open_source.mem_nhds hx, (chartAt E x).continuousAt hx h'] with y hfy hy hy'
  exact (isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas he hy hfy).2 hy'

/-- **Strict plurisubharmonicity is an open condition** on a complex manifold. If `f` is real
`C²` at `x` and strictly plurisubharmonic at `x`, then it is strictly plurisubharmonic at every
point near `x`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.eventually
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    ∀ᶠ y in 𝓝 x, IsManifoldStrictlyPlurisubharmonicAt E f y := by
  simpa only [isManifoldStronglyPseudoconvexAt_zero_iff] using
    (h.isManifoldStronglyPseudoconvexAt 0).eventually hf

end Eventually

end TauCeti

end
