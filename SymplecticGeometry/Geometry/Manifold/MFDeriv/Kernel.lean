/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Kernels of differentials under a map that covers another

Let `p : P → M` and `q : Q → N` be maps, and let `Φ : P → Q` cover `ψ : M → N` near a point `y`,
in the sense that `q ∘ Φ = ψ ∘ p` near `y`. If the differential of `ψ` at `p y` is injective and
that of `Φ` at `y` is surjective, then the differential of `Φ` at `y` maps the kernel of the
differential of `p` at `y` onto the kernel of the differential of `q` at `Φ y`
(`Filter.EventuallyEq.map_ker_mfderiv`). For maps of fibrations this says that `Φ` carries
vertical vectors onto vertical vectors. The map `ψ` may be a chart of a manifold with corners,
whose differential is invertible on the source of the chart even at boundary points.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {K : ModelWithCorners 𝕜 F G} {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {L : ModelWithCorners 𝕜 F' G'} {Q : Type*} [TopologicalSpace Q] [ChartedSpace G' Q]

/-- **Kernels of differentials under a map that covers another.** Let `Φ : P → Q` cover
`ψ : M → N` near `y`, in the sense that `q ∘ Φ = ψ ∘ p` near `y`. If `p`, `Φ`, `ψ` and `q` are
differentiable at `y`, `y`, `p y` and `Φ y`, the differential of `ψ` at `p y` is injective and
that of `Φ` at `y` is surjective, then the differential of `Φ` at `y` maps the kernel of the
differential of `p` at `y` onto the kernel of the differential of `q` at `Φ y`. -/
theorem Filter.EventuallyEq.map_ker_mfderiv {p : P → M} {q : Q → N} {Φ : P → Q} {ψ : M → N}
    {y : P} (hcomm : q ∘ Φ =ᶠ[nhds y] ψ ∘ p) (hp : MDifferentiableAt K I p y)
    (hΦ : MDifferentiableAt K L Φ y) (hψ : MDifferentiableAt I J ψ (p y))
    (hq : MDifferentiableAt L J q (Φ y)) (hψi : Function.Injective (mfderiv I J ψ (p y)))
    (hΦs : Function.Surjective (mfderiv K L Φ y)) :
    (mfderiv K I p y).ker.map (mfderiv K L Φ y).toLinearMap =
      (mfderiv L J q (Φ y)).ker := by
  have h := (mfderiv_comp y hq hΦ).symm.trans <|
    (hcomm.mfderiv_eq (I := K) (I' := J)).trans (mfderiv_comp y hψ hp)
  rw [← Submodule.map_comap_eq_of_surjective hΦs (mfderiv L J q (Φ y)).ker]
  congr 1
  ext v
  simpa [← map_eq_zero_iff _ hψi] using congr($h v = 0).symm

end
