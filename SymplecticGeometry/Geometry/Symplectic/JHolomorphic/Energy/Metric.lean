/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Density
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric

/-!
# The squared norm of a tangent map in the metric of a compatible pair

Let `(C, j)` be an almost complex surface with a two-form `dvol`, and `M` a manifold with a
two-form `ω` (`form` in the code) compatible with an almost complex structure `J`, so that
`g_J (u, v) = ω (u, J v)` is a Riemannian metric on `M`
(`TauCeti.SmoothTwoForm.Compatible.metric`). For a linear map `L : T_c C → T_x M` and a vector
`e` of `T_c C` with `dvol (e, j e) = 1`, a unit vector for the metric `dvol (·, j ·)`, the
squared norm `|L|²` of `TauCeti.SmoothTwoForm.normSq` is `g_J (L e, L e) + g_J (L j e, L j e)`:
the sum of the squared lengths, in `g_J`, of the images of the orthonormal frame `(e, j e)`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.normSq_eq_inner`: `|L|² = g_J (L e, L e) + g_J (L j e, L j e)`
  for `dvol (e, j e) = 1`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.5,
  equation (4.5.4).
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
-/

public section

open scoped ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' C : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]

/-- On a surface, for `form` compatible with `J` and a vector `e` with `dvol (e, j e) = 1`, the
squared norm of `L : T_c C → T_x M` is `g_J (L e, L e) + g_J (L (j e), L (j e))`, where
`g_J (u, v) = form (u, J v)` is the metric of the compatible pair. -/
theorem Compatible.normSq_eq_inner {form : SmoothTwoForm I M}
    {J : SmoothAlmostComplexStructure I M} (hc : form.Compatible J)
    (j : SmoothAlmostComplexStructure I' C) (h2 : Module.finrank ℝ E' = 2)
    (dvol : SmoothTwoForm I' C) {c : C} {x : M}
    (L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x) {e : TangentSpace I' c}
    (he : dvol.val c ![e, j c e] = 1) :
    form.normSq J j dvol L =
      hc.metric.inner x (L e) (L e) + hc.metric.inner x (L (j c e)) (L (j c e)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [(dvol.val c).map_coord_zero 0 (Matrix.cons_val_zero _ _)] at he
    exact zero_ne_one he
  rw [normSq_eq form J j h2 dvol L he0, he, div_one, Compatible.metric_inner,
    Compatible.metric_inner, SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply]

end SmoothTwoForm

end TauCeti

end
