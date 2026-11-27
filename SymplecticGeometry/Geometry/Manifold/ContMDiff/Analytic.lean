/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Transition maps of analytic charts

For a manifold modelled on a normed space `E` itself (the model `𝓘(𝕜, E)`), the transition map
`e' ∘ e⁻¹` between two charts of the maximal analytic atlas is analytic on its source
(`OpenPartialHomeomorph.analyticOnNhd_symm_trans_of_mem_maximalAtlas`). It is Tau Ceti's
`TauCeti.contDiffOn_symm_trans_of_mem_maximalAtlas` for `n = ω`, read through Mathlib's
`contDiffOn_omega_iff_analyticOn` on the open source of the transition map.
-/

public section

open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {e e' : OpenPartialHomeomorph M E}

/-- The transition map `e' ∘ e⁻¹` between two charts of the maximal analytic atlas of a manifold
modelled on `E` is analytic on its source. -/
theorem analyticOnNhd_symm_trans_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M) :
    AnalyticOnNhd 𝕜 (e.symm.trans e') (e.symm.trans e').source :=
  (e.symm.trans e').open_source.analyticOn_iff_analyticOnNhd.1 <|
    (contDiffOn_omega_iff_analyticOn (e.symm.trans e').open_source.uniqueDiffOn).1 <|
      TauCeti.contDiffOn_symm_trans_of_mem_maximalAtlas he he'

end OpenPartialHomeomorph

end
