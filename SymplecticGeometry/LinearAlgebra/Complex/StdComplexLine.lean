/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line

/-!
# Linear maps out of the standard complex line

Tau Ceti represents the standard complex line as `ℝ × ℝ`, with coordinate vectors
`TauCeti.stdComplexLineReal = (1, 0)` and `TauCeti.stdComplexLineImag = (0, 1)`. For vectors
`v` and `w` of a real module `V`, the linear map `(a, s) ↦ a • v + s • w`, written
`(LinearMap.toSpanSingleton ℝ V v).coprod (LinearMap.toSpanSingleton ℝ V w)`, sends these
coordinate vectors to `v` and `w`.

## Main results

* `LinearMap.coprod_toSpanSingleton_apply_stdComplexLineReal`: the image of
  `stdComplexLineReal` is `v`.
* `LinearMap.coprod_toSpanSingleton_apply_stdComplexLineImag`: the image of
  `stdComplexLineImag` is `w`.
-/

public section

namespace TauCeti

/-- The map `(a, s) ↦ a • v + s • w` sends `stdComplexLineReal = (1, 0)` to `v`. -/
theorem _root_.LinearMap.coprod_toSpanSingleton_apply_stdComplexLineReal {V : Type*}
    [AddCommMonoid V] [Module ℝ V] (v w : V) :
    (LinearMap.toSpanSingleton ℝ V v).coprod (LinearMap.toSpanSingleton ℝ V w)
      stdComplexLineReal = v := by
  simp [stdComplexLineReal_eq]

/-- The map `(a, s) ↦ a • v + s • w` sends `stdComplexLineImag = (0, 1)` to `w`. -/
theorem _root_.LinearMap.coprod_toSpanSingleton_apply_stdComplexLineImag {V : Type*}
    [AddCommMonoid V] [Module ℝ V] (v w : V) :
    (LinearMap.toSpanSingleton ℝ V v).coprod (LinearMap.toSpanSingleton ℝ V w)
      stdComplexLineImag = w := by
  simp [stdComplexLineImag_eq]

end TauCeti

end
