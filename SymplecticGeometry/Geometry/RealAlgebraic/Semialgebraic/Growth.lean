/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Polynomial.Puiseux.RealBranch
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.RootBranch

/-!
# Growth of a one-variable semialgebraic function near `0⁺`

A real function `f` of one variable that is semialgebraic just to the right of `0`, and does
not vanish identically on any interval `(0, ε)`, is comparable to a rational power of the
variable there: for some `q : ℚ` and `a ≠ 0`, `f t / t ^ q → a` as `t → 0⁺`
(`TauCeti.IsSemialgebraicOn.exists_tendsto_div_rpow_nhdsGT`).

The proof puts two results together. Near `0⁺`, `f` is continuous and is a root branch of a
polynomial `P : ℝ[X][X]` with nonzero discriminant and nonzero constant coefficient
(`TauCeti.IsSemialgebraicOn.exists_polynomial_eventually_isRoot_nhdsGT`), and such a continuous
real root branch grows like a rational power of `t`
(`Polynomial.exists_tendsto_div_rpow_of_continuousOn_isRoot`), by the Newton–Puiseux
expansion.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.5–2.6.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 3.
-/

public section

open Filter Topology

namespace TauCeti

/-- A one-variable function `f`, semialgebraic on a set `s` that contains `![t]` for all
`t > 0` close to `0`, and not identically zero on any interval `(0, ε)`, grows like a rational
power of the variable near `0⁺`: there are `q : ℚ` and a real `a ≠ 0` with
`f ![t] / t ^ q → a` as `t → 0⁺`. -/
theorem IsSemialgebraicOn.exists_tendsto_div_rpow_nhdsGT {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s)
    (hs : ∀ᶠ t in 𝓝[>] 0, ![t] ∈ s) (hne : ∃ᶠ t in 𝓝[>] 0, f ![t] ≠ 0) :
    ∃ q : ℚ, ∃ a : ℝ, a ≠ 0 ∧
      Tendsto (fun t ↦ f ![t] / t ^ (q : ℝ)) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨P, hdisc, hc0, hev⟩ := hf.exists_polynomial_eventually_isRoot_nhdsGT hs hne
  obtain ⟨ε, hε, hsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.1 hev
  exact Polynomial.exists_tendsto_div_rpow_of_continuousOn_isRoot hdisc hc0 hε
    (fun t ht ↦ (hsub ht).1.continuousWithinAt) fun t ht ↦ (hsub ht).2

end TauCeti

end
