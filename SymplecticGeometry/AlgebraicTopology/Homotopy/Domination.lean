/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma

/-!
# CW type by domination

A space `X` is *dominated* by a space `K` when there are maps `i : X → K` and `r : K → X` with
`r ∘ i` homotopic to the identity of `X`. This file proves that a space dominated by a space of
CW type has CW type (`TauCeti.CWType.of_homotopic_comp`).

The proof uses Tau Ceti's CW approximation and both halves of Whitehead's theorem, with no mapping
telescope. Let `f : S → X` be the CW approximation `TauCeti.sigmaCWApproximationMap`, a weak
homotopy equivalence out of a space of CW type. Lift `r` through `f` to `r'` with `f ∘ r' ≃ r`
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`) and put `g = r' ∘ i`. Then
`f ∘ g ≃ r ∘ i ≃ id`, hence `f ∘ (g ∘ f) ≃ f`, and `g ∘ f ≃ id` follows from
`ContinuousMap.IsWeakHomotopyEquivalence.homotopic_of_comp_homotopic`. So `f` is a homotopy
equivalence, and `X` has CW type by `ContinuousMap.HomotopyEquiv.cwType`.

## Main results

* `TauCeti.CWType.of_homotopic_comp`: a space dominated by a space of CW type has CW type.

## References

* J. Milnor, *On spaces having the homotopy type of a CW-complex*, Trans. Amer. Math. Soc. 90
  (1959), 272–280.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1,
  Propositions 4.13 and 4.22.
-/

public section

universe u

namespace TauCeti.CWType

/-- **A space dominated by a space of CW type has CW type.** If `i : X → K` and `r : K → X` are
continuous maps with `r ∘ i` homotopic to the identity of `X`, and `K` has CW type, then `X` has
CW type. The space `K` may lie in any universe. -/
theorem of_homotopic_comp {X : Type u} {K : Type*} [TopologicalSpace X]
    [TopologicalSpace K] [TauCeti.CWType K] {i : C(X, K)} {r : C(K, X)}
    (h : (r.comp i).Homotopic (ContinuousMap.id X)) : TauCeti.CWType X := by
  let f := (sigmaCWApproximationMap (TopCat.of X)).hom
  have hf : f.IsWeakHomotopyEquivalence :=
    isWeakHomotopyEquivalence_sigmaCWApproximationMap (TopCat.of X)
  obtain ⟨r', hr'⟩ := hf.exists_comp_homotopic r
  -- `g = r' ∘ i` is a right homotopy inverse of `f`.
  have hfg : (f.comp (r'.comp i)).Homotopic (ContinuousMap.id X) := by
    rw [← ContinuousMap.comp_assoc]
    exact (hr'.comp (ContinuousMap.Homotopic.refl i)).trans h
  -- Hence `f ∘ (g ∘ f) ≃ f ∘ id`, so `g ∘ f ≃ id` as `f` is a weak homotopy equivalence.
  have hgf : ((r'.comp i).comp f).Homotopic (ContinuousMap.id _) := by
    refine hf.homotopic_of_comp_homotopic ?_
    rw [← ContinuousMap.comp_assoc, ContinuousMap.comp_id]
    simpa only [ContinuousMap.id_comp] using hfg.comp (ContinuousMap.Homotopic.refl f)
  exact (ContinuousMap.HomotopyEquiv.symm
    { toFun := f, invFun := r'.comp i, left_inv := hgf, right_inv := hfg }).cwType

end TauCeti.CWType

end
