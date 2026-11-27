/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex

/-!
# Homeomorphisms carrying local orientations carry fundamental classes

Let `M` and `N` be compact Hausdorff spaces, charted on finite-dimensional real normed spaces `E`
and `F` of the same dimension `n`, with homological orientations `o` and `o'`, and let
`e : M ≃ₜ N` be a homeomorphism. If, for every `x`, the map that `e` induces on local homology
`Hₙ(M, M ∖ {x}; ℤ) ⟶ Hₙ(N, N ∖ {e x}; ℤ)` carries the local orientation `o x` to `o' (e x)`, then
`e` carries the fundamental class of `o` to that of `o'`. Equivalently, it suffices that the
local index of `e` from `o` to `o'` be `1` at every point.

No connectedness is assumed, and the two orientations may be read on different model spaces. The
proof checks the defining property of the fundamental class of `o'`
(`TauCeti.HomologicalOrientation.eq_fundamentalClass`) at each point `e x`, whose only preimage
is `x`. It follows Tau Ceti's `TauCeti.HomologicalOrientation.mapFundamentalClass_comap`, which
treats one model space and the orientation `o'.comap` pulled back along `e`. The second form
reads the local index on the whole source by
`TauCeti.HomologicalOrientation.localIndex_eq_iff_of_preimage_subset`.

## Main results

* `TauCeti.HomologicalOrientation.mapFundamentalClass_homeomorph_of_localHomologyMap`:
  `e_*[M, o] = [N, o']` when `e` carries `o x` to `o' (e x)` for every `x`.
* `TauCeti.HomologicalOrientation.mapFundamentalClass_homeomorph_of_localIndex_eq_one`:
  `e_*[M, o] = [N, o']` when the local index of `e` is `1` everywhere.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open Module

namespace TauCeti.HomologicalOrientation

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
  (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)

/-- **A homeomorphism carrying local orientations carries the fundamental class.** Let
`e : M ≃ₜ N` be a homeomorphism of compact manifolds of dimension `n` such that, at every `x`, the
map `Hₙ(M, M ∖ {x}; ℤ) ⟶ Hₙ(N, N ∖ {e x}; ℤ)` induced by `e` carries the local orientation `o x`
to `o' (e x)`. Then `e` carries the fundamental class of `o` to the fundamental class of `o'`. -/
theorem mapFundamentalClass_homeomorph_of_localHomologyMap (e : M ≃ₜ N)
    (h : ∀ x (hx : (e : C(M, N)) ⁻¹' {e x} ⊆ {x}),
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (e : C(M, N)) hx n (o x).val =
        (o' (e x)).val) :
    o.mapFundamentalClass hE (e : C(M, N)) = o'.fundamentalClass hF := by
  -- `e_*[M]` lies in the singular homology of `TopCat.of N`, read as `SSet.homology` here.
  refine o'.eq_fundamentalClass hF
    (γ := o.mapFundamentalClass hE (e : C(M, N))) fun y ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ x, (e : C(M, N)) x = y := e.surjective y
  have hx : (e : C(M, N)) ⁻¹' {(e : C(M, N)) x} ⊆ {x} := fun _ hz ↦ e.injective hz
  rw [mapFundamentalClass_def, singularHomologyFunctor_obj_map_hom_apply,
    singularHomologyToLocalHomology_singularHomologyMap _ _ hx,
    singularHomologyToLocalHomology_fundamentalClass]
  exact h x hx

/-- **A homeomorphism of local index one carries the fundamental class.** A homeomorphism
`e : M ≃ₜ N` of compact manifolds of dimension `n` whose local index from `o` to `o'` is `1` at
every point carries the fundamental class of `o` to the fundamental class of `o'`. -/
theorem mapFundamentalClass_homeomorph_of_localIndex_eq_one (e : M ≃ₜ N)
    (h : ∀ x, o.localIndex o' (e : C(M, N)) x = 1) :
    o.mapFundamentalClass hE (e : C(M, N)) = o'.fundamentalClass hF :=
  o.mapFundamentalClass_homeomorph_of_localHomologyMap hE hF o' e fun x hx ↦ by
    simpa using (o.localIndex_eq_iff_of_preimage_subset o' hF (e : C(M, N)) rfl hx).1 (h x)

end TauCeti.HomologicalOrientation

end
