/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Fundamental classes along compact sets inside an open embedding

Let `o` be a homological orientation of a manifold `M` of dimension `n`, `j : U → M` an open
embedding and `A ⊆ M` a compact set inside the range of `j`. Tau Ceti's
`TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_comap` says that `j` carries
the fundamental class of `U` along a compact set `K`, for the pulled-back orientation, to the
fundamental class of `M` along `j(K)`. This file states the same for `K = j⁻¹(A)`, with the
fundamental class of `M` along `A` itself, so that no image set `j(j⁻¹(A))` has to be rewritten
to `A`: `TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_comap_preimage`.

The proof is the uniqueness of the fundamental class along `A`
(`TauCeti.HomologicalOrientation.eq_fundamentalClassOn`), following the proof of Tau Ceti's
`TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_comap`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Module Set Topology

namespace TauCeti.HomologicalOrientation

variable {M U E : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace U] [T2Space U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [ChartedSpace E U] {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)

/-- **Fundamental classes along a compact set inside an open embedding.** For an open embedding
`j : U → M` and a compact set `A ⊆ M` inside the range of `j`, with compact preimage `j⁻¹(A)`, the
map `Hₙ(U, U ∖ j⁻¹(A); ℤ) ⟶ Hₙ(M, M ∖ A; ℤ)` induced by `j` carries the fundamental class of `U`
along `j⁻¹(A)`, for the pulled-back orientation `o.comap hj`, to the fundamental class of `o`
along `A`. -/
theorem localHomologyMap_fundamentalClassOn_comap_preimage {j : C(U, M)}
    (hj : IsOpenEmbedding j) {A : Set M} (hA : IsCompact A) (hAj : A ⊆ range j)
    (hK : IsCompact (j ⁻¹' A)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) j subset_rfl n
        ((o.comap hj).fundamentalClassOn hn hK) =
      o.fundamentalClassOn hn hA := by
  refine o.eq_fundamentalClassOn hn hA fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := hAj hx
  exact o.localHomologyRestriction_localHomologyMap_fundamentalClassOn_comap hn hj hK subset_rfl hx

end TauCeti.HomologicalOrientation

end
