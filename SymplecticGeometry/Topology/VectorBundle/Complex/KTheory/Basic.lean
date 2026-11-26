/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Newton
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# Newton classes on the K-group of complex bundle cores

Over a compact space `X`, Tau Ceti's finite-rank cores `TauCeti.FiniteRankBundleCore ℂ X` are
complex vector bundles of constant rank, and we write `K(X)` for their split Grothendieck group
`TauCeti.SplitK0 (FiniteRankBundleCore ℂ X)`, a commutative ring under the tensor product. Since
a core has a single rank over all of `X`, this is the K-group of constant-rank bundles: it agrees
with Hatcher's `K(X)` for connected `X`, but not in general (over two points it is `ℤ`, not
`ℤ²`). The Newton class `s_j` of the bundle of a core is invariant under isomorphism and
additive on Whitney sums, so it descends to an additive map `K(X) → H^{2j}(X; ℤ)`, natural in `X`.

## Main definitions

* `SymplecticGeometry.Bundle.newtonClassInvariant X j`: the Newton class `s_j` as an additive
  invariant of finite-rank cores, `A ↦ newtonClass (Fin A.rank → ℂ) A.core.Fiber j`.
* `SymplecticGeometry.Bundle.newtonClassHom X j`: its lift to `K(X) →+ H^{2j}(X; ℤ)`.

## Main results

* `TauCeti.FiniteRankBundleCore.newtonClass_eq_of_iso`, `newtonClass_whitneySum` and
  `newtonClass_pullback`: the Newton classes of cores are invariant under isomorphism, additive
  on Whitney sums and natural under pullback; by `newtonClass_trivial`, those of a trivial core
  vanish in positive degree.
* `newtonClassHom_of`: on the class of a core, `newtonClassHom` is the Newton class of its
  bundle.
* `newtonClassHom_pullback`: `newtonClassHom` commutes with pullback along a continuous map,
  acting on `K` by `TauCeti.SplitK0.mapRingHom (pullbackFunctor f)` and on cohomology by
  `TopCat.singularCohomologyMap`.
* `newtonClassHom_trivial`, `newtonClassHom_one`: in positive degree, `newtonClassHom` vanishes on
  the classes of trivial cores, the unit of `K(X)` among them.

Invariance under isomorphism uses the fibrewise equivalences
`TauCeti.FiniteRankBundleCore.isoFiberEquiv` and `newtonClass_congr`. A biproduct `A ⊞ D` in the
category of cores is isomorphic to Tau Ceti's Whitney sum `whitneySum A D` (by
`whitneyBiconeIsBilimit`), whose total space is identified with that of Mathlib's direct sum
`A.core.Fiber ×ᵇ D.core.Fiber` by `whitneySumTotalSpaceHomeomorph`; additivity is then
`newtonClass_prod`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017)][Hatcher2017], §2.1 (the
  group `K(X)`)
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §16
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti SymplecticGeometry.Bundle

/-! ### Newton classes of cores -/

namespace TauCeti.FiniteRankBundleCore

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

/-- **Isomorphic complex finite-rank cores have the same Newton classes.** -/
theorem newtonClass_eq_of_iso {A D : FiniteRankBundleCore ℂ X} (e : A ≅ D) (j : ℕ) :
    newtonClass (Fin A.rank → ℂ) A.core.Fiber j = newtonClass (Fin D.rank → ℂ) D.core.Fiber j :=
  newtonClass_congr (E := A.core.Fiber) (E' := D.core.Fiber) (isoFiberEquiv e)
    (continuous_isoFiberEquiv e) j

/-- **Additivity of the Newton classes of cores.** Over a compact space, the Newton classes of
the Whitney sum `whitneySum A D` of two cores are the sums of those of `A` and `D`. -/
@[simp]
theorem newtonClass_whitneySum (A D : FiniteRankBundleCore ℂ X) (j : ℕ) :
    newtonClass (Fin (whitneySum A D).rank → ℂ) (whitneySum A D).core.Fiber j =
      newtonClass (Fin A.rank → ℂ) A.core.Fiber j +
        newtonClass (Fin D.rank → ℂ) D.core.Fiber j := by
  rw [← newtonClass_prod]
  refine newtonClass_congr (E := (whitneySum A D).core.Fiber) (E' := A.core.Fiber ×ᵇ D.core.Fiber)
    (whitneySumFiberEquiv A D) ?_ j
  exact (whitneySumTotalSpaceHomeomorph A D).continuous.congr fun p ↦
    whitneySumTotalSpaceHomeomorph_apply A D p

/-- **Naturality of the Newton classes of cores.** For a continuous map `f : Y → X` of compact
spaces, the Newton class of the pull-back core `A.pullback f` is the pull-back of that of `A`. -/
@[simp]
theorem newtonClass_pullback {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (f : C(Y, X))
    (A : FiniteRankBundleCore ℂ X) (j : ℕ) :
    newtonClass (Fin (A.pullback f).rank → ℂ) (A.pullback f).core.Fiber j =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (2 * j)
        (newtonClass (Fin A.rank → ℂ) A.core.Fiber j) := by
  rw [← SymplecticGeometry.Bundle.newtonClass_pullback f]
  exact newtonClass_congr (E := (A.pullback f).core.Fiber) (E' := f *ᵖ A.core.Fiber)
    (fun _ ↦ ContinuousLinearEquiv.refl ℂ (Fin A.rank → ℂ))
    ((A.pullbackHomeomorph f).continuous.congr fun p ↦ A.pullbackHomeomorph_apply f p) j

/-- **The Newton classes of a trivial core vanish in positive degree**, over a compact space. -/
@[simp]
theorem newtonClass_trivial (n : ℕ) {j : ℕ} (hj : j ≠ 0) :
    newtonClass (Fin (trivial ℂ X n).rank → ℂ) (trivial ℂ X n).core.Fiber j = 0 := by
  rw [← SymplecticGeometry.Bundle.newtonClass_trivial X hj (G := Fin n → ℂ)]
  exact newtonClass_congr (E := (trivial ℂ X n).core.Fiber) (E' := Bundle.Trivial X (Fin n → ℂ))
    (fun _ ↦ ContinuousLinearEquiv.refl ℂ (Fin n → ℂ))
    ((Bundle.Trivial.isInducing_toProd X (Fin n → ℂ)).continuous_iff.2
      ((trivial ℂ X n).core.continuous_proj.prodMk continuous_trivial_snd)) j

end TauCeti.FiniteRankBundleCore

/-! ### The Newton classes on `K(X)` -/

namespace SymplecticGeometry.Bundle

variable (X : Type) [TopologicalSpace X] [CompactSpace X]

/-- The **Newton class** `s_j` as an additive invariant of complex finite-rank cores over a
compact space `X`: it sends a core `A` to the Newton class of its bundle in `H^{2j}(X; ℤ)`, is
constant on isomorphism classes and additive on biproducts. -/
def newtonClassInvariant (j : ℕ) :
    SplitK0.AdditiveInvariant (FiniteRankBundleCore ℂ X)
      ((TopCat.of X).integralCohomology (2 * j)) where
  obj A := newtonClass (Fin A.rank → ℂ) A.core.Fiber j
  map_iso _ _ e := FiniteRankBundleCore.newtonClass_eq_of_iso e j
  map_biprod A D := by
    rw [← FiniteRankBundleCore.newtonClass_eq_of_iso
      (biprod.uniqueUpToIso A D (FiniteRankBundleCore.whitneyBiconeIsBilimit A D))]
    exact FiniteRankBundleCore.newtonClass_whitneySum A D j

@[simp]
theorem newtonClassInvariant_obj (j : ℕ) (A : FiniteRankBundleCore ℂ X) :
    (newtonClassInvariant X j).obj A = newtonClass (Fin A.rank → ℂ) A.core.Fiber j :=
  (rfl)

/-- The **Newton class** `s_j : K(X) →+ H^{2j}(X; ℤ)` on the split Grothendieck group of complex
finite-rank cores over a compact space `X`, the additive map sending the class of a core to the
Newton class of its bundle. -/
def newtonClassHom (j : ℕ) :
    SplitK0 (FiniteRankBundleCore ℂ X) →+ (TopCat.of X).integralCohomology (2 * j) :=
  SplitK0.lift (newtonClassInvariant X j)

theorem newtonClassHom_def (j : ℕ) :
    newtonClassHom X j = SplitK0.lift (newtonClassInvariant X j) :=
  (rfl)

variable {X}

/-- On the class of a core, `newtonClassHom` is the Newton class of its bundle. -/
@[simp]
theorem newtonClassHom_of (j : ℕ) (A : FiniteRankBundleCore ℂ X) :
    newtonClassHom X j (SplitK0.of A) = newtonClass (Fin A.rank → ℂ) A.core.Fiber j := by
  rw [newtonClassHom_def, SplitK0.lift_of, newtonClassInvariant_obj]

/-- **Naturality of the Newton classes on `K`.** For a continuous map `f : Y → X` of compact
spaces, `s_j(f^* x) = f^* s_j(x)` for every `x ∈ K(X)`, where `f^*` acts on `K` by pulling back
cores. -/
@[simp]
theorem newtonClassHom_pullback {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (f : C(Y, X))
    (j : ℕ) (x : SplitK0 (FiniteRankBundleCore ℂ X)) :
    newtonClassHom Y j (SplitK0.mapRingHom (FiniteRankBundleCore.pullbackFunctor f) x) =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (2 * j) (newtonClassHom X j x) := by
  induction x using SplitK0.induction_on with
  | zero => simp
  | of A => rw [SplitK0.mapRingHom_of, newtonClassHom_of, newtonClassHom_of,
      FiniteRankBundleCore.pullbackFunctor_obj, FiniteRankBundleCore.newtonClass_pullback]
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]

/-- In positive degree, `newtonClassHom` vanishes on the class of a trivial core. -/
theorem newtonClassHom_trivial (n : ℕ) {j : ℕ} (hj : j ≠ 0) :
    newtonClassHom X j (SplitK0.of (FiniteRankBundleCore.trivial ℂ X n)) = 0 := by
  rw [newtonClassHom_of, FiniteRankBundleCore.newtonClass_trivial n hj]

/-- In positive degree, `newtonClassHom` vanishes on the unit `1` of `K`, the class of the trivial
line bundle. -/
@[simp]
theorem newtonClassHom_one {j : ℕ} (hj : j ≠ 0) :
    newtonClassHom X j (1 : SplitK0 (FiniteRankBundleCore ℂ X)) = 0 := by
  rw [SplitK0.one_def]
  exact newtonClassHom_trivial 1 hj

end SymplecticGeometry.Bundle

end

end
