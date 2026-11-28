/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# Extending maps into a star-convex set from a closed cofibration

Let `A ⊆ X` be a closed subset with the homotopy extension property
(`TauCeti.HasHomotopyExtensionProperty`), and let `C` be a set of a real topological vector
space that is star-convex about a point `c ∈ C`. Every map `f` that is continuous on `A` and
sends it into `C` agrees on `A` with a continuous map `X → V` with values in `C`.

The straight-line homotopy `(t, a) ↦ (1 - t) • c + t • f a` on `I × A` starts at the constant
map `c` and stays in `C`. The constant map `c` is defined on all of `X`, so the homotopy
extension property (`TauCeti.HasHomotopyExtensionProperty.exists_extension_of_isClosed`) extends
the homotopy to `I × X → C`, and its end is the extension.

## Main results

* `StarConvex.exists_continuousMap_eqOn_of_hasHomotopyExtensionProperty`: for `C` star-convex
  about `c ∈ C` and a closed subset `A` with the homotopy extension property, every map that is
  continuous on `A` and sends it into `C` agrees there with a continuous map `X → V` with range
  in `C`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the section "The Homotopy Extension Property".
-/

public section

open Set TauCeti
open scoped unitInterval

namespace StarConvex

variable {X : Type*} [TopologicalSpace X] {A : Set X} {V : Type*} [AddCommMonoid V] [Module ℝ V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] {C : Set V} {c : V} {f : X → V}

/-- Let `A ⊆ X` be a closed subset with the homotopy extension property and `C` a set that is
star-convex about a point `c ∈ C`. A map `f` that is continuous on `A` and sends `A` into `C`
agrees on `A` with a continuous map `g : X → V` whose range lies in `C`. -/
theorem exists_continuousMap_eqOn_of_hasHomotopyExtensionProperty (hC : StarConvex ℝ c C)
    (hc : c ∈ C) (hA : IsClosed A) (hAX : HasHomotopyExtensionProperty A)
    (hf : ContinuousOn f A) (hfC : MapsTo f A C) :
    ∃ g : C(X, V), EqOn g f A ∧ range g ⊆ C := by
  have hfc : Continuous fun p : I × A ↦ f p.2 := hf.domRestrict.comp continuous_snd
  have ht : Continuous fun p : I × A ↦ (p.1 : ℝ) := by fun_prop
  let H : C(I × A, C) :=
    ⟨fun p ↦ ⟨(1 - (p.1 : ℝ)) • c + (p.1 : ℝ) • f p.2,
      hC (hfC p.2.property) (sub_nonneg.2 p.1.property.2) p.1.property.1 (sub_add_cancel _ _)⟩,
      (((continuous_const.sub ht).smul continuous_const).add (ht.smul hfc)).subtype_mk _⟩
  obtain ⟨G, -, hG⟩ :=
    hAX.exists_extension_of_isClosed hA (ContinuousMap.const _ ⟨c, hc⟩) H fun a ↦ by ext; simp [H]
  refine ⟨⟨fun x ↦ G (1, x), by fun_prop⟩, fun x hx ↦ ?_, ?_⟩
  · simpa [H] using congrArg Subtype.val (hG 1 ⟨x, hx⟩)
  · rintro _ ⟨x, rfl⟩
    exact (G (1, x)).property

end StarConvex

end
