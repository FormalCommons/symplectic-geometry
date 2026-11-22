/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# A plane cut by two linear forms

Let `P` be a plane in a vector space, and let `f` and `g` be linear forms. Suppose `P` contains a
vector `v` with `f v ≠ 0` and `g v = 0`. Then the line `P ∩ ker f` meets `ker g` only in `0`
exactly when `g` does not vanish on `P` (`Submodule.inf_ker_inf_ker_eq_bot_iff`).

This is the linear algebra behind the transversality of a pencil of hyperplanes to a projective
hypersurface: there `P` is the common zero plane of a tuple of linear forms, `v` a vector of it,
`f` a coordinate with `f v ≠ 0` and `g` the differential of the polynomial at `v`, which vanishes
at `v` by Euler's identity.
-/

public section

open Module LinearMap

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Let `P` be a plane, and let `f` and `g` be linear forms with a vector `v ∈ P` such that
`f v ≠ 0` and `g v = 0`. Then `P`, `ker f` and `ker g` meet only in `0` exactly when `g` does not
vanish on `P`. -/
theorem inf_ker_inf_ker_eq_bot_iff {P : Submodule K V} (hP : finrank K P = 2)
    {f g : V →ₗ[K] K} {v : V} (hv : v ∈ P) (hfv : f v ≠ 0) (hgv : g v = 0) :
    P ⊓ ker f ⊓ ker g = ⊥ ↔ ∃ w ∈ P, g w ≠ 0 := by
  have : FiniteDimensional K P := Module.finite_of_finrank_eq_succ hP
  -- The common kernel of `P` and `f` is a line, since `f` does not vanish on `P`.
  have hT : finrank K ↥(P ⊓ ker f) = 1 := by
    have := Module.Dual.finrank_ker_inf_add_one (f := f) (U := P) fun h ↦ hfv (h hv)
    rw [inf_comm] at this
    omega
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.1 hT.ge)
    refine ⟨x, hx.1, fun hgx ↦ hx0 ?_⟩
    have : x ∈ P ⊓ ker f ⊓ ker g := ⟨hx, hgx⟩
    rwa [h, Submodule.mem_bot] at this
  · rintro ⟨w, hwP, hgw⟩
    refine eq_bot_iff.2 fun x hx ↦ ?_
    obtain ⟨⟨hxP, hxf⟩, hxg⟩ := hx
    by_contra hx0
    -- Projecting `w` along `v` into the line `P ∩ ker f` keeps `g w`, so `x`, which spans
    -- that line, cannot lie in `ker g`.
    have hw₁ : w - (f w / f v) • v ∈ P ⊓ ker f :=
      ⟨P.sub_mem hwP (P.smul_mem _ hv), by simp [div_mul_cancel₀ _ hfv]⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨x, hxP, hxf⟩ : ↥(P ⊓ ker f))
      (fun h ↦ hx0 (congrArg Subtype.val h))).1 hT ⟨_, hw₁⟩
    have := congrArg (fun y : ↥(P ⊓ ker f) ↦ g y) hc
    simp only [SetLike.val_smul, map_smul, map_sub, hgv, smul_zero, sub_zero] at this
    exact hgw (by rw [← this, mem_ker.1 hxg, smul_zero])

end Submodule
