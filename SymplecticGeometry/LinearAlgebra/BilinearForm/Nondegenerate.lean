/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Nondegeneracy of reflexive bilinear forms and of their restrictions

For a reflexive bilinear form `B` and a submodule `W`, the restriction of `B` to `W` is
nondegenerate exactly when the only vector of `W` that pairs to zero under `B` with all of `W`
is zero (`LinearMap.BilinForm.IsRefl.nondegenerate_restrict_iff`). This is the vector form of
Tau Ceti's `LinearMap.BilinForm.restrict_nondegenerate_iff_disjoint_orthogonal`, and holds over
any commutative semiring. Its proof follows the elementwise step of Tau Ceti's
`Module.Dual.isContact_iff_of_isRefl`, checking both sides of nondegeneracy directly.

## Nondegeneracy from a hyperplane with a one-dimensional radical

Let `B` be a reflexive bilinear form on a module `M` over a commutative ring without zero
divisors, and let `W` be a submodule that, together with one vector `e`, spans `M`. Suppose that
the radical of the restriction of `B` to `W` is the line spanned by a vector `x ∈ W`, and that
`B x e ≠ 0`. Then `B` is nondegenerate
(`LinearMap.BilinForm.IsRefl.nondegenerate_of_ker_restrict_eq_span_singleton`).

Over a field this applies to a hyperplane `W` and any `e ∉ W`; the hypotheses force `e ∉ W`
anyway, since `x` pairs to zero with all of `W`. For alternating forms this is the step, on each
tangent space, of the proof that the coupling forms of the minimal coupling construction of
Sternberg and Weinstein are symplectic (McDuff–Salamon, Proposition 5.1.9): there `W` is the
kernel of the differential of the coupling parameter, and `x` is the generator of the circle
action.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9
-/

public section

namespace LinearMap.BilinForm

section Restrict

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- For a reflexive bilinear form `B`, the restriction of `B` to a submodule `W` is
nondegenerate if and only if every `u ∈ W` with `B u w = 0` for all `w ∈ W` is zero. -/
theorem IsRefl.nondegenerate_restrict_iff {B : LinearMap.BilinForm R M} (hB : B.IsRefl)
    {W : Submodule R M} :
    (B.restrict W).Nondegenerate ↔ ∀ u ∈ W, (∀ w ∈ W, B u w = 0) → u = 0 :=
  ⟨fun h u hu hw ↦ congrArg Subtype.val (h.1 ⟨u, hu⟩ fun w ↦ hw w w.property),
    fun h ↦ ⟨fun u hu ↦ Subtype.ext (h u u.property fun w hw ↦ hu ⟨w, hw⟩),
      fun u hu ↦ Subtype.ext (h u u.property fun w hw ↦ hB _ _ (hu ⟨w, hw⟩))⟩⟩

end Restrict

variable {R M : Type*} [CommRing R] [NoZeroDivisors R] [AddCommGroup M] [Module R M]

/-- Let `B` be a reflexive bilinear form, and `W` a submodule with `W ⊔ R ∙ e = ⊤`. If the
kernel of the restriction of `B` to `W` is the line spanned by `x ∈ W`, and `B x e ≠ 0`, then `B`
is nondegenerate. -/
theorem IsRefl.nondegenerate_of_ker_restrict_eq_span_singleton {B : LinearMap.BilinForm R M}
    (hB : B.IsRefl) {W : Submodule R M} {x : W}
    (hW : LinearMap.ker (B.restrict W) = R ∙ x) {e : M} (hWe : W ⊔ R ∙ e = ⊤)
    (hxe : B x e ≠ 0) : B.Nondegenerate := by
  rw [Nondegenerate, LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB]
  intro v hv
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp (hWe ▸ Submodule.mem_top : v ∈ W ⊔ R ∙ e)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hx : x ∈ LinearMap.ker (B.restrict W) := hW ▸ Submodule.mem_span_singleton_self x
  have hxw : B x w = 0 := by simpa using LinearMap.congr_fun hx ⟨w, hw⟩
  have hc : c = 0 := by
    have h := hv x
    rw [map_add, LinearMap.add_apply, hB _ _ hxw, zero_add, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right fun hex ↦ hxe (hB _ _ hex)
  subst hc
  rw [zero_smul, add_zero] at hv ⊢
  have hwker : (⟨w, hw⟩ : W) ∈ LinearMap.ker (B.restrict W) :=
    LinearMap.ext fun w' ↦ by simpa using hv w'
  rw [hW] at hwker
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hwker
  have hw' : w = a • (x : M) := by simpa using congrArg Subtype.val ha.symm
  have h := hv e
  rw [hw', map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  rw [hw', (mul_eq_zero.mp h).resolve_right hxe, zero_smul]

end LinearMap.BilinForm

end
