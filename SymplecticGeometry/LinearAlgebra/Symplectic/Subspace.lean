/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.LinearAlgebra.BilinearForm.Isotropic
public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
public import TauCeti.LinearAlgebra.Dimension.Basis
import SymplecticGeometry.LinearAlgebra.BilinearForm.Nondegenerate
import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic

/-!
# Symplectic complements and Lagrangian extension

For a symplectic form `ω` on a real vector space `V` (Tau Ceti's `TauCeti.SymplecticForm`) and a
subspace `W`, this file adds to Tau Ceti's theory of the symplectic complement `W^ω`:

* `TauCeti.SymplecticForm.isLagrangian_iff_orthogonal_eq` and
  `TauCeti.SymplecticForm.IsLagrangian.orthogonal_eq`: `W` is Lagrangian exactly when
  `W^ω = W`, the equation that defines it but that Tau Ceti states in no lemma;
* `TauCeti.SymplecticForm.isCoisotropic_orthogonal_iff`: `W^ω` is coisotropic exactly when `W`
  is isotropic, in any dimension;
* `TauCeti.SymplecticForm.IsCoisotropic.isIsotropic_orthogonal`: the complement of a coisotropic
  subspace is isotropic, in any dimension; in finite dimension,
  `TauCeti.SymplecticForm.isIsotropic_orthogonal_iff` and
  `TauCeti.SymplecticForm.isLagrangian_orthogonal_iff` complete the duality: `W^ω` is isotropic
  exactly when `W` is coisotropic, and Lagrangian exactly when `W` is;
* `TauCeti.SymplecticForm.IsCoisotropic.finiteDimensional`: a space with a finite-dimensional
  coisotropic subspace is finite-dimensional;
* `TauCeti.SymplecticForm.IsIsotropic.exists_le_isLagrangian`: each isotropic `W` has a
  Lagrangian `L ⊇ W`, in any dimension: the case of a symplectic form of Tau Ceti's
  `LinearMap.BilinForm.IsAlt.exists_le_eq_orthogonal`;
* `TauCeti.SymplecticForm.IsLagrangian.exists_isDarbouxBasis_apply_zero_eq`: a basis
  `u₁, …, uₙ` of a Lagrangian subspace is the first half of a Darboux basis
  `u₁, …, uₙ, v₁, …, vₙ`, with `ω(uᵢ, vⱼ) = δᵢⱼ`, with no finiteness assumption on `V`;
* `TauCeti.SymplecticForm.isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq`: in finite
  dimension, a subspace is Lagrangian exactly when it is isotropic of half the dimension;
* `TauCeti.SymplecticForm.isLagrangian_map_iff_of_apply_eq_mul`: a linear equivalence
  `e : V ≃ W` with `ω'(e v, e w) = c · ω(v, w)` for some constant `c ≠ 0` maps the Lagrangian
  subspaces of `ω` onto those of `ω'` (for `c = -1`: an anti-symplectic map);
* `TauCeti.SymplecticForm.orthogonal_sup`: `(L ⊔ L')^ω = L^ω ⊓ L'^ω`;
* `TauCeti.SymplecticForm.isIsotropic_inf_orthogonal`: the radical `W ∩ W^ω` of a subspace is
  isotropic;
* `TauCeti.SymplecticForm.isSymplectic_left_of_isCompl`,
  `TauCeti.SymplecticForm.isSymplectic_right_of_isCompl` and
  `TauCeti.SymplecticForm.orthogonal_eq_of_isCompl`: if `V = H ⊕ L` with `H` and `L` orthogonal
  for `ω`, then both summands are symplectic and `L = H^ω`, in any dimension; the first two
  apply the library's `LinearMap.BilinForm.IsRefl.nondegenerate_iff_of_isCompl` to `ω`;
* `TauCeti.SymplecticForm.IsLagrangian.finrank_inf_add_finrank`: in finite dimension, for a
  Lagrangian `L` and any subspace `W`, `2 dim (L ∩ W) + dim V = 2 dim (L ∩ W^ω) + 2 dim W`.

It then collects these with Tau Ceti's results into two theorems:
`TauCeti.SymplecticForm.orthogonal_properties`, in finite dimension (dimension of the
complement, double complement, symplectic and isotropic subspaces versus their complements, and
Lagrangian subspaces as the isotropic ones of half dimension) and
`TauCeti.SymplecticForm.isLagrangian_properties`, in any dimension (Lagrangian extension,
Lagrangian as maximal isotropic, extension of finite bases of Lagrangian subspaces to Darboux
bases).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.1.1 and Lemma 2.1.5, and §5.4 (Remark 5.4.6 and Proposition 5.4.7) for
  `TauCeti.SymplecticForm.IsLagrangian.finrank_inf_add_finrank`.
-/

public section

namespace TauCeti.SymplecticForm

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {L : Submodule ℝ V}

/-- A subspace is Lagrangian exactly when it equals its own symplectic complement,
`L^ω = L`. -/
theorem isLagrangian_iff_orthogonal_eq : ω.IsLagrangian L ↔ ω.orthogonal L = L := by
  rw [isLagrangian_iff, isIsotropic_iff_le, isCoisotropic_iff_le]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- A Lagrangian subspace is its own symplectic complement, `L^ω = L`. -/
theorem IsLagrangian.orthogonal_eq (h : ω.IsLagrangian L) : ω.orthogonal L = L :=
  isLagrangian_iff_orthogonal_eq.1 h

/-- The symplectic complement of a subspace is coisotropic if and only if the subspace is
isotropic, in any dimension. -/
@[simp]
theorem isCoisotropic_orthogonal_iff :
    ω.IsCoisotropic (ω.orthogonal L) ↔ ω.IsIsotropic L := by
  rw [isIsotropic_iff_le, isCoisotropic_iff_le]
  exact ⟨le_orthogonal_orthogonal.trans, orthogonal_le⟩

/-- The symplectic complement of an isotropic subspace is coisotropic. -/
theorem IsIsotropic.isCoisotropic_orthogonal (h : ω.IsIsotropic L) :
    ω.IsCoisotropic (ω.orthogonal L) :=
  isCoisotropic_orthogonal_iff.2 h

/-- The symplectic complement of a coisotropic subspace is isotropic, in any dimension. -/
theorem IsCoisotropic.isIsotropic_orthogonal (h : ω.IsCoisotropic L) :
    ω.IsIsotropic (ω.orthogonal L) :=
  isIsotropic_iff_le.2 (orthogonal_le (isCoisotropic_iff_le.1 h))

/-- A symplectic vector space with a finite-dimensional coisotropic subspace is
finite-dimensional. -/
theorem IsCoisotropic.finiteDimensional [FiniteDimensional ℝ L] (h : ω.IsCoisotropic L) :
    FiniteDimensional ℝ V := by
  -- The map `v ↦ ω(v, ·)|_L` into the dual of `L` has kernel `L^ω`, which lies in `L` and so
  -- is finite-dimensional; its range lies in the finite-dimensional dual of `L`.
  let φ : V →ₗ[ℝ] Dual ℝ L := (LinearMap.lcomp ℝ ℝ L.subtype).comp ω.toBilinForm
  have hker : LinearMap.ker φ = ω.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, mem_orthogonal_iff']
    exact ⟨fun hv y hy => LinearMap.congr_fun hv ⟨y, hy⟩,
      fun hv => LinearMap.ext fun y => hv y y.property⟩
  have : FiniteDimensional ℝ (ω.orthogonal L) :=
    Submodule.finiteDimensional_of_le (isCoisotropic_iff_le.1 h)
  have : FiniteDimensional ℝ (V ⧸ ω.orthogonal L) :=
    .equiv ((Submodule.quotEquivOfEq _ _ hker).symm.trans φ.quotKerEquivRange).symm
  exact Module.Finite.of_submodule_quotient (ω.orthogonal L)

/-- **Lagrangian extension.** Every isotropic subspace of a symplectic vector space lies in a
Lagrangian subspace. No finiteness of the dimension is needed. -/
theorem IsIsotropic.exists_le_isLagrangian (h : ω.IsIsotropic L) :
    ∃ L', L ≤ L' ∧ ω.IsLagrangian L' := by
  obtain ⟨L', hle, hL'⟩ := ω.isAlt.exists_le_eq_orthogonal (isIsotropic_iff_le.1 h)
  exact ⟨L', hle, isLagrangian_iff_orthogonal_eq.2 hL'.symm⟩

/-- A basis `u₁, …, uₙ` of a Lagrangian subspace of a symplectic vector space extends to a Darboux
basis `u₁, …, uₙ, v₁, …, vₙ`, that is, one with `ω(uᵢ, uⱼ) = 0`, `ω(vᵢ, vⱼ) = 0` and
`ω(uᵢ, vⱼ) = δᵢⱼ`, where `uᵢ = b (i, 0)` and `vᵢ = b (i, 1)`. The space need not be assumed
finite-dimensional: a finite basis of a Lagrangian subspace makes it so. -/
theorem IsLagrangian.exists_isDarbouxBasis_apply_zero_eq (h : ω.IsLagrangian L) {n : ℕ}
    (e : Basis (Fin n) ℝ L) :
    ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ ∀ i, b (i, 0) = e i := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis e
  have : FiniteDimensional ℝ V := h.isCoisotropic.finiteDimensional
  obtain ⟨d, hd, hde⟩ :=
    ω.isAlt.exists_basis_toMatrix_eq_J_inl_eq ω.nondegenerate e h.orthogonal_eq.symm
  have hJ (x y : Fin n ⊕ Fin n) : ω (d x) (d y) = Matrix.J (Fin n) ℝ x y := by
    rw [← hd, LinearMap.BilinForm.toMatrix_apply]
  let v : Fin n × Fin 2 → V := fun p => if p.2 = 0 then d (.inl p.1) else -d (.inr p.1)
  have hdim : finrank ℝ V = n * 2 := by
    rw [finrank_eq_two_mul_card_of_basis_sum d, Fintype.card_fin, mul_comm]
  obtain ⟨b, hb, hbv⟩ := exists_isDarbouxBasis_coe_eq (ω := ω) hdim (v := v)
    (fun i j => by simp [v, hJ])
    (fun i j => by simp [v, hJ])
    (fun i j => by simp [v, hJ, Matrix.one_apply])
  exact ⟨b, hb, fun i => by simp [hbv, v, hde]⟩

/-- **Lagrangian extension lemma.** For any symplectic form `ω` on `V`, of any dimension,
each isotropic subspace has a Lagrangian subspace containing it; a subspace is Lagrangian iff
it is isotropic and no strictly larger subspace is; and for any finite basis `e` of a
Lagrangian subspace there is a Darboux basis `b` of `V` (so `ω(b (i, 0), b (j, 1)) = δᵢⱼ`) whose
`q`-half is `e`, that is, `b (i, 0) = e i`.

Milestone: *Lagrangian extension lemma*. -/
theorem isLagrangian_properties (ω : SymplecticForm V) :
    (∀ W : Submodule ℝ V, ω.IsIsotropic W → ∃ L, W ≤ L ∧ ω.IsLagrangian L) ∧
      (∀ L : Submodule ℝ V, ω.IsLagrangian L ↔ Maximal ω.IsIsotropic L) ∧
      ∀ L : Submodule ℝ V, ω.IsLagrangian L → ∀ {n : ℕ} (e : Basis (Fin n) ℝ L),
        ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ ∀ i, b (i, 0) = e i :=
  ⟨fun _ h => h.exists_le_isLagrangian, fun _ => isLagrangian_iff_maximal_isIsotropic,
    fun _ h _ e => h.exists_isDarbouxBasis_apply_zero_eq e⟩

/-- A linear equivalence `e : V ≃ W` that scales the symplectic forms by a nonzero constant,
`ω'(e v, e w) = c · ω(v, w)`, maps the Lagrangian subspaces of `ω` exactly onto those of `ω'`.
The case `c = 1` is invariance under symplectomorphisms, and `c = -1` covers anti-symplectic
maps. -/
theorem isLagrangian_map_iff_of_apply_eq_mul {W : Type*} [AddCommGroup W] [Module ℝ W]
    {ω' : SymplecticForm W} (e : V ≃ₗ[ℝ] W) {c : ℝ} (hc : c ≠ 0)
    (he : ∀ v w, ω' (e v) (e w) = c * ω v w) :
    ω'.IsLagrangian (L.map (e : V →ₗ[ℝ] W)) ↔ ω.IsLagrangian L := by
  have h : IsSymplectomorphism (ω.rescale c hc) ω' e := isSymplectomorphism_iff.2 fun v w ↦ by
    rw [rescale_apply, he]
  rw [h.isLagrangian_map_iff, isLagrangian_rescale_iff]

/-- The symplectic complement of a sum is the intersection of the symplectic complements. -/
theorem orthogonal_sup (ω : SymplecticForm V) (L L' : Submodule ℝ V) :
    ω.orthogonal (L ⊔ L') = ω.orthogonal L ⊓ ω.orthogonal L' :=
  Submodule.orthogonalBilin_sup (B := ω.toBilinForm) L L'

/-- The radical `W ∩ W^ω` of a subspace is isotropic. -/
theorem isIsotropic_inf_orthogonal (W : Submodule ℝ V) :
    ω.IsIsotropic (W ⊓ ω.orthogonal W) :=
  isIsotropic_iff.2 fun _ hv _ hw => mem_orthogonal_iff.1 hw.2 _ hv.1

section IsCompl

variable {H : Submodule ℝ V}

/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, then `H` is a symplectic subspace. -/
theorem isSymplectic_left_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) : ω.IsSymplectic H :=
  isSymplectic_iff_nondegenerate_restrict.2
    ((ω.isRefl.nondegenerate_iff_of_isCompl hc hHL).1 ω.nondegenerate).1

/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, then `L` is a symplectic subspace. -/
theorem isSymplectic_right_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) : ω.IsSymplectic L :=
  isSymplectic_iff_nondegenerate_restrict.2
    ((ω.isRefl.nondegenerate_iff_of_isCompl hc hHL).1 ω.nondegenerate).2

/-- If `V = H ⊕ L` and `ω h l = 0` for all `h ∈ H` and `l ∈ L`, then `L` is the symplectic
complement of `H`. -/
theorem orthogonal_eq_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) : ω.orthogonal H = L :=
  (eq_of_le_of_inf_le_of_le_sup (fun l hl ↦ mem_orthogonal_iff.2 fun h hh ↦ hHL h hh l hl)
    (by rw [inf_comm, (isSymplectic_iff_disjoint.1 (ω.isSymplectic_left_of_isCompl hc hHL)).eq_bot]
        exact bot_le)
    (by rw [hc.symm.sup_eq_top]; exact le_top)).symm

end IsCompl

variable [FiniteDimensional ℝ V]

/-- In finite dimension, the symplectic complement of a subspace is isotropic if and only if the
subspace is coisotropic. -/
@[simp]
theorem isIsotropic_orthogonal_iff :
    ω.IsIsotropic (ω.orthogonal L) ↔ ω.IsCoisotropic L := by
  rw [← isCoisotropic_orthogonal_iff, orthogonal_orthogonal]

/-- In finite dimension, the symplectic complement of a subspace is Lagrangian if and only if the
subspace is. -/
@[simp]
theorem isLagrangian_orthogonal_iff :
    ω.IsLagrangian (ω.orthogonal L) ↔ ω.IsLagrangian L := by
  rw [isLagrangian_iff, isLagrangian_iff, isIsotropic_orthogonal_iff,
    isCoisotropic_orthogonal_iff, and_comm]

/-- The Lagrangian subspaces of a finite-dimensional symplectic vector space `(V, ω)` are the
isotropic subspaces `L` with `2 · dim L = dim V`. -/
theorem isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq :
    ω.IsLagrangian L ↔ ω.IsIsotropic L ∧ 2 * finrank ℝ L = finrank ℝ V :=
  ⟨fun h => ⟨h.isIsotropic, h.two_mul_finrank⟩, fun h => h.1.isLagrangian_of_finrank h.2⟩

/-- For a Lagrangian subspace `L` and any subspace `W` of a finite-dimensional symplectic vector
space `V`, `2 dim (L ∩ W) + dim V = 2 dim (L ∩ W^ω) + 2 dim W`. -/
theorem IsLagrangian.finrank_inf_add_finrank (hL : ω.IsLagrangian L) (W : Submodule ℝ V) :
    2 * finrank ℝ ↥(L ⊓ W) + finrank ℝ V =
      2 * finrank ℝ ↥(L ⊓ ω.orthogonal W) + 2 * finrank ℝ W := by
  have h₁ := ω.finrank_add_finrank_orthogonal (L ⊔ W)
  rw [orthogonal_sup, hL.orthogonal_eq] at h₁
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq L W
  have h₃ := hL.two_mul_finrank
  omega

/-- **Symplectic complements.** For a subspace `W` of a finite-dimensional symplectic vector
space `(V, ω)`: `dim W + dim W^ω = dim V`; `W^ωω = W`; `W` and `W^ω` are symplectic together;
`W` is isotropic exactly when `W^ω` is coisotropic; and `W` is Lagrangian exactly when it is
isotropic with `2 · dim W = dim V`.

Milestone: *Symplectic complements*. -/
theorem orthogonal_properties (ω : SymplecticForm V) (W : Submodule ℝ V) :
    finrank ℝ W + finrank ℝ (ω.orthogonal W) = finrank ℝ V ∧
      ω.orthogonal (ω.orthogonal W) = W ∧
      (ω.IsSymplectic W ↔ ω.IsSymplectic (ω.orthogonal W)) ∧
      (ω.IsIsotropic W ↔ ω.IsCoisotropic (ω.orthogonal W)) ∧
      (ω.IsLagrangian W ↔ ω.IsIsotropic W ∧ 2 * finrank ℝ W = finrank ℝ V) :=
  ⟨ω.finrank_add_finrank_orthogonal W, ω.orthogonal_orthogonal W,
    isSymplectic_orthogonal_iff.symm, isCoisotropic_orthogonal_iff.symm,
    isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq⟩

end TauCeti.SymplecticForm

end
