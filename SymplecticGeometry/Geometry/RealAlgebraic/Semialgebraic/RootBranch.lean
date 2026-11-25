/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Algebra.MvPolynomial.Polynomial
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.OneVariable
public import SymplecticGeometry.RingTheory.Polynomial.Irreducible
public import SymplecticGeometry.RingTheory.UniqueFactorizationDomain
public import TauCeti.Geometry.RealAlgebraic.Nash.OfSemialgebraic
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# A one-variable semialgebraic function is a root branch near a point

Let `f` be a real function of one variable, semialgebraic on a set containing the points
`![t]`, `t > a` close to `a`, and not identically zero on any interval `(a, a + ε)`. Then, to the
right of `a`, `f` is continuous and `f t` is a root of `P (t, ·)` for one polynomial
`P : ℝ[X][X]` (the outer variable is the value, the inner one is `t`) with nonzero discriminant
and nonzero constant coefficient. This is the input that the growth of a continuous root branch
of a polynomial takes.

* `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_setOf_eval_map_eq_zero`: the points of the
  domain of a semialgebraic function `f` at which `Q (x, f x) = 0`, for a polynomial `Q` in the
  value with polynomial coefficients, form a semialgebraic set.
* `TauCeti.IsSemialgebraicOn.exists_polynomial_eventually_isRoot_nhdsGT`: the main result, near
  `a` from the right.
* `TauCeti.IsSemialgebraicOn.exists_pos_polynomial_forall_Ioo_isRoot`: its form on an interval
  `(0, ε)`.

The proof: Tau Ceti's `TauCeti.IsSemialgebraicOn.exists_ne_zero_polynomial_relation` gives a
nonzero polynomial relation `P (x, f x) = 0`. Each point is a root of one of the irreducible
factors of `P` (`UniqueFactorizationMonoid.map_eq_zero_iff_exists_mem_factors`); the points where
a given factor vanishes form a semialgebraic set, so one of these sets contains all points just
right of `a` (`TauCeti.IsSemialgebraic.eventually_nhdsGT_mem_or_notMem`). That factor `Q` is not
associated to the value variable, since `f` does not vanish identically, so its constant
coefficient is nonzero (`Polynomial.associated_X_iff_coeff_zero_eq_zero`). Being irreducible, it
is squarefree, so its discriminant is nonzero (Tau Ceti's `Squarefree.discr_ne_zero`).

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.5–2.6.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 3.
-/

public section

open Filter Set Topology

namespace TauCeti

open MvPolynomial in
/-- For a function `f` that is semialgebraic on `s` and a polynomial `Q` in one variable with
coefficients polynomials in the coordinates, the points `x ∈ s` with `Q (x, f x) = 0` form a
semialgebraic set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_eval_map_eq_zero {σ R : Type*} [Finite σ]
    [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R] {f : (σ → R) → R}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s)
    (Q : Polynomial (MvPolynomial σ R)) :
    IsSemialgebraic (s ∩ {x | (Q.map (eval x)).eval (f x) = 0}) := by
  have hF : IsSemialgebraicOn (fun x ↦ Sum.elim x fun _ : Unit ↦ f x) s := by
    have hid : IsSemialgebraicOn (fun x i ↦ eval x (X i : MvPolynomial σ R)) s :=
      isSemialgebraicOn_eval X hf.isSemialgebraic
    simp only [eval_X] at hid
    exact hid.sumElim hf
  set q : MvPolynomial (σ ⊕ Unit) R := Q.eval₂ (rename Sum.inl).toRingHom (X (Sum.inr ()))
  convert (hF.eval_comp fun _ : Unit ↦ q).isSemialgebraic_inter_setOf_eq_const 0 using 2
  ext x
  simp [q, funext_iff]

open _root_.Polynomial in
/-- A real function `f` of one variable that is semialgebraic on a set containing the points
`![t]`, `t > a` close to `a`, and that does not vanish identically on any interval `(a, a + ε)`,
is, to the right of `a`, a continuous root branch of one polynomial `P : ℝ[X][X]`: the outer
variable of `P` is the value and the inner one is `t`, and `P` has nonzero discriminant and
nonzero constant coefficient. -/
theorem IsSemialgebraicOn.exists_polynomial_eventually_isRoot_nhdsGT {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) {a : ℝ}
    (hs : ∀ᶠ t in 𝓝[>] a, ![t] ∈ s) (hne : ∃ᶠ t in 𝓝[>] a, f ![t] ≠ 0) :
    ∃ P : ℝ[X][X], P.discr ≠ 0 ∧ P.coeff 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝[>] a, ContinuousAt (fun t ↦ f ![t]) t ∧
        (P.map (evalRingHom t)).IsRoot (f ![t]) := by
  classical
  -- The polynomial relation of `f`, with coefficients moved from `MvPolynomial (Fin 1) ℝ`
  -- to `ℝ[X]`.
  obtain ⟨P₀, hP₀, hrel⟩ := hf.exists_ne_zero_polynomial_relation
  set e : MvPolynomial (Fin 1) ℝ ≃+* ℝ[X] :=
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv
  have hmap (Q : ℝ[X][X]) (x : Fin 1 → ℝ) :
      (Q.map e.symm.toRingHom).map (MvPolynomial.eval x) = Q.map (evalRingHom (x 0)) := by
    rw [Polynomial.map_map]
    congr 1
    ext <;> simp [e]
  set P := P₀.map e.toRingHom
  have hP : P ≠ 0 := (Polynomial.map_ne_zero_iff e.injective).2 hP₀
  have hPP : P.map e.symm.toRingHom = P₀ := by
    rw [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id]
  have hPrel (x : Fin 1 → ℝ) (hx : x ∈ s) : (P.map (evalRingHom (x 0))).eval (f x) = 0 := by
    rw [← hmap, hPP]
    exact hrel x hx
  have hev (Q : ℝ[X][X]) (t y : ℝ) :
      eval₂RingHom (evalRingHom t) y Q = (Q.map (evalRingHom t)).eval y :=
    (eval_map _ _).symm
  -- One irreducible factor `Q` of `P` vanishes along the graph at all points just right of `a`.
  set S : ℝ[X][X] → Set (Fin 1 → ℝ) :=
    fun Q ↦ s ∩ {x | ((Q.map e.symm.toRingHom).map (MvPolynomial.eval x)).eval (f x) = 0}
  have hex :
      ∃ Q ∈ UniqueFactorizationMonoid.factors P, ∀ᶠ t in 𝓝[>] a, ![t] ∈ S Q := by
    by_contra h
    have h' : ∀ Q ∈ (UniqueFactorizationMonoid.factors P).toFinset,
        ∀ᶠ t in 𝓝[>] a, ![t] ∉ S Q := fun Q hQ ↦
      ((hf.isSemialgebraic_inter_setOf_eval_map_eq_zero _).eventually_nhdsGT_mem_or_notMem
        a).resolve_left fun hQ' ↦ h ⟨Q, Multiset.mem_toFinset.1 hQ, hQ'⟩
    obtain ⟨t, ht, hts⟩ := ((eventually_all_finset _).2 h').and hs |>.exists
    -- The point `![t]` is a root of an irreducible factor of `P`.
    obtain ⟨Q, hQ, hQ0⟩ := (UniqueFactorizationMonoid.map_eq_zero_iff_exists_mem_factors
      (eval₂RingHom (evalRingHom (![t] 0)) (f ![t])) hP).1 (by rw [hev]; exact hPrel _ hts)
    refine ht Q (Multiset.mem_toFinset.2 hQ) ⟨hts, ?_⟩
    rwa [mem_ofPred_eq, hmap, ← hev]
  obtain ⟨Q, hQP, hQev⟩ := hex
  have hQ := UniqueFactorizationMonoid.irreducible_of_factor Q hQP
  have hroot : ∀ᶠ t in 𝓝[>] a, (Q.map (evalRingHom t)).eval (f ![t]) = 0 :=
    hQev.mono fun t ht ↦ by
      have h := ht.2
      rwa [mem_ofPred_eq, hmap, Matrix.cons_val_zero] at h
  -- `Q` is not associated to the value variable, since `f` does not vanish identically.
  have hc0 : Q.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := (associated_X_iff_coeff_zero_eq_zero hQ).2 h0
    refine hne (hroot.mono fun t ht ↦ ?_)
    have hut : ((u : ℝ[X][X]).map (evalRingHom t)).eval (f ![t]) ≠ 0 := by
      rw [← hev]
      exact (u.isUnit.map _).ne_zero
    rw [← hu] at ht
    simpa [hut] using ht
  have hcont : ∀ᶠ t in 𝓝[>] a, ContinuousAt (fun t ↦ f ![t]) t :=
    (hf.eventually_continuousAt_nhdsGT hs).mono fun t ht ↦
      ContinuousAt.comp (g := f) (f := fun t : ℝ ↦ ![t]) (continuousAt_pi.1 ht ()) (by fun_prop)
  exact ⟨Q, hQ.squarefree.discr_ne_zero, hc0, hcont.and hroot⟩

open _root_.Polynomial in
/-- A real function `f` of one variable that is semialgebraic on a set containing the points
`![t]`, `0 < t < ε₀`, and that does not vanish identically on any interval `(0, ε)`, is, on some
interval `(0, ε)`, a continuous root branch of one polynomial `P : ℝ[X][X]`: the outer variable
of `P` is the value and the inner one is `t`, and `P` has nonzero discriminant and nonzero
constant coefficient. -/
theorem IsSemialgebraicOn.exists_pos_polynomial_forall_Ioo_isRoot {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hs : ∀ t ∈ Ioo 0 ε₀, ![t] ∈ s)
    (hne : ∀ ε > 0, ∃ t ∈ Ioo 0 ε, f ![t] ≠ 0) :
    ∃ ε > 0, ∃ P : ℝ[X][X], P.discr ≠ 0 ∧ P.coeff 0 ≠ 0 ∧
      ContinuousOn (fun t ↦ f ![t]) (Ioo 0 ε) ∧
      ∀ t ∈ Ioo 0 ε, (P.map (evalRingHom t)).IsRoot (f ![t]) := by
  obtain ⟨P, hdisc, hc0, hev⟩ := hf.exists_polynomial_eventually_isRoot_nhdsGT
    (eventually_of_mem (Ioo_mem_nhdsGT hε₀) hs) ((nhdsGT_basis 0).frequently_iff.2 hne)
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  exact ⟨ε, hε, P, hdisc, hc0, fun t ht ↦ (hsub ht).1.continuousWithinAt,
    fun t ht ↦ (hsub ht).2⟩

end TauCeti

end
