module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes

/-!
# Soundness of grade `0` for head neededness, for general grades

`NRT.Has.head_needed_sound` is stated for `ℕ`.  The argument only uses that `1 ≠ 0` and
that a sum vanishes only if its first summand does, so it holds for every such semiring of
grades — in particular for the qualitative algebras of Section 5 (see
`QualitativeRelevance.lean`).
-/

@[expose] public section

namespace NRT

namespace Has

variable {B : Type} {R : Type} [Semiring R] [Nontrivial R]

theorem spine_needed_gen (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} {Γ : Fin n → Ty B R}
    {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) {x : Fin n} (hs : Spine x t) :
    V x ≠ 0 := by
  induction hs generalizing V τ with
  | var => obtain ⟨rfl, -⟩ := h.inv_var; simp [single]
  | app u _ ih =>
    obtain ⟨σ, b, V₁, V₂, h₁, h₂, rfl⟩ := h.inv_app
    exact fun h0 => ih h₁ (hzs _ _ h0)

/-- The head variable of a typed head normal form has a nonzero grade. -/
theorem head_needed_gen (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} {Γ : Fin n → Ty B R}
    {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) {x : Fin n} (hh : HeadIs x t) :
    V x ≠ 0 := by
  induction hh generalizing τ with
  | spine hs => exact h.spine_needed_gen hzs hs
  | lam _ ih =>
    obtain ⟨σ, τ', W, hb, rfl, rfl⟩ := h.inv_lam
    exact ih hb

/-- **Soundness of grade `0` w.r.t. head neededness, for general grades.**  In a nontrivial
semiring where `a + b = 0` implies `a = 0`, if `Γ ⊢_V t : τ` gives `x` grade `0` then no
β-reduct of `t` is a head normal form with head variable `x`. -/
theorem head_needed_sound_gen (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ}
    {Γ : Fin n → Ty B R} {V : Fin n → R} {t t' : Tm n} {τ : Ty B R} (h : Has Γ V t τ)
    {x : Fin n} (hx : V x = 0) (hred : Relation.ReflTransGen Step t t') : ¬ HeadIs x t' :=
  fun hh => (h.subject_reduction_star hred).head_needed_gen hzs hh hx

end Has

end NRT
