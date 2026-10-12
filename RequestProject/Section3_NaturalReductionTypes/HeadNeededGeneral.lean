module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes

/-!
# Soundness of grade `0` for head neededness, for general grades

`NRT.GTm.head_needed_sound` is stated for `ℕ`.  The argument only uses that `1 ≠ 0` and
that a sum vanishes only if its first summand does, so it holds for every such semiring of
grades — in particular for the qualitative algebras of Section 5 (see
`QualitativeRelevance.lean`).
-/

@[expose] public section

namespace NRT

namespace GTm

variable {R : Type} [Semiring R] [Nontrivial R]

theorem spine_needed_gen (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} {Γ : Fin n → Ty R}
    {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) {x : Fin n} (hs : Spine x d.erase) :
    V x ≠ 0 := by
  induction d with
  | var y => cases hs; simp [single]
  | lam d ih => cases hs
  | app d e ihd ihe =>
    cases hs with
    | app _ hs => exact fun h0 => ihd hs (hzs _ _ h0)

/-- The head variable of a typed head normal form has a nonzero grade. -/
theorem head_needed_gen (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} {Γ : Fin n → Ty R}
    {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) {x : Fin n} (hh : HeadIs x d.erase) :
    V x ≠ 0 := by
  induction d with
  | var y => cases hh with | spine hs => exact spine_needed_gen hzs _ hs
  | lam d ih =>
    cases hh with
    | spine hs => cases hs
    | lam hh => exact ih hh
  | app d e ihd ihe => cases hh with | spine hs => exact spine_needed_gen hzs (.app d e) hs

/-- **Soundness of grade `0` w.r.t. head neededness, for general grades.**  In a nontrivial
semiring where `a + b = 0` implies `a = 0`, if a typed term gives `x` grade `0` then no
β-reduct of it is a head normal form with head variable `x`. -/
theorem head_needed_sound_gen (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ}
    {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) {x : Fin n} (hx : V x = 0)
    {t' : Tm n} (hred : Relation.ReflTransGen Step d.erase t') : ¬ HeadIs x t' := by
  intro hh
  obtain ⟨d', rfl⟩ := d.subject_reduction hred
  exact d'.head_needed_gen hzs hh hx

end GTm

end NRT
