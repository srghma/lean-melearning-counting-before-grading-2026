module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.RelevantLogic

/-!
# Curry–Howard with relevant implication: both directions, and where the converse fails

`RelevantLogic.lean` proves the soundness half of the link between natural reduction types
and relevant implication `R→`, over `ℕ`.  This file completes the picture.

* `NRT.PHas.toRPf` (in `RelevantLogic.lean`, **soundness, general grades**): for any
  semiring without zero divisors in which a sum vanishes only if its summands do, a
  positively graded typing of `t` gives a proof term of `R→` with λ-term `t` whose label is
  the support of `V`.
* `NRT.RPf.toPHas` (**completeness, idempotent grades**): when `1 + 1 = 1` (the qualitative
  algebras of Section 5, e.g. trust or binding time), the λ-term of every proof term of
  `R→` has a positively graded typing with all arrows graded `1` and neededness function
  the indicator of the label.
* `NRT.rpf_iff_positive`, `NRT.rel_iff_positive`: for such grades (with `1 ≠ 0`), relevant
  derivability is *exactly* positively graded typability, even term by term.
* `NRT.not_positive_relW2` (**the converse fails over `ℕ`**): the λ-term of the `R→` proof
  `λh a k. k (h (λx. x)) (h (λx. a x x))` has *no* positively `ℕ`-graded closed typing:
  the one hypothesis `h` would need an argument used once and an argument used twice.
  Counting is strictly finer than relevance.
-/

@[expose] public section

namespace NRT

open Classical

variable {B : Type} {R : Type} [Semiring R]

/-! ## Completeness for idempotent grades -/

/-- Read a formula as a natural reduction type with every arrow graded `1`. -/
def Fm.toTy (R : Type) [Semiring R] : Fm B → Ty B R
  | .atom β => .base β
  | .imp A B => .arr 1 (A.toTy R) (B.toTy R)

@[simp] theorem Fm.toTy_erase (A : Fm B) : (A.toTy R).erase = A := by
  induction A with
  | atom β => rfl
  | imp A B ihA ihB => simp [Fm.toTy, Ty.erase, ihA, ihB]

/-- The indicator of a label, as a neededness function. -/
noncomputable def ind {n : ℕ} (U : Fin n → Prop) : Fin n → R := fun x => if U x then 1 else 0

theorem toTy_cons {n : ℕ} (A : Fm B) (Γ : Fin n → Fm B) :
    (fun x => ((Fin.cons A Γ : Fin (n + 1) → Fm B) x).toTy R) =
      Fin.cons (A.toTy R) (fun x => (Γ x).toTy R) := by
  funext x; cases x using Fin.cases <;> simp

/-- **Curry–Howard, completeness, for idempotent grades.**  If `1 + 1 = 1` (and `1 ≠ 0`),
the λ-term of every proof term of `R→` from hypotheses `Γ` with label `U` has a positively
graded typing in the context `Γ` (all arrows graded `1`) whose neededness function is the
indicator of `U`. -/
theorem RPf.toPHas [Nontrivial R] (h11 : (1 : R) + 1 = 1) {n : ℕ} {Γ : Fin n → Fm B}
    {U : Fin n → Prop} {A : Fm B} (p : RPf Γ U A) :
    PHas (fun x => (Γ x).toTy R) (ind U) p.erase (A.toTy R) := by
  induction p with
  | hyp x => exact (PHas.var x).congr rfl (by funext y; simp [single, ind]) rfl
  | @impI n Γ U A' C p h0 ih =>
    exact (PHas.lam (ih.congr (toTy_cons A' _) rfl rfl) (by simp [ind, h0])).congr rfl
      (by funext y; simp [ind]) (by simp [ind, h0, Fm.toTy])
  | impE p q ihp ihq =>
    exact (PHas.app ihp one_ne_zero ihq).congr rfl
      (by funext y; simp only [ind, one_mul]; split_ifs <;> simp_all) rfl

/-- **Curry–Howard for idempotent grades, at the level of λ-terms.**  For a nontrivial
semiring with `1 + 1 = 1`, no zero divisors and no nontrivial zero sums (e.g. the trust or
binding-time algebras of Section 5), a λ-term `t` is (the erasure of) a proof of `A` from
`Γ` with label `U` in relevant implication iff `t` has a positively graded typing in
context `Γ` (arrows graded `1`) of type `A` whose support is `U`. -/
theorem rpf_iff_positive [Nontrivial R] [NoZeroDivisors R] (h11 : (1 : R) + 1 = 1)
    (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} (Γ : Fin n → Fm B) (U : Fin n → Prop)
    (A : Fm B) (t : Tm n) :
    (∃ p : RPf Γ U A, p.erase = t) ↔ ∃ V : Fin n → R,
      PHas (fun x => (Γ x).toTy R) V t (A.toTy R) ∧ ∀ x, V x ≠ 0 ↔ U x := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨ind U, p.toPHas h11, fun x => by by_cases hx : U x <;> simp [ind, hx]⟩
  · rintro ⟨V, h, hV⟩
    obtain ⟨p, hp⟩ := h.toRPf hzs
    exact ⟨p.cast (by funext x; simp) (by funext x; simp [hV]) (by simp), by simp [hp]⟩

/-- **Curry–Howard for idempotent grades.**  Under the same hypotheses, relevant
derivability of `A` from `Γ` with label `U` is exactly positively graded typability in
context `Γ` (arrows graded `1`) at type `A` with support `U`. -/
theorem rel_iff_positive [Nontrivial R] [NoZeroDivisors R] (h11 : (1 : R) + 1 = 1)
    (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} (Γ : Fin n → Fm B) (U : Fin n → Prop)
    (A : Fm B) :
    Rel Γ U A ↔ ∃ (V : Fin n → R) (t : Tm n),
      PHas (fun x => (Γ x).toTy R) V t (A.toTy R) ∧ ∀ x, V x ≠ 0 ↔ U x := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨V, hV⟩ := (rpf_iff_positive h11 hzs Γ U A p.erase).mp ⟨p, rfl⟩
    exact ⟨V, p.erase, hV⟩
  · rintro ⟨V, t, hV⟩
    obtain ⟨p, -⟩ := (rpf_iff_positive h11 hzs Γ U A t).mpr ⟨V, hV⟩
    exact ⟨p⟩

/-! ## The converse fails over `ℕ` -/

/-- The untyped λ-term `λh a k. k (h (λx. x)) (h (λx. a x x))`. -/
def Tm.relW2 : Tm 0 := [tm| λ h a k. k (h (λ x. x)) (h (λ x. a x x))]

/-- The formula `((A → A) → B) → (A → A → A) → (B → B → C) → C`, for the atoms
`A = atom a`, `B = atom b`, `C = atom c`. -/
def relW2Fm (a b c : B) : Fm B :=
  .imp (.imp (.imp (.atom a) (.atom a)) (.atom b))
    (.imp (.imp (.atom a) (.imp (.atom a) (.atom a)))
      (.imp (.imp (.atom b) (.imp (.atom b) (.atom c))) (.atom c)))

/-- The context of the body of `relW2`: `k : B → B → C`, `a : A → A → A`,
`h : (A → A) → B` (de Bruijn order). -/
def relW2Ctx (a b c : B) : Fin 3 → Fm B :=
  Fin.cons (.imp (.atom b) (.imp (.atom b) (.atom c)))
    (Fin.cons (.imp (.atom a) (.imp (.atom a) (.atom a)))
      (Fin.cons (.imp (.imp (.atom a) (.atom a)) (.atom b)) ![]))

/-- `λx. x`, in the body context. -/
def relW2I (a b c : B) : RPf (relW2Ctx a b c) (fun _ => False) (.imp (.atom a) (.atom a)) :=
  (RPf.impI (RPf.hyp (Γ := Fin.cons (.atom a) (relW2Ctx a b c)) 0) rfl).cast rfl
    (by funext x; simp [Fin.succ_ne_zero]) rfl

/-- `λx. a x x`, in the body context. -/
def relW2J (a b c : B) : RPf (relW2Ctx a b c) (· = 1) (.imp (.atom a) (.atom a)) :=
  (RPf.impI (RPf.impE (RPf.impE (RPf.hyp (Γ := Fin.cons (.atom a) (relW2Ctx a b c)) 2)
    (RPf.hyp 0)) (RPf.hyp 0)) (Or.inr rfl)).cast rfl
    (by funext x; fin_cases x <;> simp) rfl

/-- The body `k (h (λx. x)) (h (λx. a x x))`. -/
def relW2Body (a b c : B) : RPf (relW2Ctx a b c) (fun _ => True) (.atom c) :=
  (RPf.impE (RPf.impE (RPf.hyp 0) (RPf.impE (RPf.hyp 2) (relW2I a b c)))
    (RPf.impE (RPf.hyp 2) (relW2J a b c))).cast rfl
    (by funext x; fin_cases x <;> simp) rfl

/-- `λh a k. k (h (λx. x)) (h (λx. a x x))` as a proof term of `R→`: every hypothesis is
used, `h` twice. -/
def relW2 (a b c : B) : RPf ![] (fun _ => False) (relW2Fm a b c) :=
  (RPf.impI (Γ := ![]) (RPf.impI (RPf.impI (relW2Body a b c) trivial) trivial) trivial).cast
    (funext fun x => x.elim0) (funext fun x => x.elim0) rfl

@[simp] theorem relW2_erase (a b c : B) : (relW2 a b c).erase = Tm.relW2 := by
  simp [relW2, Tm.relW2, relW2Body, relW2I, relW2J]

theorem rtheorem_relW2Fm (a b c : B) : RTheorem (relW2Fm a b c) := ⟨relW2 a b c⟩

namespace PHas

/-- Inversion for variables. -/
theorem inv_var {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {x : Fin n} {τ : Ty B R}
    (h : PHas Γ V (.var x) τ) : V = single x ∧ τ = Γ x := by
  cases h; exact ⟨rfl, rfl⟩

/-- Inversion for abstractions. -/
theorem inv_lam {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {t : Tm (n + 1)} {ρ : Ty B R}
    (h : PHas Γ V (.lam t) ρ) :
    ∃ (σ τ : Ty B R) (W : Fin (n + 1) → R), PHas (Fin.cons σ Γ) W t τ ∧ W 0 ≠ 0 ∧
      V = (fun x => W x.succ) ∧ ρ = .arr (W 0) σ τ := by
  cases h with
  | lam h h0 => exact ⟨_, _, _, h, h0, rfl, rfl⟩

/-- Inversion for applications. -/
theorem inv_app {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {t u : Tm n} {τ : Ty B R}
    (h : PHas Γ V (.app t u) τ) :
    ∃ (σ : Ty B R) (b : R) (V₁ V₂ : Fin n → R), PHas Γ V₁ t (.arr b σ τ) ∧ b ≠ 0 ∧
      PHas Γ V₂ u σ ∧ V = (fun x => V₁ x + b * V₂ x) := by
  cases h with
  | app h₁ hb h₂ => exact ⟨_, _, _, _, h₁, hb, h₂, rfl⟩

end PHas

/-- **The converse of Curry–Howard fails over `ℕ`.**  The `R→` proof term
`λh a k. k (h (λx. x)) (h (λx. a x x))` (`Tm.relW2`, the λ-term of `relW2 a b c`) has no
positively `ℕ`-graded closed typing, of any type: `h` has a single graded type
`(σ →_c σ') →_b τ`, but its first argument `λx. x` forces `c = 1` while `λx. a x x` forces
`c ≥ 2`. -/
theorem not_positive_relW2 {τ : Ty B ℕ} : ¬ PHas ![] (0 : Fin 0 → ℕ) Tm.relW2 τ := by
  intro h
  rw [Tm.relW2] at h
  obtain ⟨_, _, _, h1, -, -, -⟩ := h.inv_lam
  obtain ⟨_, _, _, h2, -, -, -⟩ := h1.inv_lam
  obtain ⟨_, _, _, h3, -, -, -⟩ := h2.inv_lam
  obtain ⟨_, _, _, _, hk, -, hhJ, -⟩ := h3.inv_app
  obtain ⟨_, _, _, _, -, -, hhI, -⟩ := hk.inv_app
  -- `h I`
  obtain ⟨σI, bI, _, _, hh1, -, hI, -⟩ := hhI.inv_app
  obtain ⟨-, eh1⟩ := hh1.inv_var
  obtain ⟨_, _, WI, hIb, -, -, eI⟩ := hI.inv_lam
  obtain ⟨eWI, -⟩ := hIb.inv_var
  -- `h J`
  obtain ⟨σJ, bJ, _, _, hh2, -, hJ, -⟩ := hhJ.inv_app
  obtain ⟨-, eh2⟩ := hh2.inv_var
  obtain ⟨_, _, WJ, hJb, -, -, eJ⟩ := hJ.inv_lam
  obtain ⟨_, c₂, U₁, U₂, hax, hc₂, hx2, eWJ⟩ := hJb.inv_app
  obtain ⟨_, c₁, U₃, U₄, ha, hc₁, hx1, eU₁⟩ := hax.inv_app
  obtain ⟨eU₄, -⟩ := hx1.inv_var
  obtain ⟨eU₂, -⟩ := hx2.inv_var
  obtain ⟨eU₃, -⟩ := ha.inv_var
  -- the two arguments of `h` have the same type
  have hσ : σI = σJ := by
    have := eh1.trans eh2.symm
    simp only [Ty.arr.injEq] at this
    exact this.2.1
  rw [eI, eJ] at hσ
  simp only [Ty.arr.injEq] at hσ
  have e1 : WI 0 = 1 := by rw [eWI]; simp [single]
  have e2 : WJ 0 = c₁ + c₂ := by
    rw [eWJ, eU₁, eU₃, eU₄, eU₂]; simp [single]
  have := hσ.1
  rw [e1, e2] at this
  omega

end NRT
