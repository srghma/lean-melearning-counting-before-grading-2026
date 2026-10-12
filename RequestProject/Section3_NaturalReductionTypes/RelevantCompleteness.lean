module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.RelevantLogic

/-!
# Curry–Howard with relevant implication: both directions, and where the converse fails

`RelevantLogic.lean` proves the soundness half of the link between natural reduction types
and relevant implication `R→`, over `ℕ`.  This file completes the picture.

* `NRT.GTm.PositiveR` is positivity over an arbitrary semiring of grades (every arrow
  introduced or eliminated has a nonzero grade); over `ℕ` it is `NRT.GTm.Positive`
  (`NRT.GTm.positiveR_iff_positive`).
* `NRT.GTm.toRPfR` (**soundness, general grades**): for any semiring without zero divisors
  in which a sum vanishes only if its summands do, a positively graded typed term erases to
  a proof term of `R→` with the same λ-term whose label is the support of `V`.
* `NRT.RPf.toGTm` (**completeness, idempotent grades**): when `1 + 1 = 1` (the qualitative
  algebras of Section 5, e.g. trust or binding time), every proof term of `R→` is the
  erasure of a positively graded typed term with the *same* λ-term, all arrows graded `1`,
  and neededness function the indicator of the label.
* `NRT.rel_iff_positive` : for such grades (with `1 ≠ 0`), relevant derivability is
  *exactly* positive graded typability.
* `NRT.not_positive_relW2` (**the converse fails over `ℕ`**): the `R→` proof term
  `λh a k. k (h (λx. x)) (h (λx. a x x))` is not the erasure of *any* positively
  `ℕ`-graded closed typed term: the one hypothesis `h` would need an argument used once
  and an argument used twice.  Counting is strictly finer than relevance.
-/

@[expose] public section

namespace NRT

open Classical

variable {R : Type}

/-! ## Erasure of contexts -/

theorem erase_consR {n : ℕ} (σ : Ty R) (Γ : Fin n → Ty R) :
    (fun x => ((Fin.cons σ Γ : Fin (n + 1) → Ty R) x).erase) =
      Fin.cons σ.erase (fun x => (Γ x).erase) := by
  funext x; cases x using Fin.cases <;> simp

variable [Semiring R]

/-! ## Positivity over an arbitrary semiring -/

/-- A typed term is *positively graded* if every arrow it introduces or eliminates carries a
nonzero grade. -/
def GTm.PositiveR {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} : GTm Γ V τ → Prop
  | .var _ => True
  | @GTm.lam _ _ _ _ _ _ V d => V 0 ≠ 0 ∧ d.PositiveR
  | @GTm.app _ _ _ _ _ _ b _ _ d e => b ≠ 0 ∧ d.PositiveR ∧ e.PositiveR

@[simp] theorem GTm.positiveR_cast {n : ℕ} {Γ : Fin n → Ty R} {V V' : Fin n → R}
    {τ τ' : Ty R} (hV : V = V') (hτ : τ = τ') (d : GTm Γ V τ) :
    (d.cast hV hτ).PositiveR ↔ d.PositiveR := by
  subst hV hτ; rfl

/-- Over `ℕ`, `PositiveR` is the positivity of `RelevantLogic.lean`. -/
theorem GTm.positiveR_iff_positive {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {τ : Ty ℕ}
    (d : GTm Γ V τ) : d.PositiveR ↔ d.Positive := by
  induction d with
  | var x => simp [GTm.PositiveR, GTm.Positive]
  | lam d ih => simp [GTm.PositiveR, GTm.Positive, ih]
  | app d e ihd ihe => simp [GTm.PositiveR, GTm.Positive, ihd, ihe]

/-- **Curry–Howard, soundness, for general grades.**  If sums vanish only when their
summands do and there are no zero divisors, a positively graded typed term gives a proof
term of `R→` whose label is the support of its neededness function. -/
def GTm.toRPfR [Nontrivial R] [NoZeroDivisors R] (hzs : ∀ a b : R, a + b = 0 → a = 0)
    {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} :
    (d : GTm Γ V τ) → d.PositiveR →
      RPf (fun x => (Γ x).erase) (fun x => V x ≠ 0) τ.erase
  | .var x, _ => (RPf.hyp x).cast rfl (by funext y; simp [single]) rfl
  | @GTm.lam _ _ _ _ σ _ _ d, h =>
      RPf.impI ((d.toRPfR hzs h.2).cast (erase_consR σ _) rfl rfl) h.1
  | .app d e, h => (RPf.impE (d.toRPfR hzs h.2.1) (e.toRPfR hzs h.2.2)).cast rfl
      (by
        funext x
        apply propext
        have hb := h.1
        constructor
        · rintro (h1 | h2) h0
          · exact h1 (hzs _ _ h0)
          · simp only at h0
            rw [add_comm] at h0
            exact h2 ((mul_eq_zero.mp (hzs _ _ h0)).resolve_left hb)
        · intro h0
          by_contra hc
          push_neg at hc
          exact h0 (by simp only; rw [hc.1, hc.2]; simp)) rfl

@[simp] theorem GTm.toRPfR_erase [Nontrivial R] [NoZeroDivisors R] (hzs : ∀ a b : R, a + b = 0 → a = 0)
    {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R}
    (d : GTm Γ V τ) (h : d.PositiveR) : (d.toRPfR hzs h).erase = d.erase := by
  induction d with
  | var x => simp [GTm.toRPfR]
  | lam d ih => simp [GTm.toRPfR, ih]
  | app d e ihd ihe => simp [GTm.toRPfR, ihd, ihe]

/-! ## Completeness for idempotent grades -/

/-- Read a formula as a natural reduction type with every arrow graded `1`. -/
def Fm.toTy (R : Type) [Semiring R] : Fm → Ty R
  | .atom n => .base n
  | .imp A B => .arr 1 (A.toTy R) (B.toTy R)

@[simp] theorem Fm.toTy_erase (A : Fm) : (A.toTy R).erase = A := by
  induction A with
  | atom n => rfl
  | imp A B ihA ihB => simp [Fm.toTy, Ty.erase, ihA, ihB]

/-- The indicator of a label, as a neededness function. -/
noncomputable def ind {n : ℕ} (U : Fin n → Prop) : Fin n → R := fun x => if U x then 1 else 0

/-- Transport a typed term along an equality of contexts. -/
def GTm.ctxCast {n : ℕ} {Γ Γ' : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} (h : Γ = Γ')
    (d : GTm Γ V τ) : GTm Γ' V τ := h ▸ d

@[simp] theorem GTm.erase_ctxCast {n : ℕ} {Γ Γ' : Fin n → Ty R} {V : Fin n → R} {τ : Ty R}
    (h : Γ = Γ') (d : GTm Γ V τ) : (d.ctxCast h).erase = d.erase := by
  subst h; rfl

@[simp] theorem GTm.positiveR_ctxCast {n : ℕ} {Γ Γ' : Fin n → Ty R} {V : Fin n → R}
    {τ : Ty R} (h : Γ = Γ') (d : GTm Γ V τ) : (d.ctxCast h).PositiveR ↔ d.PositiveR := by
  subst h; rfl

theorem toTy_cons {n : ℕ} (A : Fm) (Γ : Fin n → Fm) :
    (fun x => ((Fin.cons A Γ : Fin (n + 1) → Fm) x).toTy R) =
      Fin.cons (A.toTy R) (fun x => (Γ x).toTy R) := by
  funext x; cases x using Fin.cases <;> simp

/-- **Curry–Howard, completeness, for idempotent grades.**  If `1 + 1 = 1`, every proof
term of `R→` from hypotheses `Γ` with label `U` is a typed term in the context `Γ` (all
arrows graded `1`) whose neededness function is the indicator of `U`. -/
noncomputable def RPf.toGTm (h11 : (1 : R) + 1 = 1) {n : ℕ} {Γ : Fin n → Fm}
    {U : Fin n → Prop} {A : Fm} :
    RPf Γ U A → GTm (fun x => (Γ x).toTy R) (ind U) (A.toTy R)
  | .hyp x => (GTm.var x).cast (by funext y; simp [single, ind]) rfl
  | @RPf.impI _ _ _ A' _ p h0 =>
      (GTm.lam ((p.toGTm h11).ctxCast (toTy_cons A' _))).cast
        (by funext y; simp [ind]) (by simp [ind, h0, Fm.toTy])
  | .impE p q => (GTm.app (p.toGTm h11) (q.toGTm h11)).cast
      (by funext y; simp only [ind, one_mul]; split_ifs <;> simp_all) rfl

/-- The typed term of a proof term has the same λ-term. -/
@[simp] theorem RPf.toGTm_erase (h11 : (1 : R) + 1 = 1) {n : ℕ} {Γ : Fin n → Fm}
    {U : Fin n → Prop} {A : Fm} (p : RPf Γ U A) : (p.toGTm (R := R) h11).erase = p.erase := by
  induction p with
  | hyp x => simp [RPf.toGTm]
  | impI p h0 ih => simp [RPf.toGTm, ih]
  | impE p q ihp ihq => simp [RPf.toGTm, ihp, ihq]

/-- The typed term of a proof term is positively graded (when `1 ≠ 0`). -/
theorem RPf.toGTm_positive (h11 : (1 : R) + 1 = 1) (h10 : (1 : R) ≠ 0) {n : ℕ}
    {Γ : Fin n → Fm} {U : Fin n → Prop} {A : Fm} (p : RPf Γ U A) :
    (p.toGTm (R := R) h11).PositiveR := by
  induction p with
  | hyp x => simp [RPf.toGTm, GTm.PositiveR]
  | impI p h0 ih => simp [RPf.toGTm, GTm.PositiveR, ih, ind, h0, h10]
  | impE p q ihp ihq => simp [RPf.toGTm, GTm.PositiveR, ihp, ihq, h10]

/-- **Curry–Howard for idempotent grades.**  For a nontrivial semiring with `1 + 1 = 1`,
no zero divisors and no nontrivial zero sums (e.g. the trust or binding-time algebras of
Section 5), relevant derivability of `A` from `Γ` with label `U` is exactly the existence
of a positively graded typed term in context `Γ` (arrows graded `1`) of type `A` whose
support is `U`. -/
theorem rel_iff_positive [Nontrivial R] [NoZeroDivisors R] (h11 : (1 : R) + 1 = 1)
    (hzs : ∀ a b : R, a + b = 0 → a = 0) {n : ℕ} (Γ : Fin n → Fm) (U : Fin n → Prop)
    (A : Fm) :
    Rel Γ U A ↔ ∃ (V : Fin n → R) (d : GTm (fun x => (Γ x).toTy R) V (A.toTy R)),
      d.PositiveR ∧ ∀ x, V x ≠ 0 ↔ U x := by
  constructor
  · rintro ⟨p⟩
    exact ⟨ind U, p.toGTm h11, p.toGTm_positive h11 one_ne_zero, fun x => by
      by_cases hx : U x <;> simp [ind, hx]⟩
  · rintro ⟨V, d, hd, hV⟩
    refine ⟨(d.toRPfR hzs hd).cast (by funext x; simp) (by funext x; simp [hV]) (by simp)⟩

/-! ## The converse fails over `ℕ` -/

/-- The untyped λ-term `λh a k. k (h (λx. x)) (h (λx. a x x))`. -/
def Tm.relW2 : Tm 0 :=
  .lam (.lam (.lam (.app (.app (.var 0) (.app (.var 2) (.lam (.var 0))))
    (.app (.var 2) (.lam (.app (.app (.var 2) (.var 0)) (.var 0)))))))

/-- The formula `((A → A) → B) → (A → A → A) → (B → B → C) → C`. -/
def relW2Fm : Fm :=
  .imp (.imp (.imp (.atom 0) (.atom 0)) (.atom 1))
    (.imp (.imp (.atom 0) (.imp (.atom 0) (.atom 0)))
      (.imp (.imp (.atom 1) (.imp (.atom 1) (.atom 2))) (.atom 2)))

/-- The context of the body of `relW2`: `k : B → B → C`, `a : A → A → A`,
`h : (A → A) → B` (de Bruijn order). -/
def relW2Ctx : Fin 3 → Fm :=
  Fin.cons (.imp (.atom 1) (.imp (.atom 1) (.atom 2)))
    (Fin.cons (.imp (.atom 0) (.imp (.atom 0) (.atom 0)))
      (Fin.cons (.imp (.imp (.atom 0) (.atom 0)) (.atom 1)) ![]))

/-- `λx. x`, in the body context. -/
def relW2I : RPf relW2Ctx (fun _ => False) (.imp (.atom 0) (.atom 0)) :=
  (RPf.impI (RPf.hyp (Γ := Fin.cons (.atom 0) relW2Ctx) 0) rfl).cast rfl
    (by funext x; simp [Fin.succ_ne_zero]) rfl

/-- `λx. a x x`, in the body context. -/
def relW2J : RPf relW2Ctx (· = 1) (.imp (.atom 0) (.atom 0)) :=
  (RPf.impI (RPf.impE (RPf.impE (RPf.hyp (Γ := Fin.cons (.atom 0) relW2Ctx) 2)
    (RPf.hyp 0)) (RPf.hyp 0)) (Or.inr rfl)).cast rfl
    (by funext x; fin_cases x <;> simp) rfl

/-- The body `k (h (λx. x)) (h (λx. a x x))`. -/
def relW2Body : RPf relW2Ctx (fun _ => True) (.atom 2) :=
  (RPf.impE (RPf.impE (RPf.hyp 0) (RPf.impE (RPf.hyp 2) relW2I))
    (RPf.impE (RPf.hyp 2) relW2J)).cast rfl
    (by funext x; fin_cases x <;> simp) rfl

/-- `λh a k. k (h (λx. x)) (h (λx. a x x))` as a proof term of `R→`: every hypothesis is
used, `h` twice. -/
def relW2 : RPf ![] (fun _ => False) relW2Fm :=
  (RPf.impI (Γ := ![]) (RPf.impI (RPf.impI relW2Body trivial) trivial) trivial).cast
    (funext fun x => x.elim0) (funext fun x => x.elim0) rfl

@[simp] theorem relW2_erase : relW2.erase = Tm.relW2 := by
  simp [relW2, Tm.relW2, relW2Body, relW2I, relW2J]

theorem rtheorem_relW2Fm : RTheorem relW2Fm := ⟨relW2⟩

/-- Inversion for variables. -/
theorem GTm.inv_var {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ)
    {x : Fin n} (h : d.erase = .var x) : τ = Γ x ∧ V = single x := by
  cases d with
  | var y => simp at h; subst h; exact ⟨rfl, rfl⟩
  | lam _ => simp at h
  | app _ _ => simp at h

/-- Inversion for abstractions. -/
theorem GTm.inv_lam {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ)
    {t : Tm (n + 1)} (h : d.erase = .lam t) :
    ∃ (σ ρ : Ty R) (W : Fin (n + 1) → R) (d' : GTm (Fin.cons σ Γ) W ρ),
      τ = .arr (W 0) σ ρ ∧ V = (fun x => W x.succ) ∧ d'.erase = t ∧
      (d.PositiveR → W 0 ≠ 0 ∧ d'.PositiveR) := by
  cases d with
  | var y => simp at h
  | lam d' => simp at h; exact ⟨_, _, _, d', rfl, rfl, h, fun hp => by unfold GTm.PositiveR at hp; exact hp⟩
  | app _ _ => simp at h

/-- Inversion for applications. -/
theorem GTm.inv_app {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ)
    {t u : Tm n} (h : d.erase = .app t u) :
    ∃ (σ : Ty R) (b : R) (V₁ V₂ : Fin n → R) (d₁ : GTm Γ V₁ (.arr b σ τ)) (d₂ : GTm Γ V₂ σ),
      V = (fun x => V₁ x + b * V₂ x) ∧ d₁.erase = t ∧ d₂.erase = u ∧
      (d.PositiveR → b ≠ 0 ∧ d₁.PositiveR ∧ d₂.PositiveR) := by
  cases d with
  | var y => simp at h
  | lam _ => simp at h
  | app d₁ d₂ => simp at h; exact ⟨_, _, _, _, d₁, d₂, rfl, h.1, h.2, fun hp => by unfold GTm.PositiveR at hp; exact hp⟩

/-- **The converse of Curry–Howard fails over `ℕ`.**  The `R→` proof term
`λh a k. k (h (λx. x)) (h (λx. a x x))` (`relW2`) is not the erasure of any positively
`ℕ`-graded closed typed term, of any type: `h` has a single graded type `(σ →_c σ') →_b τ`,
but its first argument `λx. x` forces `c = 1` while `λx. a x x` forces `c ≥ 2`. -/
theorem not_positive_relW2 {τ : Ty ℕ} (d : GTm ![] 0 τ) (hd : d.erase = relW2.erase) :
    ¬ d.Positive := by
  rw [← GTm.positiveR_iff_positive]
  intro hp
  rw [relW2_erase, Tm.relW2] at hd
  obtain ⟨_, _, _, d1, -, -, h1, hp1⟩ := d.inv_lam hd
  obtain ⟨_, _, _, d2, -, -, h2, hp2⟩ := d1.inv_lam h1
  obtain ⟨_, _, _, d3, -, -, h3, hp3⟩ := d2.inv_lam h2
  obtain ⟨_, _, _, _, dk, dhJ, -, hk, hhJ, hpk⟩ := d3.inv_app h3
  obtain ⟨_, _, _, _, dk', dhI, -, hk', hhI, hpk'⟩ := dk.inv_app hk
  -- `h I`
  obtain ⟨σI, bI, _, _, dh1, dI, -, hh1, hI, hpI⟩ := dhI.inv_app hhI
  obtain ⟨eh1, -⟩ := dh1.inv_var hh1
  obtain ⟨_, _, WI, dIb, eI, -, hIb, -⟩ := dI.inv_lam hI
  obtain ⟨eIb, eWI⟩ := dIb.inv_var hIb
  -- `h J`
  obtain ⟨σJ, bJ, _, _, dh2, dJ, -, hh2, hJ, hpJ⟩ := dhJ.inv_app hhJ
  obtain ⟨eh2, -⟩ := dh2.inv_var hh2
  obtain ⟨_, _, WJ, dJb, eJ, -, hJb, hpJb⟩ := dJ.inv_lam hJ
  obtain ⟨_, c₂, U₁, U₂, dax, dx2, eWJ, hax, hx2, hpax⟩ := dJb.inv_app hJb
  obtain ⟨_, c₁, U₃, U₄, da, dx1, eU₁, ha, hx1, hpa⟩ := dax.inv_app hax
  obtain ⟨-, eU₄⟩ := dx1.inv_var hx1
  obtain ⟨-, eU₂⟩ := dx2.inv_var hx2
  obtain ⟨-, eU₃⟩ := da.inv_var ha
  have p3 := (hp3 (hp2 (hp1 hp).2).2).2
  have pk := hpk p3
  have pJ := hpJ pk.2.2
  have pJb := (hpJb pJ.2.2).2
  have pax := hpax pJb
  have pa := hpa pax.2.1
  -- the two arguments of `h` have the same type
  have hσ : σI = σJ := by
    have := eh1.trans eh2.symm
    simp only [Ty.arr.injEq] at this
    exact this.2.1
  rw [eI, eJ] at hσ
  simp only [Ty.arr.injEq] at hσ
  have h1 : WI 0 = 1 := by rw [eWI]; simp [single]
  have h2 : WJ 0 = c₁ + c₂ := by
    rw [eWJ, eU₁, eU₃, eU₄, eU₂]; simp [single]
  have := hσ.1
  rw [h1, h2] at this
  have := pa.1
  have := pax.1
  omega

end NRT
