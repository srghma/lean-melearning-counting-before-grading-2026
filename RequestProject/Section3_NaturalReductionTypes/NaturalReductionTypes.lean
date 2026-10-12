module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.Syntax

/-!
# Natural reduction types (Section 3 of *Counting before Grading*)

This file formalises the quantitative core of the note: a type system whose arrows
`σ →_b τ` carry a grade `b`, and whose judgements `Γ ⊢_V M : τ` carry a *variable
neededness function* `V` assigning a grade to each variable.  The application rule is
the semiring action of the paper:

  `App : Γ ⊢_{V₁} N₁ : σ →_b τ,  Γ ⊢_{V₂} N₂ : σ  ⟹  Γ ⊢_V N₁ N₂ : τ`,
  with `V(x) = V₁(x) + b * V₂(x)`.

The system is parametric in a semiring `R` of grades; the 1993 system is `R = ℕ`
("a polynomial algebra over the natural numbers").

Everything is well scoped by construction: a term with `n` free variables has type
`Tm n` (see `Syntax.lean`), and its context and neededness function are `Fin n → Ty R`
and `Fin n → R`, so they give a type and a grade to exactly the variables in scope.
Closed terms are `Tm 0`, typed in the empty context `![]` with the (unique) neededness
function `0`.

Main results:
* `NRT.Has.subst`: the graded substitution lemma — usage becomes `Σₓ V(x) · W(x)`.
* `NRT.subject_reduction` / `NRT.subject_reduction_star`: β-reduction (anywhere in a term)
  preserves both the type and the *exact* neededness function — proved once, generically
  over the semiring.
* `NRT.head_needed_sound`: for `ℕ`-grades, a variable of grade `0` is never the head
  variable of any reduct of the term (soundness of grade `0` w.r.t. head neededness).
* `NRT.kxx_typing`: `λx. K x x : σ →₁ σ` — the argument is *used* once, although it
  *occurs* twice (`NRT.kxx_occurrences`): the "occurrences vs uses" example.
* `NRT.twice_typing`, `NRT.compose_typing`: the counting derivations, producing a
  product of use counts for the bound variable.
-/

@[expose] public section

namespace NRT

/-- Natural reduction types over a grade algebra `R`: base types and graded arrows
`arr b σ τ`, written `σ →_b τ` in the paper. -/
inductive Ty (R : Type) : Type
  | base : ℕ → Ty R
  | arr : R → Ty R → Ty R → Ty R

/-- Number of occurrences of the variable `x` in a term. -/
def occ : {n : ℕ} → Fin n → Tm n → ℕ
  | _, x, .var y => if y = x then 1 else 0
  | _, x, .lam t => occ x.succ t
  | _, x, .app t u => occ x t + occ x u

/-- `Spine x t`: `t` is `x N₁ … Nₖ`. -/
inductive Spine : {n : ℕ} → Fin n → Tm n → Prop
  | var {n : ℕ} (x : Fin n) : Spine x (.var x)
  | app {n : ℕ} {x : Fin n} {t : Tm n} (u : Tm n) : Spine x t → Spine x (.app t u)

/-- `HeadIs x t`: `t` is a head normal form `λy₁…yₘ. x N₁ … Nₖ` whose head variable is
the free variable `x`. -/
inductive HeadIs : {n : ℕ} → Fin n → Tm n → Prop
  | spine {n : ℕ} {x : Fin n} {t : Tm n} : Spine x t → HeadIs x t
  | lam {n : ℕ} {x : Fin n} {t : Tm (n + 1)} : HeadIs x.succ t → HeadIs x (.lam t)

/-! ## The typing judgement -/

variable {R : Type} [Semiring R]

/-- The neededness function of a single use of the variable `x`. -/
def single {n : ℕ} (x : Fin n) : Fin n → R := fun y => if y = x then 1 else 0

/-- Push a neededness function forward along a renaming: the grade of `y` is the sum of
the grades of all variables renamed to `y`. -/
def rmap {n m : ℕ} (ρ : Fin n → Fin m) (V : Fin n → R) : Fin m → R :=
  fun y => ∑ x, if ρ x = y then V x else 0

/-- The typing judgement `Γ ⊢_V t : τ` of natural reduction types, for a term `t` with
`n` free variables, a context `Γ : Fin n → Ty R` and a neededness function
`V : Fin n → R`. -/
inductive Has : {n : ℕ} → (Fin n → Ty R) → (Fin n → R) → Tm n → Ty R → Prop
  | var {n : ℕ} {Γ : Fin n → Ty R} (x : Fin n) : Has Γ (single x) (.var x) (Γ x)
  | lam {n : ℕ} {Γ : Fin n → Ty R} {σ τ : Ty R} {V : Fin (n + 1) → R} {t : Tm (n + 1)} :
      Has (Fin.cons σ Γ) V t τ → Has Γ (fun x => V x.succ) (.lam t) (.arr (V 0) σ τ)
  | app {n : ℕ} {Γ : Fin n → Ty R} {σ τ : Ty R} {b : R} {V₁ V₂ : Fin n → R} {t u : Tm n} :
      Has Γ V₁ t (.arr b σ τ) → Has Γ V₂ u σ →
      Has Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ

namespace Has

variable {n : ℕ} {Γ : Fin n → Ty R}

theorem congr {V V' : Fin n → R} {t : Tm n} {τ τ' : Ty R}
    (h : Has Γ V t τ) (hV : V = V') (hτ : τ = τ') : Has Γ V' t τ' := by
  subst hV hτ; exact h

theorem var' {V : Fin n → R} {τ : Ty R} (x : Fin n)
    (hV : V = single x) (hτ : τ = Γ x) : Has Γ V (.var x) τ :=
  (Has.var x).congr hV.symm hτ.symm

theorem lam' {σ τ : Ty R} {V : Fin (n + 1) → R} {W : Fin n → R} {b : R} {t : Tm (n + 1)}
    (h : Has (Fin.cons σ Γ) V t τ) (hb : b = V 0) (hW : W = fun x => V x.succ) :
    Has Γ W (.lam t) (.arr b σ τ) :=
  (Has.lam h).congr hW.symm (by rw [hb])

theorem app' {σ τ : Ty R} {b : R} {V V₁ V₂ : Fin n → R} {t u : Tm n}
    (h₁ : Has Γ V₁ t (.arr b σ τ)) (h₂ : Has Γ V₂ u σ)
    (hV : V = fun x => V₁ x + b * V₂ x) : Has Γ V (.app t u) τ :=
  (Has.app h₁ h₂).congr hV.symm rfl

end Has

/-! ## Renaming (weakening, exchange and contraction) -/

theorem rmap_single {n m : ℕ} (ρ : Fin n → Fin m) (x : Fin n) :
    rmap ρ (single x : Fin n → R) = single (ρ x) := by
  funext y
  simp only [rmap, single]
  rw [Finset.sum_eq_single x]
  · simp [eq_comm]
  · intro b _ hb; simp [hb]
  · simp

/-- **Renaming lemma.** Typing is stable under any renaming `ρ` of the free variables
(compatible with the contexts); the neededness of a new variable `y` is the total
neededness of the old variables renamed to `y`.  This covers weakening (new variables get
grade `0`), exchange, and contraction (grades are added). -/
theorem Has.rename {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {t : Tm n} {τ : Ty R}
    (h : Has Γ V t τ) :
    ∀ {m : ℕ} (ρ : Fin n → Fin m) (Δ : Fin m → Ty R), (∀ x, Δ (ρ x) = Γ x) →
      Has Δ (rmap ρ V) (NRT.rename ρ t) τ := by
  induction h with
  | var x =>
    intro m ρ Δ hΔ
    exact Has.var' (ρ x) (rmap_single ρ x) (hΔ x).symm
  | @lam n Γ σ τ V t _ ih =>
    intro m ρ Δ hΔ
    have := ih (liftR ρ) (Fin.cons σ Δ) (fun x => by
      cases x using Fin.cases <;> simp [hΔ])
    refine Has.lam' this ?_ ?_
    · simp [rmap, Fin.sum_univ_succ, Fin.succ_ne_zero]
    · funext y; simp [rmap, Fin.sum_univ_succ, (Fin.succ_ne_zero y).symm]
  | @app n Γ σ τ b V₁ V₂ t u _ _ ih₁ ih₂ =>
    intro m ρ Δ hΔ
    refine Has.app' (ih₁ ρ Δ hΔ) (ih₂ ρ Δ hΔ) ?_
    funext y
    simp only [rmap, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp

/-- **Weakening** by a fresh variable `0` of grade `0`. -/
theorem Has.weaken {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {t : Tm n} {τ : Ty R}
    (h : Has Γ V t τ) (σ : Ty R) :
    Has (Fin.cons σ Γ) (Fin.cons 0 V) (NRT.rename Fin.succ t) τ := by
  refine (h.rename Fin.succ (Fin.cons σ Γ) (fun x => by simp)).congr ?_ rfl
  funext y
  cases y using Fin.cases with
  | zero => simp [rmap, (Fin.succ_ne_zero _)]
  | succ y => simp [rmap]

/-! ## Substitution -/

/-- **Graded substitution lemma.** Substituting, for every variable `x`, a term `s x` used
according to `W x`, the usage of the result is `y ↦ Σₓ V(x) · W(x)(y)`. -/
theorem Has.subst {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {t : Tm n} {τ : Ty R}
    (h : Has Γ V t τ) :
    ∀ {m : ℕ} (Δ : Fin m → Ty R) (s : Fin n → Tm m) (W : Fin n → Fin m → R),
      (∀ x, Has Δ (W x) (s x) (Γ x)) →
      Has Δ (fun y => ∑ x, V x * W x y) (NRT.subst s t) τ := by
  induction h with
  | var x =>
    intro m Δ s W hs
    refine (hs x).congr ?_ rfl
    funext y; simp [single]
  | @lam n Γ σ τ V t _ ih =>
    intro m Δ s W hs
    have := ih (Fin.cons σ Δ) (liftS s)
      (Fin.cons (single 0) (fun x => Fin.cons 0 (W x))) (fun x => by
        cases x using Fin.cases with
        | zero => exact Has.var' 0 (by simp) (by simp)
        | succ x => simpa using (hs x).weaken σ)
    refine Has.lam' this ?_ ?_
    · simp [Fin.sum_univ_succ, single]
    · funext y; simp [Fin.sum_univ_succ, single, Fin.succ_ne_zero]
  | @app n Γ σ τ b V₁ V₂ t u _ _ ih₁ ih₂ =>
    intro m Δ s W hs
    refine Has.app' (ih₁ Δ s W hs) (ih₂ Δ s W hs) ?_
    funext y
    simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Typing of a β-contractum `t[u]`. -/
theorem Has.inst {n : ℕ} {Γ : Fin n → Ty R} {σ τ : Ty R} {V : Fin (n + 1) → R}
    {V₂ : Fin n → R} {t : Tm (n + 1)} {u : Tm n}
    (h₁ : Has (Fin.cons σ Γ) V t τ) (h₂ : Has Γ V₂ u σ) :
    Has Γ (fun y => V y.succ + V 0 * V₂ y) (NRT.inst t u) τ := by
  refine (h₁.subst Γ (Fin.cons u Tm.var) (Fin.cons V₂ single) (fun x => by
    cases x using Fin.cases with
    | zero => simpa using h₂
    | succ x => simpa using Has.var x)).congr ?_ rfl
  funext y
  simp [Fin.sum_univ_succ, single, add_comm]

/-! ## Subject reduction -/

/-- **Subject reduction.** A β-step anywhere in a term preserves its type *and* its exact
neededness function. Generic over the grade semiring. -/
theorem subject_reduction {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {t t' : Tm n}
    {τ : Ty R} (h : Has Γ V t τ) (hs : Step t t') : Has Γ V t' τ := by
  induction hs generalizing τ with
  | beta t u =>
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | lam h₁ => exact h₁.inst h₂
  | lam _ ih =>
    cases h with
    | lam h => exact Has.lam (ih h)
  | appL u _ ih =>
    cases h with
    | app h₁ h₂ => exact Has.app (ih h₁) h₂
  | appR t _ ih =>
    cases h with
    | app h₁ h₂ => exact Has.app h₁ (ih h₂)

/-- Subject reduction for many-step β-reduction. -/
theorem subject_reduction_star {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {t t' : Tm n}
    {τ : Ty R} (h : Has Γ V t τ) (hs : Relation.ReflTransGen Step t t') : Has Γ V t' τ := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => exact subject_reduction ih hst

/-! ## Soundness of grade `0` with respect to head neededness (grades in `ℕ`) -/

theorem spine_needed {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty ℕ}
    {x : Fin n} (hs : Spine x t) (h : Has Γ V t τ) : 1 ≤ V x := by
  induction hs generalizing V τ with
  | var =>
    cases h with
    | var => simp [single]
  | app u _ ih =>
    cases h with
    | app h₁ _ => exact le_trans (ih h₁) (Nat.le_add_right _ _)

/-- The head variable of a typed head normal form always has grade `≥ 1`. -/
theorem head_needed {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty ℕ}
    {x : Fin n} (hh : HeadIs x t) (h : Has Γ V t τ) : 1 ≤ V x := by
  induction hh generalizing τ with
  | spine hs => exact spine_needed hs h
  | lam _ ih =>
    cases h with
    | lam h => exact ih h

/-- **Soundness of grade `0` w.r.t. head neededness.** If a typing of `t` assigns the
free variable `x` grade `0`, then no β-reduct of `t` is a head normal form with head
variable `x`: the variable is not head-needed. -/
theorem head_needed_sound {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {t t' : Tm n}
    {τ : Ty ℕ} {x : Fin n}
    (h : Has Γ V t τ) (hx : V x = 0) (hred : Relation.ReflTransGen Step t t') :
    ¬ HeadIs x t' := by
  intro hh
  have := head_needed hh (subject_reduction_star h hred)
  omega

/-! ## Closed terms -/

/-- Embed a closed term into any scope. -/
def Tm.embed {n : ℕ} (t : Tm 0) : Tm n := NRT.rename Fin.elim0 t

/-- A closed typing (empty context, no usage) can be used in any context, with no usage
of the context's variables. -/
theorem Has.embed {t : Tm 0} {τ : Ty R} (h : Has ![] 0 t τ) {n : ℕ} (Γ : Fin n → Ty R) :
    Has Γ 0 t.embed τ := by
  refine (h.rename Fin.elim0 Γ (fun x => x.elim0)).congr ?_ rfl
  funext y; simp [rmap]

/-! ## Worked derivations -/

/-- The closed combinator `K = λa b. a`. -/
def K : Tm 0 := .lam (.lam (.var 1))

/-- The body `K x x` of `λx. K x x`, in the scope of the bound variable `x`. -/
def kxxBody : Tm 1 := .app (.app K.embed (.var 0)) (.var 0)

/-- `λx. K x x`: the bound variable occurs twice. -/
def kxx : Tm 0 := .lam kxxBody

/-- `Twice = λf x. f (f x)`. -/
def twice : Tm 0 := .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))

/-- `Compose = λg f x. g (f x)`. -/
def compose : Tm 0 := .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))

/-- `K : σ →₁ τ →₀ σ`, as a closed term. -/
theorem K_typing (σ τ : Ty R) : Has ![] 0 K (.arr 1 σ (.arr 0 τ σ)) := by
  refine Has.lam' (Has.lam' (Has.var' 1 rfl (by simp)) ?_ rfl) ?_ ?_
  · simp [single]
  · simp [single]
  · funext n; exact n.elim0

/-- **Occurrences vs uses.** `λx. K x x : σ →₁ σ`: the argument is used exactly once. -/
theorem kxx_typing (σ : Ty R) : Has ![] 0 kxx (.arr 1 σ σ) := by
  refine Has.lam' (Has.app (Has.app ((K_typing σ σ).embed _) (Has.var' 0 rfl (by simp)))
    (Has.var' 0 rfl (by simp))) ?_ ?_
  · simp [single]
  · funext n; exact n.elim0

/-- …although the argument occurs twice in the body of `λx. K x x`. -/
theorem kxx_occurrences : occ 0 kxxBody = 2 := by decide

/-- **Counting.** `Twice : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`: the bound variable `x` receives
the product of the use counts of the two applications of `f`. -/
theorem twice_typing (σ : Ty R) (i : R) :
    Has ![] 0 twice (.arr (1 + i) (.arr i σ σ) (.arr (i * i) σ σ)) := by
  refine Has.lam' (Has.lam' (Has.app (Has.var' (τ := .arr i σ σ) 1 rfl (by simp))
    (Has.app (Has.var' (τ := .arr i σ σ) 1 rfl (by simp))
      (Has.var' (τ := σ) 0 rfl (by simp)))) ?_ rfl) ?_ ?_
  · simp [single]
  · simp [single]
  · funext n; exact n.elim0

/-- **Counting, with distinct grades.** `Compose : (σ₂ →ᵢ σ₃) →₁ (σ₁ →ⱼ σ₂) →ᵢ σ₁ →_{i·j} σ₃`:
the bound variable `x` receives the product `i * j` of the use counts. -/
theorem compose_typing (σ₁ σ₂ σ₃ : Ty R) (i j : R) :
    Has ![] 0 compose
      (.arr 1 (.arr i σ₂ σ₃) (.arr i (.arr j σ₁ σ₂) (.arr (i * j) σ₁ σ₃))) := by
  refine Has.lam' (Has.lam' (Has.lam' (Has.app (Has.var' (τ := .arr i σ₂ σ₃) 2 rfl rfl)
    (Has.app (Has.var' (τ := .arr j σ₁ σ₂) 1 rfl (by simp))
      (Has.var' (τ := σ₁) 0 rfl (by simp)))) ?_ rfl) ?_ rfl) ?_ ?_
  · simp [single]
  · simp [single]
  · simp [single]
  · funext n; exact n.elim0

/-- In `ℕ`, `Twice` at `i = 2` gives `x` grade `4`: grades genuinely count. -/
example (σ : Ty ℕ) : Has ![] 0 twice (.arr 3 (.arr 2 σ σ) (.arr 4 σ σ)) :=
  twice_typing σ 2

end NRT
