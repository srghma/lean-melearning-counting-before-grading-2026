module

public import Mathlib

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

Terms are untyped λ-terms in de Bruijn notation; contexts are total maps `ℕ → Ty R`
(every variable has a type), and neededness functions are maps `ℕ → R`.

Main results:
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

/-! ## Syntax -/

/-- Untyped λ-terms, de Bruijn indices. -/
inductive Tm : Type
  | var : ℕ → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm
  deriving DecidableEq

/-- Natural reduction types over a grade algebra `R`: base types and graded arrows
`arr b σ τ`, written `σ →_b τ` in the paper. -/
inductive Ty (R : Type) : Type
  | base : ℕ → Ty R
  | arr : R → Ty R → Ty R → Ty R

/-- Shift free variables `≥ c` up by one. -/
def shift (c : ℕ) : Tm → Tm
  | .var n => if n < c then .var n else .var (n + 1)
  | .lam t => .lam (shift (c + 1) t)
  | .app t u => .app (shift c t) (shift c u)

/-- `subst k u t` replaces variable `k` in `t` by `u` and lowers the variables above `k`. -/
def subst (k : ℕ) (u : Tm) : Tm → Tm
  | .var n => if n < k then .var n else if n = k then u else .var (n - 1)
  | .lam t => .lam (subst (k + 1) (shift 0 u) t)
  | .app t t' => .app (subst k u t) (subst k u t')

/-- Full β-reduction (one step, anywhere in the term). -/
inductive Step : Tm → Tm → Prop
  | beta (t u : Tm) : Step (.app (.lam t) u) (subst 0 u t)
  | lam {t t' : Tm} : Step t t' → Step (.lam t) (.lam t')
  | appL {t t' : Tm} (u : Tm) : Step t t' → Step (.app t u) (.app t' u)
  | appR (t : Tm) {u u' : Tm} : Step u u' → Step (.app t u) (.app t u')

/-- Number of occurrences of variable `x` in a term. -/
def occ : ℕ → Tm → ℕ
  | x, .var n => if n = x then 1 else 0
  | x, .lam t => occ (x + 1) t
  | x, .app t u => occ x t + occ x u

/-- `Spine x t`: `t` is `x N₁ … Nₖ`. -/
inductive Spine : ℕ → Tm → Prop
  | var (x : ℕ) : Spine x (.var x)
  | app {x : ℕ} {t : Tm} (u : Tm) : Spine x t → Spine x (.app t u)

/-- `HeadIs x t`: `t` is a head normal form `λy₁…yₘ. x N₁ … Nₖ` whose head variable is
the free variable `x`. -/
inductive HeadIs : ℕ → Tm → Prop
  | spine {x : ℕ} {t : Tm} : Spine x t → HeadIs x t
  | lam {x : ℕ} {t : Tm} : HeadIs (x + 1) t → HeadIs x (.lam t)

/-! ## Contexts and neededness functions -/

section Ctx
variable {α : Type}

/-- Extend a context (or neededness function) with a new variable `0`. -/
def scons (a : α) (f : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => f n

/-- Insert a new entry at position `k`. -/
def ins (k : ℕ) (a : α) (f : ℕ → α) (n : ℕ) : α :=
  if n < k then f n else if n = k then a else f (n - 1)

/-- Delete the entry at position `k`. -/
def del (k : ℕ) (f : ℕ → α) (n : ℕ) : α :=
  if n < k then f n else f (n + 1)

end Ctx

variable {R : Type} [Semiring R]

/-- The neededness function of a single use of variable `n`. -/
def single (n : ℕ) : ℕ → R := fun m => if m = n then 1 else 0

/-- The typing judgement `Γ ⊢_V t : τ` of natural reduction types. -/
inductive Has : (ℕ → Ty R) → (ℕ → R) → Tm → Ty R → Prop
  | var {Γ : ℕ → Ty R} (n : ℕ) : Has Γ (single n) (.var n) (Γ n)
  | lam {Γ : ℕ → Ty R} {σ τ : Ty R} {V : ℕ → R} {t : Tm} :
      Has (scons σ Γ) V t τ → Has Γ (fun n => V (n + 1)) (.lam t) (.arr (V 0) σ τ)
  | app {Γ : ℕ → Ty R} {σ τ : Ty R} {b : R} {V₁ V₂ : ℕ → R} {t u : Tm} :
      Has Γ V₁ t (.arr b σ τ) → Has Γ V₂ u σ →
      Has Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ

namespace Has

theorem congr {Γ : ℕ → Ty R} {V V' : ℕ → R} {t : Tm} {τ τ' : Ty R}
    (h : Has Γ V t τ) (hV : V = V') (hτ : τ = τ') : Has Γ V' t τ' := by
  subst hV hτ; exact h

theorem var' {Γ : ℕ → Ty R} {V : ℕ → R} {τ : Ty R} (n : ℕ)
    (hV : V = single n) (hτ : τ = Γ n) : Has Γ V (.var n) τ :=
  (Has.var n).congr hV.symm hτ.symm

theorem lam' {Γ : ℕ → Ty R} {σ τ : Ty R} {V W : ℕ → R} {b : R} {t : Tm}
    (h : Has (scons σ Γ) V t τ) (hb : b = V 0) (hW : W = fun n => V (n + 1)) :
    Has Γ W (.lam t) (.arr b σ τ) :=
  (Has.lam h).congr hW.symm (by rw [hb])

theorem app' {Γ : ℕ → Ty R} {σ τ : Ty R} {b : R} {V V₁ V₂ : ℕ → R} {t u : Tm}
    (h₁ : Has Γ V₁ t (.arr b σ τ)) (h₂ : Has Γ V₂ u σ)
    (hV : V = fun x => V₁ x + b * V₂ x) : Has Γ V (.app t u) τ :=
  (Has.app h₁ h₂).congr hV.symm rfl

end Has

/-! ## Weakening (shifting) -/

theorem ins_scons_succ {α : Type} (k : ℕ) (a b : α) (f : ℕ → α) :
    ins (k + 1) a (scons b f) = scons b (ins k a f) := by
  funext n
  cases n with
  | zero => simp [ins, scons]
  | succ n =>
    simp only [ins, scons]
    by_cases h1 : n < k
    · simp [h1]
    · by_cases h2 : n = k
      · simp [h2]
      · have : n + 1 - 1 = (n - 1) + 1 := by omega
        rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h2, this]

theorem scons_eq_ins {α : Type} (a : α) (f : ℕ → α) : scons a f = ins 0 a f := by
  funext n; cases n <;> simp [ins, scons]

theorem has_shift {Γ : ℕ → Ty R} {V : ℕ → R} {t : Tm} {τ : Ty R} (h : Has Γ V t τ) :
    ∀ (k : ℕ) (σ : Ty R), Has (ins k σ Γ) (ins k 0 V) (shift k t) τ := by
  induction h with
  | var n =>
    intro k σ
    by_cases hn : n < k
    · simp only [shift, hn, if_true]
      refine Has.var' n ?_ ?_
      · funext m; simp only [ins, single]; split_ifs <;> first | rfl | omega
      · simp [ins, hn]
    · simp only [shift, hn, if_false]
      refine Has.var' (n + 1) ?_ ?_
      · funext m; simp only [ins, single]; split_ifs <;> first | rfl | omega
      · simp only [ins]; rw [if_neg (by omega), if_neg (by omega)]; rfl
  | @lam Γ σ' τ V t _ ih =>
    intro k σ
    have := ih (k + 1) σ
    rw [ins_scons_succ] at this
    refine Has.lam' this ?_ ?_
    · simp [ins]
    · funext n; simp only [ins]; split_ifs <;> first | rfl | omega | (congr 1; omega)
  | @app Γ σ' τ b V₁ V₂ t u _ _ ih₁ ih₂ =>
    intro k σ
    refine Has.app' (ih₁ k σ) (ih₂ k σ) ?_
    funext n; simp only [ins]; split_ifs <;> simp

/-! ## Substitution -/

theorem has_subst {Γ : ℕ → Ty R} {V : ℕ → R} {t : Tm} {τ : Ty R} (h : Has Γ V t τ) :
    ∀ (k : ℕ) (σ : Ty R) (Δ : ℕ → Ty R) (W : ℕ → R) (u : Tm),
      Γ = ins k σ Δ → Has Δ W u σ →
      Has Δ (fun n => del k V n + V k * W n) (subst k u t) τ := by
  induction h with
  | @var Γ n =>
    intro k σ Δ W u hΓ hu
    subst hΓ
    by_cases h1 : n < k
    · simp only [subst, h1, if_true]
      refine Has.var' n ?_ ?_
      · funext m; simp only [del, single]; split_ifs <;> first | (exfalso; omega) | simp
      · simp [ins, h1]
    · by_cases h2 : n = k
      · subst h2
        simp only [subst, lt_irrefl, if_false, if_true]
        refine hu.congr ?_ ?_
        · funext m; simp only [del, single]; split_ifs <;> first | (exfalso; omega) | simp
        · simp [ins]
      · simp only [subst, h1, h2, if_false]
        refine Has.var' (n - 1) ?_ ?_
        · funext m; simp only [del, single]; split_ifs <;> first | (exfalso; omega) | simp
        · simp only [ins]; rw [if_neg h1, if_neg h2]
  | @lam Γ σ' τ V t _ ih =>
    intro k σ Δ W u hΓ hu
    subst hΓ
    have hu' := has_shift hu 0 σ'
    have e1 : ins 0 σ' Δ = scons σ' Δ := by
      funext n; cases n <;> simp [ins, scons]
    rw [e1] at hu'
    have := ih (k + 1) σ (scons σ' Δ) (ins 0 0 W) (shift 0 u) (ins_scons_succ _ _ _ _).symm hu'
    refine Has.lam' this ?_ ?_
    · simp [del, ins]
    · funext n; simp [del, ins]
  | @app Γ σ' τ b V₁ V₂ t t' _ _ ih₁ ih₂ =>
    intro k σ Δ W u hΓ hu
    refine Has.app' (ih₁ k σ Δ W u hΓ hu) (ih₂ k σ Δ W u hΓ hu) ?_
    funext n; simp only [del]; split_ifs <;> simp [add_mul, mul_add, mul_assoc] <;> abel

/-! ## Subject reduction -/

/-- **Subject reduction.** A β-step anywhere in a term preserves its type *and* its exact
neededness function. Generic over the grade semiring. -/
theorem subject_reduction {Γ : ℕ → Ty R} {V : ℕ → R} {t t' : Tm} {τ : Ty R}
    (h : Has Γ V t τ) (hs : Step t t') : Has Γ V t' τ := by
  induction hs generalizing Γ V τ with
  | beta t u =>
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | lam h₁ =>
        rw [scons_eq_ins] at h₁
        refine (has_subst h₁ 0 _ Γ _ u rfl h₂).congr ?_ rfl
        funext n; simp [del]
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
theorem subject_reduction_star {Γ : ℕ → Ty R} {V : ℕ → R} {t t' : Tm} {τ : Ty R}
    (h : Has Γ V t τ) (hs : Relation.ReflTransGen Step t t') : Has Γ V t' τ := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => exact subject_reduction ih hst

/-! ## Soundness of grade `0` with respect to head neededness (grades in `ℕ`) -/

theorem spine_needed {Γ : ℕ → Ty ℕ} {V : ℕ → ℕ} {t : Tm} {τ : Ty ℕ} {x : ℕ}
    (hs : Spine x t) (h : Has Γ V t τ) : 1 ≤ V x := by
  induction hs generalizing V τ with
  | var =>
    cases h with
    | var => simp [single]
  | app u _ ih =>
    cases h with
    | app h₁ _ => exact le_trans (ih h₁) (Nat.le_add_right _ _)

/-- The head variable of a typed head normal form always has grade `≥ 1`. -/
theorem head_needed {Γ : ℕ → Ty ℕ} {V : ℕ → ℕ} {t : Tm} {τ : Ty ℕ} {x : ℕ}
    (hh : HeadIs x t) (h : Has Γ V t τ) : 1 ≤ V x := by
  induction hh generalizing Γ V τ with
  | spine hs => exact spine_needed hs h
  | lam _ ih =>
    cases h with
    | lam h => exact ih h

/-- **Soundness of grade `0` w.r.t. head neededness.** If a typing of `t` assigns the
free variable `x` grade `0`, then no β-reduct of `t` is a head normal form with head
variable `x`: the variable is not head-needed. -/
theorem head_needed_sound {Γ : ℕ → Ty ℕ} {V : ℕ → ℕ} {t t' : Tm} {τ : Ty ℕ} {x : ℕ}
    (h : Has Γ V t τ) (hx : V x = 0) (hred : Relation.ReflTransGen Step t t') :
    ¬ HeadIs x t' := by
  intro hh
  have := head_needed hh (subject_reduction_star h hred)
  omega

/-! ## Worked derivations -/

/-- The combinator `K = λa b. a`. -/
def K : Tm := .lam (.lam (.var 1))

/-- `λx. K x x`: the bound variable occurs twice. -/
def kxx : Tm := .lam (.app (.app K (.var 0)) (.var 0))

/-- `Twice = λf x. f (f x)`. -/
def twice : Tm := .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))

/-- `Compose = λg f x. g (f x)`. -/
def compose : Tm := .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))

/-- `K : σ →₁ τ →₀ σ`, with no free-variable usage. -/
theorem K_typing (Γ : ℕ → Ty R) (σ τ : Ty R) :
    Has Γ 0 K (.arr 1 σ (.arr 0 τ σ)) := by
  refine Has.lam' (Has.lam' (Has.var 1) rfl rfl) ?_ ?_
  · simp [single]
  · funext n; simp [single]

/-- **Occurrences vs uses.** `λx. K x x : σ →₁ σ`: the argument is used exactly once. -/
theorem kxx_typing (Γ : ℕ → Ty R) (σ : Ty R) : Has Γ 0 kxx (.arr 1 σ σ) := by
  refine Has.lam' (Has.app (Has.app (K_typing _ σ σ) (Has.var 0)) (Has.var 0)) ?_ ?_
  · simp [single]
  · funext n; simp [single]

/-- …although the argument occurs twice in the body of `λx. K x x`. -/
theorem kxx_occurrences : occ 0 (.app (.app K (.var 0)) (.var 0)) = 2 := by decide

/-- **Counting.** `Twice : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`: the bound variable `x` receives
the product of the use counts of the two applications of `f`. -/
theorem twice_typing (Γ : ℕ → Ty R) (σ : Ty R) (i : R) :
    Has Γ 0 twice (.arr (1 + i) (.arr i σ σ) (.arr (i * i) σ σ)) := by
  refine Has.lam' (Has.lam' (Has.app (Has.var 1) (Has.app (Has.var 1) (Has.var 0)))
    ?_ rfl) ?_ ?_
  · simp [single]
  · simp [single]
  · funext n; simp [single]

/-- **Counting, with distinct grades.** `Compose : (σ₂ →ᵢ σ₃) →₁ (σ₁ →ⱼ σ₂) →ᵢ σ₁ →_{i·j} σ₃`:
the bound variable `x` receives the product `i * j` of the use counts. -/
theorem compose_typing (Γ : ℕ → Ty R) (σ₁ σ₂ σ₃ : Ty R) (i j : R) :
    Has Γ 0 compose (.arr 1 (.arr i σ₂ σ₃) (.arr i (.arr j σ₁ σ₂) (.arr (i * j) σ₁ σ₃))) := by
  refine Has.lam' (Has.lam' (Has.lam' (Has.app (Has.var 2) (Has.app (Has.var 1) (Has.var 0)))
    ?_ rfl) ?_ rfl) ?_ ?_
  · simp [single]
  · simp [single]
  · simp [single]
  · funext n; simp [single]

/-- In `ℕ`, `Twice` at `i = 2` gives `x` grade `4`: grades genuinely count. -/
example (Γ : ℕ → Ty ℕ) (σ : Ty ℕ) : Has Γ 0 twice (.arr 3 (.arr 2 σ σ) (.arr 4 σ σ)) :=
  twice_typing Γ σ 2

end NRT
