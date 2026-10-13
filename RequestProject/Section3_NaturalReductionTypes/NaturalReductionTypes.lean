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

## The typing judgement

`Has Γ V t τ` is the inductive judgement `Γ ⊢_V t : τ` about an untyped well-scoped term
`t : Tm n` (`Syntax.lean`), with `Γ : Fin n → Ty B R` and `V : Fin n → R`.  Its three
constructors are the three typing rules of the paper.

The metatheory is proved by induction on derivations:
* `Has.rename`: renaming (weakening, exchange, contraction) — the grade of a new variable
  is the total grade of the old variables renamed to it;
* `Has.subst`: the graded substitution lemma — usage becomes `y ↦ Σₓ V(x) · W(x)(y)`;
* `Has.inst`: typing of the β-contractum;
* `Has.subject_reduction`: β-reduction preserves the type and the *exact* neededness
  function;
* `Has.head_needed_sound`: for `ℕ`-grades, a variable of grade `0` is never the head
  variable of any reduct (soundness of grade `0` w.r.t. head neededness).

The worked examples `K`, `λx. K x x`, `Twice`, `Compose` are typed closed terms.

An intrinsically typed presentation (typed terms `GTm Γ V τ`, correct by construction) is
developed separately in `GTm.lean`, where it is shown to be equivalent to `Has`.
-/

@[expose] public section

namespace NRT

/-- Natural reduction types over a type `B` of base types and a grade algebra `R`: base
types `base β` (for `β : B`) and graded arrows `arr b σ τ`, written `σ →_b τ` in the
paper. -/
inductive Ty (B : Type) (R : Type) : Type
  | base : B → Ty B R
  | arr : R → Ty B R → Ty B R → Ty B R

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

/-- Embed a closed untyped term into any scope. -/
def Tm.embed {n : ℕ} (t : Tm 0) : Tm n := NRT.rename Fin.elim0 t

variable {B : Type} {R : Type} [Semiring R]

/-- The neededness function of a single use of the variable `x`. -/
def single {n : ℕ} (x : Fin n) : Fin n → R := fun y => if y = x then 1 else 0

/-- Push a neededness function forward along a renaming: the grade of `y` is the sum of
the grades of all variables renamed to `y`. -/
def rmap {n m : ℕ} (ρ : Fin n → Fin m) (V : Fin n → R) : Fin m → R :=
  fun y => ∑ x, if ρ x = y then V x else 0

theorem rmap_single {n m : ℕ} (ρ : Fin n → Fin m) (x : Fin n) :
    rmap ρ (single x : Fin n → R) = single (ρ x) := by
  funext y
  simp only [rmap, single]
  rw [Finset.sum_eq_single x]
  · simp [eq_comm]
  · intro b _ hb; simp [hb]
  · simp

/-! ## The typing judgement -/

/-- The typing judgement `Γ ⊢_V t : τ` of natural reduction types, for a term `t` with
`n` free variables, a context `Γ : Fin n → Ty B R` and a neededness function
`V : Fin n → R`. -/
inductive Has : {n : ℕ} → (Fin n → Ty B R) → (Fin n → R) → Tm n → Ty B R → Prop
  | var {n : ℕ} {Γ : Fin n → Ty B R} (x : Fin n) : Has Γ (single x) (.var x) (Γ x)
  | lam {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {V : Fin (n + 1) → R} {t : Tm (n + 1)} :
      Has (Fin.cons σ Γ) V t τ → Has Γ (fun x => V x.succ) (.lam t) (.arr (V 0) σ τ)
  | app {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {b : R} {V₁ V₂ : Fin n → R} {t u : Tm n} :
      Has Γ V₁ t (.arr b σ τ) → Has Γ V₂ u σ →
      Has Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ

namespace Has

variable {n : ℕ} {Γ : Fin n → Ty B R}

theorem congr {V V' : Fin n → R} {t : Tm n} {τ τ' : Ty B R}
    (h : Has Γ V t τ) (hV : V = V') (hτ : τ = τ') : Has Γ V' t τ' := by
  subst hV hτ; exact h

/-! ### Inversion -/

theorem inv_var {V : Fin n → R} {x : Fin n} {τ : Ty B R} (h : Has Γ V (.var x) τ) :
    V = single x ∧ τ = Γ x := by
  cases h; exact ⟨rfl, rfl⟩

theorem inv_lam {V : Fin n → R} {t : Tm (n + 1)} {ρ : Ty B R} (h : Has Γ V (.lam t) ρ) :
    ∃ (σ τ : Ty B R) (W : Fin (n + 1) → R), Has (Fin.cons σ Γ) W t τ ∧
      V = (fun x => W x.succ) ∧ ρ = .arr (W 0) σ τ := by
  cases h with
  | lam h => exact ⟨_, _, _, h, rfl, rfl⟩

theorem inv_app {V : Fin n → R} {t u : Tm n} {τ : Ty B R} (h : Has Γ V (.app t u) τ) :
    ∃ (σ : Ty B R) (b : R) (V₁ V₂ : Fin n → R), Has Γ V₁ t (.arr b σ τ) ∧ Has Γ V₂ u σ ∧
      V = (fun x => V₁ x + b * V₂ x) := by
  cases h with
  | app h₁ h₂ => exact ⟨_, _, _, _, h₁, h₂, rfl⟩

/-! ### Renaming and substitution -/

/-- **Renaming.** A typing can be renamed along any `ρ : Fin n → Fin m` compatible with the
contexts; the neededness of a new variable `y` is the total neededness of the old
variables renamed to `y`.  This covers weakening (new variables get grade `0`), exchange,
and contraction (grades are added). -/
theorem rename {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) :
    ∀ {m : ℕ} (ρ : Fin n → Fin m) (Δ : Fin m → Ty B R), (∀ x, Δ (ρ x) = Γ x) →
      Has Δ (rmap ρ V) (NRT.rename ρ t) τ := by
  induction h with
  | var x =>
    intro m ρ Δ hΔ
    exact (Has.var (Γ := Δ) (ρ x)).congr (rmap_single ρ x).symm (hΔ x)
  | @lam n Γ σ τ V t _ ih =>
    intro m ρ Δ hΔ
    exact (Has.lam (ih (liftR ρ) (Fin.cons σ Δ)
        (fun x => by cases x using Fin.cases <;> simp [hΔ]))).congr
      (by funext y; simp [rmap, Fin.sum_univ_succ, (Fin.succ_ne_zero y).symm])
      (by simp [rmap, Fin.sum_univ_succ, Fin.succ_ne_zero])
  | app _ _ ih₁ ih₂ =>
    intro m ρ Δ hΔ
    exact (Has.app (ih₁ ρ Δ hΔ) (ih₂ ρ Δ hΔ)).congr
      (by funext y
          simp only [rmap, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> simp) rfl

/-- **Weakening** by a fresh variable `0` of grade `0`. -/
theorem weaken {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) (σ : Ty B R) :
    Has (Fin.cons σ Γ) (Fin.cons 0 V) (NRT.rename Fin.succ t) τ :=
  (h.rename Fin.succ (Fin.cons σ Γ) (fun x => by simp)).congr
    (by
      funext y
      cases y using Fin.cases with
      | zero => simp [rmap, (Fin.succ_ne_zero _)]
      | succ y => simp [rmap]) rfl

/-- A closed typed term is typed in any context, with no usage of the context's
variables. -/
theorem embed {t : Tm 0} {τ : Ty B R} (h : Has (R := R) ![] 0 t τ) (Γ : Fin n → Ty B R) :
    Has Γ 0 t.embed τ :=
  (h.rename Fin.elim0 Γ (fun x => x.elim0)).congr (by funext y; simp [rmap]) rfl

/-- The typing of a substitution lifted under a binder of type `σ`. -/
theorem liftS {m : ℕ} {Δ : Fin m → Ty B R} {W : Fin n → Fin m → R} {s : Fin n → Tm m}
    (hs : ∀ x, Has Δ (W x) (s x) (Γ x)) (σ : Ty B R) :
    ∀ x : Fin (n + 1), Has (Fin.cons σ Δ)
      ((Fin.cons (single 0) (fun x => Fin.cons 0 (W x)) : Fin (n + 1) → Fin (m + 1) → R) x)
      (NRT.liftS s x) ((Fin.cons σ Γ : Fin (n + 1) → Ty B R) x) := by
  intro x
  cases x using Fin.cases with
  | zero => exact (Has.var (Γ := Fin.cons σ Δ) 0).congr (by simp) (by simp)
  | succ x => exact ((hs x).weaken σ).congr (by simp) (by simp)

/-- **Graded substitution.** Substituting, for every variable `x`, a term `s x` typed with
usage `W x`, the result has usage `y ↦ Σₓ V(x) · W(x)(y)`. -/
theorem subst {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) :
    ∀ {m : ℕ} (Δ : Fin m → Ty B R) (s : Fin n → Tm m) (W : Fin n → Fin m → R),
      (∀ x, Has Δ (W x) (s x) (Γ x)) →
      Has Δ (fun y => ∑ x, V x * W x y) (NRT.subst s t) τ := by
  induction h with
  | var x =>
    intro m Δ s W hs
    exact (hs x).congr (by funext y; simp [single]) rfl
  | @lam n Γ σ τ V t _ ih =>
    intro m Δ s W hs
    exact (Has.lam (ih (Fin.cons σ Δ) _ _ (liftS hs σ))).congr
      (by funext y; simp [Fin.sum_univ_succ, single, Fin.succ_ne_zero])
      (by simp [Fin.sum_univ_succ, single])
  | app _ _ ih₁ ih₂ =>
    intro m Δ s W hs
    exact (Has.app (ih₁ Δ s W hs) (ih₂ Δ s W hs)).congr
      (by funext y; simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]) rfl

/-- **Typing of the β-contractum** `t[u/0]`: its usage is `y ↦ V(y+1) + V(0) · V₂(y)`. -/
theorem inst {σ τ : Ty B R} {V : Fin (n + 1) → R} {V₂ : Fin n → R} {t : Tm (n + 1)}
    {u : Tm n} (h : Has (Fin.cons σ Γ) V t τ) (hu : Has Γ V₂ u σ) :
    Has Γ (fun y => V y.succ + V 0 * V₂ y) (NRT.inst t u) τ :=
  (h.subst Γ (Fin.cons u Tm.var) (Fin.cons V₂ single) (fun x => by
    cases x using Fin.cases with
    | zero => exact hu.congr (by simp) (by simp)
    | succ x => exact (Has.var x).congr (by simp) (by simp))).congr
    (by funext y; simp [Fin.sum_univ_succ, single, add_comm]) rfl

/-! ### Subject reduction -/

/-- **Subject reduction.** A β-step preserves the type and the *exact* neededness
function.  Generic over the grade semiring. -/
theorem subject_reduction {V : Fin n → R} {t t' : Tm n} {τ : Ty B R}
    (h : Has Γ V t τ) (hs : Step t t') : Has Γ V t' τ := by
  induction hs generalizing τ with
  | beta t u =>
    obtain ⟨σ, b, V₁, V₂, h₁, h₂, rfl⟩ := h.inv_app
    obtain ⟨σ', τ', W, hb, rfl, he⟩ := h₁.inv_lam
    simp only [Ty.arr.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hb.inst h₂
  | lam _ ih =>
    obtain ⟨σ, τ', W, hb, rfl, rfl⟩ := h.inv_lam
    exact (ih hb).lam
  | appL u _ ih =>
    obtain ⟨σ, b, V₁, V₂, h₁, h₂, rfl⟩ := h.inv_app
    exact (ih h₁).app h₂
  | appR t _ ih =>
    obtain ⟨σ, b, V₁, V₂, h₁, h₂, rfl⟩ := h.inv_app
    exact h₁.app (ih h₂)

/-- Subject reduction for many-step β-reduction. -/
theorem subject_reduction_star {V : Fin n → R} {t t' : Tm n} {τ : Ty B R}
    (h : Has Γ V t τ) (hs : Relation.ReflTransGen Step t t') : Has Γ V t' τ := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact ih.subject_reduction hs

/-! ### Soundness of grade `0` with respect to head neededness (grades in `ℕ`) -/

theorem spine_needed {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty B ℕ}
    (h : Has Γ V t τ) {x : Fin n} (hs : Spine x t) : 1 ≤ V x := by
  induction hs generalizing V τ with
  | var => obtain ⟨rfl, -⟩ := h.inv_var; simp [single]
  | app u _ ih =>
    obtain ⟨σ, b, V₁, V₂, h₁, h₂, rfl⟩ := h.inv_app
    exact le_trans (ih h₁) (Nat.le_add_right _ _)

/-- The head variable of a typed head normal form always has grade `≥ 1`. -/
theorem head_needed {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty B ℕ}
    (h : Has Γ V t τ) {x : Fin n} (hh : HeadIs x t) : 1 ≤ V x := by
  induction hh generalizing τ with
  | spine hs => exact h.spine_needed hs
  | lam _ ih =>
    obtain ⟨σ, τ', W, hb, rfl, rfl⟩ := h.inv_lam
    exact ih hb

/-- **Soundness of grade `0` w.r.t. head neededness.** If `Γ ⊢_V t : τ` gives the free
variable `x` grade `0`, then no β-reduct of `t` is a head normal form with head
variable `x`: the variable is not head-needed. -/
theorem head_needed_sound {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {t t' : Tm n} {τ : Ty B ℕ}
    {x : Fin n} (h : Has Γ V t τ) (hx : V x = 0) (hred : Relation.ReflTransGen Step t t') :
    ¬ HeadIs x t' := by
  intro hh
  have := (h.subject_reduction_star hred).head_needed hh
  omega

end Has

/-! ## Closed terms and worked examples -/

/-- The untyped closed combinator `K = λa b. a`. -/
def Tm.K : Tm 0 := .lam (.lam (.var 1))

/-- The body `K x x` of `λx. K x x`, in the scope of the bound variable `x`. -/
def Tm.kxxBody : Tm 1 := .app (.app Tm.K.embed (.var 0)) (.var 0)

/-- `λx. K x x`: the bound variable occurs twice. -/
def Tm.kxx : Tm 0 := .lam Tm.kxxBody

/-- `Twice = λf x. f (f x)`. -/
def Tm.twice : Tm 0 := .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))

/-- `Compose = λg f x. g (f x)`. -/
def Tm.compose : Tm 0 := .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))

/-- `K = λx y. x : σ →₁ τ →₀ σ`. -/
theorem K_typing (σ τ : Ty B R) : Has (R := R) ![] 0 Tm.K (.arr 1 σ (.arr 0 τ σ)) :=
  (Has.lam (Has.lam (Has.var (Γ := Fin.cons τ (Fin.cons σ ![])) 1))).congr
    (by funext x; exact x.elim0) (by simp [single])

/-- **Occurrences vs uses.** `λx. K x x : σ →₁ σ`: the argument is used exactly once. -/
theorem kxx_typing (σ : Ty B R) : Has (R := R) ![] 0 Tm.kxx (.arr 1 σ σ) :=
  (Has.lam (Has.app (Has.app ((K_typing σ σ).embed (Fin.cons σ ![]))
      (Has.var (Γ := Fin.cons σ ![]) 0)) (Has.var 0))).congr
    (by funext x; exact x.elim0) (by simp [single])

/-- …although the argument occurs twice in the body of `λx. K x x`. -/
theorem kxx_occurrences : occ 0 Tm.kxxBody = 2 := by decide

/-- **Counting.** `Twice = λf x. f (f x) : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`: the bound
variable `x` receives the product of the use counts of the two applications of `f`. -/
theorem twice_typing (σ : Ty B R) (i : R) :
    Has (R := R) ![] 0 Tm.twice (.arr (1 + i) (.arr i σ σ) (.arr (i * i) σ σ)) :=
  (Has.lam (Has.lam (Has.app (Has.var (Γ := Fin.cons σ (Fin.cons (.arr i σ σ) ![])) 1)
      (Has.app (Has.var 1) (Has.var 0))))).congr
    (by funext x; exact x.elim0) (by simp [single])

/-- **Counting, with distinct grades.**
`Compose = λg f x. g (f x) : (σ₂ →ᵢ σ₃) →₁ (σ₁ →ⱼ σ₂) →ᵢ σ₁ →_{i·j} σ₃`: the bound
variable `x` receives the product `i * j` of the use counts. -/
theorem compose_typing (σ₁ σ₂ σ₃ : Ty B R) (i j : R) :
    Has (R := R) ![] 0 Tm.compose
      (.arr 1 (.arr i σ₂ σ₃) (.arr i (.arr j σ₁ σ₂) (.arr (i * j) σ₁ σ₃))) :=
  (Has.lam (Has.lam (Has.lam (Has.app
      (Has.var (Γ := Fin.cons σ₁ (Fin.cons (.arr j σ₁ σ₂) (Fin.cons (.arr i σ₂ σ₃) ![]))) 2)
      (Has.app (Has.var 1) (Has.var 0)))))).congr
    (by funext x; exact x.elim0) (by simp [single])

/-- In `ℕ`, `Twice` at `i = 2` gives `x` grade `4`: grades genuinely count. -/
example (σ : Ty B ℕ) : Has ![] 0 Tm.twice (.arr 3 (.arr 2 σ σ) (.arr 4 σ σ)) :=
  twice_typing σ 2

end NRT
