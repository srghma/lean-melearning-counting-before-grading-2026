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

## The main grammar: intrinsically typed, graded terms

The type system is given as a grammar of terms that are correct by construction:

  `GTm Γ V τ`   (with `Γ : Fin n → Ty B R`, `V : Fin n → R`)

is the type of λ-terms with free variables in `Fin n`, of type `τ` and with neededness
function `V`.  Ill-scoped, ill-typed or wrongly graded terms cannot be written, and
`GTm ![] 0 τ` is the type of closed terms of type `τ`.  Each typed term erases
(`GTm.erase`) to an untyped well-scoped term `Tm n` (`Syntax.lean`), on which β-reduction
is defined.

All the metatheory is developed on `GTm` directly, as operations on typed terms whose
types record the result:
* `GTm.rename`: renaming (weakening, exchange, contraction) — the grade of a new variable
  is the total grade of the old variables renamed to it;
* `GTm.subst`: the graded substitution — usage becomes `y ↦ Σₓ V(x) · W(x)(y)`;
* `GTm.inst`: the typed β-contractum;
* `GStep`: β-reduction *of typed terms*; its type `GTm Γ V τ → GTm Γ V τ → Prop` says that
  type and exact neededness function are preserved.  `GStep.erase` and `GTm.lift_step`
  show that it is exactly β-reduction of the erasures (this is subject reduction);
* `GTm.head_needed_sound`: for `ℕ`-grades, a variable of grade `0` is never the head
  variable of any reduct (soundness of grade `0` w.r.t. head neededness).

The worked examples `K`, `kxx = λx. K x x`, `twice`, `compose` are closed typed terms.

## The extrinsic judgement

`Has Γ V t τ` (a typing judgement about an untyped term `t`) is *defined* from the
grammar: `t` is the erasure of some `d : GTm Γ V τ`.  The usual rules and lemmas for
`Has` are derived from those of `GTm`.
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

/-! ## The grammar of typed, graded terms -/

/-- **Natural reduction types, as a grammar.**  `GTm Γ V τ` is the type of λ-terms with
free variables in `Fin n` (typed by `Γ`), of type `τ`, whose neededness function is `V`.
The three constructors are the three typing rules of the paper; in particular `app` is the
rule `V(x) = V₁(x) + b · V₂(x)`.  `GTm ![] 0 τ` is the type of closed terms of type `τ`. -/
inductive GTm : {n : ℕ} → (Fin n → Ty B R) → (Fin n → R) → Ty B R → Type
  | var {n : ℕ} {Γ : Fin n → Ty B R} (x : Fin n) : GTm Γ (single x) (Γ x)
  | lam {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {V : Fin (n + 1) → R} :
      GTm (Fin.cons σ Γ) V τ → GTm Γ (fun x => V x.succ) (.arr (V 0) σ τ)
  | app {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {b : R} {V₁ V₂ : Fin n → R} :
      GTm Γ V₁ (.arr b σ τ) → GTm Γ V₂ σ → GTm Γ (fun x => V₁ x + b * V₂ x) τ

namespace GTm

variable {n : ℕ} {Γ : Fin n → Ty B R}

/-- Forget the typing: the underlying well-scoped untyped term. -/
def erase {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {τ : Ty B R} : GTm Γ V τ → Tm n
  | .var x => .var x
  | .lam d => .lam d.erase
  | .app d e => .app d.erase e.erase

@[simp] theorem erase_var (x : Fin n) : (GTm.var (Γ := Γ) x).erase = .var x := rfl
@[simp] theorem erase_lam {σ τ : Ty B R} {V : Fin (n + 1) → R} (d : GTm (Fin.cons σ Γ) V τ) :
    (GTm.lam d).erase = .lam d.erase := rfl
@[simp] theorem erase_app {σ τ : Ty B R} {b : R} {V₁ V₂ : Fin n → R}
    (d : GTm Γ V₁ (.arr b σ τ)) (e : GTm Γ V₂ σ) :
    (GTm.app d e).erase = .app d.erase e.erase := rfl

/-- Transport a typed term along equalities of its grade and type indices. -/
def cast {V V' : Fin n → R} {τ τ' : Ty B R} (hV : V = V') (hτ : τ = τ') (d : GTm Γ V τ) :
    GTm Γ V' τ' :=
  hV ▸ hτ ▸ d

@[simp] theorem cast_rfl {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) :
    d.cast rfl rfl = d := rfl

@[simp] theorem erase_cast {V V' : Fin n → R} {τ τ' : Ty B R} (hV : V = V') (hτ : τ = τ')
    (d : GTm Γ V τ) : (d.cast hV hτ).erase = d.erase := by
  subst hV hτ; rfl

/-! ### Renaming -/

/-- **Renaming.** A typed term can be renamed along any `ρ : Fin n → Fin m` compatible with
the contexts; the neededness of a new variable `y` is the total neededness of the old
variables renamed to `y`.  This covers weakening (new variables get grade `0`), exchange,
and contraction (grades are added). -/
def rename {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {τ : Ty B R} :
    GTm Γ V τ → ∀ {m : ℕ} (ρ : Fin n → Fin m) (Δ : Fin m → Ty B R), (∀ x, Δ (ρ x) = Γ x) →
      GTm Δ (rmap ρ V) τ
  | .var x, _, ρ, Δ, hΔ => (GTm.var (Γ := Δ) (ρ x)).cast (rmap_single ρ x).symm (hΔ x)
  | @GTm.lam _ _ _ _ _ σ _ _ d, _, ρ, Δ, hΔ =>
      (GTm.lam (d.rename (liftR ρ) (Fin.cons σ Δ)
        (fun x => by cases x using Fin.cases <;> simp [hΔ]))).cast
        (by funext y; simp [rmap, Fin.sum_univ_succ, (Fin.succ_ne_zero y).symm])
        (by simp [rmap, Fin.sum_univ_succ, Fin.succ_ne_zero])
  | .app d e, _, ρ, Δ, hΔ => (GTm.app (d.rename ρ Δ hΔ) (e.rename ρ Δ hΔ)).cast
        (by funext y
            simp only [rmap, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun x _ => ?_
            split_ifs <;> simp) rfl

@[simp] theorem erase_rename {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) {m : ℕ}
    (ρ : Fin n → Fin m) (Δ : Fin m → Ty B R) (hΔ : ∀ x, Δ (ρ x) = Γ x) :
    (d.rename ρ Δ hΔ).erase = NRT.rename ρ d.erase := by
  induction d generalizing m with
  | var x => simp [GTm.rename, NRT.rename]
  | lam d ih => simp [GTm.rename, NRT.rename, ih]
  | app d e ihd ihe => simp [GTm.rename, NRT.rename, ihd, ihe]

/-- **Weakening** by a fresh variable `0` of grade `0`. -/
def weaken {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) (σ : Ty B R) :
    GTm (Fin.cons σ Γ) (Fin.cons 0 V) τ :=
  (d.rename Fin.succ (Fin.cons σ Γ) (fun x => by simp)).cast
    (by
      funext y
      cases y using Fin.cases with
      | zero => simp [rmap, (Fin.succ_ne_zero _)]
      | succ y => simp [rmap]) rfl

@[simp] theorem erase_weaken {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) (σ : Ty B R) :
    (d.weaken σ).erase = NRT.rename Fin.succ d.erase := by
  simp [weaken]

/-- Embed a closed typed term into any context, with no usage of the context's
variables. -/
def embed {τ : Ty B R} (d : GTm (R := R) ![] 0 τ) (Γ : Fin n → Ty B R) : GTm Γ 0 τ :=
  (d.rename Fin.elim0 Γ (fun x => x.elim0)).cast (by funext y; simp [rmap]) rfl

/-! ### Substitution -/

/-- The substitution lifted under a binder of type `σ`. -/
def liftSubst {m : ℕ} {Δ : Fin m → Ty B R} {W : Fin n → Fin m → R}
    (s : ∀ x, GTm Δ (W x) (Γ x)) (σ : Ty B R) :
    ∀ x : Fin (n + 1), GTm (Fin.cons σ Δ)
      ((Fin.cons (single 0) (fun x => Fin.cons 0 (W x)) : Fin (n + 1) → Fin (m + 1) → R) x)
      ((Fin.cons σ Γ : Fin (n + 1) → Ty B R) x) :=
  fun x => Fin.cases (motive := fun x => GTm (Fin.cons σ Δ)
      ((Fin.cons (single 0) (fun x => Fin.cons 0 (W x)) : Fin (n + 1) → Fin (m + 1) → R) x)
      ((Fin.cons σ Γ : Fin (n + 1) → Ty B R) x))
    ((GTm.var 0).cast (by simp) (by simp))
    (fun x => ((s x).weaken σ).cast (by simp) (by simp)) x

/-- **Graded substitution.** Substituting, for every variable `x`, a typed term `s x` with
usage `W x`, the result has usage `y ↦ Σₓ V(x) · W(x)(y)`. -/
def subst {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {τ : Ty B R} :
    GTm Γ V τ → ∀ {m : ℕ} (Δ : Fin m → Ty B R) (W : Fin n → Fin m → R),
      (∀ x, GTm Δ (W x) (Γ x)) → GTm Δ (fun y => ∑ x, V x * W x y) τ
  | .var x, _, _, _, s => (s x).cast (by funext y; simp [single]) rfl
  | @GTm.lam _ _ _ _ _ σ _ _ d, _, Δ, W, s =>
      (GTm.lam (d.subst (Fin.cons σ Δ) _ (liftSubst s σ))).cast
        (by funext y; simp [Fin.sum_univ_succ, single, Fin.succ_ne_zero])
        (by simp [Fin.sum_univ_succ, single])
  | .app d e, _, Δ, W, s => (GTm.app (d.subst Δ W s) (e.subst Δ W s)).cast
        (by funext y; simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]) rfl

theorem erase_liftSubst {m : ℕ} {Δ : Fin m → Ty B R} {W : Fin n → Fin m → R}
    (s : ∀ x, GTm Δ (W x) (Γ x)) (σ : Ty B R) :
    (fun x => (liftSubst s σ x).erase) = liftS (fun x => (s x).erase) := by
  funext x
  cases x using Fin.cases <;> simp [liftSubst]

@[simp] theorem erase_subst {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) {m : ℕ}
    (Δ : Fin m → Ty B R) (W : Fin n → Fin m → R) (s : ∀ x, GTm Δ (W x) (Γ x)) :
    (d.subst Δ W s).erase = NRT.subst (fun x => (s x).erase) d.erase := by
  induction d generalizing m with
  | var x => simp [GTm.subst, NRT.subst]
  | lam d ih => simp [GTm.subst, NRT.subst, ih, erase_liftSubst]
  | app d e ihd ihe => simp [GTm.subst, NRT.subst, ihd, ihe]

/-- The substitution `[e/0]` used by β-reduction, as a typed substitution. -/
def instSubst {σ : Ty B R} {V₂ : Fin n → R} (e : GTm Γ V₂ σ) :
    ∀ x : Fin (n + 1), GTm Γ ((Fin.cons V₂ single : Fin (n + 1) → Fin n → R) x)
      ((Fin.cons σ Γ : Fin (n + 1) → Ty B R) x) :=
  fun x => Fin.cases (motive := fun x => GTm Γ ((Fin.cons V₂ single : Fin (n + 1) → Fin n → R) x)
      ((Fin.cons σ Γ : Fin (n + 1) → Ty B R) x))
    (e.cast (by simp) (by simp)) (fun x => (GTm.var x).cast (by simp) (by simp)) x

/-- **The typed β-contractum** `d[e/0]`: its usage is `y ↦ V(y+1) + V(0) · V₂(y)`. -/
def inst {σ τ : Ty B R} {V : Fin (n + 1) → R} {V₂ : Fin n → R}
    (d : GTm (Fin.cons σ Γ) V τ) (e : GTm Γ V₂ σ) :
    GTm Γ (fun y => V y.succ + V 0 * V₂ y) τ :=
  (d.subst Γ _ (instSubst e)).cast
    (by funext y; simp [Fin.sum_univ_succ, single, add_comm]) rfl

@[simp] theorem erase_inst {σ τ : Ty B R} {V : Fin (n + 1) → R} {V₂ : Fin n → R}
    (d : GTm (Fin.cons σ Γ) V τ) (e : GTm Γ V₂ σ) :
    (d.inst e).erase = NRT.inst d.erase e.erase := by
  simp only [inst, erase_cast, erase_subst, NRT.inst]
  congr 1
  funext x
  cases x using Fin.cases <;> simp [instSubst]

/-- Inversion: a typed term whose erasure is an abstraction is a typed abstraction. -/
theorem eq_lam_of_erase {V : Fin n → R} {ρ : Ty B R} (d : GTm Γ V ρ) {t : Tm (n + 1)}
    (h : d.erase = .lam t) :
    ∃ (σ τ : Ty B R) (W : Fin (n + 1) → R) (d' : GTm (Fin.cons σ Γ) W τ)
      (hV : (fun x => W x.succ) = V) (hρ : Ty.arr (W 0) σ τ = ρ),
      d = (GTm.lam d').cast hV hρ ∧ d'.erase = t := by
  cases d with
  | var x => simp at h
  | lam d' => exact ⟨_, _, _, d', rfl, rfl, rfl, by simpa using h⟩
  | app d e => simp at h

end GTm

/-! ## β-reduction of typed terms (subject reduction by construction) -/

/-- **β-reduction of typed terms.**  The type of `GStep` says that a reduct has the same
scope, the same type and the same neededness function: subject reduction holds by
construction. -/
inductive GStep : {n : ℕ} → {Γ : Fin n → Ty B R} → {V : Fin n → R} → {τ : Ty B R} →
    GTm Γ V τ → GTm Γ V τ → Prop
  | beta {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {V : Fin (n + 1) → R} {V₂ : Fin n → R}
      (d : GTm (Fin.cons σ Γ) V τ) (e : GTm Γ V₂ σ) : GStep (.app (.lam d) e) (d.inst e)
  | lam {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {V : Fin (n + 1) → R}
      {d d' : GTm (Fin.cons σ Γ) V τ} : GStep d d' → GStep (.lam d) (.lam d')
  | appL {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {b : R} {V₁ V₂ : Fin n → R}
      {d d' : GTm Γ V₁ (.arr b σ τ)} (e : GTm Γ V₂ σ) :
      GStep d d' → GStep (.app d e) (.app d' e)
  | appR {n : ℕ} {Γ : Fin n → Ty B R} {σ τ : Ty B R} {b : R} {V₁ V₂ : Fin n → R}
      (d : GTm Γ V₁ (.arr b σ τ)) {e e' : GTm Γ V₂ σ} :
      GStep e e' → GStep (.app d e) (.app d e')

/-- A typed reduction step is a β-step of the erasures. -/
theorem GStep.erase {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {τ : Ty B R}
    {d d' : GTm Γ V τ} (h : GStep d d') : Step d.erase d'.erase := by
  induction h with
  | beta d e => simpa using Step.beta d.erase e.erase
  | lam _ ih => exact Step.lam ih
  | appL e _ ih => exact Step.appL _ ih
  | appR d _ ih => exact Step.appR _ ih

namespace GTm

variable {n : ℕ} {Γ : Fin n → Ty B R}

/-- **Subject reduction.** Every β-step of the erasure of a typed term `d` is the erasure of
a typed step `GStep d d'`: the reduct is again a term of the grammar with the same scope,
the same type and the *exact same* neededness function. Generic over the grade semiring. -/
theorem lift_step {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) {t' : Tm n}
    (h : Step d.erase t') : ∃ d', GStep d d' ∧ d'.erase = t' := by
  induction d with
  | var x => cases h
  | lam d ih =>
    cases h with
    | lam hs =>
      obtain ⟨d', hd, rfl⟩ := ih hs
      exact ⟨.lam d', .lam hd, rfl⟩
  | app d e ihd ihe =>
    simp only [erase_app] at h
    generalize ha : d.erase = a at h
    generalize hb : e.erase = b at h
    cases h with
    | beta t u =>
      obtain ⟨σ', τ', W, d', hV, hρ, rfl, rfl⟩ := eq_lam_of_erase d ha
      subst hb hV
      cases hρ
      exact ⟨d'.inst e, .beta d' e, by simp⟩
    | appL _ hs =>
      subst ha hb
      obtain ⟨d', hd, rfl⟩ := ihd hs
      exact ⟨.app d' e, .appL e hd, rfl⟩
    | appR _ hs =>
      subst ha hb
      obtain ⟨e', he, rfl⟩ := ihe hs
      exact ⟨.app d e', .appR d he, rfl⟩

/-- Subject reduction for many-step β-reduction. -/
theorem lift_steps {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) {t' : Tm n}
    (h : Relation.ReflTransGen Step d.erase t') :
    ∃ d', Relation.ReflTransGen GStep d d' ∧ d'.erase = t' := by
  induction h with
  | refl => exact ⟨d, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨d₁, hd₁, rfl⟩ := ih
    obtain ⟨d₂, hd₂, rfl⟩ := d₁.lift_step hs
    exact ⟨d₂, hd₁.tail hd₂, rfl⟩

/-- Subject reduction, in short: every β-reduct of the erasure of `d : GTm Γ V τ` is the
erasure of some `d' : GTm Γ V τ`. -/
theorem subject_reduction {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) {t' : Tm n}
    (h : Relation.ReflTransGen Step d.erase t') : ∃ d' : GTm Γ V τ, d'.erase = t' :=
  let ⟨d', _, hd'⟩ := d.lift_steps h; ⟨d', hd'⟩

/-! ### Soundness of grade `0` with respect to head neededness (grades in `ℕ`) -/

theorem spine_needed {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ} (d : GTm Γ V τ)
    {x : Fin n} (hs : Spine x d.erase) : 1 ≤ V x := by
  induction d with
  | var y => cases hs; simp [single]
  | lam d ih => cases hs
  | app d e ihd ihe =>
    cases hs with
    | app _ hs => exact le_trans (ihd hs) (Nat.le_add_right _ _)

/-- The head variable of a typed head normal form always has grade `≥ 1`. -/
theorem head_needed {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ} (d : GTm Γ V τ)
    {x : Fin n} (hh : HeadIs x d.erase) : 1 ≤ V x := by
  induction d with
  | var y => cases hh with | spine hs => exact spine_needed _ hs
  | lam d ih =>
    cases hh with
    | spine hs => cases hs
    | lam hh => exact ih hh
  | app d e ihd ihe => cases hh with | spine hs => exact spine_needed (.app d e) hs

/-- **Soundness of grade `0` w.r.t. head neededness.** If a typed term `d` gives the free
variable `x` grade `0`, then no β-reduct of `d` is a head normal form with head
variable `x`: the variable is not head-needed. -/
theorem head_needed_sound {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ} (d : GTm Γ V τ)
    {x : Fin n} (hx : V x = 0) {t' : Tm n} (hred : Relation.ReflTransGen Step d.erase t') :
    ¬ HeadIs x t' := by
  intro hh
  obtain ⟨d', rfl⟩ := d.subject_reduction hred
  have := d'.head_needed hh
  omega

end GTm

/-! ## Closed terms and worked examples -/

/-- Embed a closed untyped term into any scope. -/
def Tm.embed {n : ℕ} (t : Tm 0) : Tm n := NRT.rename Fin.elim0 t

@[simp] theorem GTm.erase_embed {n : ℕ} {τ : Ty B R} (d : GTm (R := R) ![] 0 τ)
    (Γ : Fin n → Ty B R) : (d.embed Γ).erase = d.erase.embed := by
  simp [GTm.embed, Tm.embed]

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

/-- `K = λx y. x : σ →₁ τ →₀ σ`, as a closed typed term. -/
def K (σ τ : Ty B R) : GTm (R := R) ![] 0 (.arr 1 σ (.arr 0 τ σ)) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.var (Γ := Fin.cons τ (Fin.cons σ ![])) 1)))

@[simp] theorem K_erase (σ τ : Ty B R) : (K σ τ).erase = Tm.K := by simp [K, Tm.K]

/-- **Occurrences vs uses.** `λx. K x x : σ →₁ σ`, as a closed typed term: the argument is
used exactly once. -/
def kxx (σ : Ty B R) : GTm (R := R) ![] 0 (.arr 1 σ σ) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.app (.app ((K σ σ).embed (Fin.cons σ ![]))
      (.var (Γ := Fin.cons σ ![]) 0)) (.var 0)))

@[simp] theorem kxx_erase (σ : Ty B R) : (kxx σ).erase = Tm.kxx := by
  simp [kxx, Tm.kxx, Tm.kxxBody]

/-- …although the argument occurs twice in the body of `λx. K x x`. -/
theorem kxx_occurrences : occ 0 Tm.kxxBody = 2 := by decide

/-- **Counting.** `Twice = λf x. f (f x) : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`, as a closed typed
term: the bound variable `x` receives the product of the use counts of the two
applications of `f`. -/
def twice (σ : Ty B R) (i : R) :
    GTm (R := R) ![] 0 (.arr (1 + i) (.arr i σ σ) (.arr (i * i) σ σ)) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.app (.var (Γ := Fin.cons σ (Fin.cons (.arr i σ σ) ![])) 1)
      (.app (.var 1) (.var 0)))))

@[simp] theorem twice_erase (σ : Ty B R) (i : R) : (twice σ i).erase = Tm.twice := by
  simp [twice, Tm.twice]

/-- **Counting, with distinct grades.**
`Compose = λg f x. g (f x) : (σ₂ →ᵢ σ₃) →₁ (σ₁ →ⱼ σ₂) →ᵢ σ₁ →_{i·j} σ₃`, as a closed typed
term: the bound variable `x` receives the product `i * j` of the use counts. -/
def compose (σ₁ σ₂ σ₃ : Ty B R) (i j : R) :
    GTm (R := R) ![] 0 (.arr 1 (.arr i σ₂ σ₃) (.arr i (.arr j σ₁ σ₂) (.arr (i * j) σ₁ σ₃))) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.lam (.app
      (.var (Γ := Fin.cons σ₁ (Fin.cons (.arr j σ₁ σ₂) (Fin.cons (.arr i σ₂ σ₃) ![]))) 2)
      (.app (.var 1) (.var 0))))))

@[simp] theorem compose_erase (σ₁ σ₂ σ₃ : Ty B R) (i j : R) :
    (compose σ₁ σ₂ σ₃ i j).erase = Tm.compose := by
  simp [compose, Tm.compose]

/-- In `ℕ`, `Twice` at `i = 2` gives `x` grade `4`: grades genuinely count. -/
example (σ : Ty B ℕ) : GTm ![] 0 (.arr 3 (.arr 2 σ σ) (.arr 4 σ σ)) := twice σ 2

/-! ## The extrinsic typing judgement, derived from the grammar -/

/-- The extrinsic judgement `Γ ⊢_V t : τ` about an untyped term `t : Tm n`: `t` is the
erasure of a typed term of the grammar `GTm Γ V τ`. -/
def Has {n : ℕ} (Γ : Fin n → Ty B R) (V : Fin n → R) (t : Tm n) (τ : Ty B R) : Prop :=
  ∃ d : GTm Γ V τ, d.erase = t

/-- Every typed term types its erasure. -/
theorem GTm.has {n : ℕ} {Γ : Fin n → Ty B R} {V : Fin n → R} {τ : Ty B R} (d : GTm Γ V τ) :
    Has Γ V d.erase τ := ⟨d, rfl⟩

namespace Has

variable {n : ℕ} {Γ : Fin n → Ty B R}

theorem var (x : Fin n) : Has Γ (single x) (.var x) (Γ x) := ⟨.var x, rfl⟩

theorem lam {σ τ : Ty B R} {V : Fin (n + 1) → R} {t : Tm (n + 1)}
    (h : Has (Fin.cons σ Γ) V t τ) : Has Γ (fun x => V x.succ) (.lam t) (.arr (V 0) σ τ) :=
  let ⟨d, hd⟩ := h; ⟨.lam d, by simp [hd]⟩

theorem app {σ τ : Ty B R} {b : R} {V₁ V₂ : Fin n → R} {t u : Tm n}
    (h₁ : Has Γ V₁ t (.arr b σ τ)) (h₂ : Has Γ V₂ u σ) :
    Has Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ :=
  let ⟨d, hd⟩ := h₁; let ⟨e, he⟩ := h₂; ⟨.app d e, by simp [hd, he]⟩

theorem congr {V V' : Fin n → R} {t : Tm n} {τ τ' : Ty B R}
    (h : Has Γ V t τ) (hV : V = V') (hτ : τ = τ') : Has Γ V' t τ' := by
  subst hV hτ; exact h

/-- Renaming lemma for the extrinsic judgement (from `GTm.rename`). -/
theorem rename {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) {m : ℕ}
    (ρ : Fin n → Fin m) (Δ : Fin m → Ty B R) (hΔ : ∀ x, Δ (ρ x) = Γ x) :
    Has Δ (rmap ρ V) (NRT.rename ρ t) τ :=
  let ⟨d, hd⟩ := h; ⟨d.rename ρ Δ hΔ, by simp [hd]⟩

/-- Graded substitution lemma for the extrinsic judgement (from `GTm.subst`). -/
theorem subst {V : Fin n → R} {t : Tm n} {τ : Ty B R} (h : Has Γ V t τ) {m : ℕ}
    (Δ : Fin m → Ty B R) (s : Fin n → Tm m) (W : Fin n → Fin m → R)
    (hs : ∀ x, Has Δ (W x) (s x) (Γ x)) :
    Has Δ (fun y => ∑ x, V x * W x y) (NRT.subst s t) τ := by
  obtain ⟨d, rfl⟩ := h
  choose e he using hs
  exact ⟨d.subst Δ W e, by simp [he]⟩

/-- Subject reduction for the extrinsic judgement (from `GTm.lift_step`). -/
theorem subject_reduction {V : Fin n → R} {t t' : Tm n} {τ : Ty B R}
    (h : Has Γ V t τ) (hs : Step t t') : Has Γ V t' τ := by
  obtain ⟨d, rfl⟩ := h
  obtain ⟨d', -, rfl⟩ := d.lift_step hs
  exact d'.has

/-- Subject reduction for many-step β-reduction, for the extrinsic judgement. -/
theorem subject_reduction_star {V : Fin n → R} {t t' : Tm n} {τ : Ty B R}
    (h : Has Γ V t τ) (hs : Relation.ReflTransGen Step t t') : Has Γ V t' τ := by
  obtain ⟨d, rfl⟩ := h
  obtain ⟨d', rfl⟩ := d.subject_reduction hs
  exact d'.has

/-- Soundness of grade `0` w.r.t. head neededness, for the extrinsic judgement. -/
theorem head_needed_sound {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {t t' : Tm n} {τ : Ty B ℕ}
    {x : Fin n} (h : Has Γ V t τ) (hx : V x = 0) (hred : Relation.ReflTransGen Step t t') :
    ¬ HeadIs x t' := by
  obtain ⟨d, rfl⟩ := h
  exact d.head_needed_sound hx hred

end Has

/-- `λx. K x x : σ →₁ σ`, as a statement about the untyped term. -/
theorem kxx_typing (σ : Ty B R) : Has ![] 0 Tm.kxx (.arr 1 σ σ) := ⟨kxx σ, kxx_erase σ⟩

/-- `Twice : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`, as a statement about the untyped term. -/
theorem twice_typing (σ : Ty B R) (i : R) :
    Has ![] 0 Tm.twice (.arr (1 + i) (.arr i σ σ) (.arr (i * i) σ σ)) :=
  ⟨twice σ i, twice_erase σ i⟩

/-- `Compose : (σ₂ →ᵢ σ₃) →₁ (σ₁ →ⱼ σ₂) →ᵢ σ₁ →_{i·j} σ₃`, about the untyped term. -/
theorem compose_typing (σ₁ σ₂ σ₃ : Ty B R) (i j : R) :
    Has ![] 0 Tm.compose
      (.arr 1 (.arr i σ₂ σ₃) (.arr i (.arr j σ₁ σ₂) (.arr (i * j) σ₁ σ₃))) :=
  ⟨compose σ₁ σ₂ σ₃ i j, compose_erase σ₁ σ₂ σ₃ i j⟩

end NRT
