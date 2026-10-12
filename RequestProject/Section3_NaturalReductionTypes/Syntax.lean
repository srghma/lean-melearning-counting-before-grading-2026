module

public import Mathlib

/-!
# Well-scoped λ-terms

Untyped λ-terms are indexed by the number of free variables in scope:
`Tm n` is the type of terms whose free variables are among `0, …, n-1`
(de Bruijn indices, represented by `Fin n`).  In particular `Tm 0` is exactly the type
of **closed** terms.  Scoping is therefore correct by construction: there is no way to
write a term with a dangling index.

Renamings are maps `Fin n → Fin m`, parallel substitutions are maps `Fin n → Tm m`, and
the single substitution used by β-reduction is `t[u] = subst (Fin.cons u var) t`.
The usual fusion laws are proved, and β-reduction is shown to be stable under renaming
and substitution.
-/

@[expose] public section

namespace NRT

/-! ## Terms -/

/-- Untyped λ-terms with at most `n` free variables (de Bruijn indices in `Fin n`).
`Tm 0` is the type of closed terms. -/
inductive Tm : ℕ → Type
  | var {n : ℕ} : Fin n → Tm n
  | lam {n : ℕ} : Tm (n + 1) → Tm n
  | app {n : ℕ} : Tm n → Tm n → Tm n
  deriving DecidableEq

/-! ## Renaming and parallel substitution -/

/-- Lift a renaming under a binder. -/
def liftR {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cons 0 (fun i => (ρ i).succ)

@[simp] theorem liftR_zero {n m : ℕ} (ρ : Fin n → Fin m) : liftR ρ 0 = 0 := rfl
@[simp] theorem liftR_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    liftR ρ i.succ = (ρ i).succ := by simp [liftR]

/-- Apply a renaming. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : Tm n → Tm m
  | .var x => .var (ρ x)
  | .lam t => .lam (rename (liftR ρ) t)
  | .app t u => .app (rename ρ t) (rename ρ u)

/-- Lift a parallel substitution under a binder. -/
def liftS {n m : ℕ} (s : Fin n → Tm m) : Fin (n + 1) → Tm (m + 1) :=
  Fin.cons (.var 0) (fun i => rename Fin.succ (s i))

@[simp] theorem liftS_zero {n m : ℕ} (s : Fin n → Tm m) : liftS s 0 = .var 0 := rfl
@[simp] theorem liftS_succ {n m : ℕ} (s : Fin n → Tm m) (i : Fin n) :
    liftS s i.succ = rename Fin.succ (s i) := by simp [liftS]

/-- Apply a parallel substitution. -/
def subst {n m : ℕ} (s : Fin n → Tm m) : Tm n → Tm m
  | .var x => s x
  | .lam t => .lam (subst (liftS s) t)
  | .app t u => .app (subst s t) (subst s u)

/-- Single substitution `t[u]`: replace the bound variable `0` of `t` by `u`. -/
def inst {n : ℕ} (t : Tm (n + 1)) (u : Tm n) : Tm n := subst (Fin.cons u Tm.var) t

/-! ## Fusion laws -/

theorem rename_rename {n : ℕ} (t : Tm n) : ∀ {m k : ℕ} (ρ₁ : Fin n → Fin m) (ρ₂ : Fin m → Fin k),
    rename ρ₂ (rename ρ₁ t) = rename (ρ₂ ∘ ρ₁) t := by
  induction t with
  | var x => intros; rfl
  | lam t ih =>
    intro m k ρ₁ ρ₂
    simp only [rename, ih]
    congr 2; funext i; cases i using Fin.cases <;> simp
  | app t u iht ihu => intros; simp [rename, iht, ihu]

theorem liftR_id {n : ℕ} : liftR (id : Fin n → Fin n) = id := by
  funext i; cases i using Fin.cases <;> simp

theorem rename_id {n : ℕ} (t : Tm n) : rename id t = t := by
  induction t with
  | var x => rfl
  | lam t ih => simp only [rename, liftR_id, ih]
  | app t u iht ihu => simp [rename, iht, ihu]

theorem subst_rename {n : ℕ} (t : Tm n) : ∀ {m k : ℕ} (ρ : Fin n → Fin m) (s : Fin m → Tm k),
    subst s (rename ρ t) = subst (s ∘ ρ) t := by
  induction t with
  | var x => intros; rfl
  | lam t ih =>
    intro m k ρ s
    simp only [rename, subst, ih]
    congr 2; funext i; cases i using Fin.cases <;> simp
  | app t u iht ihu => intros; simp [rename, subst, iht, ihu]

theorem rename_subst {n : ℕ} (t : Tm n) : ∀ {m k : ℕ} (s : Fin n → Tm m) (ρ : Fin m → Fin k),
    rename ρ (subst s t) = subst (rename ρ ∘ s) t := by
  induction t with
  | var x => intros; rfl
  | lam t ih =>
    intro m k s ρ
    simp only [rename, subst, ih]
    congr 2; funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp only [Function.comp, liftS_succ, rename_rename]; rfl
  | app t u iht ihu => intros; simp [rename, subst, iht, ihu]

theorem liftS_comp {n m k : ℕ} (s₁ : Fin n → Tm m) (s₂ : Fin m → Tm k) :
    liftS (fun i => subst s₂ (s₁ i)) = fun i => subst (liftS s₂) (liftS s₁ i) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [liftS_succ, subst_rename, rename_subst]
    congr 1

theorem subst_subst {n : ℕ} (t : Tm n) : ∀ {m k : ℕ} (s₁ : Fin n → Tm m) (s₂ : Fin m → Tm k),
    subst s₂ (subst s₁ t) = subst (fun i => subst s₂ (s₁ i)) t := by
  induction t with
  | var x => intros; rfl
  | lam t ih =>
    intro m k s₁ s₂
    simp only [subst, ih, liftS_comp]
  | app t u iht ihu => intros; simp [subst, iht, ihu]

theorem liftS_var {n : ℕ} : liftS (Tm.var : Fin n → Tm n) = Tm.var := by
  funext i; cases i using Fin.cases <;> simp [rename]

theorem subst_var {n : ℕ} (t : Tm n) : subst Tm.var t = t := by
  induction t with
  | var x => rfl
  | lam t ih => simp only [subst, liftS_var, ih]
  | app t u iht ihu => simp [subst, iht, ihu]

/-- Instantiating a lifted substitution. -/
theorem inst_subst_liftS {n m : ℕ} (t : Tm (n + 1)) (s : Fin n → Tm m) (u : Tm m) :
    inst (subst (liftS s) t) u = subst (Fin.cons u s) t := by
  rw [inst, subst_subst]
  congr 1; funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [liftS_succ, subst_rename, Fin.cons_succ]
    convert subst_var (s i) using 2

theorem subst_inst {n m : ℕ} (s : Fin n → Tm m) (t : Tm (n + 1)) (u : Tm n) :
    subst s (inst t u) = inst (subst (liftS s) t) (subst s u) := by
  rw [inst_subst_liftS, inst, subst_subst]
  congr 1; funext i; cases i using Fin.cases <;> simp [subst]

theorem rename_inst {n m : ℕ} (ρ : Fin n → Fin m) (t : Tm (n + 1)) (u : Tm n) :
    rename ρ (inst t u) = inst (rename (liftR ρ) t) (rename ρ u) := by
  rw [inst, inst, rename_subst, subst_rename]
  congr 1; funext i; cases i using Fin.cases <;> simp [rename]

/-! ## β-reduction -/

/-- Full β-reduction (one step, anywhere in the term). -/
inductive Step : {n : ℕ} → Tm n → Tm n → Prop
  | beta {n : ℕ} (t : Tm (n + 1)) (u : Tm n) : Step (.app (.lam t) u) (inst t u)
  | lam {n : ℕ} {t t' : Tm (n + 1)} : Step t t' → Step (.lam t) (.lam t')
  | appL {n : ℕ} {t t' : Tm n} (u : Tm n) : Step t t' → Step (.app t u) (.app t' u)
  | appR {n : ℕ} (t : Tm n) {u u' : Tm n} : Step u u' → Step (.app t u) (.app t u')

/-- β-reduction is closed under renaming. -/
theorem Step.rename {n : ℕ} {t t' : Tm n} (h : Step t t') :
    ∀ {m : ℕ} (ρ : Fin n → Fin m), Step (NRT.rename ρ t) (NRT.rename ρ t') := by
  induction h with
  | beta t u => intro m ρ; rw [rename_inst]; exact Step.beta _ _
  | lam _ ih => intro m ρ; exact Step.lam (ih _)
  | appL u _ ih => intro m ρ; exact Step.appL _ (ih ρ)
  | appR t _ ih => intro m ρ; exact Step.appR _ (ih ρ)

/-- β-reduction is closed under parallel substitution. -/
theorem Step.subst {n : ℕ} {t t' : Tm n} (h : Step t t') :
    ∀ {m : ℕ} (s : Fin n → Tm m), Step (NRT.subst s t) (NRT.subst s t') := by
  induction h with
  | beta t u => intro m s; rw [subst_inst]; exact Step.beta _ _
  | lam _ ih => intro m s; exact Step.lam (ih _)
  | appL u _ ih => intro m s; exact Step.appL _ (ih s)
  | appR t _ ih => intro m s; exact Step.appR _ (ih s)

theorem Step.inst {n : ℕ} {t t' : Tm (n + 1)} (h : Step t t') (u : Tm n) :
    Step (NRT.inst t u) (NRT.inst t' u) := h.subst _

/-- Steps out of a renamed term come from steps of the original term. -/
theorem Step.of_rename {m : ℕ} {e e' : Tm m} (h : Step e e') :
    ∀ {n : ℕ} (ρ : Fin n → Fin m) (t : Tm n), NRT.rename ρ t = e →
      ∃ t', Step t t' ∧ NRT.rename ρ t' = e' := by
  induction h with
  | beta b u =>
    intro n ρ t ht
    cases t with
    | var x => cases ht
    | lam t => cases ht
    | app t₁ t₂ =>
      cases t₁ with
      | var x => cases ht
      | app _ _ => cases ht
      | lam b' =>
        simp only [NRT.rename, Tm.app.injEq, Tm.lam.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ⟨_, Step.beta b' t₂, rename_inst _ _ _⟩
  | lam _ ih =>
    intro n ρ t ht
    cases t with
    | var x => cases ht
    | app _ _ => cases ht
    | lam t =>
      simp only [NRT.rename, Tm.lam.injEq] at ht
      obtain ⟨t', hs, rfl⟩ := ih _ t ht
      exact ⟨_, Step.lam hs, rfl⟩
  | appL u _ ih =>
    intro n ρ t ht
    cases t with
    | var x => cases ht
    | lam _ => cases ht
    | app t₁ t₂ =>
      simp only [NRT.rename, Tm.app.injEq] at ht
      obtain ⟨h₁, rfl⟩ := ht
      obtain ⟨t', hs, rfl⟩ := ih ρ t₁ h₁
      exact ⟨_, Step.appL _ hs, rfl⟩
  | appR t _ ih =>
    intro n ρ t' ht
    cases t' with
    | var x => cases ht
    | lam _ => cases ht
    | app t₁ t₂ =>
      simp only [NRT.rename, Tm.app.injEq] at ht
      obtain ⟨rfl, h₂⟩ := ht
      obtain ⟨t', hs, rfl⟩ := ih ρ t₂ h₂
      exact ⟨_, Step.appR _ hs, rfl⟩

end NRT
