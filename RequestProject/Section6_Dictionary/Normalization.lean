module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes

/-!
# Strong normalisation of natural reduction types (Curry–Howard–Tait)

The dictionary of the note pairs "Curry–Howard–Tait to relevant logic" with "generic
normalisation". This file proves, by Tait's reducibility method, that every term typeable
in natural reduction types is strongly normalising for full β-reduction — once, for an
arbitrary grade semiring (`NRT.strong_normalization`).

Combined with subject reduction and soundness for head neededness this gives
`NRT.normal_form_head`: over `ℕ`, a typeable term reduces to a β-normal form, and no
reduct of the term has a grade-`0` variable at its head.

The de Bruijn infrastructure (renaming, parallel substitution and their fusion laws)
is developed first and connected to the single substitution `NRT.subst` used by `Step`.
-/

@[expose] public section

namespace NRT

/-! ## Renaming and parallel substitution -/

/-- Lift a renaming under a binder. -/
def upR (ρ : ℕ → ℕ) : ℕ → ℕ := scons 0 (fun n => ρ n + 1)

/-- Apply a renaming. -/
def rename : (ℕ → ℕ) → Tm → Tm
  | ρ, .var n => .var (ρ n)
  | ρ, .lam t => .lam (rename (upR ρ) t)
  | ρ, .app t u => .app (rename ρ t) (rename ρ u)

/-- Lift a parallel substitution under a binder. -/
def upS (s : ℕ → Tm) : ℕ → Tm := scons (.var 0) (fun n => rename Nat.succ (s n))

/-- Apply a parallel substitution. -/
def psub : (ℕ → Tm) → Tm → Tm
  | s, .var n => s n
  | s, .lam t => .lam (psub (upS s) t)
  | s, .app t u => .app (psub s t) (psub s u)

theorem rename_rename (t : Tm) : ∀ ρ₁ ρ₂ : ℕ → ℕ,
    rename ρ₂ (rename ρ₁ t) = rename (ρ₂ ∘ ρ₁) t := by
  induction t with
  | var n => intros; rfl
  | lam t ih =>
    intro ρ₁ ρ₂
    simp only [rename, ih]
    congr 2; funext n; cases n <;> rfl
  | app t u iht ihu => intros; simp [rename, iht, ihu]

theorem psub_rename (t : Tm) : ∀ (ρ : ℕ → ℕ) (s : ℕ → Tm),
    psub s (rename ρ t) = psub (s ∘ ρ) t := by
  induction t with
  | var n => intros; rfl
  | lam t ih =>
    intro ρ s
    simp only [rename, psub, ih]
    congr 2; funext n; cases n <;> rfl
  | app t u iht ihu => intros; simp [rename, psub, iht, ihu]

theorem rename_psub (t : Tm) : ∀ (ρ : ℕ → ℕ) (s : ℕ → Tm),
    rename ρ (psub s t) = psub (rename ρ ∘ s) t := by
  induction t with
  | var n => intros; rfl
  | lam t ih =>
    intro ρ s
    simp only [rename, psub, ih]
    congr 2; funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Function.comp, upS, scons, rename_rename]
      rfl
  | app t u iht ihu => intros; simp [rename, psub, iht, ihu]

theorem upS_comp (s₁ s₂ : ℕ → Tm) :
    upS (fun n => psub s₂ (s₁ n)) = fun n => psub (upS s₂) (upS s₁ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [upS, scons, psub_rename, rename_psub]
    rfl

theorem psub_psub (t : Tm) : ∀ s₁ s₂ : ℕ → Tm,
    psub s₂ (psub s₁ t) = psub (fun n => psub s₂ (s₁ n)) t := by
  induction t with
  | var n => intros; rfl
  | lam t ih =>
    intro s₁ s₂
    simp only [psub, ih, upS_comp]
  | app t u iht ihu => intros; simp [psub, iht, ihu]

theorem psub_var (t : Tm) : ∀ s : ℕ → Tm, (∀ n, s n = .var n) → psub s t = t := by
  induction t with
  | var n => intro s hs; exact hs n
  | lam t ih =>
    intro s hs
    simp only [psub]
    rw [ih]
    intro n; cases n with
    | zero => rfl
    | succ n => simp [upS, scons, hs, rename]
  | app t u iht ihu => intro s hs; simp [psub, iht s hs, ihu s hs]

theorem shift_eq_rename (t : Tm) : ∀ c : ℕ,
    shift c t = rename (fun n => if n < c then n else n + 1) t := by
  induction t with
  | var n => intro c; simp only [shift, rename]; split_ifs <;> rfl
  | lam t ih =>
    intro c
    simp only [shift, rename, ih]
    congr 2; funext n
    cases n with
    | zero => simp [upR, scons]
    | succ n => simp only [upR, scons]; split_ifs <;> omega
  | app t u iht ihu => intro c; simp [shift, rename, iht, ihu]

theorem shift_zero_eq (t : Tm) : shift 0 t = rename Nat.succ t := by
  rw [shift_eq_rename]; rfl

theorem subst_eq_psub (t : Tm) : ∀ (k : ℕ) (u : Tm),
    subst k u t = psub (fun n => if n < k then .var n else if n = k then u else .var (n - 1))
      t := by
  induction t with
  | var n => intro k u; rfl
  | lam t ih =>
    intro k u
    simp only [subst, psub, ih]
    congr 2; funext n
    cases n with
    | zero => simp [upS, scons]
    | succ n =>
      simp only [upS, scons, shift_zero_eq]
      split_ifs <;> first | rfl | omega | (simp [rename]; omega)
  | app t u iht ihu => intro k v; simp [subst, psub, iht, ihu]

theorem subst0_eq_psub (u t : Tm) : subst 0 u t = psub (scons u Tm.var) t := by
  rw [subst_eq_psub]; congr 1; funext n; cases n <;> simp [scons]

/-- Substituting into a lifted substitution. -/
theorem subst0_psub_upS (u : Tm) (s : ℕ → Tm) (t : Tm) :
    subst 0 u (psub (upS s) t) = psub (scons u s) t := by
  rw [subst0_eq_psub, psub_psub]
  congr 1; funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [upS, scons, psub_rename]
    exact psub_var _ _ (fun _ => rfl)

theorem psub_subst0 (s : ℕ → Tm) (u t : Tm) :
    psub s (subst 0 u t) = subst 0 (psub s u) (psub (upS s) t) := by
  rw [subst0_psub_upS, subst0_eq_psub, psub_psub]
  congr 1; funext n; cases n <;> rfl

/-- β-reduction is closed under parallel substitution. -/
theorem step_psub {t t' : Tm} (h : Step t t') (s : ℕ → Tm) : Step (psub s t) (psub s t') := by
  induction h generalizing s with
  | beta t u =>
    rw [psub_subst0]; exact Step.beta _ _
  | lam _ ih => exact Step.lam (ih _)
  | appL u _ ih => exact Step.appL _ (ih s)
  | appR t _ ih => exact Step.appR _ (ih s)

theorem step_subst0 {t t' : Tm} (h : Step t t') (u : Tm) : Step (subst 0 u t) (subst 0 u t') := by
  rw [subst0_eq_psub, subst0_eq_psub]; exact step_psub h _

/-! ## Strong normalisation -/

/-- `t` is strongly normalising: there is no infinite β-reduction sequence from `t`. -/
def SN (t : Tm) : Prop := Acc (fun b a => Step a b) t

theorem SN.step {t t' : Tm} (h : SN t) (hs : Step t t') : SN t' := Acc.inv h hs

theorem SN.intro' {t : Tm} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

theorem SN.of_app {t u : Tm} (h : SN (.app t u)) : SN t := by
  suffices ∀ x, SN x → ∀ t, x = .app t u → SN t from this _ h t rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    rintro t rfl
    exact SN.intro' fun t' hs => ih _ (Step.appL u hs) t' rfl

theorem SN.of_subst0 {t u : Tm} (h : SN (subst 0 u t)) : SN t := by
  suffices ∀ x, SN x → ∀ t, x = subst 0 u t → SN t from this _ h t rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    rintro t rfl
    exact SN.intro' fun t' hs => ih _ (step_subst0 hs u) t' rfl

/-- Neutral terms: not an abstraction. -/
def Neutral : Tm → Prop
  | .lam _ => False
  | _ => True

/-! ## Reducibility candidates -/

variable {R : Type}

/-- Tait's reducibility predicate, by recursion on the (grade-erased) type. -/
def Red : Ty R → Tm → Prop
  | .base _, t => SN t
  | .arr _ σ τ, t => ∀ u, Red σ u → Red τ (.app t u)

theorem var_no_step {n : ℕ} {t : Tm} : ¬ Step (.var n) t := by
  intro h; cases h

/-- The three properties CR1–CR3 of reducibility candidates. -/
theorem cr (τ : Ty R) :
    (∀ t, Red τ t → SN t) ∧ (∀ t t', Red τ t → Step t t' → Red τ t') ∧
      (∀ t, Neutral t → (∀ t', Step t t' → Red τ t') → Red τ t) := by
  induction τ with
  | base n =>
    refine ⟨fun t h => h, fun t t' h hs => h.step hs, fun t _ h => SN.intro' h⟩
  | arr b σ τ ihσ ihτ =>
    obtain ⟨cr1σ, cr2σ, cr3σ⟩ := ihσ
    obtain ⟨cr1τ, cr2τ, cr3τ⟩ := ihτ
    have hvar : Red σ (.var 0) := cr3σ _ trivial (fun t' hs => absurd hs var_no_step)
    refine ⟨?_, ?_, ?_⟩
    · intro t h
      exact (cr1τ _ (h _ hvar)).of_app
    · intro t t' h hs u hu
      exact cr2τ _ _ (h u hu) (Step.appL u hs)
    · intro t hn h u hu
      have hsn : SN u := cr1σ u hu
      induction hsn with
      | intro u _ ih =>
        refine cr3τ (.app t u) trivial ?_
        intro t' hs
        cases hs with
        | beta => exact absurd hn id
        | appL _ hs => exact h _ hs u hu
        | appR _ hs => exact ih _ hs (cr2σ _ _ hu hs)

theorem red_var (τ : Ty R) (n : ℕ) : Red τ (.var n) :=
  (cr τ).2.2 _ trivial (fun _ hs => absurd hs var_no_step)

/-- The abstraction lemma. -/
theorem red_lam {σ τ : Ty R} {t : Tm} (hsn : SN t)
    (h : ∀ v, Red σ v → Red τ (subst 0 v t)) {u : Tm} (hu : Red σ u) :
    Red τ (.app (.lam t) u) := by
  have hu' : SN u := (cr σ).1 u hu
  induction hsn generalizing u with
  | intro t _ iht =>
    induction hu' with
    | intro u _ ihu =>
      refine (cr τ).2.2 (.app (.lam t) u) trivial ?_
      intro t' hs
      cases hs with
      | beta => exact h u hu
      | appL _ hs =>
        cases hs with
        | lam hs =>
          exact iht _ hs (fun v hv => (cr τ).2.1 _ _ (h v hv) (step_subst0 hs v)) hu
            ((cr σ).1 u hu)
      | appR _ hs => exact ihu _ hs ((cr σ).2.1 _ _ hu hs)

/-- **Fundamental lemma**: a typeable term under a reducible substitution is reducible. -/
theorem red_fundamental [Semiring R] {Γ : ℕ → Ty R} {V : ℕ → R} {t : Tm} {τ : Ty R} (h : Has Γ V t τ) :
    ∀ s : ℕ → Tm, (∀ n, Red (Γ n) (s n)) → Red τ (psub s t) := by
  induction h with
  | var n => intro s hs; exact hs n
  | @lam Γ σ τ V t _ ih =>
    intro s hs
    have hsub : ∀ v, Red σ v → Red τ (subst 0 v (psub (upS s) t)) := by
      intro v hv
      rw [subst0_psub_upS]
      exact ih _ (fun n => by cases n with | zero => exact hv | succ n => exact hs n)
    have hsn : SN (psub (upS s) t) := ((cr τ).1 _ (hsub _ (red_var σ 0))).of_subst0
    intro u hu
    exact red_lam hsn hsub hu
  | app _ _ ih₁ ih₂ => intro s hs; exact ih₁ s hs _ (ih₂ s hs)

/-- **Strong normalisation.** Every term typeable in natural reduction types (over any
grade semiring) is strongly normalising for full β-reduction. -/
theorem strong_normalization [Semiring R] {Γ : ℕ → Ty R} {V : ℕ → R} {t : Tm} {τ : Ty R}
    (h : Has Γ V t τ) : SN t := by
  have := red_fundamental h Tm.var (fun n => red_var _ n)
  rw [psub_var t _ (fun _ => rfl)] at this
  exact (cr τ).1 _ this

/-- `t` is β-normal. -/
def Normal (t : Tm) : Prop := ∀ t', ¬ Step t t'

/-- A strongly normalising term reduces to a normal form. -/
theorem SN.exists_normal {t : Tm} (h : SN t) :
    ∃ t', Relation.ReflTransGen Step t t' ∧ Normal t' := by
  induction h with
  | intro t _ ih =>
    by_cases hn : Normal t
    · exact ⟨t, .refl, hn⟩
    · simp only [Normal, not_forall, not_not] at hn
      obtain ⟨t₁, hs⟩ := hn
      obtain ⟨t', hr, hn'⟩ := ih t₁ hs
      exact ⟨t', Relation.ReflTransGen.head hs hr, hn'⟩

/-- **Normalisation with head neededness** (grades in `ℕ`). A typeable term reduces to a
β-normal form of the same type and neededness function, and no reduct — in particular not
the normal form — has a variable of grade `0` at its head. -/
theorem normal_form_head {Γ : ℕ → Ty ℕ} {V : ℕ → ℕ} {t : Tm} {τ : Ty ℕ}
    (h : Has Γ V t τ) :
    ∃ t', Relation.ReflTransGen Step t t' ∧ Normal t' ∧ Has Γ V t' τ ∧
      ∀ x, V x = 0 → ¬ HeadIs x t' := by
  obtain ⟨t', hr, hn⟩ := (strong_normalization h).exists_normal
  exact ⟨t', hr, hn, subject_reduction_star h hr, fun x hx => head_needed_sound h hx hr⟩

end NRT
