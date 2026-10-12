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

Terms are well scoped (`Tm n`), so reducibility is defined in Kripke style: a term of
arrow type is reducible if every renaming of it into a larger scope, applied to a
reducible argument, is reducible.
-/

@[expose] public section

namespace NRT

/-! ## Strong normalisation -/

/-- `t` is strongly normalising: there is no infinite β-reduction sequence from `t`. -/
def SN {n : ℕ} (t : Tm n) : Prop := Acc (fun b a => Step a b) t

theorem SN.step {n : ℕ} {t t' : Tm n} (h : SN t) (hs : Step t t') : SN t' := Acc.inv h hs

theorem SN.intro' {n : ℕ} {t : Tm n} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

theorem SN.of_app {n : ℕ} {t u : Tm n} (h : SN (.app t u)) : SN t := by
  suffices ∀ x, SN x → ∀ t, x = .app t u → SN t from this _ h t rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    rintro t rfl
    exact SN.intro' fun t' hs => ih _ (Step.appL u hs) t' rfl

theorem SN.of_rename {n m : ℕ} {ρ : Fin n → Fin m} {t : Tm n} (h : SN (rename ρ t)) :
    SN t := by
  suffices ∀ x, SN x → ∀ t, x = rename ρ t → SN t from this _ h t rfl
  intro x hx
  induction hx with
  | intro x _ ih =>
    rintro t rfl
    exact SN.intro' fun t' hs => ih _ (hs.rename ρ) t' rfl

theorem SN.rename {n m : ℕ} (ρ : Fin n → Fin m) {t : Tm n} (h : SN t) :
    SN (NRT.rename ρ t) := by
  induction h with
  | intro t _ ih =>
    refine SN.intro' fun e hs => ?_
    obtain ⟨t', hs', rfl⟩ := hs.of_rename ρ t rfl
    exact ih t' hs'

/-- Neutral terms: not an abstraction. -/
def Neutral {n : ℕ} : Tm n → Prop
  | .lam _ => False
  | _ => True

theorem Neutral.rename {n m : ℕ} (ρ : Fin n → Fin m) {t : Tm n} (h : Neutral t) :
    Neutral (NRT.rename ρ t) := by
  cases t with
  | var => trivial
  | lam => exact h.elim
  | app => trivial

theorem rename_liftS {n m k : ℕ} (ρ : Fin m → Fin k) (s : Fin n → Tm m) :
    (fun x => NRT.rename (liftR ρ) (liftS s x)) = liftS (fun x => NRT.rename ρ (s x)) := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
    simp only [liftS_succ, rename_rename]
    congr 1

/-! ## Reducibility candidates -/

variable {R : Type}

/-- Tait's reducibility predicate, by recursion on the (grade-erased) type, in Kripke
style over scopes. -/
def Red : Ty R → {n : ℕ} → Tm n → Prop
  | .base _, _, t => SN t
  | .arr _ σ τ, n, t =>
      ∀ {m : ℕ} (ρ : Fin n → Fin m) (u : Tm m), Red σ u → Red τ (.app (rename ρ t) u)

theorem var_no_step {n : ℕ} {x : Fin n} {t : Tm n} : ¬ Step (.var x) t := by
  intro h; cases h

/-- Reducibility is stable under renaming. -/
theorem Red.rename {τ : Ty R} {n m : ℕ} (ρ : Fin n → Fin m) {t : Tm n} (h : Red τ t) :
    Red τ (NRT.rename ρ t) := by
  cases τ with
  | base => exact SN.rename ρ h
  | arr b σ τ =>
    intro k ρ' u hu
    rw [rename_rename]
    exact h (ρ' ∘ ρ) u hu

/-- The three properties CR1–CR3 of reducibility candidates. -/
theorem cr (τ : Ty R) :
    (∀ {n : ℕ} (t : Tm n), Red τ t → SN t) ∧
    (∀ {n : ℕ} (t t' : Tm n), Red τ t → Step t t' → Red τ t') ∧
    (∀ {n : ℕ} (t : Tm n), Neutral t → (∀ t', Step t t' → Red τ t') → Red τ t) := by
  induction τ with
  | base n =>
    exact ⟨fun t h => h, fun t t' h hs => h.step hs, fun t _ h => SN.intro' h⟩
  | arr b σ τ ihσ ihτ =>
    obtain ⟨cr1σ, cr2σ, cr3σ⟩ := ihσ
    obtain ⟨cr1τ, cr2τ, cr3τ⟩ := ihτ
    refine ⟨?_, ?_, ?_⟩
    · intro n t h
      have hvar : Red σ (.var 0 : Tm (n + 1)) :=
        cr3σ _ trivial (fun t' hs => absurd hs var_no_step)
      exact (cr1τ _ (h Fin.succ _ hvar)).of_app.of_rename
    · intro n t t' h hs m ρ u hu
      exact cr2τ _ _ (h ρ u hu) (Step.appL u (hs.rename ρ))
    · intro n t hn h m ρ u hu
      have hsn : SN u := cr1σ u hu
      induction hsn with
      | intro u _ ih =>
        refine cr3τ (.app (NRT.rename ρ t) u) trivial ?_
        intro e hs
        generalize hr : NRT.rename ρ t = r at hs
        have hnr : Neutral r := hr ▸ hn.rename ρ
        cases hs with
        | beta => exact hnr.elim
        | appL _ hs =>
          obtain ⟨t', hst, rfl⟩ := hs.of_rename ρ t hr
          exact h t' hst ρ u hu
        | appR _ hs => subst hr; exact ih _ hs (cr2σ _ _ hu hs)

theorem red_var (τ : Ty R) {n : ℕ} (x : Fin n) : Red τ (.var x) :=
  (cr τ).2.2 _ trivial (fun _ hs => absurd hs var_no_step)

/-- The abstraction lemma. -/
theorem red_lam {σ τ : Ty R} {n : ℕ} {t : Tm (n + 1)} (hsn : SN t)
    (h : ∀ v, Red σ v → Red τ (inst t v)) {u : Tm n} (hu : Red σ u) :
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
          exact iht _ hs (fun v hv => (cr τ).2.1 _ _ (h v hv) (hs.inst v)) hu
            ((cr σ).1 u hu)
      | appR _ hs => exact ihu _ hs ((cr σ).2.1 _ _ hu hs)

/-- **Fundamental lemma**: a typeable term under a reducible substitution is reducible. -/
theorem red_fundamental [Semiring R] {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R} {t : Tm n}
    {τ : Ty R} (h : Has Γ V t τ) :
    ∀ {m : ℕ} (s : Fin n → Tm m), (∀ x, Red (Γ x) (s x)) → Red τ (subst s t) := by
  induction h with
  | var x => intro m s hs; exact hs x
  | @lam n Γ σ τ V t _ ih =>
    intro m s hs k ρ u hu
    simp only [subst, NRT.rename, rename_subst]
    rw [show (NRT.rename (liftR ρ) ∘ liftS s) = liftS (fun x => NRT.rename ρ (s x)) from
      rename_liftS ρ s]
    have hsub : ∀ v, Red σ v →
        Red τ (inst (subst (liftS fun x => NRT.rename ρ (s x)) t) v) := by
      intro v hv
      rw [inst_subst_liftS]
      exact ih _ (fun x => by
        cases x using Fin.cases with
        | zero => simpa using hv
        | succ x => simpa using (hs x).rename ρ)
    have hsn : SN (subst (liftS fun x => NRT.rename ρ (s x)) t) :=
      (cr τ).1 _ (ih _ (fun x => by
        cases x using Fin.cases with
        | zero => simpa using red_var σ 0
        | succ x => simpa [rename_rename] using (hs x).rename (Fin.succ ∘ ρ)))
    exact red_lam hsn hsub hu
  | app _ _ ih₁ ih₂ =>
    intro m s hs
    have := ih₁ s hs id _ (ih₂ s hs)
    rwa [rename_id] at this

/-- **Strong normalisation.** Every term typeable in natural reduction types (over any
grade semiring) is strongly normalising for full β-reduction. -/
theorem strong_normalization [Semiring R] {n : ℕ} {Γ : Fin n → Ty R} {V : Fin n → R}
    {t : Tm n} {τ : Ty R} (h : Has Γ V t τ) : SN t := by
  have := red_fundamental h Tm.var (fun x => red_var _ x)
  rw [subst_var] at this
  exact (cr τ).1 _ this

/-- `t` is β-normal. -/
def Normal {n : ℕ} (t : Tm n) : Prop := ∀ t', ¬ Step t t'

/-- A strongly normalising term reduces to a normal form. -/
theorem SN.exists_normal {n : ℕ} {t : Tm n} (h : SN t) :
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
theorem normal_form_head {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty ℕ}
    (h : Has Γ V t τ) :
    ∃ t', Relation.ReflTransGen Step t t' ∧ Normal t' ∧ Has Γ V t' τ ∧
      ∀ x, V x = 0 → ¬ HeadIs x t' := by
  obtain ⟨t', hr, hn⟩ := (strong_normalization h).exists_normal
  exact ⟨t', hr, hn, subject_reduction_star h hr, fun x hx => head_needed_sound h hx hr⟩

/-- In particular, every closed typeable term (`Tm 0`, empty context) has a β-normal
form of the same type. -/
theorem closed_normalizes [Semiring R] {t : Tm 0} {τ : Ty R} (h : Has ![] 0 t τ) :
    ∃ t', Relation.ReflTransGen Step t t' ∧ Normal t' ∧ Has ![] 0 t' τ := by
  obtain ⟨t', hr, hn⟩ := (strong_normalization h).exists_normal
  exact ⟨t', hr, hn, subject_reduction_star h hr⟩

end NRT
