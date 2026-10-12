module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes

/-!
# Natural reduction types and relevant implication (Section 3, Curry–Howard)

The note states that the 1993 discipline comes "with Curry–Howard to the implicational
fragment of relevant logic". This file makes the soundness half of that link precise.

* `NRT.Fm` are implicational formulas and `NRT.Rel Γ U A` is the labelled
  (Anderson–Belnap style) natural deduction for relevant implication `R→`: the label
  `U` is the set of hypotheses actually used, implication introduction may only discharge
  a hypothesis that *was* used, and implication elimination takes the union of labels.
  A theorem of `R→` is a derivation with the empty label.
* `NRT.PHas` is the positively graded fragment of natural reduction types over `ℕ`
  (every arrow that is introduced or eliminated has grade `≥ 1`); it is a sub-system
  of `NRT.Has` (`NRT.PHas.toHas`).
* `NRT.PHas.toRel` (**Curry–Howard, soundness**): erasing the grades of a positively
  graded derivation gives an `R→` derivation whose label is *exactly* the support of
  the neededness function, `{x | V x ≠ 0}`.
* The grade `0` is what takes the full system beyond relevant logic: `K : σ →₁ τ →₀ σ`
  is typeable (`NRT.K_typing`) but `A → B → A` is not a theorem of `R→`
  (`NRT.rel_not_K`), shown by soundness of `R→` for the three-element Sugihara monoid
  (`NRT.rel_sound_sugihara`).
-/

@[expose] public section

namespace NRT

/-! ## Relevant implication -/

/-- Implicational formulas. -/
inductive Fm : Type
  | atom : ℕ → Fm
  | imp : Fm → Fm → Fm
  deriving DecidableEq

/-- Labelled natural deduction for relevant implication `R→`. `Rel Γ U A`: `A` is derivable
from the hypotheses `Γ` (indexed by `ℕ`), using exactly the hypotheses in `U`. -/
inductive Rel : (ℕ → Fm) → (ℕ → Prop) → Fm → Prop
  | hyp {Γ : ℕ → Fm} (n : ℕ) : Rel Γ (· = n) (Γ n)
  | impI {Γ : ℕ → Fm} {U : ℕ → Prop} {A B : Fm} :
      Rel (scons A Γ) U B → U 0 → Rel Γ (fun n => U (n + 1)) (.imp A B)
  | impE {Γ : ℕ → Fm} {U U' : ℕ → Prop} {A B : Fm} :
      Rel Γ U (.imp A B) → Rel Γ U' A → Rel Γ (fun n => U n ∨ U' n) B

/-- `A` is a theorem of `R→`: derivable using no hypotheses. -/
def RTheorem (A : Fm) : Prop := ∃ Γ : ℕ → Fm, Rel Γ (fun _ => False) A

theorem Rel.congr {Γ : ℕ → Fm} {U U' : ℕ → Prop} {A : Fm} (h : Rel Γ U A) (hU : U = U') :
    Rel Γ U' A := hU ▸ h

/-! ## Grade erasure and the positively graded fragment -/

/-- Erase the grades of a natural reduction type. -/
def Ty.erase {R : Type} : Ty R → Fm
  | .base n => .atom n
  | .arr _ σ τ => .imp σ.erase τ.erase

/-- The positively graded fragment of natural reduction types over `ℕ`: the same rules
as `Has`, but every arrow introduced or eliminated carries a grade `≥ 1`. -/
inductive PHas : (ℕ → Ty ℕ) → (ℕ → ℕ) → Tm → Ty ℕ → Prop
  | var {Γ : ℕ → Ty ℕ} (n : ℕ) : PHas Γ (single n) (.var n) (Γ n)
  | lam {Γ : ℕ → Ty ℕ} {σ τ : Ty ℕ} {V : ℕ → ℕ} {t : Tm} :
      PHas (scons σ Γ) V t τ → V 0 ≠ 0 →
      PHas Γ (fun n => V (n + 1)) (.lam t) (.arr (V 0) σ τ)
  | app {Γ : ℕ → Ty ℕ} {σ τ : Ty ℕ} {b : ℕ} {V₁ V₂ : ℕ → ℕ} {t u : Tm} :
      PHas Γ V₁ t (.arr b σ τ) → PHas Γ V₂ u σ → b ≠ 0 →
      PHas Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ

/-- The positively graded fragment is a fragment of natural reduction types. -/
theorem PHas.toHas {Γ : ℕ → Ty ℕ} {V : ℕ → ℕ} {t : Tm} {τ : Ty ℕ} (h : PHas Γ V t τ) :
    Has Γ V t τ := by
  induction h with
  | var n => exact Has.var n
  | lam _ _ ih => exact Has.lam ih
  | app _ _ _ ih₁ ih₂ => exact Has.app ih₁ ih₂

theorem erase_scons (σ : Ty ℕ) (Γ : ℕ → Ty ℕ) :
    (fun n => (scons σ Γ n).erase) = scons σ.erase (fun n => (Γ n).erase) := by
  funext n; cases n <;> rfl

/-- **Curry–Howard, soundness.** Erasing the grades of a positively graded natural
reduction typing gives a derivation in relevant implication `R→` whose set of used
hypotheses is exactly the support `{x | V x ≠ 0}` of the neededness function. -/
theorem PHas.toRel {Γ : ℕ → Ty ℕ} {V : ℕ → ℕ} {t : Tm} {τ : Ty ℕ} (h : PHas Γ V t τ) :
    Rel (fun n => (Γ n).erase) (fun n => V n ≠ 0) τ.erase := by
  induction h with
  | var n =>
    refine (Rel.hyp n).congr ?_
    funext m; simp [single]
  | @lam Γ σ τ V t _ h0 ih =>
    rw [erase_scons] at ih
    exact Rel.impI ih h0
  | @app Γ σ τ b V₁ V₂ t u _ _ hb ih₁ ih₂ =>
    refine (Rel.impE ih₁ ih₂).congr ?_
    funext n; simp [hb]; tauto

/-- A closed positively graded typing (no variable needed) erases to a theorem of `R→`. -/
theorem PHas.toRTheorem {Γ : ℕ → Ty ℕ} {t : Tm} {τ : Ty ℕ} (h : PHas Γ 0 t τ) :
    RTheorem τ.erase :=
  ⟨_, h.toRel.congr (by funext n; simp)⟩

/-! ## Examples: `I`, `B`, `W` and `Twice` -/

/-- `W = λf x. f x x`. -/
def wcomb : Tm := .lam (.lam (.app (.app (.var 1) (.var 0)) (.var 0)))

/-- `W : (σ →ᵢ σ →ⱼ τ) →₁ σ →_{i+j} τ`, positively graded when `i, j ≥ 1`. -/
theorem wcomb_typing (Γ : ℕ → Ty ℕ) (σ τ : Ty ℕ) (i j : ℕ) (hi : i ≠ 0) (hj : j ≠ 0) :
    PHas Γ 0 wcomb (.arr 1 (.arr i σ (.arr j σ τ)) (.arr (i + j) σ τ)) := by
  have h := PHas.lam (PHas.lam (PHas.app (PHas.app (PHas.var (Γ := scons σ (scons
    (.arr i σ (.arr j σ τ)) Γ)) 1) (PHas.var 0) hi) (PHas.var 0) hj) (by simp [single]; omega)
    ) (by simp [single])
  convert h using 2
  simp [single]

/-- The contraction axiom `(A → A → B) → A → B` of `R→`, read off from the typing of `W`. -/
theorem rtheorem_W (A B : Fm) : RTheorem (.imp (.imp A (.imp A B)) (.imp A B)) := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Ty ℕ, σ.erase = A := by
    induction A with
    | atom n => exact ⟨.base n, rfl⟩
    | imp A B ihA ihB =>
      obtain ⟨σ, rfl⟩ := ihA; obtain ⟨τ, rfl⟩ := ihB; exact ⟨.arr 1 σ τ, rfl⟩
  obtain ⟨τ, rfl⟩ : ∃ τ : Ty ℕ, τ.erase = B := by
    induction B with
    | atom n => exact ⟨.base n, rfl⟩
    | imp A B ihA ihB =>
      obtain ⟨σ, rfl⟩ := ihA; obtain ⟨τ, rfl⟩ := ihB; exact ⟨.arr 1 σ τ, rfl⟩
  exact (wcomb_typing (fun _ => σ) σ τ 1 1 one_ne_zero one_ne_zero).toRTheorem

/-! ## The Sugihara countermodel: `K` is not a theorem of `R→` -/

/-- The three-element Sugihara monoid `{-1, 0, 1}`. -/
inductive Sug : Type
  | neg | zero | pos
  deriving DecidableEq, Fintype

namespace Sug

/-- Integer value. -/
def toInt : Sug → ℤ
  | neg => -1
  | zero => 0
  | pos => 1

/-- Fusion: the element of larger absolute value, and the minimum on ties. -/
def mul : Sug → Sug → Sug
  | zero, b => b
  | a, zero => a
  | pos, pos => pos
  | _, _ => neg

/-- Implication (the residual of fusion). -/
def imp : Sug → Sug → Sug
  | neg, _ => pos
  | zero, neg => neg
  | zero, zero => zero
  | zero, pos => pos
  | pos, pos => pos
  | pos, _ => neg

/-- The order `-1 < 0 < 1`. -/
def le (a b : Sug) : Prop := a.toInt ≤ b.toInt

instance (a b : Sug) : Decidable (le a b) := inferInstanceAs (Decidable (_ ≤ _))

instance : CommMonoid Sug where
  mul := mul
  one := zero
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide

theorem mul_idem (a : Sug) : a * a = a := by revert a; decide

theorem le_refl' (a : Sug) : le a a := by revert a; decide

theorem residuation (a b c : Sug) : le (a * c) b ↔ le c (imp a b) := by
  revert a b c; decide

theorem modus_ponens (a b c d : Sug) (h₁ : le c (imp a b)) (h₂ : le d a) : le (c * d) b := by
  revert a b c d; decide

theorem one_not_le : ¬ le 1 (imp zero (imp pos zero)) := by decide

end Sug

/-- Interpretation of formulas in the Sugihara monoid under a valuation of atoms. -/
def Fm.sval (v : ℕ → Sug) : Fm → Sug
  | .atom n => v n
  | .imp A B => Sug.imp (A.sval v) (B.sval v)

open Classical in
/-- The set of values of the used hypotheses. -/
noncomputable def usedVals (v : ℕ → Sug) (Γ : ℕ → Fm) (U : ℕ → Prop) : Finset Sug :=
  Finset.univ.filter (fun a => ∃ n, U n ∧ (Γ n).sval v = a)

theorem prod_union_idem (s t : Finset Sug) : (s ∪ t).prod id = s.prod id * t.prod id := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.insert_union, Finset.prod_insert ha]
    by_cases hat : a ∈ s ∪ t
    · rw [Finset.insert_eq_of_mem hat, ih]
      rcases Finset.mem_union.mp hat with h | h
      · exact absurd h ha
      · rw [← Finset.mul_prod_erase t id h]
        simp only [id]
        rw [mul_comm a (s.prod _), mul_assoc, ← mul_assoc a a, Sug.mul_idem]
    · rw [Finset.prod_insert hat, ih, mul_assoc]

/-- **Soundness of `R→` for the Sugihara monoid**: the fusion of the values of the used
hypotheses is below the value of the conclusion. -/
theorem rel_sound_sugihara {Γ : ℕ → Fm} {U : ℕ → Prop} {A : Fm} (h : Rel Γ U A)
    (v : ℕ → Sug) : Sug.le ((usedVals v Γ U).prod id) (A.sval v) := by
  classical
  induction h with
  | @hyp Γ n =>
    have : usedVals v Γ (· = n) = {(Γ n).sval v} := by
      ext a; simp [usedVals, eq_comm]
    rw [this, Finset.prod_singleton]; exact Sug.le_refl' _
  | @impI Γ U A B _ h0 ih =>
    have e : usedVals v (scons A Γ) U =
        insert (A.sval v) (usedVals v Γ (fun n => U (n + 1))) := by
      ext a
      simp only [usedVals, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨n, hn, rfl⟩
        cases n with
        | zero => left; rfl
        | succ n => right; exact ⟨n, hn, rfl⟩
      · rintro (rfl | ⟨n, hn, rfl⟩)
        · exact ⟨0, h0, rfl⟩
        · exact ⟨n + 1, hn, rfl⟩
    rw [e, Finset.insert_eq, prod_union_idem, Finset.prod_singleton] at ih
    exact (Sug.residuation _ _ _).mp ih
  | @impE Γ U U' A B _ _ ih₁ ih₂ =>
    have e : usedVals v Γ (fun n => U n ∨ U' n) = usedVals v Γ U ∪ usedVals v Γ U' := by
      ext a; simp only [usedVals, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · rintro ⟨n, hn | hn, rfl⟩
        · exact Or.inl ⟨n, hn, rfl⟩
        · exact Or.inr ⟨n, hn, rfl⟩
      · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
        · exact ⟨n, Or.inl hn, rfl⟩
        · exact ⟨n, Or.inr hn, rfl⟩
    rw [e, prod_union_idem]
    exact Sug.modus_ponens _ _ _ _ ih₁ ih₂

/-- **`K` is not relevant.** `A → B → A` is not a theorem of relevant implication (for
distinct atoms `A`, `B`), although `K : σ →₁ τ →₀ σ` is typeable in natural reduction types:
the grade `0` is what takes the full system beyond `R→`. -/
theorem rel_not_K : ¬ RTheorem (.imp (.atom 0) (.imp (.atom 1) (.atom 0))) := by
  rintro ⟨Γ, h⟩
  have := rel_sound_sugihara h (fun n => if n = 0 then .zero else .pos)
  have e : usedVals (fun n => if n = 0 then .zero else .pos) Γ (fun _ => False) = ∅ := by
    ext a; simp [usedVals]
  rw [e, Finset.prod_empty] at this
  exact Sug.one_not_le this

/-- `K` erases to `A → B → A`, so its typing `σ →₁ τ →₀ σ` has no positively graded
counterpart. -/
theorem K_not_positive (Γ : ℕ → Ty ℕ) :
    ¬ PHas Γ 0 K (.arr 1 (.base 0) (.arr 0 (.base 1) (.base 0))) :=
  fun h => rel_not_K h.toRTheorem

end NRT
