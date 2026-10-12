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
from the `n` hypotheses `Γ : Fin n → Fm`, using exactly the hypotheses in `U`. -/
inductive Rel : {n : ℕ} → (Fin n → Fm) → (Fin n → Prop) → Fm → Prop
  | hyp {n : ℕ} {Γ : Fin n → Fm} (x : Fin n) : Rel Γ (· = x) (Γ x)
  | impI {n : ℕ} {Γ : Fin n → Fm} {U : Fin (n + 1) → Prop} {A B : Fm} :
      Rel (Fin.cons A Γ) U B → U 0 → Rel Γ (fun x => U x.succ) (.imp A B)
  | impE {n : ℕ} {Γ : Fin n → Fm} {U U' : Fin n → Prop} {A B : Fm} :
      Rel Γ U (.imp A B) → Rel Γ U' A → Rel Γ (fun x => U x ∨ U' x) B

/-- `A` is a theorem of `R→`: derivable from the empty set of hypotheses. -/
def RTheorem (A : Fm) : Prop := Rel ![] (fun _ => False) A

theorem Rel.congr {n : ℕ} {Γ Γ' : Fin n → Fm} {U U' : Fin n → Prop} {A : Fm} (h : Rel Γ U A)
    (hΓ : Γ = Γ') (hU : U = U') : Rel Γ' U' A := hΓ ▸ hU ▸ h

/-! ## Grade erasure and the positively graded fragment -/

/-- Erase the grades of a natural reduction type. -/
def Ty.erase {R : Type} : Ty R → Fm
  | .base n => .atom n
  | .arr _ σ τ => .imp σ.erase τ.erase

/-- The positively graded fragment of natural reduction types over `ℕ`: the same rules
as `Has`, but every arrow introduced or eliminated carries a grade `≥ 1`. -/
inductive PHas : {n : ℕ} → (Fin n → Ty ℕ) → (Fin n → ℕ) → Tm n → Ty ℕ → Prop
  | var {n : ℕ} {Γ : Fin n → Ty ℕ} (x : Fin n) : PHas Γ (single x) (.var x) (Γ x)
  | lam {n : ℕ} {Γ : Fin n → Ty ℕ} {σ τ : Ty ℕ} {V : Fin (n + 1) → ℕ} {t : Tm (n + 1)} :
      PHas (Fin.cons σ Γ) V t τ → V 0 ≠ 0 →
      PHas Γ (fun x => V x.succ) (.lam t) (.arr (V 0) σ τ)
  | app {n : ℕ} {Γ : Fin n → Ty ℕ} {σ τ : Ty ℕ} {b : ℕ} {V₁ V₂ : Fin n → ℕ} {t u : Tm n} :
      PHas Γ V₁ t (.arr b σ τ) → PHas Γ V₂ u σ → b ≠ 0 →
      PHas Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ

/-- The positively graded fragment is a fragment of natural reduction types. -/
theorem PHas.toHas {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty ℕ}
    (h : PHas Γ V t τ) :
    Has Γ V t τ := by
  induction h with
  | var x => exact Has.var x
  | lam _ _ ih => exact Has.lam ih
  | app _ _ _ ih₁ ih₂ => exact Has.app ih₁ ih₂

theorem erase_cons {n : ℕ} (σ : Ty ℕ) (Γ : Fin n → Ty ℕ) :
    (fun x => ((Fin.cons σ Γ : Fin (n + 1) → Ty ℕ) x).erase) = Fin.cons σ.erase (fun x => (Γ x).erase) := by
  funext x; cases x using Fin.cases <;> simp

/-- **Curry–Howard, soundness.** Erasing the grades of a positively graded natural
reduction typing gives a derivation in relevant implication `R→` whose set of used
hypotheses is exactly the support `{x | V x ≠ 0}` of the neededness function. -/
theorem PHas.toRel {n : ℕ} {Γ : Fin n → Ty ℕ} {V : Fin n → ℕ} {t : Tm n} {τ : Ty ℕ}
    (h : PHas Γ V t τ) :
    Rel (fun x => (Γ x).erase) (fun x => V x ≠ 0) τ.erase := by
  induction h with
  | var x =>
    refine (Rel.hyp x).congr rfl ?_
    funext y; simp [single]
  | @lam n Γ σ τ V t _ h0 ih =>
    rw [erase_cons] at ih
    exact Rel.impI ih h0
  | @app n Γ σ τ b V₁ V₂ t u _ _ hb ih₁ ih₂ =>
    refine (Rel.impE ih₁ ih₂).congr rfl ?_
    funext x; simp [hb]; tauto

/-- A positively graded typing of a closed term erases to a theorem of `R→`. -/
theorem PHas.toRTheorem {t : Tm 0} {τ : Ty ℕ} (h : PHas ![] 0 t τ) :
    RTheorem τ.erase :=
  h.toRel.congr (funext fun x => x.elim0) (funext fun x => x.elim0)

/-! ## Examples: `I`, `B`, `W` and `Twice` -/

/-- `W = λf x. f x x`. -/
def wcomb : Tm 0 := .lam (.lam (.app (.app (.var 1) (.var 0)) (.var 0)))

/-- `W : (σ →ᵢ σ →ⱼ τ) →₁ σ →_{i+j} τ`, positively graded when `i, j ≥ 1`. -/
theorem wcomb_typing (σ τ : Ty ℕ) (i j : ℕ) (hi : i ≠ 0) (hj : j ≠ 0) :
    PHas ![] 0 wcomb (.arr 1 (.arr i σ (.arr j σ τ)) (.arr (i + j) σ τ)) := by
  have h := PHas.lam (PHas.lam (PHas.app (PHas.app (PHas.var (Γ := Fin.cons σ (Fin.cons
    (.arr i σ (.arr j σ τ)) ![])) 1) (PHas.var 0) hi) (PHas.var 0) hj) (by simp [single]; omega)
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
  exact (wcomb_typing σ τ 1 1 one_ne_zero one_ne_zero).toRTheorem

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
noncomputable def usedVals {n : ℕ} (v : ℕ → Sug) (Γ : Fin n → Fm) (U : Fin n → Prop) :
    Finset Sug :=
  Finset.univ.filter (fun a => ∃ x, U x ∧ (Γ x).sval v = a)

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
theorem rel_sound_sugihara {n : ℕ} {Γ : Fin n → Fm} {U : Fin n → Prop} {A : Fm}
    (h : Rel Γ U A)
    (v : ℕ → Sug) : Sug.le ((usedVals v Γ U).prod id) (A.sval v) := by
  classical
  induction h with
  | @hyp n Γ x =>
    have : usedVals v Γ (· = x) = {(Γ x).sval v} := by
      ext a; simp [usedVals, eq_comm]
    rw [this, Finset.prod_singleton]; exact Sug.le_refl' _
  | @impI n Γ U A B _ h0 ih =>
    have e : usedVals v (Fin.cons A Γ) U =
        insert (A.sval v) (usedVals v Γ (fun x => U x.succ)) := by
      ext a
      simp only [usedVals, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨x, hx, rfl⟩
        cases x using Fin.cases with
        | zero => left; simp
        | succ x => right; exact ⟨x, hx, by simp⟩
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨0, h0, by simp⟩
        · exact ⟨x.succ, hx, by simp⟩
    rw [e, Finset.insert_eq, prod_union_idem, Finset.prod_singleton] at ih
    exact (Sug.residuation _ _ _).mp ih
  | @impE n Γ U U' A B _ _ ih₁ ih₂ =>
    have e : usedVals v Γ (fun x => U x ∨ U' x) = usedVals v Γ U ∪ usedVals v Γ U' := by
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
  intro h
  have := rel_sound_sugihara h (fun n => if n = 0 then .zero else .pos)
  have e : usedVals (fun n => if n = 0 then .zero else .pos) ![] (fun _ => False) = ∅ := by
    ext a; simp [usedVals]
  rw [e, Finset.prod_empty] at this
  exact Sug.one_not_le this

/-- `K` erases to `A → B → A`, so its typing `σ →₁ τ →₀ σ` has no positively graded
counterpart. -/
theorem K_not_positive :
    ¬ PHas ![] 0 K (.arr 1 (.base 0) (.arr 0 (.base 1) (.base 0))) :=
  fun h => rel_not_K h.toRTheorem

end NRT
