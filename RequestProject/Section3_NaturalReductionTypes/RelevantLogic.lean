module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes

/-!
# Natural reduction types and relevant implication (Section 3, Curry–Howard)

The note states that the 1993 discipline comes "with Curry–Howard to the implicational
fragment of relevant logic". This file makes the soundness half of that link precise.

* `NRT.Fm B` are implicational formulas over atoms indexed by `B`.  Relevant implication `R→` is given as a grammar
  of proof terms: `NRT.RPf Γ U A` is the type of (labelled, Anderson–Belnap style)
  natural-deduction proofs of `A` from hypotheses `Γ : Fin n → Fm B` using exactly the
  hypotheses in `U`.  Implication introduction may only discharge a hypothesis that *was*
  used, and implication elimination takes the union of labels.  Derivability `NRT.Rel`
  is inhabitedness of `RPf`; a theorem of `R→` is a proof with the empty label.
* `NRT.GTm.Positive` singles out the positively graded typed terms over `ℕ` (every arrow
  introduced or eliminated has grade `≥ 1`).
* `NRT.GTm.toRPf` (**Curry–Howard, soundness**): erasing the grades of a positively graded
  typed term gives a proof term of `R→` — with the *same* underlying λ-term
  (`NRT.GTm.toRPf_erase`) — whose label is *exactly* the support of the neededness
  function, `{x | V x ≠ 0}`.
* The grade `0` is what takes the full system beyond relevant logic: `K : σ →₁ τ →₀ σ`
  is a typed term (`NRT.K`) but `A → B → A` is not a theorem of `R→`
  (`NRT.rel_not_K`), shown by soundness of `R→` for the three-element Sugihara monoid
  (`NRT.rel_sound_sugihara`); hence no closed typed term of that type is positively graded
  (`NRT.K_not_positive`).
-/

@[expose] public section

namespace NRT

variable {B : Type}

/-! ## Relevant implication: the grammar of proof terms -/

/-- Implicational formulas. -/
inductive Fm (B : Type) : Type
  | atom : B → Fm B
  | imp : Fm B → Fm B → Fm B
  deriving DecidableEq

/-- **Relevant implication `R→`, as a grammar of proof terms.**  `RPf Γ U A` is the type
of (labelled, Anderson–Belnap style) natural-deduction proofs of `A` from the `n`
hypotheses `Γ : Fin n → Fm B` that use *exactly* the hypotheses in `U`.  Implication
introduction may only discharge a hypothesis that was used; implication elimination takes
the union of the labels. -/
inductive RPf : {n : ℕ} → (Fin n → Fm B) → (Fin n → Prop) → Fm B → Type
  | hyp {n : ℕ} {Γ : Fin n → Fm B} (x : Fin n) : RPf Γ (· = x) (Γ x)
  | impI {n : ℕ} {Γ : Fin n → Fm B} {U : Fin (n + 1) → Prop} {A C : Fm B} :
      RPf (Fin.cons A Γ) U C → U 0 → RPf Γ (fun x => U x.succ) (.imp A C)
  | impE {n : ℕ} {Γ : Fin n → Fm B} {U U' : Fin n → Prop} {A C : Fm B} :
      RPf Γ U (.imp A C) → RPf Γ U' A → RPf Γ (fun x => U x ∨ U' x) C

namespace RPf

/-- Curry–Howard: the λ-term of a proof, in the same scope. -/
def erase {n : ℕ} {Γ : Fin n → Fm B} {U : Fin n → Prop} {A : Fm B} : RPf Γ U A → Tm n
  | .hyp x => .var x
  | .impI p _ => .lam p.erase
  | .impE p q => .app p.erase q.erase

@[simp] theorem erase_hyp {n : ℕ} {Γ : Fin n → Fm B} (x : Fin n) :
    (RPf.hyp (Γ := Γ) x).erase = .var x := rfl
@[simp] theorem erase_impI {n : ℕ} {Γ : Fin n → Fm B} {U : Fin (n + 1) → Prop} {A C : Fm B}
    (p : RPf (Fin.cons A Γ) U C) (h : U 0) : (RPf.impI p h).erase = .lam p.erase := rfl
@[simp] theorem erase_impE {n : ℕ} {Γ : Fin n → Fm B} {U U' : Fin n → Prop} {A C : Fm B}
    (p : RPf Γ U (.imp A C)) (q : RPf Γ U' A) : (RPf.impE p q).erase = .app p.erase q.erase :=
  rfl

/-- Transport a proof along equalities of its indices. -/
def cast {n : ℕ} {Γ Γ' : Fin n → Fm B} {U U' : Fin n → Prop} {A A' : Fm B}
    (hΓ : Γ = Γ') (hU : U = U') (hA : A = A') (p : RPf Γ U A) : RPf Γ' U' A' :=
  hΓ ▸ hU ▸ hA ▸ p

@[simp] theorem erase_cast {n : ℕ} {Γ Γ' : Fin n → Fm B} {U U' : Fin n → Prop} {A A' : Fm B}
    (hΓ : Γ = Γ') (hU : U = U') (hA : A = A') (p : RPf Γ U A) :
    (p.cast hΓ hU hA).erase = p.erase := by
  subst hΓ hU hA; rfl

end RPf

/-- Derivability in relevant implication: there is a proof term. -/
def Rel {n : ℕ} (Γ : Fin n → Fm B) (U : Fin n → Prop) (A : Fm B) : Prop := Nonempty (RPf Γ U A)

theorem Rel.hyp {n : ℕ} {Γ : Fin n → Fm B} (x : Fin n) : Rel Γ (· = x) (Γ x) := ⟨.hyp x⟩

theorem Rel.impI {n : ℕ} {Γ : Fin n → Fm B} {U : Fin (n + 1) → Prop} {A C : Fm B}
    (h : Rel (Fin.cons A Γ) U C) (h0 : U 0) : Rel Γ (fun x => U x.succ) (.imp A C) :=
  ⟨.impI h.some h0⟩

theorem Rel.impE {n : ℕ} {Γ : Fin n → Fm B} {U U' : Fin n → Prop} {A C : Fm B}
    (h₁ : Rel Γ U (.imp A C)) (h₂ : Rel Γ U' A) : Rel Γ (fun x => U x ∨ U' x) C :=
  ⟨.impE h₁.some h₂.some⟩

/-- `A` is a theorem of `R→`: derivable from the empty set of hypotheses. -/
def RTheorem (A : Fm B) : Prop := Rel ![] (fun _ => False) A

theorem Rel.congr {n : ℕ} {Γ Γ' : Fin n → Fm B} {U U' : Fin n → Prop} {A : Fm B} (h : Rel Γ U A)
    (hΓ : Γ = Γ') (hU : U = U') : Rel Γ' U' A := hΓ ▸ hU ▸ h

/-! ## Grade erasure and positively graded terms -/

/-- Erase the grades of a natural reduction type. -/
def Ty.erase {R : Type} : Ty B R → Fm B
  | .base n => .atom n
  | .arr _ σ τ => .imp σ.erase τ.erase

/-- A typed term over `ℕ` is *positively graded* if every arrow it introduces or eliminates
carries a grade `≥ 1`. -/
def GTm.Positive {n : ℕ} {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ} : GTm Γ V τ → Prop
  | .var _ => True
  | @GTm.lam _ _ _ _ _ _ _ V d => V 0 ≠ 0 ∧ d.Positive
  | @GTm.app _ _ _ _ _ _ _ b _ _ d e => b ≠ 0 ∧ d.Positive ∧ e.Positive

@[simp] theorem GTm.positive_cast {n : ℕ} {Γ : Fin n → Ty B ℕ} {V V' : Fin n → ℕ}
    {τ τ' : Ty B ℕ} (hV : V = V') (hτ : τ = τ') (d : GTm Γ V τ) :
    (d.cast hV hτ).Positive ↔ d.Positive := by
  subst hV hτ; rfl

theorem erase_cons {n : ℕ} (σ : Ty B ℕ) (Γ : Fin n → Ty B ℕ) :
    (fun x => ((Fin.cons σ Γ : Fin (n + 1) → Ty B ℕ) x).erase) =
      Fin.cons σ.erase (fun x => (Γ x).erase) := by
  funext x; cases x using Fin.cases <;> simp

/-- **Curry–Howard, soundness.** Erasing the grades of a positively graded typed term gives
a proof term of relevant implication `R→`, whose set of used hypotheses is exactly the
support `{x | V x ≠ 0}` of the neededness function. -/
def GTm.toRPf {n : ℕ} {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ} :
    (d : GTm Γ V τ) → d.Positive →
      RPf (fun x => (Γ x).erase) (fun x => V x ≠ 0) τ.erase
  | .var x, _ => (RPf.hyp x).cast rfl (by funext y; simp [single]) rfl
  | @GTm.lam _ _ _ _ _ σ _ _ d, h => RPf.impI ((d.toRPf h.2).cast (erase_cons σ _) rfl rfl) h.1
  | .app d e, h => (RPf.impE (d.toRPf h.2.1) (e.toRPf h.2.2)).cast rfl
      (by funext x; simp [h.1]; tauto) rfl

/-- The proof term of a positively graded typed term *is* the same λ-term. -/
@[simp] theorem GTm.toRPf_erase {n : ℕ} {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ}
    (d : GTm Γ V τ) (h : d.Positive) : (d.toRPf h).erase = d.erase := by
  induction d with
  | var x => simp [GTm.toRPf]
  | lam d ih => simp [GTm.toRPf, ih]
  | app d e ihd ihe => simp [GTm.toRPf, ihd, ihe]

/-- Curry–Howard, soundness, at the level of derivability. -/
theorem GTm.toRel {n : ℕ} {Γ : Fin n → Ty B ℕ} {V : Fin n → ℕ} {τ : Ty B ℕ}
    (d : GTm Γ V τ) (h : d.Positive) :
    Rel (fun x => (Γ x).erase) (fun x => V x ≠ 0) τ.erase := ⟨d.toRPf h⟩

/-- A positively graded closed typed term erases to a theorem of `R→`. -/
theorem GTm.toRTheorem {τ : Ty B ℕ} (d : GTm ![] 0 τ) (h : d.Positive) :
    RTheorem τ.erase :=
  (d.toRel h).congr (funext fun x => x.elim0) (funext fun x => x.elim0)

/-! ## Example: `W` and contraction -/

/-- The untyped term `W = λf x. f x x`. -/
def Tm.wcomb : Tm 0 := .lam (.lam (.app (.app (.var 1) (.var 0)) (.var 0)))

/-- `W = λf x. f x x : (σ →ᵢ σ →ⱼ τ) →₁ σ →_{i+j} τ`, as a closed typed term. -/
def W (σ τ : Ty B ℕ) (i j : ℕ) :
    GTm ![] 0 (.arr 1 (.arr i σ (.arr j σ τ)) (.arr (i + j) σ τ)) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.app (.app (.var (Γ := Fin.cons σ (Fin.cons (.arr i σ (.arr j σ τ)) ![])) 1)
      (.var 0)) (.var 0))))

@[simp] theorem W_erase (σ τ : Ty B ℕ) (i j : ℕ) : (W σ τ i j).erase = Tm.wcomb := by
  simp [W, Tm.wcomb]

/-- `W` is positively graded when `i, j ≥ 1`. -/
theorem W_positive (σ τ : Ty B ℕ) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    (W σ τ i j).Positive := by
  simp [W, GTm.Positive, single, hi, hj]

/-- The contraction axiom `(A → A → C) → A → C` of `R→`, read off from the typing of `W`. -/
theorem rtheorem_W (A C : Fm B) : RTheorem (.imp (.imp A (.imp A C)) (.imp A C)) := by
  obtain ⟨σ, rfl⟩ : ∃ σ : Ty B ℕ, σ.erase = A := by
    induction A with
    | atom β => exact ⟨.base β, rfl⟩
    | imp A C ihA ihC =>
      obtain ⟨σ, rfl⟩ := ihA; obtain ⟨τ, rfl⟩ := ihC; exact ⟨.arr 1 σ τ, rfl⟩
  obtain ⟨τ, rfl⟩ : ∃ τ : Ty B ℕ, τ.erase = C := by
    induction C with
    | atom β => exact ⟨.base β, rfl⟩
    | imp A C ihA ihC =>
      obtain ⟨σ, rfl⟩ := ihA; obtain ⟨τ, rfl⟩ := ihC; exact ⟨.arr 1 σ τ, rfl⟩
  exact (W σ τ 1 1).toRTheorem (W_positive σ τ one_ne_zero one_ne_zero)

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
def Fm.sval (v : B → Sug) : Fm B → Sug
  | .atom β => v β
  | .imp A C => Sug.imp (A.sval v) (C.sval v)

open Classical in
/-- The set of values of the used hypotheses. -/
noncomputable def usedVals {n : ℕ} (v : B → Sug) (Γ : Fin n → Fm B) (U : Fin n → Prop) :
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
theorem rel_sound_sugihara {n : ℕ} {Γ : Fin n → Fm B} {U : Fin n → Prop} {A : Fm B}
    (h : Rel Γ U A)
    (v : B → Sug) : Sug.le ((usedVals v Γ U).prod id) (A.sval v) := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | @hyp n Γ x =>
    have : usedVals v Γ (· = x) = {(Γ x).sval v} := by
      ext a; simp [usedVals, eq_comm]
    rw [this, Finset.prod_singleton]; exact Sug.le_refl' _
  | @impI n Γ U A C _ h0 ih =>
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
  | @impE n Γ U U' A C _ _ ih₁ ih₂ =>
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

/-- **`K` is not relevant.** `A → C → A` is not a theorem of relevant implication for
distinct atoms `A = atom a`, `C = atom c`, although `K : σ →₁ τ →₀ σ` is typeable in natural
reduction types: the grade `0` is what takes the full system beyond `R→`. -/
theorem rel_not_K {a c : B} (hac : a ≠ c) :
    ¬ RTheorem (.imp (.atom a) (.imp (.atom c) (.atom a))) := by
  classical
  intro h
  have := rel_sound_sugihara h (fun β => if β = a then .zero else .pos)
  have e : usedVals (fun β => if β = a then .zero else .pos) ![] (fun _ => False) = ∅ := by
    ext x; simp [usedVals]
  rw [e, Finset.prod_empty] at this
  simp only [Fm.sval, if_neg hac.symm] at this
  exact Sug.one_not_le this

/-- `K : σ →₁ τ →₀ σ` is a typed term, but for distinct base types `a`, `c` its type
`base a →₁ base c →₀ base a` erases to `A → C → A`: **no** closed typed term of this type is
positively graded. -/
theorem K_not_positive {a c : B} (hac : a ≠ c)
    (d : GTm ![] 0 (.arr 1 (.base a) (.arr 0 (.base c) (.base a)))) :
    ¬ d.Positive :=
  fun h => rel_not_K hac (d.toRTheorem h)

/-- In particular the typed term `K` itself is not positively graded. -/
example : ¬ (K (.base 0) (.base 1) : GTm (B := ℕ) ![] 0 _).Positive :=
  K_not_positive (by decide) _

end NRT
