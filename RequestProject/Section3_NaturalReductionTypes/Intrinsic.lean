module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes
public import RequestProject.Section6_Dictionary.Normalization
public import RequestProject.Section3_NaturalReductionTypes.RelevantLogic

/-!
# Intrinsically scoped, typed and graded terms

`Tm n` (in `Syntax.lean`) makes *scoping* correct by construction.  Here the same idea is
pushed to typing and grading: an element of

  `GTm Γ V τ`   (with `Γ : Fin n → Ty R`, `V : Fin n → R`)

is a λ-term with free variables in `Fin n` that has type `τ` and neededness function `V`.
Ill-scoped, ill-typed or wrongly graded terms cannot be written at all.  `GTm ![] 0 τ` is
the type of closed terms of type `τ`.

The family is shown to be exactly the extrinsic judgement `Has`:
* `GTm.erase_has`: the erasure of an intrinsic term is typed by `Has`;
* `GTm.exists_of_has`: every `Has` derivation is the erasure of an intrinsic term;
* `GTm.has_iff`: `Has Γ V t τ ↔ ∃ d : GTm Γ V τ, d.erase = t`.

Consequently the metatheory transfers: β-reduction of the erasure stays inside
`GTm Γ V τ` (`GTm.subject_reduction`) and every intrinsic term is strongly normalising
(`GTm.sn`).  The worked examples are given as closed intrinsic terms.

The same treatment is given to relevant implication: `RPf Γ U A` is the type of proof
terms with hypotheses `Γ : Fin n → Fm` that use exactly the hypotheses in `U`; it is
inhabited iff `Rel Γ U A` holds (`RPf.nonempty_iff`), and proofs erase to `Tm n`.
-/

@[expose] public section

namespace NRT

variable {R : Type} [Semiring R]

/-- Intrinsically well-scoped, well-typed, graded λ-terms: `GTm Γ V τ` contains the terms
with free variables in `Fin n`, of type `τ`, with neededness function `V`.  The rules are
those of natural reduction types; `GTm ![] 0 τ` is the type of closed terms of type `τ`. -/
inductive GTm : {n : ℕ} → (Fin n → Ty R) → (Fin n → R) → Ty R → Type
  | var {n : ℕ} {Γ : Fin n → Ty R} (x : Fin n) : GTm Γ (single x) (Γ x)
  | lam {n : ℕ} {Γ : Fin n → Ty R} {σ τ : Ty R} {V : Fin (n + 1) → R} :
      GTm (Fin.cons σ Γ) V τ → GTm Γ (fun x => V x.succ) (.arr (V 0) σ τ)
  | app {n : ℕ} {Γ : Fin n → Ty R} {σ τ : Ty R} {b : R} {V₁ V₂ : Fin n → R} :
      GTm Γ V₁ (.arr b σ τ) → GTm Γ V₂ σ → GTm Γ (fun x => V₁ x + b * V₂ x) τ

namespace GTm

variable {n : ℕ} {Γ : Fin n → Ty R}

/-- Forget the typing: the underlying well-scoped term. -/
noncomputable def erase {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) : Tm n :=
  GTm.rec (motive := fun {n} _ _ _ _ => Tm n)
    (fun x => .var x) (fun _ r => .lam r) (fun _ _ r s => .app r s) d

@[simp] theorem erase_var (x : Fin n) : (GTm.var (Γ := Γ) x).erase = .var x := rfl
@[simp] theorem erase_lam {σ τ : Ty R} {V : Fin (n + 1) → R} (d : GTm (Fin.cons σ Γ) V τ) :
    (GTm.lam d).erase = .lam d.erase := rfl
@[simp] theorem erase_app {σ τ : Ty R} {b : R} {V₁ V₂ : Fin n → R}
    (d : GTm Γ V₁ (.arr b σ τ)) (e : GTm Γ V₂ σ) :
    (GTm.app d e).erase = .app d.erase e.erase := rfl

/-- Transport an intrinsic term along equalities of its grade and type indices. -/
def cast {V V' : Fin n → R} {τ τ' : Ty R} (hV : V = V') (hτ : τ = τ') (d : GTm Γ V τ) :
    GTm Γ V' τ' :=
  hV ▸ hτ ▸ d

@[simp] theorem erase_cast {V V' : Fin n → R} {τ τ' : Ty R} (hV : V = V') (hτ : τ = τ')
    (d : GTm Γ V τ) : (d.cast hV hτ).erase = d.erase := by
  subst hV hτ; rfl

/-- Soundness: an intrinsic term is typed, by the extrinsic judgement, with its indices. -/
theorem erase_has {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) : Has Γ V d.erase τ := by
  induction d with
  | var x => exact Has.var x
  | lam d ih => exact Has.lam ih
  | app d e ihd ihe => exact Has.app ihd ihe

/-- Completeness: every extrinsic typing derivation is the erasure of an intrinsic term. -/
theorem exists_of_has {V : Fin n → R} {t : Tm n} {τ : Ty R} (h : Has Γ V t τ) :
    ∃ d : GTm Γ V τ, d.erase = t := by
  induction h with
  | var x => exact ⟨.var x, rfl⟩
  | lam _ ih =>
    obtain ⟨d, rfl⟩ := ih
    exact ⟨.lam d, rfl⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨d, rfl⟩ := ih₁
    obtain ⟨e, rfl⟩ := ih₂
    exact ⟨.app d e, rfl⟩

/-- The intrinsic family is exactly the extrinsic judgement. -/
theorem has_iff {V : Fin n → R} {t : Tm n} {τ : Ty R} :
    Has Γ V t τ ↔ ∃ d : GTm Γ V τ, d.erase = t :=
  ⟨exists_of_has, fun ⟨d, hd⟩ => hd ▸ d.erase_has⟩

/-- Subject reduction, intrinsically: a β-reduct of the erasure of `d : GTm Γ V τ` is the
erasure of some `d' : GTm Γ V τ` — same scope, same type, same neededness function. -/
theorem subject_reduction {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) {t' : Tm n}
    (hs : Relation.ReflTransGen Step d.erase t') : ∃ d' : GTm Γ V τ, d'.erase = t' :=
  exists_of_has (subject_reduction_star d.erase_has hs)

/-- Strong normalisation, intrinsically: every intrinsic term is strongly normalising. -/
theorem sn {V : Fin n → R} {τ : Ty R} (d : GTm Γ V τ) : SN d.erase :=
  strong_normalization d.erase_has

/-- Every closed intrinsic term reduces to a β-normal form which is again a closed
intrinsic term of the same type. -/
theorem closed_normalizes {τ : Ty R} (d : GTm ![] 0 τ) :
    ∃ d' : GTm ![] 0 τ, Relation.ReflTransGen Step d.erase d'.erase ∧ Normal d'.erase := by
  obtain ⟨t', hred, hnf⟩ := d.sn.exists_normal
  obtain ⟨d', rfl⟩ := d.subject_reduction hred
  exact ⟨d', hred, hnf⟩

end GTm

/-! ## The worked examples as closed intrinsic terms -/

/-- `K = λx y. x : σ →₁ τ →₀ σ`, as a closed intrinsic term. -/
def gK (σ τ : Ty R) : GTm (R := R) ![] 0 (.arr 1 σ (.arr 0 τ σ)) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.var (Γ := Fin.cons τ (Fin.cons σ ![])) 1)))

theorem gK_erase (σ τ : Ty R) : (gK σ τ).erase = K := by simp [gK, K]

/-- `Twice = λf x. f (f x) : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`, as a closed intrinsic term. -/
def gTwice (σ : Ty R) (i : R) :
    GTm (R := R) ![] 0 (.arr (1 + i) (.arr i σ σ) (.arr (i * i) σ σ)) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.app (.var (Γ := Fin.cons σ (Fin.cons (.arr i σ σ) ![])) 1)
      (.app (.var 1) (.var 0)))))

theorem gTwice_erase (σ : Ty R) (i : R) : (gTwice σ i).erase = twice := by
  simp [gTwice, twice]

/-- Composition `λg f x. g (f x) : (σ₂ →ᵢ σ₃) →₁ (σ₁ →ⱼ σ₂) →ᵢ σ₁ →_{i·j} σ₃`. -/
def gCompose (σ₁ σ₂ σ₃ : Ty R) (i j : R) :
    GTm (R := R) ![] 0 (.arr 1 (.arr i σ₂ σ₃) (.arr i (.arr j σ₁ σ₂) (.arr (i * j) σ₁ σ₃))) :=
  GTm.cast (by funext x; exact x.elim0) (by simp [single])
    (.lam (.lam (.lam (.app
      (.var (Γ := Fin.cons σ₁ (Fin.cons (.arr j σ₁ σ₂) (Fin.cons (.arr i σ₂ σ₃) ![]))) 2)
      (.app (.var 1) (.var 0))))))

theorem gCompose_erase (σ₁ σ₂ σ₃ : Ty R) (i j : R) :
    (gCompose σ₁ σ₂ σ₃ i j).erase = compose := by
  simp [gCompose, compose]

/-! ## Intrinsic proof terms for relevant implication -/

/-- Intrinsically scoped proof terms of relevant implication `R→`: `RPf Γ U A` contains the
proofs of `A` from the hypotheses `Γ : Fin n → Fm` that use exactly the hypotheses in `U`.
Closed proofs (theorems of `R→`) are `RPf ![] (fun _ => False) A`. -/
inductive RPf : {n : ℕ} → (Fin n → Fm) → (Fin n → Prop) → Fm → Type
  | hyp {n : ℕ} {Γ : Fin n → Fm} (x : Fin n) : RPf Γ (· = x) (Γ x)
  | impI {n : ℕ} {Γ : Fin n → Fm} {U : Fin (n + 1) → Prop} {A B : Fm} :
      RPf (Fin.cons A Γ) U B → U 0 → RPf Γ (fun x => U x.succ) (.imp A B)
  | impE {n : ℕ} {Γ : Fin n → Fm} {U U' : Fin n → Prop} {A B : Fm} :
      RPf Γ U (.imp A B) → RPf Γ U' A → RPf Γ (fun x => U x ∨ U' x) B

namespace RPf

variable {n : ℕ} {Γ : Fin n → Fm}

/-- Curry–Howard: the λ-term of a proof, in the same scope. -/
noncomputable def erase {U : Fin n → Prop} {A : Fm} (p : RPf Γ U A) : Tm n :=
  RPf.rec (motive := fun {n} _ _ _ _ => Tm n)
    (fun x => .var x) (fun _ _ r => .lam r) (fun _ _ r s => .app r s) p

@[simp] theorem erase_hyp (x : Fin n) : (RPf.hyp (Γ := Γ) x).erase = .var x := rfl

/-- A proof term is a relevant-logic derivation. -/
theorem toRel {U : Fin n → Prop} {A : Fm} (p : RPf Γ U A) : Rel Γ U A := by
  induction p with
  | hyp x => exact Rel.hyp x
  | impI _ h ih => exact Rel.impI ih h
  | impE _ _ ih₁ ih₂ => exact Rel.impE ih₁ ih₂

/-- `Rel` holds exactly when there is an intrinsic proof term. -/
theorem nonempty_iff {U : Fin n → Prop} {A : Fm} : Rel Γ U A ↔ Nonempty (RPf Γ U A) := by
  refine ⟨fun h => ?_, fun ⟨p⟩ => p.toRel⟩
  induction h with
  | hyp x => exact ⟨.hyp x⟩
  | impI _ h ih => exact ⟨.impI ih.some h⟩
  | impE _ _ ih₁ ih₂ => exact ⟨.impE ih₁.some ih₂.some⟩

end RPf

end NRT
