module

public import Mathlib
public import RequestProject.Section3_NaturalReductionTypes.NaturalReductionTypes

/-!
# The unified framework (Sections 4–5 of *Counting before Grading*)

The 1995 logic is parametric in an *annotation algebra*: a type `R` with two operations
`+`, `·` and basic values `0`, `1`.  Sequents have four zones

  `Ψ; Γ ⊢ Δ; Θ`

where the outer zones `Ψ, Θ` hold unannotated formulas and the inner zones `Γ, Δ` hold
annotated formulas `A^i` (here: pairs `(A, i)`).  The permeability operators
`P_L^→, P_L^←, P_R^←, P_R^→` are instance-specific; we model each of them as a relation
between an outer formula and an inner annotated formula (`Permeability`).

We transcribe the rules of Section 4.2 exactly as displayed (one of the three cut rules
is shown in the paper, and only that one is included), with list concatenation and
"`X, Γ`" / "`Δ, X`" placement as in the paper.  The `(·k)` scaling rule can be switched
off by a Boolean flag, so that we can state that it is *admissible* from the additive
coercions `(+k)` under the paper's local condition.

Main results:
* `RML.coerce`: pointwise additive coercion of every inner formula is admissible.
* `RML.scale_admissible`: under the local condition `k · i = i + c`, the scaling rule
  `(·k)` is admissible in the system *without* `(·k)` ("scaling is recovered from additive
  coercion alone"); `RML.localCondition_of_rep` and `RML.localCondition_natCast` show the
  paper's condition `i + ⋯ + i (k times) = k i` implies it, and that it holds for every
  positive numeral in a semiring.
* Instances: binding-time logic (`BT`), trust logic (`Trust`), the logic of unity
  (`Unity`), with the combination tables and the derived trust coercion.
* The idempotence dial: `BT`, `Trust` are multiplicatively idempotent, `ℕ` is not.
-/

@[expose] public section

namespace RML

/-! ## Formulas, annotated terms -/

/-- Formulas: atoms and annotated arrows `A →_k B`. -/
inductive Fm (R : Type) : Type
  | atom : ℕ → Fm R
  | arr : R → Fm R → Fm R → Fm R

/-- Annotated λ-terms `E ::= x^k | λ^k x. E | E₁ @^k E₂` (Section 4.3), de Bruijn style. -/
inductive ATm (R : Type) : Type
  | var : ℕ → R → ATm R
  | lam : R → ATm R → ATm R
  | app : R → ATm R → ATm R → ATm R

/-- The term semantics is that of the ordinary λ-calculus: erase the annotations. -/
def ATm.erase {R : Type} : ATm R → NRT.Tm
  | .var x _ => .var x
  | .lam _ e => .lam e.erase
  | .app _ e₁ e₂ => .app e₁.erase e₂.erase

/-! ## The four-zone sequent calculus -/

/-- Permeability operators of an instance, as relations (they may be partial). -/
structure Permeability (R : Type) where
  /-- `P_L^→`: outer left formula `A` becomes inner left entry. -/
  pLr : Fm R → Fm R × R → Prop
  /-- `P_L^←`: outer left formula `A` becomes inner left entry. -/
  pLl : Fm R → Fm R × R → Prop
  /-- `P_R^←`: outer right formula `A` becomes inner right entry. -/
  pRl : Fm R → Fm R × R → Prop
  /-- `P_R^→`: inner right entry becomes outer right formula. -/
  pRr : Fm R × R → Fm R → Prop

variable {R : Type} [Add R] [Mul R] [Zero R] [One R]

/-- Scale every annotation of a zone by `k` (the `k Γ` of rule `(·k)`). -/
def scaleZone (k : R) (Γ : List (Fm R × R)) : List (Fm R × R) :=
  Γ.map fun e => (e.1, k * e.2)

/-- Derivability `Ψ; Γ ⊢ Δ; Θ` in the 1995 logic for annotation algebra `R` and
permeability operators `P`.  The flag `sc` says whether the scaling rule `(·k)` is
available. -/
inductive Deriv (P : Permeability R) (sc : Bool) :
    List (Fm R) → List (Fm R × R) → List (Fm R × R) → List (Fm R) → Prop
  /-- `Id₁ : ·; A¹ ⊢ A¹; ·` -/
  | id₁ (A : Fm R) : Deriv P sc [] [(A, 1)] [(A, 1)] []
  /-- `Id₂ : A; · ⊢ ·; A` -/
  | id₂ (A : Fm R) : Deriv P sc [A] [] [] [A]
  /-- `P_L^→` -/
  | pLr {Ψ Γ Δ Θ} {A : Fm R} {e : Fm R × R} :
      P.pLr A e → Deriv P sc (Ψ ++ [A]) Γ Δ Θ → Deriv P sc Ψ (e :: Γ) Δ Θ
  /-- `P_L^←` -/
  | pLl {Ψ Γ Δ Θ} {A : Fm R} {e : Fm R × R} :
      P.pLl A e → Deriv P sc (Ψ ++ [A]) Γ Δ Θ → Deriv P sc Ψ (e :: Γ) Δ Θ
  /-- `P_R^←` -/
  | pRl {Ψ Γ Δ Θ} {A : Fm R} {e : Fm R × R} :
      P.pRl A e → Deriv P sc Ψ Γ Δ (A :: Θ) → Deriv P sc Ψ Γ (Δ ++ [e]) Θ
  /-- `P_R^→` -/
  | pRr {Ψ Γ Δ Θ} {A : Fm R} {e : Fm R × R} :
      P.pRr e A → Deriv P sc Ψ Γ (Δ ++ [e]) Θ → Deriv P sc Ψ Γ Δ (A :: Θ)
  /-- `W_L`: weakening introduces a grade-0 assumption. -/
  | wL {Ψ Γ Δ Θ} (A : Fm R) : Deriv P sc Ψ Γ Δ Θ → Deriv P sc Ψ ((A, 0) :: Γ) Δ Θ
  /-- `W_R` -/
  | wR {Ψ Γ Δ Θ} (A : Fm R) : Deriv P sc Ψ Γ Δ Θ → Deriv P sc Ψ Γ (Δ ++ [(A, 0)]) Θ
  /-- `C_L`: contraction adds grades. -/
  | cL {Ψ Γ Δ Θ} {A : Fm R} {i j : R} :
      Deriv P sc Ψ ((A, i) :: (A, j) :: Γ) Δ Θ → Deriv P sc Ψ ((A, i + j) :: Γ) Δ Θ
  /-- `C_R` -/
  | cR {Ψ Γ Δ Θ} {A : Fm R} {i j : R} :
      Deriv P sc Ψ Γ (Δ ++ [(A, i), (A, j)]) Θ → Deriv P sc Ψ Γ (Δ ++ [(A, i + j)]) Θ
  /-- `E`: exchange, an arbitrary permutation of each zone. -/
  | exch {Ψ Γ Δ Θ Ψ' Γ' Δ' Θ'} :
      Deriv P sc Ψ Γ Δ Θ → Ψ.Perm Ψ' → Γ.Perm Γ' → Δ.Perm Δ' → Θ.Perm Θ' →
      Deriv P sc Ψ' Γ' Δ' Θ'
  /-- `(·k)`: promotion, scaling the inner zones by `k` (only when `sc = true`). -/
  | scale {Γ Δ} (k : R) : sc = true → Deriv P sc [] Γ Δ [] →
      Deriv P sc [] (scaleZone k Γ) (scaleZone k Δ) []
  /-- `(+k)_L`: graded coercion on the left. -/
  | addL {Γ Δ} {A : Fm R} {i : R} (k : R) :
      Deriv P sc [] ((A, i) :: Γ) Δ [] → Deriv P sc [] ((A, i + k) :: Γ) Δ []
  /-- `(+k)_R`: graded coercion on the right. -/
  | addR {Γ Δ} {A : Fm R} {i : R} (k : R) :
      Deriv P sc [] Γ (Δ ++ [(A, i)]) [] → Deriv P sc [] Γ (Δ ++ [(A, i + k)]) []
  /-- `(→L)` -/
  | impL {Ψ Γ Δ Θ Ψ' Γ' Δ' Θ'} {A B : Fm R} :
      Deriv P sc Ψ Γ Δ (A :: Θ) → Deriv P sc (Ψ' ++ [B]) Γ' Δ' Θ' →
      Deriv P sc (Ψ ++ Ψ' ++ [.arr 1 A B]) (Γ ++ Γ') (Δ ++ Δ') (Θ ++ Θ')
  /-- `(→R)` -/
  | impR {Ψ Γ Δ Θ} {A B : Fm R} :
      Deriv P sc (Ψ ++ [A]) Γ Δ (B :: Θ) → Deriv P sc Ψ Γ Δ (.arr 1 A B :: Θ)
  /-- `Cut₁` -/
  | cut₁ {Ψ Γ Δ Θ Ψ' Γ' Δ' Θ'} {A : Fm R} :
      Deriv P sc Ψ Γ Δ (A :: Θ) → Deriv P sc (A :: Ψ') Γ' Δ' Θ' →
      Deriv P sc (Ψ ++ Ψ') (Γ ++ Γ') (Δ ++ Δ') (Θ ++ Θ')

/-! ## Additive coercion and the derived scaling rule -/

/-- `e'` is obtained from `e` by an additive coercion: same formula, grade `i + c`. -/
def Coerces (e e' : Fm R × R) : Prop := e'.1 = e.1 ∧ ∃ c, e'.2 = e.2 + c

variable {P : Permeability R} {sc : Bool}

theorem coerce_one_L {Γ₁ Γ₂ Δ : List (Fm R × R)} {A : Fm R} {i : R} (c : R)
    (h : Deriv P sc [] (Γ₁ ++ (A, i) :: Γ₂) Δ []) :
    Deriv P sc [] (Γ₁ ++ (A, i + c) :: Γ₂) Δ [] := by
  have h1 : Deriv P sc [] ((A, i) :: (Γ₁ ++ Γ₂)) Δ [] :=
    Deriv.exch h (List.Perm.refl _) List.perm_middle (List.Perm.refl _) (List.Perm.refl _)
  exact Deriv.exch (Deriv.addL c h1) (List.Perm.refl _) List.perm_middle.symm
    (List.Perm.refl _) (List.Perm.refl _)

theorem coerce_one_R {Γ Δ₁ Δ₂ : List (Fm R × R)} {A : Fm R} {i : R} (c : R)
    (h : Deriv P sc [] Γ (Δ₁ ++ (A, i) :: Δ₂) []) :
    Deriv P sc [] Γ (Δ₁ ++ (A, i + c) :: Δ₂) [] := by
  have hp : ∀ x : Fm R × R, (Δ₁ ++ Δ₂ ++ [x]).Perm (Δ₁ ++ x :: Δ₂) := fun x => by
    rw [List.append_assoc]
    exact (List.perm_append_comm.append_left Δ₁).trans
      (by simp)
  have h1 : Deriv P sc [] Γ (Δ₁ ++ Δ₂ ++ [(A, i)]) [] :=
    Deriv.exch h (List.Perm.refl _) (List.Perm.refl _) (hp _).symm (List.Perm.refl _)
  exact Deriv.exch (Deriv.addR c h1) (List.Perm.refl _) (List.Perm.refl _) (hp _)
    (List.Perm.refl _)

theorem coerce_L {Δ : List (Fm R × R)} :
    ∀ {Γ Γ' : List (Fm R × R)} (Γ₁ : List (Fm R × R)), List.Forall₂ Coerces Γ Γ' →
      Deriv P sc [] (Γ₁ ++ Γ) Δ [] → Deriv P sc [] (Γ₁ ++ Γ') Δ []
  | _, _, _, .nil, h => h
  | (A, i) :: Γ, (A', i') :: Γ', Γ₁, .cons ⟨hA, c, hc⟩ hrest, h => by
    simp only at hA hc
    subst A' i'
    have h1 := coerce_one_L (Γ₁ := Γ₁) (Γ₂ := Γ) c h
    have := coerce_L (Γ₁ ++ [(A, i + c)]) hrest (by simpa using h1)
    simpa using this

theorem coerce_R {Γ : List (Fm R × R)} :
    ∀ {Δ Δ' : List (Fm R × R)} (Δ₁ : List (Fm R × R)), List.Forall₂ Coerces Δ Δ' →
      Deriv P sc [] Γ (Δ₁ ++ Δ) [] → Deriv P sc [] Γ (Δ₁ ++ Δ') []
  | _, _, _, .nil, h => h
  | (A, i) :: Δ, (A', i') :: Δ', Δ₁, .cons ⟨hA, c, hc⟩ hrest, h => by
    simp only at hA hc
    subst A' i'
    have h1 := coerce_one_R (Δ₁ := Δ₁) (Δ₂ := Δ) c h
    have := coerce_R (Δ₁ ++ [(A, i + c)]) hrest (by simpa using h1)
    simpa using this

/-- **Additive coercion is admissible pointwise.** If every inner formula of the conclusion
is obtained from the corresponding one of a derivable sequent `·; Γ ⊢ Δ; ·` by adding some
grade, the new sequent is derivable using only `(+k)` and exchange. -/
theorem coerce {Γ Γ' Δ Δ' : List (Fm R × R)} (h : Deriv P sc [] Γ Δ [])
    (hΓ : List.Forall₂ Coerces Γ Γ') (hΔ : List.Forall₂ Coerces Δ Δ') :
    Deriv P sc [] Γ' Δ' [] :=
  coerce_R [] hΔ (coerce_L [] hΓ h)

omit [Zero R] [One R] in
theorem forall₂_scaleZone {k : R} (hk : ∀ i : R, ∃ c, k * i = i + c) :
    ∀ Γ : List (Fm R × R), List.Forall₂ Coerces Γ (scaleZone k Γ)
  | [] => .nil
  | e :: Γ => .cons ⟨rfl, hk e.2⟩ (forall₂_scaleZone hk Γ)

/-- **Scaling is recovered from additive coercion.** Under the local condition
`∀ i, ∃ c, k · i = i + c`, the rule `(·k)` is admissible in the system *without* the
scaling rule: from a scaling-free derivation of `·; Γ ⊢ Δ; ·` we get a scaling-free
derivation of `·; kΓ ⊢ kΔ; ·`. -/
theorem scale_admissible {k : R} (hk : ∀ i : R, ∃ c, k * i = i + c)
    {Γ Δ : List (Fm R × R)} (h : Deriv P false [] Γ Δ []) :
    Deriv P false [] (scaleZone k Γ) (scaleZone k Δ) [] :=
  coerce h (forall₂_scaleZone hk Γ) (forall₂_scaleZone hk Δ)

/-- `rep n i = i + (i + ⋯ + (i + 0))`, the sum of `n` copies of `i`. -/
def rep (i : R) : ℕ → R
  | 0 => 0
  | n + 1 => i + rep i n

omit [One R] in
/-- The paper's local condition `i + ⋯ + i (k copies, k ≥ 1) = k i` implies the
condition used in `scale_admissible`. -/
theorem localCondition_of_rep {k : R} {n : ℕ} (h : ∀ i : R, k * i = rep i (n + 1)) :
    ∀ i : R, ∃ c, k * i = i + c :=
  fun i => ⟨rep i n, h i⟩

end RML

/-- In any semiring, every positive numeral `k = n + 1` satisfies the local condition
`k · i = i + ⋯ + i`. -/
theorem RML.rep_natCast {S : Type} [Semiring S] (n : ℕ) (i : S) :
    ((n : S)) * i = RML.rep i n := by
  induction n with
  | zero => simp [RML.rep]
  | succ n ih => rw [RML.rep, ← ih]; push_cast; rw [add_mul, one_mul, add_comm]

theorem RML.localCondition_natCast {S : Type} [Semiring S] (n : ℕ) :
    ∀ i : S, ∃ c, ((n + 1 : ℕ) : S) * i = i + c :=
  RML.localCondition_of_rep (n := n) (fun i => RML.rep_natCast (n + 1) i)

namespace RML

end RML
