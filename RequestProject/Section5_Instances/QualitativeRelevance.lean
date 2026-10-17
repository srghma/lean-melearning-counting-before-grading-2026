module

public import Mathlib
public import RequestProject.Section5_Instances.Instances
public import RequestProject.Section3_NaturalReductionTypes.RelevantCompleteness
public import RequestProject.Section3_NaturalReductionTypes.HeadNeededGeneral

/-!
# The idempotence dial meets Curry–Howard

Over the qualitative (idempotent, `1 + 1 = 1`) algebras of Section 5, positively graded
natural reduction types are *exactly* relevant implication (`NRT.rel_iff_positive`).
Over the quantitative algebra `ℕ` this fails at the level of proof terms
(`NRT.not_positive_relW2`): counting distinguishes proofs that relevance identifies.

The soundness of grade `0` for head neededness also holds over these algebras: an
untrusted (`U`) variable, or a dynamic (`D`) one, never becomes the head variable of any
reduct (`RML.trust_untrusted_not_head`, `RML.bt_dynamic_not_head`).  This is a
head-position form of the "trusted iff all inputs trusted" reading; it is *not* a full
non-interference theorem, which the note itself says is absent.
-/

@[expose] public section

namespace RML

variable {B : Type}

instance : Nontrivial Trust := ⟨⟨.U, .T, by decide⟩⟩

instance : NoZeroDivisors Trust where
  eq_zero_or_eq_zero_of_mul_eq_zero := by decide

instance : Nontrivial BT := ⟨⟨.D, .S, by decide⟩⟩

instance : NoZeroDivisors BT where
  eq_zero_or_eq_zero_of_mul_eq_zero := by decide

/-- **Trust-graded Curry–Howard.**  Relevant derivability of `A` from `Γ` using exactly the
hypotheses `U` is the same as a positively trust-graded typing in context `Γ` at type `A`
whose trusted (`T`) variables are exactly `U`. -/
theorem trust_rel_iff_positive {n : ℕ} (Γ : Fin n → NRT.Fm B) (U : Fin n → Prop) (A : NRT.Fm B) :
    NRT.Rel Γ U A ↔ ∃ (V : Fin n → Trust) (t : NRT.Tm n),
      NRT.PHas (fun x => (Γ x).toTy Trust) V t (A.toTy Trust) ∧ ∀ x, V x ≠ 0 ↔ U x :=
  NRT.rel_iff_positive trust_one_add_one (by decide) Γ U A

/-- **Binding-time-graded Curry–Howard**, likewise. -/
theorem bt_rel_iff_positive {n : ℕ} (Γ : Fin n → NRT.Fm B) (U : Fin n → Prop) (A : NRT.Fm B) :
    NRT.Rel Γ U A ↔ ∃ (V : Fin n → BT) (t : NRT.Tm n),
      NRT.PHas (fun x => (Γ x).toTy BT) V t (A.toTy BT) ∧ ∀ x, V x ≠ 0 ↔ U x :=
  NRT.rel_iff_positive bt_one_add_one (by decide) Γ U A

/-- The λ-term `λh a k. k (h (λx. x)) (h (λx. a x x))` of a proof of relevant implication
*has* a positively trust-graded closed typing… -/
theorem relW2_trust (a b c : B) :
    NRT.PHas ![] (0 : Fin 0 → Trust) NRT.Tm.relW2 ((NRT.relW2Fm a b c).toTy Trust) := by
  have := (NRT.relW2 a b c).toPHas (R := Trust) trust_one_add_one
  rw [NRT.relW2_erase] at this
  exact this.congr (funext fun x => x.elim0) (funext fun x => x.elim0) rfl

/-- …but no positively `ℕ`-graded closed typing, of any type. -/
theorem relW2_not_nat {τ : NRT.Ty B ℕ} : ¬ NRT.PHas ![] (0 : Fin 0 → ℕ) NRT.Tm.relW2 τ :=
  NRT.not_positive_relW2

/-- In the trust instance, an untrusted variable never reaches head position in any
reduct. -/
theorem trust_untrusted_not_head {n : ℕ} {Γ : Fin n → NRT.Ty B Trust} {V : Fin n → Trust}
    {t t' : NRT.Tm n} {τ : NRT.Ty B Trust} (h : NRT.Has Γ V t τ) {x : Fin n} (hx : V x = .U)
    (hred : Relation.ReflTransGen NRT.Step t t') : ¬ NRT.IsHeadOfHnf x t' :=
  h.head_needed_sound_gen (by decide) hx hred

/-- In the binding-time instance, a dynamic variable never reaches head position in any
reduct. -/
theorem bt_dynamic_not_head {n : ℕ} {Γ : Fin n → NRT.Ty B BT} {V : Fin n → BT}
    {t t' : NRT.Tm n} {τ : NRT.Ty B BT} (h : NRT.Has Γ V t τ) {x : Fin n} (hx : V x = .D)
    (hred : Relation.ReflTransGen NRT.Step t t') : ¬ NRT.IsHeadOfHnf x t' :=
  h.head_needed_sound_gen (by decide) hx hred

end RML
