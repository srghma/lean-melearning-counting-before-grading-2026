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
hypotheses `U` is the same as a positively trust-graded typed term in context `Γ` of type
`A` whose trusted (`T`) variables are exactly `U`. -/
theorem trust_rel_iff_positive {n : ℕ} (Γ : Fin n → NRT.Fm B) (U : Fin n → Prop) (A : NRT.Fm B) :
    NRT.Rel Γ U A ↔ ∃ (V : Fin n → Trust)
      (d : NRT.GTm (fun x => (Γ x).toTy Trust) V (A.toTy Trust)),
      d.PositiveR ∧ ∀ x, V x ≠ 0 ↔ U x :=
  NRT.rel_iff_positive trust_one_add_one (by decide) Γ U A

/-- **Binding-time-graded Curry–Howard**, likewise. -/
theorem bt_rel_iff_positive {n : ℕ} (Γ : Fin n → NRT.Fm B) (U : Fin n → Prop) (A : NRT.Fm B) :
    NRT.Rel Γ U A ↔ ∃ (V : Fin n → BT)
      (d : NRT.GTm (fun x => (Γ x).toTy BT) V (A.toTy BT)),
      d.PositiveR ∧ ∀ x, V x ≠ 0 ↔ U x :=
  NRT.rel_iff_positive bt_one_add_one (by decide) Γ U A

/-- The proof term `λh a k. k (h (λx. x)) (h (λx. a x x))` of relevant implication *is* a
positively trust-graded closed typed term (same λ-term)… -/
theorem relW2_trust (a b c : B) :
    ∃ d : NRT.GTm ![] 0 ((NRT.relW2Fm a b c).toTy Trust), d.PositiveR ∧ d.erase = NRT.Tm.relW2 := by
  refine ⟨((NRT.relW2 a b c).toGTm trust_one_add_one).ctxCast (funext fun x => x.elim0) |>.cast
    (funext fun x => x.elim0) rfl, ?_, ?_⟩
  · simpa using (NRT.relW2 a b c).toGTm_positive trust_one_add_one (by decide)
  · simp

/-- …but no positively `ℕ`-graded closed typed term has this λ-term. -/
theorem relW2_not_nat {τ : NRT.Ty B ℕ} (d : NRT.GTm ![] 0 τ) (hd : d.erase = NRT.Tm.relW2) :
    ¬ d.Positive :=
  NRT.not_positive_relW2 d hd

/-- In the trust instance, an untrusted variable never reaches head position in any
reduct. -/
theorem trust_untrusted_not_head {n : ℕ} {Γ : Fin n → NRT.Ty B Trust} {V : Fin n → Trust}
    {τ : NRT.Ty B Trust} (d : NRT.GTm Γ V τ) {x : Fin n} (hx : V x = .U) {t' : NRT.Tm n}
    (hred : Relation.ReflTransGen NRT.Step d.erase t') : ¬ NRT.HeadIs x t' :=
  d.head_needed_sound_gen (by decide) hx hred

/-- In the binding-time instance, a dynamic variable never reaches head position in any
reduct. -/
theorem bt_dynamic_not_head {n : ℕ} {Γ : Fin n → NRT.Ty B BT} {V : Fin n → BT}
    {τ : NRT.Ty B BT} (d : NRT.GTm Γ V τ) {x : Fin n} (hx : V x = .D) {t' : NRT.Tm n}
    (hred : Relation.ReflTransGen NRT.Step d.erase t') : ¬ NRT.HeadIs x t' :=
  d.head_needed_sound_gen (by decide) hx hred

end RML
