# Formalization of *Counting before Grading* (D. A. Wright, 2026)

Most of the note is historical and bibliographic: the arc of the programme, the
dictionary in Table 1, the discussion of what was anticipated, and the question of
credit. Those parts make no mathematical claims and are **not** formalized. What follows
covers the technical content of Sections 3–5 and the facts about the annotation algebras
that the note relies on.

All files build with no `sorry`. The only axioms used are the standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

## Layout

The Lean files are grouped into directories named after the sections of the paper:

| Directory | Paper section | Files |
| --- | --- | --- |
| `RequestProject/Section3_NaturalReductionTypes/` | 3. The quantitative core: natural reduction types (1993) | `Syntax.lean`, `NaturalReductionTypes.lean`, `GTm.lean`, `RelevantLogic.lean`, `RelevantCompleteness.lean`, `HeadNeededGeneral.lean` |
| `RequestProject/Section4_UnifiedFramework/` | 4. The unified framework (1995) | `ResourceLogic.lean` |
| `RequestProject/Section5_Instances/` | 5. Three instances (1995) | `Instances.lean`, `QualitativeRelevance.lean` |
| `RequestProject/Section6_Dictionary/` | 6. A dictionary (generic normalisation) | `Normalization.lean` |

Sections 1, 2, 7 and 8 contain no formalizable claims, so they have no directory.

## `RequestProject/Section3_NaturalReductionTypes/NaturalReductionTypes.lean` — Section 3 (1993 system)

| Paper | Lean |
|---|---|
| base types | `NRT.Ty.base β`, for `β : B` (the type `B` of base-type names is a parameter) |
| graded arrows `σ →_b τ` | `NRT.Ty.arr b σ τ` |
| the judgement `A ⊢_V M : τ` with neededness function `V` | `NRT.Has Γ V M τ` |
| App rule, `V(x) = V₁(x) + b × V₂(x)` | constructor `NRT.Has.app` |

Types `NRT.Ty B R` are parametrized by the type `B` of base types and the grades `R`. The type
system is generic over any semiring `R` of grades; the 1993 system is `R = ℕ`.

**The typing judgement.** The type system is the inductive judgement

```lean
inductive Has : {n : ℕ} → (Fin n → Ty B R) → (Fin n → R) → Tm n → Ty B R → Prop
  | var (x : Fin n) : Has Γ (single x) (.var x) (Γ x)
  | lam : Has (Fin.cons σ Γ) V t τ → Has Γ (fun x => V x.succ) (.lam t) (.arr (V 0) σ τ)
  | app : Has Γ V₁ t (.arr b σ τ) → Has Γ V₂ u σ →
      Has Γ (fun x => V₁ x + b * V₂ x) (.app t u) τ
```

about untyped well-scoped terms `t : Tm n`, a context `Γ : Fin n → Ty B R` and a neededness
function `V : Fin n → R`.

**Untyped well-scoped syntax.** `Syntax.lean` defines `NRT.Tm : ℕ → Type` with
`var : Fin n → Tm n`, `lam : Tm (n+1) → Tm n` and `app`, so `Tm 0` is the type of closed
terms. Renaming, parallel substitution, the single substitution `t[u]` (`NRT.inst`) and
β-reduction `NRT.Step` live there.

**Metatheory, by induction on derivations.**

* `NRT.Has.rename` (weakening, exchange, contraction): renaming along `ρ` gives usage
  `rmap ρ V` (the grade of a new variable is the sum of the grades of the old variables
  renamed to it). `NRT.Has.weaken` and `NRT.Has.embed` (closed terms in any context, with
  no usage) are special cases.
* `NRT.Has.subst` (graded parallel substitution): substituting terms `s x` typed with
  usage `W x` gives usage `y ↦ Σₓ V(x)·W(x)(y)`. `NRT.Has.inst` types the β-contractum,
  with usage `y ↦ V(y+1) + V(0)·V₂(y)`.
* `NRT.Has.subject_reduction`, `NRT.Has.subject_reduction_star`: β-reduction preserves the
  type and the **exact** neededness function, for an arbitrary grade semiring. Inversion
  lemmas `NRT.Has.inv_var`, `inv_lam`, `inv_app` are used here.
* `NRT.Has.head_needed_sound` (grades in `ℕ`): if `Γ ⊢_V t : τ` gives a free variable `x`
  grade `0`, then no β-reduct of `t` is a head normal form whose head variable is `x`. The
  1993 paper also claims a **completeness** result, but the note does not state it
  precisely enough to formalize, so it is not formalized here.

**Worked examples** (untyped terms `NRT.Tm.K`, `NRT.Tm.kxx`, `NRT.Tm.twice`,
`NRT.Tm.compose`):

* `NRT.K_typing : Has ![] 0 Tm.K (σ →₁ τ →₀ σ)`.
* `NRT.kxx_typing : Has ![] 0 Tm.kxx (σ →₁ σ)` for `λx. K x x`: its argument is used once,
  although it occurs twice in the body (`NRT.kxx_occurrences`).
* `NRT.twice_typing`: `λf x. f (f x) : (σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`, and
  `NRT.compose_typing`: `λg f x. g (f x)` gives `x` the grade `i·j`.
  **Note:** the paper says that the derivation for `Twice` produces `i × j`. With simple
  types, `f` has a single arrow grade `i`, so the bound variable gets `i·i`. A genuine
  product `i·j` of two different grades shows up for composition.

## `RequestProject/Section3_NaturalReductionTypes/GTm.lean` — the intrinsic presentation (typed terms)

An alternative presentation of the same type system, as a grammar of typed, graded terms
that are correct by construction:

```lean
inductive GTm : {n : ℕ} → (Fin n → Ty B R) → (Fin n → R) → Ty B R → Type
  | var (x : Fin n) : GTm Γ (single x) (Γ x)
  | lam : GTm (Fin.cons σ Γ) V τ → GTm Γ (fun x => V x.succ) (.arr (V 0) σ τ)
  | app : GTm Γ V₁ (.arr b σ τ) → GTm Γ V₂ σ → GTm Γ (fun x => V₁ x + b * V₂ x) τ
```

* `NRT.GTm.erase` gives the underlying untyped term; `NRT.has_iff_gtm` shows
  `Has Γ V t τ ↔ ∃ d : GTm Γ V τ, d.erase = t`.
* Renaming, weakening, embedding, graded substitution and the β-contractum as operations on
  typed terms (`NRT.GTm.rename`, `weaken`, `embed`, `subst`, `inst`), each with a lemma
  describing its erasure.
* `NRT.GStep` is β-reduction **of typed terms**, `GTm Γ V τ → GTm Γ V τ → Prop`, so
  subject reduction holds by construction; `NRT.GStep.erase` and
  `NRT.GTm.lift_step`/`lift_steps` show it is exactly β-reduction of erasures.
* `NRT.GTm.head_needed_sound` (grades in `ℕ`), typed versions of the worked examples
  (`NRT.K`, `NRT.kxx`, `NRT.twice`, `NRT.compose`), and normalisation by typed reduction
  (`NRT.GTm.normal_form_head`, `NRT.GTm.closed_normalizes`).

Nothing else in the project depends on this file.

## `RequestProject/Section4_UnifiedFramework/ResourceLogic.lean` — Section 4 (1995 framework)

* `RML.Deriv P sc Ψ Γ Δ Θ` is the four-zone sequent `Ψ; Γ ⊢ Δ; Θ`. It is parametric in an
  annotation algebra (`+`, `·`, `0`, `1`) and in permeability operators `P`, which are
  modelled as relations because they can be partial. Every displayed rule is included
  as printed: Id₁, Id₂, the four permeability rules, W, C, E, `(·k)`, `(+k)_L`,
  `(+k)_R`, `(→L)`, `(→R)` and Cut₁. The flag `sc` switches the scaling rule `(·k)` on
  or off.
* `RML.ATm` and `RML.ATm.erase` are the annotated terms `x^k | λ^k x.E | E₁ @^k E₂`
  together with annotation erasure.
* `RML.coerce`: additive coercion of every inner formula is admissible.
* `RML.scale_admissible`: under the local condition `∀ i, ∃ c, k·i = i + c`, the rule
  `(·k)` is admissible in the system **without** `(·k)`. This is the claim that
  "scaling is recovered from additive coercion alone".
  `RML.localCondition_of_rep` shows that the paper's condition
  `i + ⋯ + i (k copies) = k i`, for `k ≥ 1`, implies this local condition.
  `RML.localCondition_natCast` shows that every positive numeral in a semiring
  satisfies it. For `k = 0` the condition cannot be met, which is why `k ≥ 1` is
  required.

## `RequestProject/Section5_Instances/Instances.lean` — Section 5 (instances) and the idempotence dial

* `RML.BT` is binding-time logic (`D = 0`, `S = 1`, join and meet). `RML.bt_table`
  checks the paper's eight-row combination table for `(i + k) j`, and
  `RML.bt_static_iff` characterises when a redex is static.
* `RML.Trust` is trust logic. `RML.trust_app_iff` says the application grade `j k` is
  `T` iff both `j` and `k` are `T`. `RML.trust_coerce` derives the trust coercion
  `·; Γ ⊢ Δ; · ⟹ ·; Γ ⊢ T + Δ; ·` from `(+k)_R`.
* `RML.Unity` is the logic of unity, with grades `{0, 1, ω}`, and `RML.unityPerm` gives
  its permeabilities. The results are dereliction `·; A^ω ⊢ ·; A`
  (`RML.unity_dereliction`), `·; A^ω ⊢ A^ω; ·`, and the facts that `ω` can be both
  contracted and weakened. The note does not fix the operations of this algebra beyond
  the grade list, so the three-element "none/one/many" semiring is a modelling choice.
* The idempotence dial: `RML.bt_mul_idem` and `RML.trust_mul_idem` show `k·k = k` for
  the two Boolean algebras. `RML.nat_not_mul_idem` and `RML.nat_counts` show that this
  fails for `ℕ`, where `1 + 1 = 2`. `RML.nat_scale_admissible` instantiates admissible
  scaling for the usage instance `ℕ` with any `k ≥ 1`.

## `RequestProject/Section3_NaturalReductionTypes/RelevantLogic.lean` — Section 3, Curry–Howard to relevant logic

* `NRT.Fm B` are implicational formulas over atoms indexed by `B` (the same `B` as the base
  types; grade erasure `NRT.Ty.erase` sends `base β` to `atom β`). Relevant implication `R→` is given as a grammar of
  proof terms: `NRT.RPf Γ U A` is the type of labelled natural-deduction proofs of `A` from
  hypotheses `Γ : Fin n → Fm B` that use exactly the hypotheses in `U`. `→I` may only
  discharge a hypothesis that was used, and `→E` takes the union of the labels. Proofs
  erase to untyped terms (`NRT.RPf.erase`). Derivability `NRT.Rel Γ U A` is defined as
  `Nonempty (RPf Γ U A)`, and `NRT.RTheorem A` means `A` is derivable with the empty label.
* `NRT.PHas Γ V t τ` is the positively graded typing judgement: `Has` with every arrow
  introduced or eliminated carrying a nonzero grade (`≥ 1` over `ℕ`); `NRT.PHas.toHas`.
* `NRT.PHas.toRPf` (Curry–Howard, soundness): in a nontrivial semiring with no zero divisors
  where `a + b = 0` implies `a = 0` (e.g. `ℕ`, see `NRT.PHas.toRPf_nat`), a positively graded
  typing of `t` gives an `R→` proof term with the same λ-term `t`, whose label is
  **exactly** the support `{x | V x ≠ 0}` of the neededness function. `NRT.PHas.toRel`
  and `NRT.PHas.toRTheorem` are the derivability versions. As an example, the contraction
  axiom `(A → A → C) → A → C` is obtained from the typing of `W = λf x. f x x`
  (`NRT.W_typing`, `NRT.W_positive`, `NRT.rtheorem_W`).
* Grade `0` goes beyond relevant logic. `NRT.rel_sound_sugihara` proves `R→` sound for
  the three-element Sugihara monoid, and `NRT.rel_not_K` deduces that `A → C → A` is not
  a theorem of `R→` for distinct atoms `A`, `C`. `K : σ →₁ τ →₀ σ` is still typeable, so
  **no** closed term has a positively graded typing of that type (`NRT.K_not_positive`).
* The converse direction, for idempotent grades, is in `RelevantCompleteness.lean`.

## `RequestProject/Section6_Dictionary/Normalization.lean` — Section 6 (dictionary), normalisation ("Curry–Howard–Tait")

* `NRT.Step.rename`, `NRT.Step.subst` and `NRT.Step.of_rename` (in `Syntax.lean`) show
  that β-reduction commutes with renaming in both directions. Since terms are well scoped,
  reducibility is defined Kripke-style: a term of arrow type is reducible if every renaming
  of it into a larger scope, applied to a reducible argument, is reducible.
* `NRT.strong_normalization`: for any grade semiring, every term `t` with
  `Has Γ V t τ` is strongly normalising for full β-reduction. It is proved with Tait's
  reducibility method (`NRT.Red`, `NRT.cr`, `NRT.red_fundamental`, the last by induction
  on the typing derivation).
* `NRT.normal_form_head` (grades in `ℕ`): a typed term reduces to a β-normal form which is
  typed with the same type and neededness function, and no grade-`0` variable is at the
  head of any reduct.
* `NRT.closed_normalizes`: every closed typed term reduces to a β-normal closed term of
  the same type.

## `RequestProject/Section3_NaturalReductionTypes/RelevantCompleteness.lean` — Curry–Howard, both directions

The note says the 1993 discipline comes "with Curry–Howard to the implicational fragment of
relevant logic" without fixing the algebra of grades. This file settles both directions.

* Soundness for general grades is `NRT.PHas.toRPf` (see `RelevantLogic.lean`).
* `NRT.RPf.toPHas` (completeness, idempotent grades): if `1 + 1 = 1` (and `1 ≠ 0`), the
  λ-term of every relevant-logic proof term has a positively graded typing with all arrows
  graded `1` and neededness function the indicator of the label.
* `NRT.rpf_iff_positive`, `NRT.rel_iff_positive`: for such grades, relevant derivability
  **is** positively graded typability (the first even λ-term by λ-term).
* `NRT.not_positive_relW2` (**the converse fails over `ℕ`**): the λ-term `Tm.relW2` of the
  proof `λh a k. k (h (λx. x)) (h (λx. a x x))` of `((A→A)→B) → (A→A→A) → (B→B→C) → C`
  (`NRT.relW2`, `NRT.rtheorem_relW2Fm`) has no positively `ℕ`-graded closed typing: `h`
  would need an argument of grade exactly `1` and one of grade `≥ 2`. Inversion lemmas
  `NRT.PHas.inv_var`, `inv_lam`, `inv_app` are used for this.

## `RequestProject/Section3_NaturalReductionTypes/HeadNeededGeneral.lean` — head neededness for general grades

* `NRT.Has.head_needed_sound_gen`: the soundness of grade `0` for head neededness holds in any
  nontrivial semiring where `a + b = 0` implies `a = 0` (not only `ℕ`).

## `RequestProject/Section5_Instances/QualitativeRelevance.lean` — the idempotence dial meets Curry–Howard

* `RML.trust_rel_iff_positive`, `RML.bt_rel_iff_positive`: over the trust and binding-time
  algebras, relevant implication is exactly positive graded typing.
* `RML.relW2_trust` vs `RML.relW2_not_nat`: the same λ-term has a positively trust-graded
  closed typing but no positive `ℕ`-graded one — counting is finer than relevance.
* `RML.trust_untrusted_not_head`, `RML.bt_dynamic_not_head`: an untrusted (resp. dynamic)
  variable never becomes the head variable of any reduct. This is only a head-position
  statement, not a full non-interference theorem.

## Not formalized

* Cut elimination for the 1995/1996 logic. The note only mentions it ("proved once,
  generically") and refers to the 1996 paper for it.
* Completeness of the 1993 system with respect to head neededness.
* The converse direction of the Curry–Howard correspondence over `ℕ` at the level of
  formulas (it fails at the level of proof terms, see above; it holds for idempotent grades).
* Full non-interference for the trust instance, which the note itself says is absent
  (only the head-position statement above is proved).
