# Formalization of *Counting before Grading* (D. A. Wright, 2026)

Most of the note is historical and bibliographic: the arc of the programme, the
dictionary in Table 1, the discussion of what was anticipated, and the question of
credit. Those parts make no mathematical claims and are **not** formalized. What follows
covers the technical content of Sections 3–5 and the facts about the annotation algebras
that the note relies on.

All files build with no `sorry`. The only axioms used are the standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

## `RequestProject/NaturalReductionTypes.lean` — Section 3 (1993 system)

| Paper | Lean |
|---|---|
| graded arrows `σ →_b τ` | `NRT.Ty.arr b σ τ` |
| judgement `A ⊢_V M : τ` with neededness function `V` | `NRT.Has Γ V M τ` |
| App rule, `V(x) = V₁(x) + b × V₂(x)` | constructor `NRT.Has.app` |

The type system is generic over any semiring `R` of grades; the 1993 system is `R = ℕ`.
Terms are untyped λ-terms with de Bruijn indices, and a context gives a type to every
variable.

* `NRT.subject_reduction`, `NRT.subject_reduction_star`: β-reduction anywhere in a term
  preserves the type **and the exact neededness function**. This is proved once for an
  arbitrary semiring; neither commutativity nor idempotence is needed. It rests on the
  graded substitution lemma `NRT.has_subst`, whose usage is `Γ + r·Δ`.
* `NRT.head_needed_sound` (grades in `ℕ`): suppose a typing gives a free variable `x`
  grade `0`. Then no β-reduct of the term is a head normal form whose head variable is
  `x`. This is soundness of grade `0` with respect to head neededness. The 1993 paper
  also claims a **completeness** result, but the note does not state it precisely
  enough to formalize, so it is not formalized here.
* `NRT.kxx_typing` and `NRT.kxx_occurrences` cover "occurrences vs uses": the term
  `λx. K x x` has type `σ →₁ σ`, so its argument is used once, even though it occurs
  twice.
* `NRT.twice_typing`: `Twice = λf x. f (f x)` has type `(σ →ᵢ σ) →_{1+i} σ →_{i·i} σ`.
  `NRT.compose_typing`: `λg f x. g (f x)` gives `x` the grade `i·j`.
  **Note:** the paper says that the derivation for `Twice` produces `i × j`. With simple
  types, `f` has a single arrow grade `i`, so the bound variable gets `i·i`. A genuine
  product `i·j` of two different grades shows up for composition.

## `RequestProject/ResourceLogic.lean` — Section 4 (1995 framework)

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

## `RequestProject/Instances.lean` — Section 5 (instances) and the idempotence dial

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

## `RequestProject/RelevantLogic.lean` — Section 3, Curry–Howard to relevant logic

* `NRT.Fm` are implicational formulas. `NRT.Rel Γ U A` is labelled natural deduction
  for relevant implication `R→`. The label `U` is the set of hypotheses actually used:
  `→I` may only discharge a hypothesis that was used, and `→E` takes the union of the
  labels. `NRT.RTheorem A` means `A` is derivable with the empty label.
* `NRT.PHas` is the positively graded fragment of natural reduction types over `ℕ`
  (every arrow introduced or eliminated has grade `≥ 1`). `NRT.PHas.toHas` shows it is a
  fragment of `NRT.Has`.
* `NRT.PHas.toRel` (Curry–Howard, soundness): erasing the grades gives an `R→`
  derivation whose label is **exactly** the support `{x | V x ≠ 0}` of the neededness
  function. `NRT.PHas.toRTheorem` covers closed typings. As an example, the contraction
  axiom `(A → A → B) → A → B` is obtained from the typing of `W = λf x. f x x`
  (`NRT.wcomb_typing`, `NRT.rtheorem_W`).
* Grade `0` goes beyond relevant logic. `NRT.rel_sound_sugihara` proves `R→` sound for
  the three-element Sugihara monoid, and `NRT.rel_not_K` deduces that `A → B → A` is not
  a theorem of `R→`. `K : σ →₁ τ →₀ σ` is still typeable, so it has no positively
  graded typing (`NRT.K_not_positive`).
* The converse direction (lifting every `R→` proof to a graded typing) is not
  formalized: the note does not say exactly how the correspondence is set up.

## `RequestProject/Normalization.lean` — normalisation ("Curry–Howard–Tait")

* De Bruijn infrastructure: renaming, parallel substitution and their fusion laws. These
  are connected to the substitution `NRT.subst` used by β-reduction, and
  `NRT.step_psub` shows β-reduction is stable under substitution.
* `NRT.strong_normalization`: for any grade semiring, every term typeable in natural
  reduction types is strongly normalising for full β-reduction. It is proved with Tait's
  reducibility method (`NRT.Red`, `NRT.cr`, `NRT.red_fundamental`).
* `NRT.normal_form_head` (grades in `ℕ`): a typeable term reduces to a β-normal form with
  the same type and neededness function, and no grade-`0` variable is at its head.

## Not formalized

* Cut elimination for the 1995/1996 logic. The note only mentions it ("proved once,
  generically") and refers to the 1996 paper for it.
* Completeness of the 1993 system with respect to head neededness.
* The converse (completeness) direction of the Curry–Howard correspondence with relevant logic.
* Non-interference for the trust instance, which the note itself says is absent.
