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
| `RequestProject/Section3_NaturalReductionTypes/` | 3. The quantitative core: natural reduction types (1993) | `Syntax.lean`, `NaturalReductionTypes.lean`, `RelevantLogic.lean` |
| `RequestProject/Section4_UnifiedFramework/` | 4. The unified framework (1995) | `ResourceLogic.lean` |
| `RequestProject/Section5_Instances/` | 5. Three instances (1995) | `Instances.lean` |
| `RequestProject/Section6_Dictionary/` | 6. A dictionary (generic normalisation) | `Normalization.lean` |

Sections 1, 2, 7 and 8 contain no formalizable claims, so they have no directory.

## `RequestProject/Section3_NaturalReductionTypes/NaturalReductionTypes.lean` — Section 3 (1993 system)

| Paper | Lean |
|---|---|
| graded arrows `σ →_b τ` | `NRT.Ty.arr b σ τ` |
| derivations of `A ⊢_V M : τ` with neededness function `V` | terms of the grammar `NRT.GTm Γ V τ` |
| App rule, `V(x) = V₁(x) + b × V₂(x)` | constructor `NRT.GTm.app` |
| the judgement about an untyped term `M` | `NRT.Has Γ V M τ` (derived: `M` is the erasure of some `d : GTm Γ V τ`) |

The type system is generic over any semiring `R` of grades; the 1993 system is `R = ℕ`.

**The main grammar: typed, graded terms (correct by construction).** The type system is
given as an indexed family of terms

```lean
inductive GTm : {n : ℕ} → (Fin n → Ty R) → (Fin n → R) → Ty R → Type
  | var (x : Fin n) : GTm Γ (single x) (Γ x)
  | lam : GTm (Fin.cons σ Γ) V τ → GTm Γ (fun x => V x.succ) (.arr (V 0) σ τ)
  | app : GTm Γ V₁ (.arr b σ τ) → GTm Γ V₂ σ → GTm Γ (fun x => V₁ x + b * V₂ x) τ
```

An element of `GTm Γ V τ` is a λ-term with free variables in `Fin n`, of type `τ`, with
neededness function `V`. Ill-scoped, ill-typed or wrongly graded terms cannot be written,
and `GTm ![] 0 τ` is the type of closed terms of type `τ`. `NRT.GTm.erase` (computable,
defined by pattern matching) gives the underlying untyped term.

**Untyped well-scoped syntax.** `Syntax.lean` defines the untyped terms that typed terms
erase to: `NRT.Tm : ℕ → Type` with `var : Fin n → Tm n`, `lam : Tm (n+1) → Tm n` and
`app`, so `Tm 0` is the type of closed terms. Renaming, parallel substitution, the single
substitution `t[u]` (`NRT.inst`) and β-reduction `NRT.Step` live there.

**Metatheory as operations on typed terms.** Each lemma is a function whose result type
records the conclusion, together with a lemma saying what it does to the erasure:

* `NRT.GTm.rename` (weakening, exchange, contraction): renaming along `ρ` gives usage
  `rmap ρ V` (the grade of a new variable is the sum of the grades of the old variables
  renamed to it). `NRT.GTm.weaken` and `NRT.GTm.embed` (closed terms in any context, with
  no usage) are special cases.
* `NRT.GTm.subst` (graded parallel substitution): substituting typed terms `s x` with
  usage `W x` gives usage `y ↦ Σₓ V(x)·W(x)(y)`. `NRT.GTm.inst` is the typed β-contractum,
  with usage `y ↦ V(y+1) + V(0)·V₂(y)`.
* `NRT.GStep` is β-reduction **of typed terms**. Its type
  `GTm Γ V τ → GTm Γ V τ → Prop` says that the type and the exact neededness function
  are preserved, so subject reduction holds by construction. `NRT.GStep.erase` shows each
  typed step is a β-step of the erasures, and `NRT.GTm.lift_step` / `NRT.GTm.lift_steps`
  show the converse: every β-step of `d.erase` comes from a typed step `GStep d d'`. This
  is subject reduction, proved once for an arbitrary semiring.
* `NRT.GTm.head_needed_sound` (grades in `ℕ`): if a typed term gives a free variable `x`
  grade `0`, then no β-reduct of it is a head normal form whose head variable is `x`. The
  1993 paper also claims a **completeness** result, but the note does not state it
  precisely enough to formalize, so it is not formalized here.

**Worked examples, as closed typed terms.**

* `NRT.kxx σ : GTm ![] 0 (σ →₁ σ)` is `λx. K x x` (`NRT.kxx_erase`): its argument is used
  once, although it occurs twice in the body (`NRT.kxx_occurrences`).
* `NRT.K σ τ : GTm ![] 0 (σ →₁ τ →₀ σ)`.
* `NRT.twice σ i : GTm ![] 0 ((σ →ᵢ σ) →_{1+i} σ →_{i·i} σ)` is `λf x. f (f x)`, and
  `NRT.compose σ₁ σ₂ σ₃ i j` is `λg f x. g (f x)`, giving `x` the grade `i·j`.
  **Note:** the paper says that the derivation for `Twice` produces `i × j`. With simple
  types, `f` has a single arrow grade `i`, so the bound variable gets `i·i`. A genuine
  product `i·j` of two different grades shows up for composition.
* The untyped terms are `NRT.Tm.K`, `NRT.Tm.kxx`, `NRT.Tm.twice`, `NRT.Tm.compose`;
  `NRT.kxx_typing`, `NRT.twice_typing`, `NRT.compose_typing` restate the examples with
  `Has`.

**The extrinsic judgement.** `NRT.Has Γ V t τ` is defined as `∃ d : GTm Γ V τ, d.erase = t`.
Its rules (`Has.var`, `Has.lam`, `Has.app`) and lemmas (`Has.rename`, `Has.subst`,
`Has.subject_reduction`, `Has.subject_reduction_star`, `Has.head_needed_sound`) are
derived from the corresponding operations on `GTm`.

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

* `NRT.Fm` are implicational formulas. Relevant implication `R→` is given as a grammar of
  proof terms: `NRT.RPf Γ U A` is the type of labelled natural-deduction proofs of `A` from
  hypotheses `Γ : Fin n → Fm` that use exactly the hypotheses in `U`. `→I` may only
  discharge a hypothesis that was used, and `→E` takes the union of the labels. Proofs
  erase to untyped terms (`NRT.RPf.erase`). Derivability `NRT.Rel Γ U A` is defined as
  `Nonempty (RPf Γ U A)`, and `NRT.RTheorem A` means `A` is derivable with the empty label.
* `NRT.GTm.Positive` (over `ℕ`) says every arrow a typed term introduces or eliminates has
  grade `≥ 1`.
* `NRT.GTm.toRPf` (Curry–Howard, soundness): a positively graded typed term is turned into
  an `R→` proof term with the same underlying λ-term (`NRT.GTm.toRPf_erase`), whose label
  is **exactly** the support `{x | V x ≠ 0}` of the neededness function. `NRT.GTm.toRel`
  and `NRT.GTm.toRTheorem` are the derivability versions. As an example, the contraction
  axiom `(A → A → B) → A → B` is obtained from the typed term `NRT.W` for
  `W = λf x. f x x` (`NRT.W_positive`, `NRT.rtheorem_W`).
* Grade `0` goes beyond relevant logic. `NRT.rel_sound_sugihara` proves `R→` sound for
  the three-element Sugihara monoid, and `NRT.rel_not_K` deduces that `A → B → A` is not
  a theorem of `R→`. `K : σ →₁ τ →₀ σ` is still a typed term, so **no** closed typed term
  of that type is positively graded (`NRT.K_not_positive`).
* The converse direction (lifting every `R→` proof to a graded typing) is not
  formalized: the note does not say exactly how the correspondence is set up.

## `RequestProject/Section6_Dictionary/Normalization.lean` — Section 6 (dictionary), normalisation ("Curry–Howard–Tait")

* `NRT.Step.rename`, `NRT.Step.subst` and `NRT.Step.of_rename` (in `Syntax.lean`) show
  that β-reduction commutes with renaming in both directions. Since terms are well scoped,
  reducibility is defined Kripke-style: a term of arrow type is reducible if every renaming
  of it into a larger scope, applied to a reducible argument, is reducible.
* `NRT.strong_normalization`: for any grade semiring, the erasure of every typed term
  `d : GTm Γ V τ` is strongly normalising for full β-reduction. It is proved with Tait's
  reducibility method (`NRT.Red`, `NRT.cr`, `NRT.red_fundamental`, the last by induction
  on the typed term). `NRT.Has.sn` is the version for the extrinsic judgement.
* `NRT.normal_form_head` (grades in `ℕ`): a typed term reduces, by typed reduction
  `GStep`, to a typed term (same type, same neededness function) whose erasure is β-normal,
  and no grade-`0` variable is at its head.
* `NRT.closed_normalizes`: every closed typed term `d : GTm ![] 0 τ` reduces to a closed
  typed term of the same type whose erasure is β-normal.

## Not formalized

* Cut elimination for the 1995/1996 logic. The note only mentions it ("proved once,
  generically") and refers to the 1996 paper for it.
* Completeness of the 1993 system with respect to head neededness.
* The converse (completeness) direction of the Curry–Howard correspondence with relevant logic.
* Non-interference for the trust instance, which the note itself says is absent.
