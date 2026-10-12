# Summary of changes for run 79531985-77ad-416a-9a46-a949937f8343
`Ty` now takes the type of base types as a parameter, so base types are no longer fixed to `ℕ`:

```lean
inductive Ty (B : Type) (R : Type) : Type
  | base : B → Ty B R
  | arr : R → Ty B R → Ty B R → Ty B R
```

The whole project builds with no errors, no warnings and no `sorry`. I spot-checked the axioms of four of the changed theorems (`not_positive_relW2`, `K_not_positive`, `relW2_trust`, `strong_normalization`); they use only the standard ones. The work is committed.

**What changed**
- **Everywhere `Ty` is used:** every `Ty R` / `Ty ℕ` is now `Ty B R` / `Ty B ℕ`, with an implicit `{B : Type}`. This covers `NaturalReductionTypes.lean`, `HeadNeededGeneral.lean`, `RelevantLogic.lean`, `RelevantCompleteness.lean`, `QualitativeRelevance.lean` and `Normalization.lean`. Every theorem now holds for any type of base types, not just `ℕ`. `ℕ` is used only in one small worked `example` about `K`.
- **Relevant-logic formulas:** grade erasure turns `base β` into a formula atom, so the formulas had to change too. `NRT.Fm` is now `Fm B` with `atom : B → Fm B`, using the same `B`. Because `B` now names this type, I renamed formula variables called `B` to `C` (for example in `RPf`, `Rel.impI` and `rtheorem_W`). The Sugihara valuations now have type `B → Sug`.
- **Examples that used fixed atom numbers:**
  - `rel_not_K` and `K_not_positive` now take any two base types `a c : B` with `a ≠ c`.
  - The counterexample formula `relW2Fm` and its proof `relW2` now take three atoms `a b c : B`.
  - `not_positive_relW2` and `relW2_not_nat` are now stated directly about the λ-term `Tm.relW2`. That λ-term doesn't depend on the atoms.
  - `relW2_trust` takes the three atoms `a b c`.
- **Docs:** `FORMALIZATION.md` and the docstrings now describe the `B` parameter.

**Properties table:** I updated the Lean statements of the affected entries to match. Their statuses are unchanged: everything that was proved still builds. I also added an entry for the `Ty` definition itself.

**Not changed:** the Section 4 resource-logic formulas (`RML.Fm R` in `ResourceLogic.lean`) still use `atom : ℕ → Fm R`. You didn't ask for that file, but it is the same pattern and could be parametrized the same way.

# Summary of changes for run 0be5d7dd-5716-4fd6-9b34-3d7af0fc4623
I removed all three `omit ... in` uses from the project. Instead of declaring every type-class assumption up front and then omitting some, each file now adds an assumption only at the point where the following declarations start to need it. The whole project builds with no errors, no warnings and no `sorry`. No statement or proof changed, only where declarations sit in their files.

**`RequestProject/Section4_UnifiedFramework/ResourceLogic.lean`**
- This file used to start with `variable {R : Type} [Add R] [Mul R] [Zero R] [One R]` and needed two `omit` lines. The assumptions now come in steps:
  - `variable {R : Type}`, then `[Add R] [Mul R]`, covering `scaleZone`, `Coerces` and `forall₂_scaleZone`.
  - `[Zero R]`, covering `rep` and `localCondition_of_rep`.
  - `[One R]`, covering the four-zone calculus `Deriv`, the coercion lemmas and `scale_admissible`.
- To make this possible, the annotation arithmetic now sits in its own section ("Annotation arithmetic: scaling, coercion, repeated sums"), placed before the sequent calculus. The old heading above `Permeability` became "Permeability operators".

**`RequestProject/Section3_NaturalReductionTypes/RelevantCompleteness.lean`**
- `variable {R : Type}` now comes first. `erase_consR` doesn't use any algebra on the grades, so it moved under a new "Erasure of contexts" heading before `variable [Semiring R]`.

The Properties table didn't need changes, because none of its entries contained `omit`. The work is committed.

# Summary of changes for run 9887be3a-902b-4a9e-adbc-be684613cb18
I continued the formalization with three new files. The project builds with no `sorry`, and the new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**`RequestProject/Section3_NaturalReductionTypes/RelevantCompleteness.lean`: the link to relevant logic, in both directions.** The paper says the 1993 system comes "with Curry–Howard to the implicational fragment of relevant logic" but doesn't say which grades it means. Earlier work only had the direction from typed terms to proofs, over \(\mathbb N\).
- **Typed terms to proofs, for more grade algebras (`GTm.toRPfR`):** this now works for any grades where \(1 \neq 0\), there are no zero divisors, and a sum is zero only when its parts are. Every arrow must have a nonzero grade. Over \(\mathbb N\) this matches the earlier notion of positive grading (`positiveR_iff_positive`).
- **Proofs to typed terms, when \(1+1=1\) (`RPf.toGTm`):** every relevant-logic proof becomes a typed term with all arrows graded 1. It has the same underlying λ-term, and the variables with nonzero grade are exactly the hypotheses the proof uses.
- **Full equivalence (`rel_iff_positive`):** for such grades, being derivable in relevant logic is exactly the same as having a typing where every arrow has a nonzero grade.
- **The converse fails over \(\mathbb N\) (`not_positive_relW2`):** take the relevant-logic proof \(\lambda h\,a\,k.\ k\,(h\,(\lambda x.x))\,(h\,(\lambda x.\,a\,x\,x))\). No closed \(\mathbb N\)-graded typed term with all grades at least 1 has this λ-term, whatever its type. The variable \(h\) has a single graded type, but its first argument \(\lambda x.x\) forces grade exactly 1 and its second argument \(\lambda x.\,a\,x\,x\) forces grade at least 2. This failure is about this particular proof. Whether the formula itself has some other proof with such an \(\mathbb N\)-typing is still open.

**`RequestProject/Section3_NaturalReductionTypes/HeadNeededGeneral.lean`:** `GTm.head_needed_sound_gen` extends the head-neededness soundness result beyond \(\mathbb N\). In any grade algebra where \(1 \neq 0\) and a sum is zero only if its first part is, a grade-0 variable is never the head variable of any reduct.

**`RequestProject/Section5_Instances/QualitativeRelevance.lean`:** this applies the results above to the Section 5 algebras.
- `trust_rel_iff_positive` and `bt_rel_iff_positive`: the full equivalence holds for the trust and binding-time algebras.
- `relW2_trust` and `relW2_not_nat`: the same λ-term has a trust grading with no zero grades, but no such \(\mathbb N\)-grading. This is a concrete case of the "idempotence dial": counting tells apart proofs that relevance treats as the same.
- `trust_untrusted_not_head` and `bt_dynamic_not_head`: an untrusted (or dynamic) variable never becomes the head variable of any reduct. This only covers head position. It is not a full non-interference theorem, which the paper itself says is missing.

`FORMALIZATION.md` describes the new files and updates the "Not formalized" list. The Properties table has three new entries, all marked proved.

**Still not formalized:**
- Cut elimination for the 1995/1996 logic.
- Completeness of the 1993 system with respect to head neededness.
- Full non-interference for the trust instance.

# Summary of changes for run 00fd3079-d8b7-46d8-8f25-397e3c1d2ec5
I didn't change any files. Here is the answer.

**Why "this term has these several gradings" couldn't be written directly without `Tm`**

In the typed grammar, the type and the grades are part of the term itself. A value `d : GTm Γ V τ` is a term together with one fixed type \(\tau\) and one fixed grading \(V\). Two different gradings of `K`, say \(\sigma \to_1 \tau \to_0 \sigma\) and another one, are therefore two separate elements living in two different Lean types, such as `GTm ![] 0 τ₁` and `GTm ![] 0 τ₂`. Nothing in the typed grammar says they are "the same `K`", so there is no single object that "has" both gradings.

The paper's statement is about one plain λ-term \(M\) that gets several judgements \(A \vdash_V M : \tau\). To write that, you need \(M\) as an object of its own, apart from any grading. That object is the untyped `Tm`. It lets us state `Has Γ V₁ t τ₁ ∧ Has Γ V₂ t τ₂` for the same `t`, or equivalently "`d₁.erase = d₂.erase`". Without `Tm`, you would need some ad-hoc relation saying two typed terms "have the same shape", which amounts to defining `Tm` again in a roundabout way.

**What `RPf` and `ATm` are**

- **`RPf`** (in `Section3_NaturalReductionTypes/RelevantLogic.lean`) is the grammar of proof terms for the implicational fragment of relevant logic. This is the logic the paper's Section 3 links to by Curry–Howard. `RPf Γ U A` is a proof of formula \(A\) from hypotheses `Γ` that uses exactly the hypotheses in the set `U`. Its three constructors are:
  - `hyp`: use one hypothesis;
  - `impI`: implication introduction, which may only discharge a hypothesis that was actually used;
  - `impE`: implication elimination, which takes the union of the used sets.
- **`ATm`** (in `Section4_UnifiedFramework/ResourceLogic.lean`) is the Section 4 annotated term grammar \(E ::= x^k \mid \lambda^k x.E \mid E_1 @^k E_2\). Every variable, λ and application carries a resource annotation \(k\). The paper gives these terms "the term semantics of the ordinary λ-calculus (erase annotations)".

**Why the "same term" results need `Tm`**

`GTm`, `RPf` and `ATm` are three unrelated grammars. Each has its own erasure into `Tm`, and the "same term" results are stated as equalities of erasures. For example, `GTm.toRPf_erase` says that turning a positively graded typed term into a relevant-logic proof keeps the underlying λ-term.

Without `Tm`, each pair of grammars would need its own translation, plus its own proof that the translation "keeps the term". That is more work. It also says less, because you only learn that one translation exists, not that both sides are literally the same λ-program.

# Summary of changes for run d2a75697-3187-4484-90b3-e781dec16399
I didn't change any files. Here is the answer.

**Does the paper use untyped terms?** Yes. It types terms "Curry-style": types and grades are assigned to plain λ-terms, rather than built into the terms themselves.
- **Section 3:** the judgement is \(A \vdash_V M : \tau\), where \(M\) is an ordinary λ-term and \(V\) records how much each variable is needed. The same term can get several gradings: `K` has type \(\sigma \to_1 \tau \to_0 \sigma\) as one instance among others.
- **Soundness and completeness are stated with respect to head neededness.** Head neededness is a property of how the plain term runs under β-reduction, so you need a notion of "the program" that exists apart from its typing.
- **The \(\lambda x.\,K\,x\,x\) example** compares how often \(x\) *occurs* in the term (twice) with how often it is *used* (once). That only makes sense if the term exists separately from its derivation.
- **Section 4:** the annotated terms \(E ::= x^k \mid \lambda^k x.E \mid E_1 @^k E_2\) are given "the term semantics of the ordinary λ-calculus (erase annotations)". Erasure to untyped terms is part of the definition.
- **Curry–Howard to relevant logic** says that a typing derivation and a relevant-logic proof correspond to the *same* λ-term.

**How the formalization uses untyped `Tm`:** it is the one grammar that the three typed or annotated grammars all erase to: `GTm` (Section 3 typed terms), `RPf` (relevant-logic proof terms) and `ATm` (Section 4 annotated terms). It is used for:
- the plain-term β-reduction behind head neededness;
- the "same underlying term" results (`GTm.toRPf_erase`, `ATm.erase`, the erasures of `K`, `twice`, `compose` and `kxx`);
- `Has`, which is defined as "`t` is the erasure of some typed term" and exists to state the paper's judgement form.

The strong-normalization proof in `Normalization.lean` also uses it internally.

**Could we use only the typed grammar?** Technically yes, but I wouldn't. Typed reduction (`GStep`), typed substitution and the head-neededness result on typed terms already exist, and the normalization proof could be redone on typed terms. Dropping `Tm` would cost:
1. Faithfulness: the paper's judgement form \(A \vdash_V M : \tau\) and statements of the form "this term has these several gradings" could no longer be written directly.
2. The comparison between grammars: every "same term" result would have to become a direct translation between `GTm`, `RPf` and `ATm`, which is more work and says less.
3. Head-neededness soundness would only be about typed reduction, not about how the plain program runs, which is what the paper's claim is about.

`Tm` is small (it lives in `Syntax.lean`). Typed terms are already the main grammar everywhere, and `Tm` mostly serves as the shared target that erasure maps into. The sensible setup is the current one: typed terms as the main grammar, plus untyped `Tm` for erasure, β-reduction and cross-system statements.

# Summary of changes for run c662a164-4bee-4735-8608-72f83bf4aaa8
The typed, graded terms `GTm` are now the main grammar of the type system, and every result is stated in terms of them. `Intrinsic.lean` has been merged into the main files and deleted. The whole project builds with no `sorry` and no warnings. The key theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**`Section3_NaturalReductionTypes/NaturalReductionTypes.lean`**
- **Main grammar:** `GTm Γ V τ` is now defined here. Its three constructors are the three typing rules, so a term with the wrong scope, type or grades can't be written.
- **Erasure:** `GTm.erase` now uses ordinary pattern matching and is no longer `noncomputable`. For example, `#eval (kxx σ).erase` prints `λx. K x x`.
- **Untyped terms:** `Syntax.lean` is unchanged. The untyped terms `Tm n` are still what typed terms erase to and where β-reduction is defined.
- **Operations on typed terms:** renaming, weakening, embedding a closed term, graded substitution \(y \mapsto \sum_x V(x)\,W(x)(y)\) and the β-contractum (`GTm.inst`) now act directly on typed terms. The resulting grades show up in each result's type, and each operation has a lemma saying what it does to the erasure.
- **Typed reduction (`GStep`):** a new reduction relation on typed terms. A step goes from `GTm Γ V τ` to `GTm Γ V τ`, so it keeps the type and grades by construction.
- **Subject reduction (`GTm.lift_step`, `GTm.lift_steps`):** every β-step of `d.erase` comes from a typed step `GStep d d'`. `GStep.erase` gives the converse.
- **Head neededness:** `GTm.head_needed_sound` is now stated for typed terms.
- **Worked examples as closed typed terms:** `K`, `twice` and `compose`. `kxx` (\(\lambda x.\,K\,x\,x\)) is now also typed; the earlier version couldn't build it because typed renaming was missing. Each comes with a lemma giving its erasure. The untyped versions are now `Tm.K`, `Tm.kxx` and so on.
- **`Has`:** now *defined* as "`t` is the erasure of some `d : GTm Γ V τ`". Its rules and lemmas (renaming, substitution, subject reduction, head neededness) are derived from the typed versions.

**`Section3_NaturalReductionTypes/RelevantLogic.lean`**
- **Proof terms:** `RPf` (proofs that use exactly the hypotheses in `U`) is now the main grammar, and `Rel` is defined as `Nonempty RPf`.
- **Positive grading:** the old `PHas` predicate is replaced by `GTm.Positive`, a condition on typed terms.
- **Curry–Howard (`GTm.toRPf`, `GTm.toRel`):** a positively graded typed term becomes a relevant-logic proof term whose set of used hypotheses is exactly \(\{x \mid V(x) \neq 0\}\). `GTm.toRPf_erase` shows the proof term has the same underlying λ-term.
- **Contraction example:** `W` is now a typed term, with `W_positive`.
- **`K_not_positive` (stronger than before):** *no* closed typed term of type \(\sigma \to_1 \tau \to_0 \sigma\) is positively graded.

**`Section6_Dictionary/Normalization.lean`**
- `strong_normalization`: the erasure of every typed term is strongly normalising. The key lemma is now proved by induction on the typed term, and `Has.sn` gives the version for `Has`.
- `normal_form_head` and `closed_normalizes`: these now produce a typed normal form, reached by typed reduction.

**Renamed or removed statements:** top-level `subject_reduction` and `subject_reduction_star` are now `Has.subject_reduction` and `Has.subject_reduction_star`. `PHas` and `PHas.toRel` are replaced by `GTm.Positive` and `GTm.toRel`. `GTm.has_iff` and `RPf.nonempty_iff` are gone, because `Has` and `Rel` are now defined by those equivalences.

**Records:**
- `FORMALIZATION.md` describes the new structure.
- In the Properties table:
  - The affected entries are updated and still marked proved.
  - `GStep` and `RPf` are added.
  - The two equivalence entries are removed.

# Summary of changes for run 3b4ff10d-689a-4c1d-a8b5-f23d69419828
I added a new Lean file, `RequestProject/Section3_NaturalReductionTypes/Intrinsic.lean`, in which typing and grading, not just scoping, are correct by construction. The whole project builds with no `sorry`, and the new results use only the standard axioms.

The well-scoped terms were already in place before this session (`Tm : ℕ → Type` with `var : Fin n → Tm n`, so `Tm 0` is the closed terms). The context and grades of `Has`, the relevant-logic derivations and the Section 4 annotated terms were all indexed by `Fin n` in the same way. I left all of that unchanged and built on it.

**Typed terms that carry their own grades**
```lean
inductive GTm : {n : ℕ} → (Fin n → Ty R) → (Fin n → R) → Ty R → Type
  | var (x : Fin n) : GTm Γ (single x) (Γ x)
  | lam : GTm (Fin.cons σ Γ) V τ → GTm Γ (fun x => V x.succ) (.arr (V 0) σ τ)
  | app : GTm Γ V₁ (.arr b σ τ) → GTm Γ V₂ σ → GTm Γ (fun x => V₁ x + b * V₂ x) τ
```
An element of `GTm Γ V τ` is a term with free variables in `Fin n`, type `τ` and neededness function `V`. A term with the wrong scope, type or grades can't be written, and `GTm ![] 0 τ` is the type of closed terms of type `τ`.
- **Same as the existing judgement (`GTm.has_iff`):** `Has Γ V t τ` holds exactly when `t` is the erasure of some `d : GTm Γ V τ`.
- **Results carried over:**
  - `GTm.subject_reduction`: a β-reduct of a typed term is again a typed term with the same scope, type and grades.
  - `GTm.sn`: every typed term is strongly normalising.
  - `GTm.closed_normalizes`: a closed typed term reduces to a β-normal closed term of the same type.
- **Worked examples as closed typed terms:** `gK : GTm ![] 0 (σ →₁ τ →₀ σ)`, `gTwice` and `gCompose`. Each is proved to erase to the existing `K`, `twice` and `compose`.

**Proofs in relevant logic**
`RPf Γ U A` is the type of proof terms with hypotheses `Γ : Fin n → Fm` that use exactly the hypotheses in `U`. `RPf.nonempty_iff` shows that `Rel Γ U A` holds exactly when such a proof term exists, and each proof erases to a `Tm n`.

**Limitations:**
- The erasure functions are marked `noncomputable`. Lean's pattern matching doesn't accept these index shapes, so I defined erasure with the recursors; the typed terms themselves are ordinary data.
- `λx. K x x` has no typed version yet. Building it would need renaming for typed terms, which I haven't written.
- Type and formula atoms are still `ℕ`-named, and the Section 4 sequent zones are still lists, because neither involves bound variables.

`FORMALIZATION.md` has a new section describing the file. The Properties table now includes `NRT.GTm` and the two equivalences, `GTm.has_iff` and `RPf.nonempty_iff`, both marked proved.

# Summary of changes for run fe1b6fb9-ab90-4f80-8a3d-9aaa90f69c33
I changed the syntax so scoping is correct by construction. All the earlier results still hold in the new form. The whole project builds with no `sorry`, and the main theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Terms (new file `RequestProject/Section3_NaturalReductionTypes/Syntax.lean`)**
```lean
inductive Tm : ℕ → Type
  | var {n : ℕ} : Fin n → Tm n
  | lam {n : ℕ} : Tm (n + 1) → Tm n
  | app {n : ℕ} : Tm n → Tm n → Tm n
```
`Tm n` holds exactly the terms whose free variables are among `0 … n-1`, so `Tm 0` is the type of closed terms and an out-of-range index can't be written. The same file has renaming (`Fin n → Fin m`), parallel substitution (`Fin n → Tm m`), the single substitution `t[u]` used by β (`inst`), β-reduction `Step`, and the rules for combining these.

**The other datatypes follow the same pattern**
- **Typing judgement (`NRT.Has`):** for `t : Tm n`, the context is `Fin n → Ty R` and the neededness function is `Fin n → R`, so both cover exactly the variables in scope. A closed typing is written `Has ![] 0 t τ`.
- **Graded lemmas (rewritten):** substitution `Has.subst` now substitutes for all variables at once, and the new usage is \(y \mapsto \sum_x V(x)\,W(x)(y)\). Renaming `Has.rename` covers weakening, exchange and contraction.
- **Closed terms in larger scopes (new):** `Has.embed` lets a closed term be used in any scope without using any of its variables.
- **Positively graded fragment and relevant logic:** `PHas` and the relevant-logic derivations `Rel` are indexed by `Fin n`. `RTheorem A` now means "derivable from the empty set of hypotheses".
- **Annotated terms (Section 4):** these are now `RML.ATm R n`, and erasure maps them to `NRT.Tm n`.
- **Worked examples:** `K`, `λx. K x x`, `Twice`, `Compose` and `W` are now closed terms of type `Tm 0`, typed in the empty context. `K_not_positive` is now stated as `¬ PHas ![] 0 K …`.
- **Normalisation:** with scoped terms, reducibility at arrow type is now defined over all renamings into larger scopes. The proof needed two new facts: β-reduction commutes with renaming in both directions (`Step.rename`, `Step.of_rename`). There is a new corollary, `closed_normalizes`: every typeable closed term has a β-normal form of the same type.

**Unchanged:** the four-zone sequents of Section 4 were already lists of formulas, and type and formula atoms are names rather than bound variables, so they keep `ℕ`.

`FORMALIZATION.md` describes the new scoped design. In the Properties table, the changed statements have been updated (statuses unchanged) and `NRT.Tm` has been added.

# Summary of changes for run 6bb44566-c02f-447a-a28c-36acdbcb10db
I moved the Lean files into directories named after the sections of the paper:

- `RequestProject/Section3_NaturalReductionTypes/`: `NaturalReductionTypes.lean` (the 1993 system) and `RelevantLogic.lean` (the Curry–Howard link to relevant logic, which the paper states in Section 3).
- `RequestProject/Section4_UnifiedFramework/`: `ResourceLogic.lean` (the 1995 framework).
- `RequestProject/Section5_Instances/`: `Instances.lean` (the three instances).
- `RequestProject/Section6_Dictionary/`: `Normalization.lean` (strong normalisation, matching the dictionary's "Curry–Howard–Tait" and "generic normalisation" entries).

`Normalization.lean` was the one judgement call. It proves strong normalisation for the 1993 system, so it could also have gone under Section 3. I put it in Section 6 because the paper names this result in the dictionary. Sections 1, 2, 7 and 8 make no formal claims, so they have no directory. `RequestProject/Main.lean` stays where it was.

Moving the files changed their module names, so I updated the `import` lines that refer to them. In `FORMALIZATION.md`, I updated the file paths and added a short "Layout" table matching directories to paper sections. The Properties table entries now point to the new file locations, and their statuses are unchanged.

The full project builds successfully with the new layout, and there is no `sorry` anywhere. The proofs themselves were not edited.

# Summary of changes for run 41437202-e7d2-40f7-85f5-4378461e55f3
I added two new Lean files that cover more of the note's Section 3. The whole project builds, there is no `sorry`, and the new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). `FORMALIZATION.md` now covers both files.

**`RequestProject/RelevantLogic.lean`: the link to relevant logic.** The note says the 1993 system comes "with Curry–Howard to the implicational fragment of relevant logic", but doesn't say exactly how the correspondence is set up. So I formalized one direction, for a restricted part of the system.
- **Relevant logic:** I defined natural deduction for relevant implication (`NRT.Rel`). Each derivation records which hypotheses it actually uses. Implication introduction may only discharge a hypothesis that was used, and implication elimination combines the used sets.
- **Positive grades:** `NRT.PHas` is the part of the type system where every arrow that is introduced or eliminated has grade at least 1. It is contained in the full system (`NRT.PHas.toHas`).
- **Main theorem (`NRT.PHas.toRel`):** erasing the grades from such a typing gives a relevant-logic derivation. Its set of used hypotheses is exactly the set of variables with nonzero grade, \(\{x \mid V(x) \neq 0\}\).
- **Example:** the contraction axiom \((A \to A \to B) \to A \to B\) follows from the typing of \(W = \lambda f\,x.\ f\,x\,x\) (`NRT.rtheorem_W`).
- **Grade 0 goes beyond relevant logic:** relevant logic is sound for a three-element algebraic model (`NRT.rel_sound_sugihara`). From this, \(A \to B \to A\) is not a theorem of relevant logic (`NRT.rel_not_K`). But \(K : \sigma \to_1 \tau \to_0 \sigma\) is typeable, so \(K\) has no typing with only positive grades (`NRT.K_not_positive`).

**`RequestProject/Normalization.lean`: normalisation.** This corresponds to the dictionary's "Curry–Howard–Tait" and "generic normalisation" entries.
- **Strong normalisation (`NRT.strong_normalization`):** for any semiring of grades, every typeable term is strongly normalising for full β-reduction. The proof uses Tait's reducibility method and needed some new infrastructure for substitution, connected to the existing reduction relation.
- **Corollary (`NRT.normal_form_head`, natural-number grades):** every typeable term reduces to a β-normal form with the same type and the same grades. No variable with grade 0 is at its head.

The three new results are in the Properties table, marked proved.

**Still not formalized:**
- Lifting every relevant-logic proof back to a graded typing (the converse of the Curry–Howard link).
- Completeness of the 1993 system with respect to head neededness.
- Cut elimination for the 1995/1996 logic.
- Non-interference for the trust instance.

The note doesn't state the first three precisely enough to formalize. It says itself that non-interference is absent.

# Summary of changes for run 52f3701d-99b8-49a9-9583-fb05db6fe3a5
I formalized the mathematical content of *Counting before Grading* (Sections 3–5) in Lean. Everything builds with no `sorry`, and the only axioms used are the standard ones. Most of the note is history, the comparison table and the discussion of credit; those parts make no mathematical claims, so there was nothing to formalize there. `FORMALIZATION.md` maps each part of the paper to its Lean declaration.

**`RequestProject/NaturalReductionTypes.lean` (Section 3, the 1993 system).**
- **The type system:** types with graded arrows \(\sigma \to_b \tau\), and the judgement `NRT.Has Γ V t τ` with a neededness function \(V\). Its application rule is the paper's \(V(x) = V_1(x) + b \cdot V_2(x)\). It works for any semiring of grades; the 1993 system is the natural-number case.
- **Subject reduction** (`subject_reduction_star`): β-reduction anywhere in a term keeps both the type and the exact neededness function. It is proved once for any semiring.
- **Soundness for head neededness** (`head_needed_sound`, natural-number grades): if a variable has grade 0, no reduct of the term is a head normal form with that variable at its head.
- **Worked examples:**
  - `λx. K x x : σ →₁ σ`: the argument is used once but occurs twice (`kxx_typing`, `kxx_occurrences`).
  - `Twice` gets type \((\sigma\to_i\sigma)\to_{1+i}\sigma\to_{i\cdot i}\sigma\).
  - Composition gives the product \(i\cdot j\).

**`RequestProject/ResourceLogic.lean` (Section 4, the 1995 framework).**
- **The logic:** the four-zone sequent calculus `RML.Deriv`. It is parametric in the annotation algebra and in the permeability operators, and includes every displayed rule as printed. The annotated terms and their erasure are also defined.
- **Additive coercion** (`coerce`): adding a grade to any formula in the inner zones preserves derivability.
- **Scaling from coercion** (`scale_admissible`): under the paper's local condition, the scaling rule \((\cdot k)\) can be removed, because anything it derives is also derivable from the additive coercion rules. `localCondition_of_rep` and `localCondition_natCast` connect this to the condition \(i+\dots+i = k\,i\) and show it holds for every \(k \ge 1\) in a semiring.

**`RequestProject/Instances.lean` (Section 5).**
- **Binding-time logic:** the paper's eight-row combination table for \((i+k)j\) is checked.
- **Trust logic:** an application is trusted iff both the function and the argument are trusted, and the coercion of conclusions to \(T\) is derived from \((+k)_R\).
- **Logic of unity:** dereliction \(\cdot; A^\omega \vdash \cdot; A\) is derivable, and the grade \(\omega\) can be contracted and weakened.
- **Idempotence:** \(k\cdot k = k\) in the two Boolean algebras but not in \(\mathbb N\), where \(1+1=2\).
- **The natural-number instance:** removing the scaling rule works for every \(k \ge 1\).

**Discrepancies and modelling choices:**
- The paper says the derivation for `Twice` yields \(i\times j\). With simple types, `f` has only one grade, so the result is \(i\cdot i\). A genuine product \(i\cdot j\) appears for composition, which I proved separately.
- The paper lists grades for the logic of unity but does not define the operations, so the three-element none/one/many semiring I used is my own choice.

**Not formalized:**
- The completeness half of the 1993 result: the note does not state it precisely.
- Cut elimination: the note only mentions it and points to the 1996 paper.
- The Curry–Howard link to relevant logic.
- Non-interference for the trust instance, which the note itself says is absent.