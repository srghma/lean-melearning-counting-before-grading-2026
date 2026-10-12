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