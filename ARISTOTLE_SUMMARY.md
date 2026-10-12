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