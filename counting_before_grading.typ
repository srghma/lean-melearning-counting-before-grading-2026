#import "@preview/curryst:0.6.0": prooftree, rule

#show sym.tack.r: math.scripts

#set page(
  paper: "a4",
  margin: (x: 2.5cm, top: 2.5cm, bottom: 2.5cm),
  header: context {
    if counter(page).get().first() > 1 {
      text(size: 9pt)[
        #grid(
          columns: (1fr, 1fr),
          align(left)[Counting before Grading],
          align(right)[David A. Wright],
        )
      ]
    }
  },
  footer: context {
    text(size: 10pt)[
      #align(center)[#counter(page).display()]
    ]
  },
)

#set text(
  font: "New Computer Modern",
  size: 10pt,
  lang: "en",
)

#set par(
  justify: true,
  leading: 0.6em,
  first-line-indent: 1.5em,
)

// Title block
#align(center)[
  #v(1.2em)
  #text(17pt)[Counting before Grading]\
  #v(0.4em)
  #text(12pt)[A Resource-Annotation Programme for Type Systems (1989--2003)\ and its Relation to Graded and Coeffect Types]\
  #v(1.2em)
  #text(10.5pt)[David A. Wright]\
  #v(0.3em)
  #text(10pt)[June 2026]
  #v(1.5em)
]

// Abstract
#block(
  inset: (x: 2.5em),
  [
    #set text(size: 9pt)
    #set par(first-line-indent: 0pt, justify: true)
    #align(center)[#strong[Abstract]]
    #v(0.3em)
    Graded and bounded type systems---semiring-indexed refinements of the linear-logic exponential that track how many times, and how shareably, a program uses its context---are usually traced to Bounded Linear Logic (1992) and to the coeffect / graded-modal line of the 2010s. This note documents an earlier and largely uncited body of my own work, running from strictness analysis in the late 1980s to a logic of passivity in 2003, that arrived independently at the central ideas of graded typing. Its quantitative core (natural-number grading with the semiring action, proved sound and complete) is in print by 1993; its diagnosis of why the linear $!$ is too coarse---that it counts occurrences, not uses---is stated there too. Its organising abstraction---a single annotated logic instantiated by choice of algebra, with idempotent and non-idempotent algebras as different points---is realised, with worked instances for usage, binding-time and information-flow (trust) analyses, in a 1995 working paper now archived with a DOI. I sketch the arc of the programme, present the 1995 logic and its examples in a clean formulation, give an explicit correspondence (a "dictionary") to modern graded type systems, delimit what was and was not anticipated, and assess the question of scholarly credit.
  ],
)
#v(1.2em)

#set heading(numbering: "1.1")
#show heading: set text(size: 10.5pt, weight: "bold")
#show heading.where(level: 1): it => {
  v(1.5em)
  text(11pt, weight: "bold")[#it]
  v(0.6em)
}

= The modern picture, in one paragraph

A graded (or quantitative) type system replaces the binary linear/non-linear distinction with a modality $square.stroked_r A$ indexed by an element $r$ of a semiring $R$ of grades. Grade 1 is linear use, 0 is non-use, $omega$ (or $lt.eq infinity$) is unrestricted use; the additive structure of $R$ governs contraction (when a variable is shared, its grades add) and the multiplicative structure governs promotion (entering a modality scales the whole context by the grade). When $R = NN$ or an interval algebra over $NN$, the system counts: it expresses bounded reuse and recovers Bounded Linear Logic. This is the common shape of Bounded Linear Logic [10], the resource semiring of Ghica and Smith [12], the coeffect calculi [13, 14], their unification with effects [15], the graded-modal language Granule [16], and the generic substructural framework of Wood and Atkey [17]. The selling points are uniformity (many analyses as one parametrised system) and modular metatheory (prove soundness once, generically over the semiring). Information-flow security appears as a prominent instance, with a security lattice serving as the grade algebra.

= A programme, 1989--2003

I approached the ideas above, by a different route and under different names, in a sequence of papers (with Clement Baker-Finch on one of them). The route is static program analysis and relevant logic rather than linear logic and category theory, which is part of why the connection has been missed; the venues---a technical report, a TAPSOFT session, a thesis, a static-analysis workshop, and two editions of an Australasian theory symposium---sit outside the ESOP/ICFP/LICS circuit where the graded-types literature later formed.

#strong[Genesis: strictness, reduction types, intensionality (1989--1992).] The programme begins in strictness analysis. _Strictness Analysis via (Type) Inference_ [1] and _A New Technique for Strictness Analysis_ [2] cast a classical analysis as a type-inference problem; the doctoral thesis _Reduction Types and Intensionality in the Lambda-Calculus_ [3] introduces the reduction types on which the later usage work is built, with _intensionality_---tracking how a term computes, not merely what it denotes---as the organising theme. (I characterise these from their titles and their role in the documented lineage; the 1993 paper builds directly on the reduction-types framework of the thesis.) The essential germ is already here: decorate types with information about use, and infer it.

#strong[The quantitative core (1993).] _Usage Analysis with Natural Reduction Types_ [4], with Baker-Finch, annotates function constructors with natural numbers and proves a usage discipline sound and complete. This is the counting system; Section 3 treats it in detail.

#strong[The unified framework (1995).] _Resource Monitoring and Control_ [5], a working paper dated 8 June 1995 and now archived, presents a single annotated logic, parametric in the annotation algebra, and instantiates it across several analyses. This is the organising abstraction of the whole programme; Section 4 and Section 5 present its logic and examples.

#strong[The published framework, and passivity (1996, 2003).] _Linear, Strictness and Usage Logics_ [6] publishes a framework in which Linear, Affine, Usage and Strictness logics are instances chosen by algebra, with cut-elimination proved once, generically. _Linearity and Passivity_ [7] integrates linearity with Reynolds's syntactic control of interference [8]---passivity as a contraction discipline---using the zoned-sequent notation whose origin is the 1995 paper.

Two structural facts organise the rest of this note. First, the counting is in the earliest published paper (1993), and the occurrences-vs-uses critique of $!$ is stated there. Second, the variation across algebras was the thesis, not an artefact of separate papers: multiplicative idempotence was a dial, pulled in for the qualitative instances (the Boolean algebras of strictness, binding-time and trust, where $k dot.c k = k$) and left out for the quantitative one ($NN$, where $1 + 1 = 2$ and the system genuinely counts). The 1995 paper is where both facts become visible at once.

= The quantitative core: natural reduction types (1993)
<sec:quantitative>

== Grades are natural numbers; the application rule is the semiring action

The 1993 system fixes ground arrows ${arrow.r_0, arrow.r_1, arrow.r_2, dots}$, one per $n in NN$, with operations defined as ordinary arithmetic, $arrow.r_i + arrow.r_j = arrow.r_(i+j)$ and $arrow.r_i times arrow.r_j = arrow.r_(i times j)$---in the paper's words, "a polynomial algebra over the natural numbers." A judgement $A scripts(tack.r)_V M : tau$ carries a variable neededness function $V$. The rule that matters is application:

#v(0.4em)
#align(center)[
  #grid(
    columns: (auto, auto),
    gutter: 2.5em,
    align: horizon,
    prooftree(rule(
      name: "App",
      $A scripts(tack.r)_(V_1) N_1 : sigma arrow.r_b tau$,
      $A scripts(tack.r)_(V_2) N_2 : sigma$,
      $A scripts(tack.r)_V N_1 med N_2 : tau$,
    )),
    [$V(x) = V_1(x) + (b times V_2(x))$.],
  )
]
#v(0.4em)

Read $V$ as a graded context: applying a function whose arrow is graded $b$ scales the argument's usage context by $b$ and adds it to the function's. That is precisely the interaction of promotion ($r dot.c Gamma$) and contraction ($Gamma + Delta$) in modern graded calculi. Because $+$ and $times$ are honest $NN$ operations, the system counts: the derivation for $"Twice" = lambda f x. f (f x)$ yields $i times j$ for the bound variable, an actual product of use-counts.

== It is sound and complete, and diagnoses the coarseness of !

The discipline is proved sound and complete with respect to head neededness, with Curry--Howard to the implicational fragment of relevant logic. Its conclusion compares natural reduction types to linear logic and states the gap that bounded/graded systems were later built to close: linear $!$ "confuses sharing with absence" and "at best indicates several occurrences rather than several uses". The illustration is $lambda x. K x x$: where linear logic offers $!sigma multimap sigma$, the reduction type $sigma arrow.r_1 sigma$ records that the argument is used once though it occurs twice. The proposed cure---annotate with a number, propagate arithmetically---is the move from $!$ to a counting modality.

= The unified framework (1995)
<sec:framework>

The 1995 paper carries the title _Resource Monitoring and Control: two axes_ (describing usage versus restricting it) that the programme treats as one design space. Its logic is parametric in an annotation algebra with two operations $+$ and $dot.c$ and basic values $0, 1$, each instance fixing the algebra; a table maps grades ($0, 1, lt.eq 1, gt.eq 1, lt.eq infinity, dots$) to the compiler optimisations they enable ($0$: redundant; $1$: update-in-place / call-by-value; and so on). I give the logic in its fullest, four-zone form below---which I take to be the most elegant formulation, for the reason given in Section 4.1---and note where the 2003 paper trades that symmetry for compactness.

== Judgements: zoned sequents
<sec:judgements>

A sequent has four zones,
$ Psi; Gamma tack.r Delta; Theta, $
where the position of an assumption encodes its contraction permission. The outer zones $Psi$ (left) and $Theta$ (right) carry assumptions usable without restriction; the inner zones $Gamma, Delta$ carry assumptions whose use is governed by their annotation. Movement between outer and inner zones is mediated by explicit permeability operators---this is the device that internalises the 1993 "neededness function" into the context structure, and the ancestor of the #smallcaps[Passify] rule of the 2003 paper. The left/right symmetry is not incidental: the left zones carry the hypothesis-facing (necessity / coeffect) annotations and the right zones the conclusion-facing (possibility / effect) annotations, so the two modal readings discussed in Section 7 sit cleanly on opposite sides of the turnstile. This is why the four-zone presentation is, despite its size, the more elegant of the formulations: it keeps separate things separate. (The 2003 paper is more compact---it collapses to three one-sided zones---but in doing so it folds the two sides together and loses exactly this separation.) In present-day terms the separation has a name on each side: the left (hypothesis-facing) zones are a graded _coeffect_ discipline---how the conclusion uses its assumptions---and the right (conclusion-facing) zones a graded _effect_ discipline---what the conclusion itself carries. The symmetric sequent is thus both at once, in one system. The unification of effects and coeffects by grading is a development of the later literature [15]; what the 1995 formulation supplies is the structural shape of that combination---grades on both sides of a single turnstile---if not its vocabulary or its categorical semantics.

== Rules

#block[
  #strong[Identity and permeability.]
  #v(0.3em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    align: center,
    prooftree(rule(name: $"Id"_1$, $dot.c; A^1 tack.r A^1; dot.c$)),
    prooftree(rule(name: $"Id"_2$, $A; dot.c tack.r dot.c; A$)),
  )
  #v(0.4em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    align: center,
    prooftree(rule(
      name: $P_L^arrow.r$,
      $Psi, A; Gamma tack.r Delta; Theta$,
      $Psi; P_L^arrow.r (A), Gamma tack.r Delta; Theta$,
    )),
    prooftree(rule(
      name: $P_R^arrow.l$,
      $Psi; Gamma tack.r Delta; A, Theta$,
      $Psi; Gamma tack.r Delta, P_R^arrow.l (A); Theta$,
    )),
  )
  #v(0.4em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    align: center,
    prooftree(rule(
      name: $P_L^arrow.l$,
      $Psi, A; Gamma tack.r Delta; Theta$,
      $Psi; P_L^arrow.l (A), Gamma tack.r Delta; Theta$,
    )),
    prooftree(rule(
      name: $P_R^arrow.r$,
      $Psi; Gamma tack.r Delta, A; Theta$,
      $Psi; Gamma tack.r Delta; P_R^arrow.r (A), Theta$,
    )),
  )
]

#v(0.4em)
#block[
  #strong[Structural rules (weakening, contraction, exchange).] Weakening introduces a grade-0 assumption; contraction adds grades.
  #v(0.3em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    align: center,
    prooftree(rule(
      name: $W_L$,
      $Psi; Gamma tack.r Delta; Theta$,
      $Psi; A^0, Gamma tack.r Delta; Theta$,
    )),
    prooftree(rule(
      name: $W_R$,
      $Psi; Gamma tack.r Delta; Theta$,
      $Psi; Gamma tack.r Delta, A^0; Theta$,
    )),
  )
  #v(0.4em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    align: center,
    prooftree(rule(
      name: $C_L$,
      $Psi; A^i, A^j, Gamma tack.r Delta; Theta$,
      $Psi; A^(i+j), Gamma tack.r Delta; Theta$,
    )),
    prooftree(rule(
      name: $C_R$,
      $Psi; Gamma tack.r Delta, A^i, A^j; Theta$,
      $Psi; Gamma tack.r Delta, A^(i+j); Theta$,
    )),
  )
  #v(0.4em)
  #align(center)[
    #prooftree(rule(
      name: $E$,
      $Psi; Gamma tack.r Delta; Theta$,
      $sigma(Psi); sigma'(Gamma) tack.r tau(Delta); tau'(Theta)$,
    ))
  ]
]

#v(0.4em)
#block[
  #strong[Annotation rules.] Scaling the context by $k$ is promotion; adding $k$ to a grade is a graded coercion.
  #v(0.3em)
  #grid(
    columns: (1fr, 1fr, 1fr),
    gutter: 1em,
    align: center,
    prooftree(rule(
      name: $(dot.c k)$,
      $dot.c; Gamma tack.r Delta; dot.c$,
      $dot.c; k Gamma tack.r k Delta; dot.c$,
    )),
    prooftree(rule(
      name: $(+k)_L$,
      $dot.c; A^i, Gamma tack.r Delta; dot.c$,
      $dot.c; A^(i+k), Gamma tack.r Delta; dot.c$,
    )),
    prooftree(rule(
      name: $(+k)_R$,
      $dot.c; Gamma tack.r Delta, A^i; dot.c$,
      $dot.c; Gamma tack.r Delta, A^(i+k); dot.c$,
    )),
  )
]

#v(0.4em)
#block[
  #strong[Implication, and cut.] The connective is the annotated arrow; one of the three cut rules (one per zone pairing) is shown.
  #v(0.4em)
  #align(center)[
    #prooftree(rule(
      name: $(arrow.r L)$,
      $Psi; Gamma tack.r Delta; A, Theta$,
      $Psi', B; Gamma' tack.r Delta'; Theta'$,
      $Psi, Psi', A arrow.r_1 B; Gamma, Gamma' tack.r Delta, Delta'; Theta, Theta'$,
    ))
  ]
  #v(0.4em)
  #align(center)[
    #prooftree(rule(
      name: $(arrow.r R)$,
      $Psi, A; Gamma tack.r Delta; B, Theta$,
      $Psi; Gamma tack.r Delta; A arrow.r_1 B, Theta$,
    ))
  ]
  #v(0.4em)
  #align(center)[
    #prooftree(rule(
      name: $"Cut"_1$,
      $Psi; Gamma tack.r Delta; A, Theta$,
      $A, Psi'; Gamma' tack.r Delta'; Theta'$,
      $Psi, Psi'; Gamma, Gamma' tack.r Delta, Delta'; Theta, Theta'$,
    ))
  ]
]

A short derived-rules development relates $(dot.c k)$ to repeated $(+k)$: under the local condition
$ overbrace(i + dots.c + i, k) = k i, $
scaling is recovered from additive coercion alone. This is exactly the local algebraic side-condition on which the generic metatheory of later graded frameworks turns.

== Terms

Proofs are encoded by annotated $lambda$-terms (Curry--Howard--Tait),
$ E ::= x^k | lambda^k x. E | E_1 \@^k E_2, $
where $k$ ranges over the annotation algebra of the chosen instance; the term semantics is that of the ordinary $lambda$-calculus (erase annotations).

= Three instances (1995)
<sec:instances>

The framework is instantiated by choosing the algebra. The draft works three examples; I give each with its algebra and the way annotations combine at an application.

#block[
  #strong[A Logic of Unity.] The unrestricted end, with $lt.eq infinity$ as the "of course" grade and permeability $P_R^arrow.r (A^(lt.eq infinity)) = A^(lt.eq infinity), P_L^arrow.r (A) = A$ (and symmetrically). This is the instance in which the linear/intuitionistic decomposition of Girard's logic of unity is recovered; $lt.eq infinity$ is the reusable grade.
]

#block[
  #strong[Binding-Time Logic.] The two-element Boolean algebra with $D = 0$ (dynamic) and $S = 1$ (static); $+$ is join and $dot.c$ is meet. At an application the result grade is $(i + k)j$. Correctness---that only consistently-annotated terms are produced---is argued in the sense of Palsberg. The combination table:

  #v(0.3em)
  #align(center)[
    #table(
      columns: (2.5em, 2.5em, 2.5em, 4.5em, 6em),
      align: center,
      stroke: 0.4pt,
      table.header([$i$], [$j$], [$k$], [$(i+k)j$], [redex]),
      [$D$], [$D$], [$D$], [$D$], [dynamic],
      [$D$], [$D$], [$S$], [$D$], [dynamic],
      [$D$], [$S$], [$D$], [$D$], [dynamic],
      [$D$], [$S$], [$S$], [$S$], [static],
      [$S$], [$D$], [$D$], [$D$], [dynamic],
      [$S$], [$D$], [$S$], [$D$], [dynamic],
      [$S$], [$S$], [$D$], [$S$], [static],
      [$S$], [$S$], [$S$], [$S$], [static],
    )
  ]
]

#block[
  #strong[Trust Logic.] The two-element Boolean algebra with $U = 0$ (untrusted) and $T = 1$ (trusted). At an application the result grade is $j k$ (meet): the result is trusted only if the function and its argument are. A trust-coercion rule $dot.c; Gamma tack.r Delta; dot.c => dot.c; Gamma tack.r T + Delta; dot.c$ is derivable from $(+k)_R$. This is an _information-flow_ discipline: "trusted iff all inputs trusted" is the non-interference reading, with ${U, T}$ the two-point security lattice. It anticipates security-as-grading---one of the headline applications of the modern coeffect literature---by roughly two decades. (Trust analysis as a concept is due to Ørbæk; the contribution here is its rendering as one instance of a single parametric annotated logic alongside usage and binding-time.)
]

= A dictionary

Table 1 aligns the 1993 and 1995 systems with a contemporary graded presentation. The correspondence is structural; it is tight everywhere except the framing of the modality (an annotated arrow / proposition, not a graded exponential) and the substructural home (relevant logic, not linear logic).

The decisive entries are the application rule ($Gamma + b dot.c Delta$, the semiring action, present in 1993) and the trio (algebra-as-parameter, the zoned context, the Boolean security instance) that the 1995 paper supplies.

#figure(
  table(
    columns: (1fr, 1.15fr),
    align: (left, left),
    stroke: 0.4pt,
    table.header(
      [*Wright (1993 nrt; 1995 rmc)*],
      [*Modern graded / coeffect types*],
    ),
    [ground arrow $arrow.r_n$; grade on a proposition], [grade $r$ on the modality $square.stroked_r A$],
    [$arrow.r_i + arrow.r_j = arrow.r_(i+j)$; $A^i, A^j tack.r A^(i+j)$ (C)], [additive structure $r + s$ (contraction)],
    [$arrow.r_i times arrow.r_j = arrow.r_(i times j)$; $(dot.c k)$ scaling $k Gamma$], [multiplicative structure $r dot.c s$; promotion $r dot.c Gamma$],
    [neededness function $V$ (1993) $arrow.squiggly$ zoned context (1995)], [graded context $x :_r A$ (annotation internal to the context)],
    [$"APP": V(x) = V_1(x) + (b times V_2(x))$], [promotion then contraction: $Gamma + b dot.c Delta$],
    [grade $0$; $W$ introduces $A^0$], [grade $0$ (weakenable)],
    [permeability $P_L^arrow.r, P_R^arrow.r, dots$ (zone shifts)], [dereliction / structural rules of the modality],
    [choose the algebra (incl. idempotent vs not)], [choose the semiring $R$],
    [$NN$ non-idempotent ($1 + 1 = 2$)], [quantitative semirings ($NN$, intervals): BLL, bounded reuse],
    [Boolean ${D, S}, {U, T}$], [strictness / binding-time / security lattices as grades],
    [Curry--Howard--Tait to relevant logic], [substructural type theory; generic normalisation],
  ),
  caption: [The 1993 and 1995 systems against modern graded type systems.],
) <tbl:dictionary>

= What was anticipated, and what was not
<sec:anticipated>

Calibration matters; the claim is anticipation, not identity.

#strong[Genuinely present (1993--1995).]
- A non-idempotent $NN$-graded usage discipline, the semiring action realised by the application rule, proved sound and complete (nrt, 1993).
- The _occurrences-vs-uses_ critique of $!$---the stated motivation for bounded grading---with the numerical-annotation cure (nrt, 1993).
- A single parametric logic---zoned, permeable sequents with the semiring action---instantiated across usage, binding-time and information-flow (trust), with the annotation algebra (idempotent or not) as the explicit knob (rmc, 1995).
- The information-flow (security-lattice) instance specifically, two decades before it became a headline coeffect application (rmc, 1995).
- Grades on both sides of the turnstile---in modern terms a graded _coeffect_ discipline (hypotheses) and a graded _effect_ discipline (conclusions) carried in one symmetric system---structurally anticipating the later unification of effects and coeffects by grading [15] (rmc, 1995).
- Generic metatheory as the goal ("once-and-for-all" normalisation), with the local algebraic side-condition it depends on (rmc, 1995; cats, 1996).

#strong[Not present, or differently framed.]
- _Not framed as a graded exponential modality over linear logic:_ the carrier is an annotated arrow / proposition in a relevant-logic setting, not a graded $!$. This is a difference of presentation rather than of capability. An annotation $k$ on a proposition already behaves as a graded necessity---a "somewhat necessary" $square.stroked_k$---and nothing in the framework appears to preclude the dual graded possibility ("highly likely", $diamond.stroked_k$) reading; the annotation-on-proposition form is in fact neutral between the comonadic (coeffect / necessity) and monadic (effect / possibility) readings that the later literature separates. The neutrality is structural, not accidental: the four-zone sequent (Section 4.1) annotates both hypotheses and conclusions, placing the necessity-facing grades on the left of the turnstile and the possibility-facing grades on the right, so both modal readings are carried at once on their respective sides. What is absent is thus the explicit development of the annotation as a modality---its packaging as an exponential of linear logic, and the categorical semantics noted next---not the availability of the modal interpretation itself.
- _No categorical / denotational account via graded comonads,_ central to the modern semantic story. (As above, the framework does not exclude such a reading; it simply does not develop one.)
- The instances are mostly carried to soundness or consistency, not to the full metatheory (e.g. the trust instance is given algebra, coercion and combination table, but no non-interference theorem).
- Trust analysis as a concept is not original here (cf. Ørbæk); the contribution is the unification.

= On credit

The anticipation is real, and now citable. The assumption that quantitative grading begins with Bounded Linear Logic and matures only in the 2010s understates the record. The $NN$-graded counting calculus with the semiring action and a completeness result is in print in 1993; the _occurrences-vs-uses_ diagnosis is stated there; and the organising abstraction---one parametric annotated logic, instantiated by choice of algebra across usage, binding-time and information-flow, with idempotence as a dial---is realised in the 1995 working paper, now archived with a DOI [5] and so independently verifiable. A history or survey of graded and coeffect types would now be more complete for including it.

This is independent rediscovery, and that is no fault. The modern graded and coeffect systems reached these ideas independently, from Bounded Linear Logic and Wadler's linear types [11]; the framing differs (relevant logic and static analysis, not a graded exponential), and the earlier work was genuinely hard to find---scattered across obscure venues, with the central unifying paper unpublished until 2026. Independent rediscovery of a good idea is normal and entirely legitimate, and a literature search that does not surface work published in such places is an understandable outcome rather than a lapse to be laid at anyone's door. The sources the modern systems actually built on are properly cited, and their systems are their own. The point of recording the earlier work is not to move credit away from the later authors, but simply to let the lineage be seen whole.

Where this leaves the matter. I set this down not to claim more than the record supports, but to place it. The $NN$-graded counting calculus and its completeness result (1993), and the unifying "instantiate by choice of algebra" framework with its usage, binding-time and information-flow instances (1995), predate the graded and coeffect literature that later, and independently, arrived at the same shape. With the 1995 paper now archived and dated, that lineage is at last something a reader can check. Recording it is all this note is for.

= References

#set text(size: 9pt)
#set par(first-line-indent: 0em, hanging-indent: 2em, leading: 0.55em)

[1] D. A. Wright. _Strictness Analysis via (Type) Inference_. Technical Report TR89-3, University of Tasmania, September 1989.

[2] D. A. Wright. _A New Technique for Strictness Analysis_. In TAPSOFT'91, Vol. 2 (CCPSD), LNCS 494, Springer, 1991.

[3] D. A. Wright. _Reduction Types and Intensionality in the Lambda-Calculus_. Ph.D. thesis, University of Tasmania, 1992.

[4] D. A. Wright and C. A. Baker-Finch. _Usage Analysis with Natural Reduction Types_. In Static Analysis (WSA'93), LNCS 724, Springer, 1993.

[5] D. A. Wright. _Resource Monitoring and Control_. Working paper, 8 June 1995; archived Zenodo, 2026, CC BY 4.0. DOI: 10.5281/zenodo.20738711.

[6] D. A. Wright. _Linear, Strictness and Usage Logics_. In Proc. CATS'96 (Computing: The Australasian Theory Symposium), Melbourne, 1996.

[7] D. A. Wright. _Linearity and Passivity_. Electronic Notes in Theoretical Computer Science 78:100--111, 2003 (Proc. CATS'03, Computing: the Australasian Theory Symposium; J. Harland, ed.). DOI: 10.1016/S1571-0661(04)81008-9.

[8] J. C. Reynolds. _Syntactic Control of Interference_. In Proc. 5th ACM Symposium on Principles of Programming Languages (POPL), pp. 39--46, 1978.

[9] J.-Y. Girard. _Linear Logic_. Theoretical Computer Science 50(1):1--102, 1987.

[10] J.-Y. Girard, A. Scedrov and P. J. Scott. _Bounded Linear Logic: A Modular Approach to Polynomial-Time Computability_. Theoretical Computer Science 97(1):1--66, 1992.

[11] P. Wadler. _Is There a Use for Linear Logic?_ In Proc. Partial Evaluation and Semantics-Based Program Manipulation (PEPM), 1991.

[12] D. R. Ghica and A. I. Smith. _Bounded Linear Types in a Resource Semiring_. In Programming Languages and Systems (ESOP 2014), LNCS 8410, pp. 331--350, 2014.

[13] T. Petricek, D. Orchard and A. Mycroft. _Coeffects: A Calculus of Context-Dependent Computation_. In Proc. ICFP, pp. 123--135, 2014.

[14] A. Brunel, M. Gaboardi, D. Mazza and S. Zdancewic. _A Core Quantitative Coeffect Calculus_. In Programming Languages and Systems (ESOP 2014), Springer, 2014.

[15] M. Gaboardi, S. Katsumata, D. Orchard, F. Breuvart and T. Uustalu. _Combining Effects and Coeffects via Grading_. In Proc. ICFP, pp. 476--489, 2016.

[16] D. Orchard, V.-B. Liepelt and H. Eades III. _Quantitative Program Reasoning with Graded Modal Types_. Proc. ACM on Programming Languages 3(ICFP), Article 110, 2019.

[17] J. Wood and R. Atkey. _A Framework for Substructural Type Systems_. In Programming Languages and Systems (ESOP 2022), Springer, 2022.
